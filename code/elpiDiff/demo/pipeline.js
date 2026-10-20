// pipeline.js: the elpiDiff Julia pipeline on Elpi-in-wasm, shared by the page
// (app.js) and the node tests.
//   Julia text --jlparse.js--> jl-function facts --jlfront.elpi (jl-to-l0)--> L0
//   L0 --adjudge.elpi + jsdrive.elpi (js-to-julia)--> the tangent / adjoint Julia code
// E is the Elpi API of elpijs (globalThis.elpi), parser a tree-sitter parser
// for Julia.

import { toFacts, toTerms, JlSyntaxError } from './jlparse.js';

const now = () => performance.now();

// compiles the static program once: every file of files.json, main demo.elpi
export async function loadElpi(E, getText) {
  const files = JSON.parse(await getText('files.json'));
  const texts = await Promise.all(files.map(getText));
  files.forEach((f, i) => E.addFile(f, texts[i]));
  const r = E.load('demo.elpi');
  if (!r.ok) throw new Error('compiling the Elpi sources failed: ' + r.msg);
  return r;
}

// the message of std.fatal-error (halt prints the string term, quoted)
export function elpiMessage(r) {
  let m = (r.msg || '').trim();
  const s = /^"([\s\S]*)"$/.exec(m);
  if (s) m = s[1].replace(/\\"/g, '"').replace(/\\\\/g, '\\');
  m = m.replace(/\s*\n\s*/g, ' ');
  return m || (r.err || '').trim() || 'the query failed';
}

// ---------------------------------------------------------------------------
// The arguments of each function, for the choice of what is differentiated.
// The same reading of the types as jlfront.elpi (param-type): a real (no
// annotation, Real, Float64, …) or an array (SVector, MVector, SizedVector)
// can be made passive; an Int or a Bool is passive already; an array the
// function writes (`y[i] = …` or `y = …` anywhere in the body) is its output.
// argumentsOf(parser, source) -> [{ fn, args: [{ name, choosable, reason }] }]
// (fn as in the source, with its !), or null when the code does not parse.

const REALS = ['Real', 'Float64', 'Float32', 'Number', 'AbstractFloat'];
const INTS = ['Int', 'Int64', 'Int32', 'Integer'];
const ARRAYS = ['SVector', 'MVector', 'SizedVector'];

function assignedIn(t, out) {
  if (t.k !== 'j') return out;
  if (['=', '+=', '-=', '*=', '/='].includes(t.h) && t.a.length === 2) {
    const l = t.a[0];
    if (l.k === 'jsym') out.add(l.s);
    else if (l.k === 'j' && l.h === 'ref' && l.a[0] && l.a[0].k === 'jsym') out.add(l.a[0].s);
  }
  for (const a of t.a) assignedIn(a, out);
  return out;
}

function argument(p, written) {
  if (p.k === 'jsym') return { name: p.s, choosable: true, reason: 'real' };
  if (p.k !== 'j' || p.h !== '::' || !p.a[0] || p.a[0].k !== 'jsym') return null;
  const name = p.a[0].s, ty = p.a[1];
  if (ty.k === 'jsym' && REALS.includes(ty.s)) return { name, choosable: true, reason: 'real' };
  if (ty.k === 'jsym' && INTS.includes(ty.s)) return { name, choosable: false, reason: 'Int: never differentiated' };
  if (ty.k === 'jsym' && ty.s === 'Bool') return { name, choosable: false, reason: 'Bool: never differentiated' };
  if (ty.k === 'j' && ty.h === 'curly' && ty.a[0] && ARRAYS.includes(ty.a[0].s))
    return written.has(name) ? { name, choosable: false, reason: 'written: its derivative is the output' }
                             : { name, choosable: true, reason: 'array' };
  return { name, choosable: false, reason: 'unsupported type' };
}

export function argumentsOf(parser, source) {
  let ts;
  try { ts = toTerms(parser, source); } catch (e) { if (e instanceof JlSyntaxError) return null; throw e; }
  const fns = [];
  for (const t of ts) {
    let sig = t.a[0];
    while (sig && sig.k === 'j' && sig.h === 'where') sig = sig.a[0];
    if (!sig || sig.k !== 'j' || sig.h !== 'call' || !sig.a[0] || sig.a[0].k !== 'jsym') continue;
    const written = t.a[1] ? assignedIn(t.a[1], new Set()) : new Set();
    fns.push({ fn: sig.a[0].s, args: sig.a.slice(1).map(p => argument(p, written)).filter(a => a) });
  }
  return fns;
}

// the facts of a choice: passive = [[fn, arg], ...]
export const passiveFacts = passive =>
  passive.map(([f, x]) => `jl-passive "${f}" "${x}".\n`).join('');

// run: one click; passive: the arguments made passive, [[fn, arg], ...]. Returns
//   { stage: 'syntax' | 'front' | 'done', message, facts, l0,
//     modes: { tangent: { code, refused: [..] }, adjoint: ... }, ms: {...} }
export function run(E, base, parser, source, modes, name = 'editor', passive = []) {
  const ms = {}, res = { modes: {}, ms };
  let t = now();
  try {
    const { text, count } = toFacts(parser, source, name + '.jl');
    res.facts = text + passiveFacts(passive);
    if (count === 0) return { ...res, stage: 'syntax', message: 'no function definition found (write `function f(x) … end` or `f(x) = …`)' };
  } catch (e) {
    if (e instanceof JlSyntaxError) return { ...res, stage: 'syntax', message: e.message };
    throw e;
  } finally { ms.parse = now() - t; }

  t = now();
  const a = E.extend(base, 'ast.elpi', res.facts);
  if (!a.ok) throw new Error('adding the facts failed: ' + a.msg);
  const q = E.query(a.id, `jl-to-l0 ["${name}.jl"].`);
  ms.front = now() - t;
  if (!q.ok) return { ...res, stage: 'front', message: elpiMessage(q) };
  res.l0 = q.out;

  t = now();
  const p = E.extend(base, 'primal.elpi', q.out.replace(/^accumulate adjudge\.$/m, ''));
  if (!p.ok) throw new Error('adding the L0 program failed: ' + p.msg);
  ms.l0load = now() - t;
  for (const m of modes) {
    t = now();
    const r = E.query(p.id, `js-to-julia ["${name}", "${m}"].`);
    ms[m] = now() - t;
    if (!r.ok) { res.modes[m] = { code: '', refused: [], error: elpiMessage(r) }; continue; }
    const refused = r.err.split('\n').filter(l => l.startsWith('# refused: ')).map(l => l.slice(11));
    res.modes[m] = { code: r.out, refused };
  }
  return { ...res, stage: 'done' };
}
