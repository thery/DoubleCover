// pipeline.js: the elpiDiff Julia pipeline on Elpi-in-wasm, shared by the page
// (app.js) and the node tests.
//   Julia text --jlparse.js--> jl-function facts --jlfront.elpi (jl-to-l0)--> L0
//   L0 --adjudge.elpi + jsdrive.elpi (js-to-julia)--> the tangent / adjoint Julia code
// E is the Elpi API of elpijs (globalThis.elpi), parser a tree-sitter parser
// for Julia.

import { toFacts, JlSyntaxError } from './jlparse.js';

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

// run: one click. Returns
//   { stage: 'syntax' | 'front' | 'done', message, facts, l0,
//     modes: { tangent: { code, refused: [..] }, adjoint: ... }, ms: {...} }
export function run(E, base, parser, source, modes, name = 'editor') {
  const ms = {}, res = { modes: {}, ms };
  let t = now();
  try {
    const { text, count } = toFacts(parser, source, name + '.jl');
    res.facts = text;
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
