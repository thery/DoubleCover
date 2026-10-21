// pipeline.mjs: the page's pipeline (pipeline.js: jlparse.js + Elpi in wasm) under
// node, against the native pipeline (native.sh: julia2elpi.jl + native elpi), on
// every example of the menu and on examples/julia/functions.jl, and on a few
// choices of passive arguments (the same jl-passive facts on both sides). The generated
// files must be byte-identical after their first line (which names the source).
//   node test/pipeline.cjs
import { Parser, Language } from 'web-tree-sitter';
import { loadElpi, run } from '../pipeline.js';
import { EXAMPLES } from '../examples.js';
import fs from 'fs'; import path from 'path'; import os from 'os';
import { spawnSync } from 'child_process';

const here = path.dirname(new URL(import.meta.url).pathname);
const demo = path.join(here, '..');
const CODE = process.env.ELPIDIFF || path.resolve(path.dirname(new URL(import.meta.url).pathname), '../..');
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'jlpipe-'));

// run through pipeline.cjs, which loads the bundle
let t = globalThis.ELPI_T0;
while (!globalThis.elpi) await new Promise(r => setTimeout(r, 5));
const E = globalThis.elpi;
const tBundle = performance.now() - t;
t = performance.now();
const base = await loadElpi(E, f => fs.promises.readFile(path.join(demo, 'elpi', f), 'utf8'));
const tCompile = performance.now() - t;
await Parser.init();
const parser = new Parser();
parser.setLanguage(await Language.load(path.join(demo, 'vendor/tree-sitter-julia.wasm')));
console.log(`node: wasm bundle ${tBundle.toFixed(0)} ms, Elpi sources compiled ${tCompile.toFixed(0)} ms`);

const cases = EXAMPLES.map(e => ({ name: e.name.split(' ')[0], code: e.code }));
const fjl = fs.readFileSync(path.join(CODE, 'examples/julia/functions.jl'), 'utf8');
cases.push({ name: 'functions.jl', code: fjl });
// passive arguments: what the page's checkboxes give (pairs [function, argument])
cases.push({ name: 'functions.jl', code: fjl, passive: [['f', 'x2'], ['transcend', 'y'], ['advect!', 'c'], ['damped', 'nu']] });
cases.push({ name: 'functions.jl', code: fjl, passive: [['xsin', 'x'], ['sumsq', 'x'], ['square_scaled!', 'x']] });
cases.push({ name: 'functions.jl', code: fjl, passive: [['branch', 'p']] });            // an Int: refused
cases.push({ name: 'functions.jl', code: fjl, passive: [['advect!', 'u']] });           // written: refused
const tail = s => s.split('\n').slice(1).join('\n');
let bad = 0;
for (const c of cases) {
  const src = path.join(tmp, c.name.replace(/[^A-Za-z0-9_.]/g, '_') + (c.name.endsWith('.jl') ? '' : '.jl'));
  fs.writeFileSync(src, c.code);
  const spec = (c.passive || []).map(([f, x]) => f + ':' + x).join(',');
  if (spec) c.name += ` (passive ${spec})`;
  const out = src + (spec ? '.' + spec.replace(/[^A-Za-z0-9_]/g, '_') : '') + '.out';
  spawnSync('sh', [path.join(here, 'native.sh'), src, out, spec], { stdio: 'inherit' });
  const r = run(E, base.id, parser, c.code, ['tangent', 'adjoint-value'], 'editor', c.passive || []);
  const times = Object.entries(r.ms).map(([k, v]) => `${k} ${v.toFixed(0)}`).join(', ');
  if (fs.existsSync(path.join(out, 'refused.txt'))) {
    const want = fs.readFileSync(path.join(out, 'refused.txt'), 'utf8').trim();
    const ok = r.stage === 'front' && r.message === want;
    if (!ok) bad++;
    console.log(`${ok ? 'ok  ' : 'FAIL'} ${c.name}: refused by jlfront: native "${want}", wasm "${r.message}" (${times} ms)`);
    continue;
  }
  const same = [];
  for (const m of ['tangent', 'adjoint-value']) {
    const want = fs.readFileSync(path.join(out, m + '.jl'), 'utf8');
    const got = r.modes[m] ? r.modes[m].code : '';
    if (tail(want) === tail(got)) same.push(m); else { bad++; fs.writeFileSync(path.join(out, m + '.wasm.jl'), got); console.log(`FAIL ${c.name} ${m}: diff ${out}/${m}.jl ${out}/${m}.wasm.jl`); }
  }
  const l0 = fs.readFileSync(path.join(out, 'primal.elpi'), 'utf8');
  const l0same = tail(l0).trim() === tail(r.l0).trim();
  if (!l0same) { bad++; console.log(`FAIL ${c.name}: L0 differs`); }
  console.log(`${same.length === 2 && l0same ? 'ok  ' : 'FAIL'} ${c.name}: L0 ${l0same ? 'identical' : 'DIFFERENT'}, identical: ${same.join(' ') || 'none'} (${times} ms)`);
}
// the committed outputs of run.sh, for functions.jl
const r = run(E, base.id, parser, fs.readFileSync(path.join(CODE, 'examples/julia/functions.jl'), 'utf8'), ['tangent', 'adjoint-value']);
for (const m of ['tangent', 'adjoint-value']) {
  const ok = tail(fs.readFileSync(path.join(CODE, 'examples/julia/out', m + '.jl'), 'utf8')) === tail(r.modes[m].code);
  if (!ok) bad++;
  console.log(`${ok ? 'ok  ' : 'FAIL'} functions.jl ${m}: ${ok ? 'identical to' : 'differs from'} examples/julia/out/${m}.jl`);
}
console.log(bad ? `${bad} failure(s)` : 'all identical');
process.exit(bad ? 1 : 0);
