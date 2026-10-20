// equiv.mjs: the Elpi facts of the JS walker (jlparse.js, tree-sitter) against
// those of tools/julia2elpi.jl (Julia's parser), and the L0 that jlfront.elpi
// (native elpi) gives from each, on examples/julia/functions.jl and test/cases/*.jl.
//   ELPIDIFF=<elpiDiff dir> JULIA=<julia> node test/equiv.mjs
import { Parser, Language } from 'web-tree-sitter';
import { toFacts } from '../jlparse.js';
import fs from 'fs'; import path from 'path'; import os from 'os';
import { spawnSync } from 'child_process';

const here = path.dirname(new URL(import.meta.url).pathname);
const CODE = process.env.ELPIDIFF || path.resolve(path.dirname(new URL(import.meta.url).pathname), '../..');
const JULIA = process.env.JULIA || path.join(os.homedir(), '.juliaup/bin/julia');
await Parser.init();
const parser = new Parser();
parser.setLanguage(await Language.load(path.join(here, '../vendor/tree-sitter-julia.wasm')));

const files = [path.join(CODE, 'examples/julia/functions.jl'),
  ...fs.readdirSync(path.join(here, 'cases')).filter(f => f.endsWith('.jl')).sort().map(f => path.join(here, 'cases', f))];
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'jleq-'));
const body = t => t.split('\n').slice(1).join('\n');   // the facts, without the header comment

function front(facts, name) {               // native jlfront.elpi: the L0, or its refusal
  const d = fs.mkdtempSync(path.join(tmp, 'c'));
  fs.writeFileSync(path.join(d, 'ast.elpi'), facts);
  const r = spawnSync('elpi', ['-I', path.join(CODE, 'elpi'), '-I', d, path.join(CODE, 'elpi', 'front', 'jlfront.elpi'), '-exec', 'jl-to-l0', '--', name], { encoding: 'utf8' });
  if (r.status === 0) return 'L0 ' + r.stdout.replace(/\nSuccess:[\s\S]*$/, '').trim();
  const m = /Fatal error:\s*([\s\S]*)/.exec(r.stdout + r.stderr);
  return 'REFUSED ' + (m ? m[1].trim().replace(/\s+/g, ' ') : (r.stdout + r.stderr).trim().split('\n').slice(-2).join(' '));
}

let bad = 0;
for (const f of files) {
  const name = path.basename(f);
  const jl = spawnSync(JULIA, ['--startup-file=no', path.join(CODE, 'tools/julia2elpi.jl'), f], { encoding: 'utf8' });
  const src = fs.readFileSync(f, 'utf8');
  let js, jsErr = null;
  try { js = toFacts(parser, src, name).text; } catch (e) { jsErr = e.message; }
  if (jl.status !== 0 || jsErr) {
    const ok = jl.status !== 0 && jsErr;
    if (!ok) bad++;
    console.log(`${ok ? 'ok  ' : 'FAIL'} ${name}: syntax error: julia ${jl.status !== 0 ? 'yes' : 'no'}, walker ${jsErr ? 'yes (' + jsErr + ')' : 'no'}`);
    continue;
  }
  const same = body(js) === body(jl.stdout);
  const nfun = (js.match(/^jl-function/mg) || []).length;
  if (!same) {
    bad++;
    fs.writeFileSync(path.join(tmp, name + '.jl.elpi'), jl.stdout); fs.writeFileSync(path.join(tmp, name + '.js.elpi'), js);
    console.log(`FAIL ${name}: facts differ: diff ${tmp}/${name}.{jl,js}.elpi`);
  }
  const a = front(jl.stdout, name), b = front(js, name);
  if (a !== b) { bad++; console.log(`FAIL ${name}: jlfront differs:\n  julia:  ${a.slice(0, 300)}\n  walker: ${b.slice(0, 300)}`); continue; }
  if (same) console.log(`ok   ${name}: ${nfun} function(s), identical facts; jlfront: ${a.startsWith('L0') ? 'same L0' : a}`);
}
console.log(bad ? `${bad} failure(s)` : `all ${files.length} files agree`);
process.exit(bad ? 1 : 0);
