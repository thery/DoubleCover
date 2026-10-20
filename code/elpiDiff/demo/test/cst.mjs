// cst.mjs FILE.jl: prints tree-sitter-julia's CST of FILE (named nodes, with field names)
import { Parser, Language } from 'web-tree-sitter';
import fs from 'fs';
const here = new URL('..', import.meta.url).pathname;
await Parser.init();
const lang = await Language.load(here + 'node_modules/tree-sitter-julia/tree-sitter-julia.wasm');
const p = new Parser(); p.setLanguage(lang);
const src = fs.readFileSync(process.argv[2], 'utf8');
const t = p.parse(src);
function pr(n, ind, field) {
  const f = field ? field + ': ' : '';
  const txt = n.childCount === 0 ? ' ' + JSON.stringify(n.text) : '';
  console.log(ind + f + (n.isNamed ? n.type : JSON.stringify(n.type)) + txt + (n.hasError ? ' !ERR' : ''));
  for (let i = 0; i < n.childCount; i++) pr(n.child(i), ind + '  ', n.fieldNameForChild(i));
}
pr(t.rootNode, '', null);
