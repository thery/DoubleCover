// jlparse.js: Julia source -> the Elpi facts `jl-function E` of elpiDiff's
// tools/julia2elpi.jl, in the browser, with tree-sitter-julia instead of Julia.
//
// julia2elpi.jl prints Julia's AST (Meta.parseall) untouched: an Expr is
// `j Head [Args]` (LineNumberNodes dropped), a Symbol `jsym`, a literal `jint`,
// `jfloat` (Julia's repr), `jbool`, anything else `jother` (its repr). This
// module walks tree-sitter's concrete syntax tree and rebuilds the same Expr:
// same heads, same argument order, the same folding of `-1` into a literal,
// the same n-ary `+` and `*`, chained comparisons, `elseif` conditions wrapped
// in a block, short function bodies wrapped in a block. It decides nothing
// about what the code means: that is jlfront.elpi's job, which refuses what L0
// cannot express with its own reason.
//
//   toFacts(parser, source, name) -> { text, count }   or throws JlSyntaxError

export class JlSyntaxError extends Error {}

// ---------------------------------------------------------------------------
// Terms (as julia2elpi.jl prints them)

const J = (h, a) => ({ k: 'j', h, a });
const sym = s => ({ k: 'jsym', s });
const int = s => ({ k: 'jint', s });
const flt = s => ({ k: 'jfloat', s });
const bool = s => ({ k: 'jbool', s });
const other = s => ({ k: 'jother', s });

const q = s => '"' + s.replace(/\\/g, '\\\\').replace(/"/g, '\\"') + '"';

export function termText(t, ind = '') {
  if (t.k !== 'j') return `${t.k} ${q(t.s)}`;
  if (t.a.length === 0) return `j ${q(t.h)} []`;
  const sub = t.a.map(a => ind + '  ' + termText(a, ind + '  ')).join(',\n');
  return `j ${q(t.h)} [\n${sub}]`;
}

// ---------------------------------------------------------------------------
// Literals, printed as Julia prints them

// shortest round-trip digits and the position of the point (Ryu's output)
function shortest(v, f32) {
  let s;
  if (!f32) s = v.toExponential();
  else for (let p = 1; p <= 9; p++) {
    s = v.toExponential(p - 1);
    if (Math.fround(Number(s)) !== v) continue;
    // toExponential rounds a tie up; Ryu takes the even neighbour
    const [m0, e0] = s.split('e'), d = m0.replace('.', '');
    if (d.at(-1) % 2 === 1 && d.at(-1) !== '0') {
      const lower = (BigInt(d) - 1n).toString();
      if (lower.length === d.length) {
        const t = lower[0] + (lower.length > 1 ? '.' + lower.slice(1) : '') + 'e' + e0;
        if (Math.fround(Number(t)) === v && Math.abs(Number(t) - v) === Math.abs(Number(s) - v)) s = t;
      }
    }
    break;
  }
  const [m, e] = s.split('e');
  return { digits: m.replace('.', ''), pt: parseInt(e, 10) + 1 };
}

// Julia's repr of a Float64 (Base.Ryu.writeshortest), or of a Float32 with f32
export function juliaFloat(v, f32 = false) {
  const suffix = f32 ? 'f0' : '';
  if (Number.isNaN(v)) return f32 ? 'NaN32' : 'NaN';
  if (!Number.isFinite(v)) return (v < 0 ? '-' : '') + (f32 ? 'Inf32' : 'Inf');
  if (v === 0) return (Object.is(v, -0) ? '-0.0' : '0.0') + suffix;
  const sign = v < 0 ? '-' : '';
  const { digits, pt } = shortest(Math.abs(v), f32);
  const n = digits.length;
  let out;
  if (-4 < pt && pt <= 6) {
    if (pt <= 0) out = '0.' + '0'.repeat(-pt) + digits;
    else if (pt < n) out = digits.slice(0, pt) + '.' + digits.slice(pt);
    else out = digits + '0'.repeat(pt - n) + '.0';
    out += suffix;
  } else {
    out = digits[0] + '.' + (n > 1 ? digits.slice(1) : '0') + (f32 ? 'f' : 'e') + (pt - 1);
  }
  return sign + out;
}

function floatLit(text, neg) {
  let t = text.replace(/_/g, '');
  let f32 = false;
  if (!/^0x/i.test(t) && /f/.test(t)) { f32 = true; t = t.replace('f', 'e'); }
  let v = /^0x/i.test(t) ? hexFloat(t) : Number(t);
  if (f32) v = Math.fround(v);
  return flt(juliaFloat(neg ? -v : v, f32));
}

function hexFloat(t) {                    // 0x1.8p3
  const m = /^0x([0-9a-f]*)(?:\.([0-9a-f]*))?p([+-]?\d+)$/i.exec(t);
  if (!m) return NaN;
  const frac = m[2] || '';
  return parseInt((m[1] || '0') + frac, 16) * Math.pow(2, parseInt(m[3], 10) - 4 * frac.length);
}

// an integer literal: julia2elpi.jl prints string(x), the decimal value
function intLit(text, neg) {
  const t = text.replace(/_/g, '');
  const v = /^0[xob]/i.test(t) ? BigInt(t) : BigInt(t.replace(/^0+(?=\d)/, ''));
  return int((neg ? '-' : '') + v.toString());
}

// ---------------------------------------------------------------------------
// The tree

const COMMENT = new Set(['line_comment', 'block_comment']);

function named(n) {
  const r = [];
  for (let i = 0; i < n.childCount; i++) {
    const c = n.child(i);
    if (c && c.isNamed && !COMMENT.has(c.type)) r.push(c);
  }
  return r;
}

// the statements of a node that holds a block: its named children but the
// signature, condition, bindings and the else/elseif clauses
const NOT_STMT = new Set(['signature', 'for_binding', 'else_clause', 'elseif_clause', 'catch_clause',
  'finally_clause', 'let_binding']);
function stmts(n) {
  const r = [];
  for (let i = 0; i < n.childCount; i++) {
    const c = n.child(i);
    if (!c || !c.isNamed || COMMENT.has(c.type) || NOT_STMT.has(c.type)) continue;
    const f = n.fieldNameForChild(i);
    if (f === 'condition' || f === 'alternative') continue;
    r.push(c);
  }
  return r;
}
const block = ns => J('block', ns.map(ex));

function fail(n, msg) {
  const p = n.startPosition;
  throw new JlSyntaxError(`line ${p.row + 1}, column ${p.column + 1}: ${msg}`);
}

const COMPARISON = new Set(['<', '>', '<=', '>=', '==', '!=', '===', '!==', '≤', '≥', '≠', '≡', '≢',
  '<:', '>:', 'in', 'isa', '∈', '∉', '∋', '∌', '⊆', '⊈', '⊂', '⊄', '⊊', '⊇', '⊉', '⊃', '⊅', '⊋']);

function opOf(n) {
  const k = named(n).find(c => c.type === 'operator');
  if (k) return k.text;
  for (let i = 0; i < n.childCount; i++) if (!n.child(i).isNamed) return n.child(i).type;
  return '?';
}
const operands = n => named(n).filter(c => c.type !== 'operator');

// x op y op z, left-nested in the tree, flattened while the operator is the same
// (a parenthesized operand is a parenthesized_expression: never flattened)
function chain(n, sameOp) {
  const [l, r] = operands(n);
  const left = l.type === 'binary_expression' && sameOp(opOf(l)) ? chain(l, sameOp) : [l];
  return [...left, { op: opOf(n) }, r];
}

function binary(n) {
  const op = opOf(n);
  if (op === '&&' || op === '||') {          // right-nested in Julia
    const xs = chain(n, o => o === op).filter(x => !x.op).map(ex);
    return xs.reduceRight((acc, x) => J(op, [x, acc]));
  }
  if (COMPARISON.has(op)) {
    const xs = chain(n, o => COMPARISON.has(o));
    if (xs.length === 3) {
      const [a, , b] = xs;
      return op === '<:' || op === '>:' ? J(op, [ex(a), ex(b)]) : J('call', [sym(op), ex(a), ex(b)]);
    }
    return J('comparison', xs.map(x => x.op ? sym(x.op) : ex(x)));
  }
  if (op === '+' || op === '*') {            // n-ary in Julia
    const xs = chain(n, o => o === op).filter(x => !x.op);
    return J('call', [sym(op), ...xs.map(ex)]);
  }
  if (op === '=>' ) return J('call', [sym(op), ...operands(n).map(ex)]);
  const [a, b] = operands(n);
  return J('call', [sym(op), ex(a), ex(b)]);
}

// -1, +1.5, -2x: a sign written against a number literal is part of it
function unary(n) {
  const opn = named(n).find(c => c.type === 'operator') || n.child(0);
  const op = opn.text;
  const x = operands(n)[0];
  const glued = x && opn.endIndex === x.startIndex;
  if ((op === '-' || op === '+') && glued) {
    const neg = op === '-';
    if (x.type === 'integer_literal') return intLit(x.text, neg);
    if (x.type === 'float_literal') return floatLit(x.text, neg);
    if (x.type === 'juxtaposition_expression') {
      const [a, b] = named(x);
      if (a.type === 'integer_literal' || a.type === 'float_literal')
        return J('call', [sym('*'), a.type === 'integer_literal' ? intLit(a.text, neg) : floatLit(a.text, neg), ex(b)]);
    }
  }
  return J('call', [sym(op), ex(x)]);
}

// arguments of a call: positional and keyword ones, then those after `;`
function args(list) {
  const pos = [], params = [];
  let semi = false;
  for (let i = 0; i < list.childCount; i++) {
    const c = list.child(i);
    if (!c.isNamed) { if (c.type === ';') semi = true; continue; }
    if (COMMENT.has(c.type)) continue;
    (semi ? params : pos).push(c.type === 'named_argument' ? kw(c) : ex(c));
  }
  return semi ? [J('parameters', params), ...pos] : pos;
}
function kw(n) { const [a, b] = operands(n); return J('kw', [ex(a), ex(b)]); }

// f(x) = e, f(x) where T = e, f(x)::T = e: a function, whose body is a block
const isSig = n => n.type === 'call_expression' || n.type === 'where_expression' ||
  (n.type === 'typed_expression' && ['call_expression', 'where_expression'].includes(named(n)[0].type));

function assignment(n) {
  const [l, r] = operands(n);
  if (isSig(l)) return J('=', [ex(l), r.type === 'compound_statement' ? block(stmts(r)) : J('block', [ex(r)])]);
  return J('=', [ex(l), ex(r)]);
}

function ifClause(n, head) {
  const c = n.childForFieldName('condition');
  const alts = [];
  for (let i = 0; i < n.childCount; i++) if (n.fieldNameForChild(i) === 'alternative') alts.push(n.child(i));
  const cond = head === 'elseif' ? J('block', [ex(c)]) : ex(c);
  const rest = [];
  if (alts.length) {
    const [a, ...more] = alts;
    if (a.type === 'elseif_clause') rest.push(elseifChain(a, more));
    else rest.push(block(stmts(a)));
  }
  return J(head, [cond, block(stmts(n)), ...rest]);
}
// tree-sitter lists the elseif and else clauses side by side; Julia nests them
function elseifChain(a, more) {
  const c = a.childForFieldName('condition');
  const rest = [];
  if (more.length) {
    const [b, ...more2] = more;
    rest.push(b.type === 'elseif_clause' ? elseifChain(b, more2) : block(stmts(b)));
  }
  return J('elseif', [J('block', [ex(c)]), block(stmts(a)), ...rest]);
}

function forStmt(n) {
  const bs = named(n).filter(c => c.type === 'for_binding').map(b => {
    const [v, it] = operands(b);
    return J('=', [ex(v), ex(it)]);
  });
  return J('for', [bs.length === 1 ? bs[0] : J('block', bs), block(stmts(n))]);
}

function range(n) {
  const [a, b] = named(n);
  const left = a.type === 'range_expression' ? range(a).a.slice(1) : [ex(a)];
  return J('call', [sym(':'), ...left, ex(b)]);
}

function stringLit(n) {
  const parts = named(n);
  if (!parts.some(p => p.type === 'string_interpolation')) return other(n.text);
  return J('string', parts.map(p => p.type === 'string_interpolation' ? ex(named(p)[0]) : other(JSON.stringify(p.text))));
}

function ex(n) {
  if (n.isMissing) fail(n, `missing ${n.type}`);
  if (n.type === 'ERROR') fail(n, 'syntax error');
  const ks = () => named(n);
  switch (n.type) {
    case 'identifier': case 'operator': return sym(n.text);
    case 'integer_literal': return intLit(n.text, false);
    case 'float_literal': return floatLit(n.text, false);
    case 'boolean_literal': return bool(n.text);
    case 'string_literal': return stringLit(n);
    case 'character_literal': return other(n.text);
    case 'quote_expression': return other(':(' + n.text + ')');
    case 'parenthesized_expression': {
      const k = ks();
      return k.length === 1 ? ex(k[0]) : block(k);
    }
    case 'binary_expression': return binary(n);
    case 'unary_expression': return unary(n);
    case 'juxtaposition_expression': return J('call', [sym('*'), ...ks().map(ex)]);
    case 'ternary_expression': return J('if', ks().map(ex));
    case 'call_expression': {
      const [f, list, ...more] = ks();
      if (more.length) fail(more[0], 'do-blocks are not supported');
      return J('call', [ex(f), ...args(list)]);
    }
    case 'broadcast_call_expression': {
      const [f, list] = ks();
      return J('.', [ex(f), J('tuple', args(list))]);
    }
    case 'index_expression': {
      const [a, v] = ks();
      return J('ref', [ex(a), ...named(v).map(ex)]);
    }
    case 'field_expression': {
      const [a, b] = ks();
      return J('.', [ex(a), other(':(:' + b.text + ')')]);
    }
    case 'range_expression': return range(n);
    case 'typed_expression': return J('::', ks().map(ex));
    case 'parametrized_type_expression': {
      const [a, c] = ks();
      return J('curly', [ex(a), ...named(c).map(ex)]);
    }
    case 'curly_expression': return J('braces', ks().map(ex));
    case 'where_expression': {
      const [a, b] = ks();
      return J('where', [ex(a), ...(b.type === 'curly_expression' ? named(b).map(ex) : [ex(b)])]);
    }
    case 'tuple_expression': case 'open_tuple': return J('tuple', ks().map(ex));
    case 'vector_expression': return J('vect', ks().map(ex));
    case 'splat_expression': return J('...', ks().map(ex));
    case 'adjoint_expression': return J("'", ks().map(ex));
    case 'arrow_function_expression': {
      const [a, b] = ks();
      return J('->', [ex(a), J('block', [ex(b)])]);
    }
    case 'macrocall_expression': {
      const [m, ...rest] = ks();
      const as = rest.flatMap(r => r.type === 'macro_argument_list' ? named(r) : [r]);
      return J('macrocall', [sym(m.text), ...as.map(ex)]);
    }
    case 'assignment': return assignment(n);
    case 'compound_assignment_expression': {
      const [a, b] = operands(n);
      return J(opOf(n), [ex(a), ex(b)]);
    }
    case 'compound_statement': return block(stmts(n));
    case 'if_statement': return ifClause(n, 'if');
    case 'for_statement': return forStmt(n);
    case 'while_statement': return J('while', [ex(n.childForFieldName('condition')), block(stmts(n))]);
    case 'return_statement': {
      const k = ks();
      return J('return', [k.length ? ex(k[0]) : other('nothing')]);
    }
    case 'local_statement': return J('local', ks().map(ex));
    case 'global_statement': return J('global', ks().map(ex));
    case 'const_statement': return J('const', ks().map(ex));
    case 'break_statement': return J('break', []);
    case 'continue_statement': return J('continue', []);
    case 'let_statement': return J('let', [J('block', []), block(stmts(n))]);
    case 'try_statement': return J('try', [block(stmts(n))]);
    case 'function_definition': return functionDef(n);
    default:
      // unknown to this walker: an Expr with tree-sitter's name for it, which
      // jlfront.elpi refuses as an unsupported construct or expression
      return J(n.type.replace(/_(expression|statement)$/, ''), ks().map(ex));
  }
}

function functionDef(n) {
  const sig = named(n).find(c => c.type === 'signature');
  const s = sig && named(sig)[0];
  if (!s) fail(n, 'a function without a signature');
  if (s.type === 'identifier') return J('function', [sym(s.text)]);
  return J('function', [ex(s), block(stmts(n))]);
}

// the top-level functions, as julia2elpi.jl's isfunction selects them
const isFunction = n => n.type === 'function_definition' ||
  (n.type === 'assignment' && ['call_expression', 'where_expression'].includes(named(n)[0].type));

function firstError(n) {
  if (n.type === 'ERROR' || n.isMissing) return n;
  if (!n.hasError) return null;
  for (let i = 0; i < n.childCount; i++) { const e = firstError(n.child(i)); if (e) return e; }
  return n;
}

export function toTerms(parser, source) {
  const tree = parser.parse(source);
  try {
    const root = tree.rootNode;
    const e = firstError(root);
    if (e) {
      const near = e.text.split('\n')[0].slice(0, 40);
      fail(e, e.isMissing ? `syntax error: missing ${e.type}` : `syntax error near \`${near}\``);
    }
    return named(root).filter(isFunction).map(ex);
  } finally { tree.delete(); }
}

export function toFacts(parser, source, name = 'input.jl') {
  const ts = toTerms(parser, source);
  const lines = [`% the functions of ${name}, parsed by tree-sitter-julia (jlparse.js)`];
  for (const t of ts) lines.push(`jl-function (${termText(t, '')}).`);
  return { text: lines.join('\n') + '\n', count: ts.length };
}
