#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: it => block(above: 1.2em, below: 0.7em)[#it]
#show raw: set text(font: "DejaVu Sans Mono", size: 9pt)

#align(center)[
  #text(size: 17pt)[*Proving the Capla version of `htr3.c`*]

  #v(0.4em)
  #text(size: 10pt)[The plan, cut into tasks for separate agents]
]

#v(1em)

`code/APaul/capla/htr3/htr3.b` is the search of `code/APaul/htr3_new.c` in
Capla, for one line of a table. The goal is a Rocq theorem saying that it
returns the hard-to-round cases: *on a line that satisfies the six
conditions (`line_ok` of `code/exptable9`), every input $x_0 + j u$,
$0 <= j < n$, with $exp(x_0 + j u) slash v$ within $2^(-m)$ of an
integer is in the output of `search`.* The search walks
$j = 0, dots, n - 1$, the half-open $[x_0, x_1)$ of `htr3_new.c`. The
output may hold more
candidates; the theorem is that none is missed.

= What is assumed

- *`WP_sound`*, admitted in Capla itself (`bfrontend/WP.v`): every
  result on a Capla program goes through Capla's weakest-precondition
  calculus, whose soundness is not proved yet.
- *The C driver* `main_htr3.c`: reading the file, $u = "ulp"(x_0)$ by
  `frexp`, printing $x_0 + j u$. The theorem is stated on the numbers of a
  line; that the text of a line means these numbers is `parse_sound` of
  `code/exptable9`, for the Rocq parser, not for the C one.
- *The capacity of the output*: `search` writes the first `cap`
  candidates and returns their number; the theorem assumes the number is
  at most `cap`.

= The program, cut into functions

`htr3.b` is rewritten as five functions, each proved on its own; the
rewritten program must give the same output as `htr3.c` on the tests of
the README.

#table(columns: 2, stroke: 0.4pt, inset: 4pt,
  [function], [what it does, on the flat array $B$ of $k ell$ words],
  [`addw B m ia ib l`], [$B_(i a) arrow.l B_(i a) + B_(i b) mod beta^ell$ (words $[i a, i a + ell)$)],
  [`subw B m ia ib l`], [$B_(i a) arrow.l B_(i a) - B_(i b) mod beta^ell$],
  [`difftab B m k l`], [for $i = 1 .. k - 1$, for $j = k - 1$ down to $i$: `subw` $j$, $j - 1$],
  [`tstep B m k l`], [for $t = 0 .. k - 2$: `addw` $t$, $t + 1$ (`step` is a Capla keyword)],
  [`search B m k l n err out cap`], [`difftab`; top word of $B_0$ += `err`; for $j = 0 .. n - 1$: test, record, `tstep`],
)

= The tasks

Each task is one file with fixed statements (written before the task
starts, with `Admitted`); the agent replaces the `Admitted` by proofs and
may use the statements of the other tasks, not their proofs. All Capla
files build in the opam switch `capla` (Rocq 9.0); with `coq-lsp`
installed there, rocq-mcp can drive them after `rocq_switch`.

#table(columns: 4, stroke: 0.4pt, inset: 4pt,
  [task], [file], [proves], [needs],
  [T0], [`HtrBase.v`, `htr3.v`], [setup (done before the others): the program as a Rocq term, the common definitions (`val`, the coefficient $B_i$ of a flat array, $M = beta^ell$), the list and carry lemmas of `add_proof.v`], [--],
  [T1], [`AddwProof.v`], [`addw_spec`: the words of $B_(i a)$ become $(B_(i a) + B_(i b)) mod M$, the others are unchanged], [T0],
  [T2], [`SubwProof.v`], [`subw_spec`: the same with $-$], [T0],
  [T3], [`DifftabProof.v`], [`difftab_spec`: the coefficients become the differences of the input ones, modulo $M$ (`difftabZ`, a plain function on `list Z` defined in T0)], [T0, T2],
  [T4], [`TstepProof.v`], [`tstep_spec`: the coefficients become `tstepZ` of them modulo $M$ ($B_t + B_(t+1)$, the last one unchanged)], [T0, T1],
  [T5], [`SearchProof.v`], [`search_spec`: the output is the list of the $j < n$ whose top word of $B_0$, after `difftabZ`, the window and $j$ `tstepZ`, is at most $2$ `err`], [T0, T3, T4],
  [T6], [`HtrMath.v`], [no Capla: (a) `difftabZ` of $P(0), dots, P(k-1)$ is the table of differences of $P$ modulo $M$, and $j$ `tstepZ` give $P(j)$ in $B_0$ (from `Shift.v`); (b) the test of `hscan` implies the top-word test (`hscan_exp` scans $j < n$, as the search does); written in `code/APaul/rocq` next to `TaylorLink.v`, in the switch `native`, and carried over by T7], [T0],
  [T7], [port], [`code/APaul/rocq/{Shift, TaylorScan, TaylorReal, TaylorLink}.v`, `HtrMath.v` and the proof files of `code/exptable9` build in the switch `capla` (Rocq 9.0)], [--, then T6],
  [T8], [`HtrFinal.v`], [the theorem of the introduction: from `line_ok` and the hard input, $j$ is in the output of `search`], [T5, T6, T7],
)

T1, T2, T6 and T7 can start at once, after T0; then T3 and T4; then T5;
then T8.

= What each statement says

To be fixed in T0, before the agents start:

- the numbers of a flat array: `coef B i` is the list of the $ell$ words of
  $B_i$, and `vcoef B i := val (coef B i)` its value, least significant word
  first;
- `difftabZ` and `tstepZ` on `list Z`, and the top word
  `top b := (b mod M) / 2^(64 (ell - 1))`;
- for the Capla functions, the shape of `add_spec` (`code/APaul/capla/htr3/proof/add_proof.v`):
  from `eval_funcall ge (Internal f) args e1 (Some result)`, the final
  array in `e1`, its length unchanged, and the numbers it holds.

= Order of the work

+ T0, by hand: the cut of `htr3.b`, its tests, the generated `htr3.v`,
  `HtrBase.v` and the stub files, all compiling in the switch `capla`.
+ Four agents in parallel: T1, T2, T6, T7.
+ Then T3 and T4 in parallel, then T5, then T8.

Estimated, not measured: T1 and T2 are close to the proof of `add`
(91 lines and reusable lemmas); T3 and T5 are the larger ones (nested
loops, calls to proved functions, as `mul_basecase` in Capla's examples);
T6 and T8 are mostly statements.
