# Restyling Stdlib proofs to ssreflect

Rules used for `TangentTop_math.v`, `TangentLoops_math.v`, `TangentMode_math.v`,
`TangentGood_math.v` and `TangentCorrect_math.v` (the ssreflect versions of the
corresponding files): statements, names, comments and order unchanged, every proof
ends with `Qed`, Stdlib types and lemmas (list, Z, Reals) kept, no mathcomp library,
only the ssreflect tactic language.

## Import

After the existing imports, add:

    From Corelib Require Import ssreflect ssrbool ssrfun.
    Set Bullet Behavior "None".

Add both lines in each file you restyle. The second line is what mathcomp's own
`boot/ssreflect.v` does (`Global Set Bullet Behavior "None"`); Corelib's ssreflect does
not set it. It makes bullets mere markers, so easy cases can be bulleted and the last
case continued unbulleted (see Layout). Without it, a tactic after a finished bullet fails
with "No such goal. Focus next goal with bullet -".

The ssreflect import changes `rewrite`, `case`, `elim` and `set` for the
whole file, so every proof in that file has to compile under the ssreflect semantics.
For example, `rewrite A, B` and `rewrite ... by tac` become syntax errors.
`ssrfun` provides `erefl`.

## Layout (mathcomp style)

Reference: the proofs of `mathcomp/boot` (`seq.v`, `ssrnat.v`, `fintype.v`) in
`~/opam-rocq.9.1.0/native/lib/coq/user-contrib/mathcomp/boot/`.

- The proof script starts at column 0; one-line proofs are `Proof. by ... Qed.`
- No `{ ... }` blocks. A local fact is `have H : P.` followed by its proof indented
  by 2 spaces, whose last line closes it (`by ...`, `exact: ...`); or
  `have H : P by tac.` on one line. The main proof continues at the outer indentation.
- When a tactic leaves several goals, close the side ones first, indented by 2, each
  ended by a `by` line, then continue the main one unindented. Order the goals with
  `last first` / `last 2 first` / `first last` so that the hard case is the last one
  (`case Eo: (owner wP PTop) => [o |]; last first.` + `  by case: ...`).
- Bullets for case splits with several short cases, typically one line each
  (`- by ...`); the last (main) case continues unbulleted. This relies on
  `Set Bullet Behavior "None"`.
- Inside a `have` proof, bullets are fine too (they are only markers).
- Lines within 80 columns in proofs (statements are kept as in the original file,
  even when longer). Break long `have` statements after `/\` or `->`, and long
  intro patterns with an extra `have [..] := Hrest.`
- Descriptive hypothesis names (`sz_m`, `def_s1`, `ne_xy`, `IHs`) are welcome when they
  help; when restyling, keeping the original names is fine.

## Idioms

| Stdlib | ssreflect |
|---|---|
| `intros x H` | `move=> x H` |
| `revert x` / `induction l; intros t` | `elim: l t => [|a l IH] t` |
| `destruct x as [a|b]` | `case: x => [a|b]` |
| `destruct (e) eqn:E` | `case E: (e) => [..]` |
| `induction H` (H : Forall2/Forall ...) | `elim: H args => [|...]` |
| `induction 1` | `elim=> [|...]` |
| induction on `Forall P (rev L)` (index not a variable) | `move: H; elim: (rev L) => [|p AL IH] //= /Forall_cons_iff [Hg /IH {}IH]` |
| `rewrite A, <- B` | `rewrite A -B` |
| `rewrite L by tac` | `rewrite L; first by tac` (side goals come first), `rewrite L //`, or pass the premises `rewrite (L _ H)` |
| `unfold d` / `unfold d in H` | `rewrite /d` / `rewrite /d in H` |
| `fold d in H` | `rewrite -/d in H` |
| `change (KVar (f y)) with (keyv y)` | `rewrite -/(keyv y)` |
| `simpl` / `simpl in H` | `rewrite /=` / `rewrite /= in H` |
| `simpl f` (one head only) | `rewrite [f _ _ _ _]/=` |
| `set (x := e) in *` | `set x := e in H1 H2 *.` |
| `assert (H : T) by tac` | `have H : T by tac.` |
| `assert (H : T). { ... }` | `have H : T.` + indented proof |
| `destruct (lem args) as [x Hx]` | `have [x Hx] := lem args.` |
| `pose proof (lem ..) as H; destruct H as [..]` | `have := lem ..; rewrite Hob => -[..]` |
| `inversion H` (NoDup/Forall cons) | views `/NoDup_cons_iff [Hq Hnd]`, `/Forall_cons_iff [..]` |
| `apply in_map_iff in H as [..]` | `move: H => /(in_map_iff _ _ _) [..]` |
| `apply Forall_forall; intros p Hp` | `apply/Forall_forall => p Hp` (`exact/Forall_forall` when it closes) |
| `destruct (Nat.eqb_spec a b)` | `case: (Nat.eqb_spec a b) => [E|NE]` |
| `injection H as E1 E2` | `case: H => E1 E2` (or intro pattern `[E1 E2]`) |
| `apply X; auto` | `by apply: X` |
| `exact (f a b)` | `exact: f a b` |
| `f_equal` | `congr (_ :: _)`, `congr (_ ++ _ ++ _)`, `congr VArray` |
| `replace a with b by lia` | `have -> : a = b by lia.` |
| `[reflexivity | discriminate]` closing branches | `//` |
| `exfalso; apply Hq` | the same (`case:` on a negation does not work) |

## Pitfalls met, with fixes

- **ssr `<-` / `->` rewrite only the goal**. Ltac `injection H as <- <-`, `[-> H]` or
  `apply in_gT in HrT as [_ ->]` substitute everywhere; the ssr intro patterns rewrite
  the goal only, and fail ("The RHS ... does not match any subterm of the goal") or leave
  the variable in other hypotheses (and in `set` definitions such as `wT`). Fix: name the
  equation and `subst`: `move=> [? [? [? HA]]]; subst n' t' r'`, `[Ep Hx0]; subst p`,
  `move/in_gT: HrT => [_ Eyt]; subst yt`, `case: Hg => ? ?; subst nm role`.
  Use `->`/`<-` only when the variable occurs in the goal alone.
- **`move: H; rewrite E /=` changes the whole goal**, not only H (here it rewrote `y` and
  simplified the main goal). To change only H: `rewrite E /= in H`.
- **`//=` also simplifies the goal**; use `rewrite /= in H` when only H must change.
  After `//=`, terms like `k + S n` may already be reduced, so a planned
  `have -> : k + S n = ...` no longer matches; rewrite with lemmas instead
  (`rewrite -Nat.add_succ_comm -H3`).
- **Conditional rewrite lemmas: the side conditions come FIRST.** After
  `rewrite store_get_set_other`, the goal `k <> k'` is first: write
  `rewrite store_get_set_other; first by ...` (or `rewrite L //` when `done` closes the
  side goal). Same for `nth_error_app1/2`, `xev_set_other`, `Hfr1 y0 Hb Hc`.
- **Views on Stdlib lemmas with implicit arguments**: `move=> /in_rev`, `/In_nth_error`,
  `/in_map_iff`, `/in_app_or` fail with "Pattern ... was not completely instantiated". Give
  the arguments: `/(in_rev L)`, `/(In_nth_error _ _)`, `/(in_map_iff _ _ _)`,
  `/(in_app_or _ _ _)`; for an iff goal use `rewrite -in_rev` instead of `apply/in_rev`.
  `/NoDup_cons_iff`, `/Forall_cons_iff`, `/nth_error_None`, `/nth_error_Some`,
  `/existsb_exists`, `/filter_In`, `/in_concat` work as is.
- **`case: x` when another hypothesis mentions x** ("x is used in hypothesis H"):
  generalize it (`case: rT HrT`, `case: r Ht {Hd}`), or case on the term in parentheses,
  `case: (t)`, which abstracts the goal only (move the needed hypotheses into the goal
  first: `move: Hraw Hwr; rewrite Hvy; case: (t) => //= _; case: (r)`). Inside a `have`
  the generalized hypotheses (`case Ein: (inplace ..) Hfr1 Hres => ..`) stay intact for
  the main goal.
- **Bullets inside a `have` inside a bullet**: with the default bullet behavior, once
  the bullets have closed the `have` goals the main goal is not focused ("No such goal.
  Focus next goal with bullet -"). Fix: `Set Bullet Behavior "None".` (see Import and
  Layout); do not use `{ ... }`.
- **`//` / `done` closes more than expected**: `done` also runs `split`, `discriminate`
  (including on hypotheses such as `E : keyv (stored p) = keyv (DotOf ResultVar)` after
  hnf) and `contradiction`. It can close a `/\` completely, so a following `do 2!split`
  fails with "No applicable tactic".
- **`erefl`** needs ssrfun and fails when the type cannot be inferred; it works as an
  argument whose expected type is known (`keyv_inj y0 (stored y) Hcy erefl`). Otherwise
  state it (`have C : consistent i by []`).
- **`set` definitions** need `rewrite /x` before rewriting inside them.
- **Name clash in `elim: H`** on an inductive predicate whose index is a variable
  ("AL already used"): rename in the pattern (`[|p AL' [_ Hg] HAL' IH]`).
- **`length`**: the goals print `Datatypes.length` because `String` is imported too.
  Inside `have` statements, write `Datatypes.length` if `length` resolves to
  `String.length`.
- **`exact: IH` when IH has premises**: use `by apply: IH`.
- **After a Section closes**, lemmas that used a section variable take it as an extra
  first argument.
- **`rewrite Hob`** rewrites inside `open_pairs t n` found in a hypothesis up to
  `set` definitions (`wT`), which removed the Ltac `match type of H with context [...] =>
  replace ... end` blocks.

- **`set x := e in *` is rejected** ("assumptions should be named explicitly"): list
  the hypotheses, `set n := DBound (j, j) in Hst Hob *.`
- **ssr intro patterns unfold `In`**: `move=> p u1 u2 [E1 | [E1 | I1]]` on
  `In _ (a :: b :: gW L)` leaves `I1` as the unfolded `fix In ...`, so a later Ltac
  `match goal with I : In (_, _) (gW L) |- _ => ...` no longer fires. Keep `intros`
  with Stdlib patterns there (`live_cont2`), or use views (`case/in_gW: I`) which
  work up to conversion.
- **Ltac `apply` uses the conjuncts of a lemma, ssr `apply:` does not**:
  `apply (c_top ... Hc o eq_refl eq_refl)` proved one conjunct of the conclusion,
  `apply (c_place ...)` one conjunct of `place_ok`; in ssr, destructure:
  `have [_ [Hv _]] := c_top ... Hia; exact: Hv Hlivo.`
- **`destruct (e) eqn:E` where `e` occurs in a hypothesis H**: `case E: (e) H => H.`
  (or `move: H; case E: (e) => // H`), so that `H` is rewritten too.
- **`rewrite (_ : lhs = rhs)`: the equation is the FIRST goal**: write
  `rewrite (_ : run _ s = run [..] s).` and close the equation on the next line,
  indented: `  by rewrite /tan_map /bodyst; case: (varied_anf _ _).` The `_` in the
  left-hand side is instantiated by the first match, which replaces the Ltac
  `match goal with |- context [run ?t s] => replace (run t s) with .. by .. end`.
- **`match goal with |- context [open_pairs ?t (S c)] => destruct (open_pairs t ..)
  eqn:Hob; pose proof (open_pairs_mono t ..)`** becomes
  `case Hob: (open_pairs _ (S c)) => [[sb [vb db]] c2].` and
  `have Hc2 : (S c <= c2)%nat by rewrite -[c2]/(snd (sb, (vb, db), c2)) -Hob;
  exact: open_pairs_mono.` (no need to spell `t`). Later
  `replace (open_pairs t (S c)) with .. in IHb` becomes `rewrite Hob` on the
  generalized `have := IHb ...`.
- **`destruct svr` where `svr` is a `set` variable used in other `set` definitions**
  (`bodyst`, `s1`): `case: (svr)` after unfolding the definitions in the goal
  (`rewrite /pre /s1; case: (svr)`); or `case Hsvr: (svr)` and then
  `rewrite /bodyst Hsvr`. Occurrences inside `pose`d predicates (`Inv`) are not
  touched: close `svr = true -> ..` with `move=> Hs; rewrite Hs in Hsvr`.
- **`change t with svr` matches syntactically**: after `destruct initP as [o | |]`
  the goal has `varied (amap pa (AVar o))`, not `varied (AVar (pa o))`; Ltac `change`
  then silently changes nothing. Copy the term as it is displayed.
- **`//` after a conditional rewrite may close a side goal you planned to close
  yourself** (`below (S c) i` is `c < S c`, closed by `done`'s hints), and the next
  `first by ..; lia` then hits the main goal ("Cannot find witness"). Check which goals
  remain, or write the rewrite so that both orders work.
- **`-[]` on an equation that gives no new equation** prints the warning
  `spurious-ssr-injection`; use `case` in the branch that needs injection only
  (`split; first case.` / `split; last case.`).
- **`have [x [-> ...]] := lem`** rewrites only the goal (see the first pitfall); it is
  fine when the variable occurs in the goal only, otherwise name the equation and
  `subst`.
- **Hypothesis names produced by `value_intro`** (H1, H4, H7, H10) can clash with
  names chosen later (`Hb` in a pattern after an earlier `have Hb`): "Hb already used".

- **`have H : match e with ... end.` gets `return Type`**: the statement is elaborated
  as a type, so the `match` is typed `return Type`, and passing `H` where the lemma
  expects the same `match` in `Prop` fails with an error whose two types print
  identically. Write `match e return Prop with ... end` in the `have` statement.
- **The position of rewrite side goals varies**: seen first (`store_get_set_other`,
  `tvaried_amap`, `rewrite (_ : run _ s = ..)` with a `_` in the pattern) and last
  (`rewrite (_ : S (length pre) = ..)` fully explicit, `rewrite .. IH; last by ..`).
  Do not guess: prefer `have -> : lhs = rhs by ..`, pass the premise as an argument
  (`rewrite -(seed_args_dual _ _ _ Hfit Hle) in Hev`), or check the goal order once.
- **`case: (vr)` / `case Hvr: (vr)` on a `set` variable leaves the other local
  definitions alone**: `sc2 := if vr then .. else ..` keeps `vr`, and `sx := PV .. svr ..`
  keeps `tdot (pt sx)` unreduced, so `exact: Hsc2` or a `discriminate` fails after the
  case. Use Ltac `destruct vr eqn:Hvr` there (it also rewrites inside the bodies of the
  local definitions), or unfold the definitions first (`rewrite /sc2; case: (vr)`).
- **`ltac:(assumption)` arguments**: name the hypotheses generated by an intro macro
  (`rename H6 into HAt, H3 into HWt, H0 into HTt`) and pass them explicitly; an
  `ltac:(..)` proof of a side fact becomes a named `have` before the call.
- **Views that rewrite a variable**: `move=> x /repeat_spec ->` fails ("indeterminate
  pattern") and `/repeat_spec Ex; subst x` fails ("__view_subject__ is used in
  hypothesis Ex"); use `move=> x Hx; rewrite (repeat_spec _ _ _ Hx)`.
- **`exact: lem` with premises left**: `exact:` does not close remaining premises from
  the context; use `by apply: lem`.
- **Stale `.vo` in the worktree**: `rocq_start` failed with "The reference reals_of_val
  was not found" because `DualsDerive.vo` was older than `Eval.vo` ("makes
  inconsistent assumptions over library ElpiDiff.Eval" with `rocq compile`). Recompile
  the stale dependency (`rocq compile -native-compiler no -R . ElpiDiff DualsDerive.v`)
  and restart the server state (`rocq_start` with `force_restart`).
- **`=> /= Hev` versus `=> Hev /=`**: in `case Hcmp: (comparison f) Hev => /= Hev` the
  `/=` runs while `Hev` is still in the goal and unfolds it too far (`dom_cmp` became
  `real_cmp`, `dom_op2` a `match f`), so a later `case: (dom_cmp ..) Hev` finds nothing.
  Introduce first and simplify the goal only: `=> Hev /=`.
- **A view on `In x (dvars (DOp2 ..))`**: `move=> x /in_app_or [Hx | Hx]` fails with
  "Pattern was not completely instantiated" (the list is not yet an `app`); use
  `move=> x Hx; case: (in_app_or _ _ _ Hx)`.
- **An injection that yields two equations**: `case: Hst => Hj'` on
  `DBound (j, j) = DBound (n, n)` leaves the second equation as a premise of the goal;
  name it (`case: Hst => Hj' _`).
- **`->` in a `case` pattern rewrites the goal only**: in
  `case: (H x Hx) => [[p [Hp [-> | ->]]] | ..]` the hypothesis `E : keyv x = ..` keeps
  `x`; generalize it first: `case: (H x Hx) E => [[p [Hp [-> | ->]]] | ..] E`.
- **`repeat split=> E`** introduces only in the last goal ("No such hypothesis: E");
  write `repeat split; move=> E`. `split=> x Hx E` (one split) does introduce in both.
- **`case: aP => [p | s | z] H /=; try by repeat split=> x []`** silently left the two
  literal cases open; put the easy cases first with bullets:
  `case: aP => [p | s | z] H /=; last 2 first.` then `- by repeat split; move=> x [].`
- **Nested patterns on `Z`**: `[| | [] |]` for a `Z` argument fails ("not a rewritable
  relation: positive"); `Z` has arguments, use `[| ? | ?]`.
- **`-[<- <-]` on `Some (t, sp) = Some (t', sp')` when `sp` is not in the goal**:
  "The RHS of __top_assumption_ does not match"; drop the useless one with `-[<- _]`.
- **A view with a hole**: `case: E => /(IH Ha _ Hb) ->` fails ("Illegal application
  (Non-functional construction)"); give the argument: `/(IH Ha b Hb) ->`.
- **`apply: frame_set => //; [a | b]`**: the `//` closes the trivial premise, so the
  `[..|..]` list has the wrong length ("Incorrect number of goals"); list all premises
  and leave the trivial one empty: `apply: frame_set; [apply: frame_refl | | left]`.
- **`case: b` when `b` occurs in hypotheses**: "b is used in hypothesis H"; list them
  (`case: b Hcd Hev Hsc Hsc0 => Hcd Hev Hsc Hsc0`) or consume the hypothesis first
  (`move: H; rewrite /xev => ->; case: b`).
- **Impossible constructors of a typed value**: in `case: ve Hht Hev .. => [[x dx] | | | |]
  // _ Hev ..` put the typing hypothesis (`has_type Real ve`, which reduces to `False`
  for the other constructors) first, so that `//` closes those cases before the intros.
- **`rewrite store_get_set_other ?store_get_set_same //`** also closes the side goal
  `keyv a <> keyv b` when both keys are concrete constructors (`done` discriminates);
  a following `exact: not_eq_sym (keyv_dot_neq _)` then fails with no goal.
- **A `match` scrutinee convertible to a hypothesis**: after `rewrite run_branch` the
  goal is `match run (..) s0 with .. end = ..` where `run (..) s0` is only convertible to
  the left side of `Htail2`, so `rewrite Htail2` fails; the Ltac
  `match goal with |- (match ?r with _ => _ end) = _ => replace r with .. by .. end`
  stays.

- **`elim` on an inductive predicate whose indices are variables of the goal**
  (`term_equiv G t1 t2`, `gd sc wr ss`): `elim=> [G x1 x2 Hin | ..]` fails with
  "G already used"; clear the old variables first: `elim=> {G t1 t2} [G x1 x2 Hin | ..]`.
- **`rewrite L in H *` with different instances in H and in the goal** (`exec_define`
  at `s` in H and at `s'` in the goal) rewrites one instance only; write
  `rewrite !L in H *`. `rewrite ?ex_cons in H *` works for the same reason.
- **`case: va vb H1 H2 {E1 E2} => [..] [..]`** failed with "Incorrect number of goals
  (expected 2 tactics)"; case the two values one after the other:
  `move: H1 H2; case: va {E1} => [p | ..]; case: vb {E2} => [q | ..] //= H1 H2`.
- **`++` inside a tactic term means `String.append`** when `String` is imported:
  `rewrite -(IH (pre ++ [r]))` fails with "pre has type list R while it is expected to
  have type string"; write `app pre [r]` (statements are not affected).
- **A view in an `elim` intro pattern applies to every branch**:
  `elim: ss => [| st r IH] //= /orb_false_iff [..]` also applies the view in the
  nil case; close that case first (`first by move=> _ []`) and use the view on the
  next line.
- **`rewrite [map _ _]/=` reduces the whole matched subterm**, so the recursive
  `map f r` inside is unfolded to its `fix` body and no longer matches the induction
  hypothesis; use `cbn [map]` (and `cbn [simplify_stmt]`, `cbn [replace_stmt]` for the
  head) as `simpl map` did.
- **Intro patterns after `case:` need every constructor argument**: in
  `case: f => [| | | | | | k |] H` the last branch binds `H` to the `string` argument
  of `Unknown1`; name all arguments (`[| | | | | | k | g] H`). The same for `case: a H`
  on a 6-constructor `dexpr` (`[v | l | n | b i | [..] a' | g b c] H`).
- **`exact: Hsim` where `Hsim : sim sc t t'`** (a `forall` whose premises include the
  execution `ex t s = Some t0`) failed with "No applicable tactic"; give the premise:
  `exact: Hsim H`.
- **`eexists; split; last exact: agree_set`** failed; give the witness
  (`exists (store_set s' k w); split=> //; exact: agree_set`).
- **`-1` is `- 1` in `R_scope`**: `have -> : -1 = - 1 by ring` fails with "all matches
  of the LHS are equal to the RHS"; the term is already the one the lemma expects.
- **Inside a section, `exact: lem H1 H2` may fail** ("Cannot apply lemma eval_forward")
  where `exact: (lem _ _ _ H1 H2)` works: give the leading explicit arguments as holes.
- **rocq-mcp: a comment line followed by a bullet** in a `rocq_check` body gives
  "Syntax error: [vernac_control] expected"; check without the comments and add them
  when saving the proof in the file.
- **`[<- <- <-]` on `Some (st :: b', m', a') = Some (b, m, a)`** where `m` and `a`
  are lemma parameters used in the induction hypothesis: the goal is rewritten but not
  the IH; name the equations and `subst b m a`.

## When to keep Stdlib/Ltac

- `destruct` on a variable used in many hypotheses and in `set` definitions
  (`destruct res`, `destruct resT`, `destruct yP`, `destruct t as [| | | z]` in
  `tangent_simulates_duals`): ssr `case:` refuses ("res is used in hypothesis Ho").
- `decide equality` proofs (`dvar_eq_dec`).
- `lia` and `lra` for arithmetic, `eauto` for existential witnesses.
- `change` with a large term (one occurrence), `subst`, `constructor`.
- `rename`, `match goal with H : .. |- _ => rename H into .. end` after `value_intro`.
- `destruct initP as [o | |]`, `destruct pp`, `destruct wP`, `destruct s0`,
  `destruct st` in `sim_fold`/`sim_map` (each used in many hypotheses).
- `intros` with Stdlib patterns before a Ltac `match goal` on `In _ (gW L)`
  (`live_cont2`), `inversion E` inside that `match`.
- `crush_match`, `cbn [..]`, `cbv beta iota` (no ssr counterpart for partial reduction).
- `first [ .. | .. ]` and `try (..)` combinators for families of similar subgoals.
- `destruct vr eqn:Hvr` on a `set` boolean used in other local definitions (see the
  pitfall above), `inversion E` inside a Ltac `match` loop, `simpl in *`, `crush_match`.
- In `TangentCorrect_math.v`: the automation-driven proofs (`tangent_op2`,
  `occurs_transfer`, `open_with_storage`, `type_of_ok`, `inplace_array`,
  `inplace_value_s`) keep their Ltac skeleton (`destruct .. ; simpl in ..; try ..;
  crush_match`) laid out at column 0; `repeat (apply avoid_op1 || apply avoid_op2 || ..)`
  in `avoid_partial1/2`; `apply keyv_inj in E` (it opens the `consistent` side goals
  that `auto` closes); `unfold_ops Hd`; `destruct va as .., vb as ..` in `sim_op2` and
  `destruct pp`, `destruct tail`, `destruct aP` in `sim_set`/`sim_get`/`sim_ite`
  (variables used in many hypotheses); the `match goal .. replace r with ..` in
  `sim_ite` (see the pitfall above).

- In `DualsDerive_math.v` and `SimplifyCorrect_math.v`: `inversion` to invert
  `term_equiv`, `definition_equiv` and `gd` at a constructor (`by inversion 1; eauto 6`
  in the `equiv_*` lemmas, `inversion Hg as [..]; subst` in `fuse_*`,
  `gd_app_inv`, `gd_app`, `eval_definition_near`); `gd_mono` and `good_gd` keep their
  automation (`induction 1; econstructor; try (..)`, a `repeat match goal` splitting
  `_ || _ = false`); `cbn [..]` for partial reduction (`dual_op1_spec`, `cbn [map]`,
  `cbn [simplify_stmt]`, `cbn [replace_stmt]`, `cbn [fuse]`); `vm_compute
  read_literal` (`lit_0`, `lit_1`, `lit_m1`); the Ltac definitions `inv_some`,
  `inv_eval`, `decide_ifs` (the last one used in `real_cmp_lt` and `point_cmp`);
  `field`, `ring`, `lra`, `lia`, `tauto`, `intuition`.

## No inline ltac

Never write `ltac:(...)` inside terms. Use a named `have H : ... by ...` instead.

## Workflow

- Restyle lemma by lemma, replacing only the `Proof. ... Qed.` text so that the
  statements cannot change (a small script replaces the text between `Proof.` and `Qed.`
  of a named lemma); compare the files with proofs stripped at the end.
- Check interactively with rocq-mcp: `rocq_start` on the lemma, then `rocq_check` with
  several sentences, or several whole lemmas (`Qed.` and the next `Lemma` statement) in
  one body. For a long proof keep a live state and extend it block by block (one `have`
  at a time), appending each validated block to a scratch file; restart with `rocq_start`
  after editing the file above the current position.
- The goal display of a large proof is long (5-10K characters per goal, and a
  failing command prints all of them): prefer one candidate per `rocq_check` over
  many in `rocq_step_multi`, never `Show`, and send large blocks that are likely right.
- A heavy Ltac macro such as `value_intro` goes in its own sentence (`value_intro.`
  then `rewrite /= in ...`): `value_intro; rewrite ...` timed out at 30 s while the
  two sentences take 4 s. Give `rocq_check` a larger `timeout` for such proofs.
- One compile at the end:
  `rocq compile -native-compiler no -R . ElpiDiff TangentTop_math.v`
  (without `-native-compiler no` the native step fails because the dependencies have no
  native objects: "Unbound module NElpiDiff_Syntax"; the Rocq part is fine), then delete
  the produced `.vo/.vos/.vok/.glob`.

## Additions from `AdjointCorrect_math.v`

- **`last first` reverses three goals**: after `case: vo => [[t | y] |]` the goals
  `[AReturns; AWrites; None]` become `[None; AWrites; AReturns]` with `; last first`,
  and `[AWrites; None; AReturns]` with `; last 2 first`. To put one easy case first,
  case in two steps (`case: vo => [r |] ..; last first.` for the `None` case, then
  `case: r => [t | y]` with the easy constructor as the indented side goal).
- **`case: e => _ H` when `e` occurs in the goal** fails with "_a_ is used in
  conclusion" (`case: (in_dec ..) => _ H`, `case: (dual_partial1 ..) => //= _ [<-]`);
  name the argument (`=> I H`, `=> [p |] //= [<-]`).
- **`//=` in a `case` that moves hypotheses also simplifies them**:
  `case: z Hp Hd => [| z | z] //= ..` unfolds `real_lit "0"` in `Hd`, and a later
  `rewrite lit_0 in Hd` finds nothing. Case without `/=` and simplify only the
  hypothesis that needs it (`=> Hp Hd; rewrite /= in Hp; try discriminate`).
- **The `return Type` pitfall of `have H : match ..`** shows up only when `H` is
  passed to a lemma, as an error between `@eq (dvar W)` and
  `@eq (dvar (prod nat nat))` (`Hst0`, `Hst1`, `Hst2` in `asim_let`); write
  `match storage wP tail eP return Prop with ..`.
- **`apply: H` when `H` concludes `False`** fails with "Cannot apply lemma"; use
  `case: (H ..)` (or `exfalso; exact: H ..`).
- **`erefl` for a `consistent n` premise** fails ("erefl has type ?x = ?x while it is
  expected to have type consistent ?n") when `n` is only fixed by a later argument;
  give the explicit arguments first (`barv_set_other s2 (DBound (c, c)) m0 (VReal 0)
  erefl ..`, `keyv_inj (BarOf n) v Hn Hcv K`).
- **Injection of `stored o = stored p`** (`DBound (pn o, pn o)`) gives two equations:
  `[Hex]` leaves `pn p = pn p ->` in front of the goal and a later `exact` fails;
  write `[Hex _]` (same for `case: E => E _`).
- **The `match goal .. replace r with ..` of `sim_ite` was not needed here**:
  `rewrite run_app R1` closes `run (fe ++ fb) s = ..` after `run fe s = Some se1`, and
  `rewrite Happ run_app (_ : run [_] s = Some s0)` (with
  `Happ : forall a b, [a; b] = ([a] ++ [b])%list`) replaces the
  `change [..; ..] with (app [..] [..])` of `afwd_set`/`arev_set`.
- **rocq-mcp with a large context** (`asim_let`, 60 hypotheses): a failing command prints
  20-40K characters and the goal, printed last, is cut by the truncation. To see the
  goals, run `all: match goal with |- ?g => idtac "GOAL" g end.` in a `rocq_check`:
  the goals come in the `feedback` field, before the truncated context. Avoid
  `rocq_step_multi` with several candidates there (each successful candidate prints
  the full context) and never `Abort.` inside a chain (the answer then lists the
  whole chain of tactics).
- **A 700-line proof**: translate it by blocks of 20-40 sentences, each checked from
  the state the previous block returned, and append each validated block to a scratch
  file; check the last case first when the cases are independent. The file can keep
  `Admitted` in place of the proof meanwhile, so that `rocq_start` reaches the later
  lemmas (with a proof that does not parse under ssreflect, e.g. `rewrite .. by`,
  the server stops reading the file there and later lemmas are "not found").

## When to keep Stdlib/Ltac in `AdjointCorrect_math.v`

- The macros `unfold_ops`, `none_case`, `fwd_intro`, `rev_intro`, `act_intro`,
  `needs_let_tac`, `split_reads`, `below_tac`, `fresh_case'` (all unchanged), and the
  `repeat match goal .. atom_graph ..` of `owner_set`.
- `repeat match type of H with context [match ?e with _ => _ end] => destruct e end`
  in `assign_bar`, `straight_no_top`; `crush_match` in `act_op1`; `cbn [..]`,
  `change .. with ..` and `cbv zeta` (`run_increment_at`, `IH`/`IHr'` in `asim_let`).
- `destruct` on variables used in many hypotheses or in `set` definitions: `aP`, `vP`,
  `wP`, `pp`, `m`, `vo`, `te`, `pd q`, `va`/`vb` (`act_op2`), `avaried (pa p)` and
  `vty (pw p)` in `asim_ret`; `destruct eA, eW, eD` and `destruct bA, bW, bT, bD`.
- `decide equality` (`dvar_eq_dec_c`), `repeat split; simpl; auto; try lia;
  discriminate` (`Hxs` in `asim_let`), the `first [..|..]` in `dvar_eq_consistent`,
  `lia`, `ring`, `congruence`, `eauto`.

## Pitfalls met in `AdjointBranch_math.v`

- `store_get_set_other` (and `barv_set_other`) put the side condition `k <> k'`
  (set key first) as the FIRST goal: `rewrite store_get_set_other; first by ...`.
  With `keyv_inj` as a view the consistency proofs follow the same order:
  `by move=> /(keyv_inj _ _ Hc_set Hc_get)`; name them (`have Hci : consistent i
  by []`). For `DBound (a, a) = DBound (b, b)` use `[] *; lia` (two equations).
- `case E: (st (S jn)) H1 H2` only rewrites in the listed hypotheses, unlike
  `destruct .. eqn:`: rewrite the other hypotheses and the goal by hand before
  `lra` (`dso (st jn)` stayed folded in `arev_fold`).
- `case: v H` fails with "v is used in hypothesis st" when a `set` definition
  mentions `v`: keep `destruct v as [..]` there.
- `move: (f H) Hw {H}` clears `H` before `f H` is built: `have := f H; clear H`.
- `subst x` after `atom_graph` can consume an equation of another hypothesis:
  check which ones remain (`Elo` vanished in `inplace_map`).
- Name clashes with earlier `have`s inside a long proof (`Hrm` was already a
  lemma about `atom_remove`): "Hrm already used".
- `have {H} H := ..` warns (duplicate clear): write `have {}H := ..`.
- The five `Replay = Forward -> ..` premises of `asim_body`: `move=>
  /(_ (Hnf _) (Hnf _) (Hnf _) Hpb (Hnf _))` with `Hnf : forall P : Prop,
  Replay = Forward -> P by []` and `Hpb : Replay = Replay -> PScalar <> PTop`.
- To see a goal cut by truncation, `rocq_step_multi` with `clear -H1 H2 ..`
  prints a short context first.
