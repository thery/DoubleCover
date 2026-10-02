(** * The table check and the Capla search, through [line_ok]

    [check_raw] is the check of a table file (code/exptable9): when it
    answers [true], every line of the file satisfies [line_ok]
    ([ExpProof.check_rawP]).  Here, on a line that satisfies [line_ok],
    the Capla [search] of [htr3.b], run with the parameters of the table
    ([k = 9] coefficients of [l = 6] words, the window [err = 0x600000],
    the inputs [j = 0 .. n-1]), returns every hard-to-round input of the
    line, when their number fits in the output array.  So:
    [check_raw] -> [line_ok] -> no [hard] input is missed. *)

From Stdlib Require Import Reals Lra.
From ExpTable9 Require ExpCheck ExpParse ExpProof ExpHard.
From APaulRocq Require TaylorReal.

From Stdlib Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Import Htr3.HtrBase.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Require Import Htr3.SearchProof Htr3.HtrFinal.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Local Notation line_ok := ExpCheck.line_ok.
Local Notation check_raw := ExpParse.check_raw.
Local Notation parse := ExpParse.parse.
Local Notation hard := ExpHard.hard.
Local Notation bp := ExpCheck.bp.
Local Notation uexp := ExpCheck.uexp.

(** ** The two descriptions of a line agree *)

(** The sums of [ExpCheck] and of [TaylorReal]. *)
Lemma sumR_TaylorReal (f : nat -> R) (N : nat) :
  TaylorReal.sumR N f = ExpCheck.sumR f N.
Proof. by elim: N => [|N IH] //=; rewrite IH. Qed.

(** The polynomials of [ExpCheck] and of [HtrDefs]. *)
Lemma Pz_polyZ (A : list Z) j :
  length A = ExpCheck.k -> ExpCheck.Pz A j = polyZ A j.
Proof. by move=> hA; rewrite /ExpCheck.Pz /polyZ hA. Qed.

(** [beta^l] of [ExpCheck] is [base 6]. *)
Lemma beta_l_base : ExpCheck.beta_l = base 6.
Proof. by vm_compute. Qed.

(** The window [E] of [ExpCheck] is [err beta^(l-1)], [err = 0x600000]. *)
Lemma E_err :
  ExpCheck.E =
  (Int64.unsigned (Int64.repr 0x600000) * 2 ^ (64 * (Z.of_nat 6 - 1)))%Z.
Proof. by vm_compute. Qed.

(** A natural number [j] as a real. *)
Lemma INR_Z2N (j : Z) : (0 <= j)%Z -> INR (Z.to_nat j) = IZR j.
Proof. by move=> j0; rewrite INR_IZR_INZ Z2Nat.id. Qed.

(** The [n] of a line fits in a word. *)
Lemma line_ok_n S0 ex n B :
  line_ok S0 ex n B -> (1 <= n < 2 ^ 53)%Z.
Proof.
move=> hok; destruct hok as (e & hn & h52 & h53 & hsg & _).
change ExpCheck.drop with 1%Z in *.
have : (0 < S0 /\ 0 < S0 + n - 1 \/ S0 < 0 /\ S0 + n - 1 < 0)%Z by nia.
by lia.
Qed.

(** ** On one line *)

Theorem search_line S0 ex n B :
  line_ok S0 ex n B ->
  forall xs len outs cap e1 result,
  (* the array holds B, each B_i in 6 words, the least significant first *)
  length xs = nat_of len -> (54 <= nat_of len)%coq_nat ->
  vcoefs xs 6 9 = B ->
  length outs = nat_of cap ->
  (* the run of search, with k = 9, l = 6 and err = 0x600000 *)
  eval_funcall ge (Internal search46)
    [Varr (map Vint64 xs); Vint64 len; Vint64 (Int64.repr 9);
     Vint64 (Int64.repr 6); Vint64 (Int64.repr n);
     Vint64 (Int64.repr 0x600000); Varr (map Vint64 outs); Vint64 cap]
    e1 (Some result) ->
  exists c outs', result = Vint64 c /\
    e1!(param 6 search46) = Some (Varr (map Vint64 outs')) /\
    forall j, (0 <= j < n)%Z ->
    hard (IZR (S0 + j) * bp (uexp ex)) ->
    (nat_of c <= nat_of cap)%coq_nat ->
    In (Z.to_nat j) (firstn (nat_of c) (map nat_of outs')).
Proof.
move=> hok xs len outs cap e1 result hxs hlen hv houts hrun.
have [n1 n53] := line_ok_n S0 ex n B hok.
have nk : nat_of (Int64.repr 9) = 9%nat by vm_compute.
have nl : nat_of (Int64.repr 6) = 6%nat by vm_compute.
have nn : nat_of (Int64.repr n) = Z.to_nat n.
  rewrite /nat_of Int64.unsigned_repr //.
  by change Int64.max_unsigned with (2 ^ 64 - 1)%Z; lia.
have herr : (2 * Int64.unsigned (Int64.repr 0x600000) <=
             Int64.max_unsigned)%Z by vm_compute.
(* the count and the output array, from the run *)
have [c [outs' [hc [he1 _]]]] := search_spec xs len (Int64.repr 9)
  (Int64.repr 6) (Int64.repr n) (Int64.repr 0x600000) outs cap e1 result
  hxs ltac:(rewrite nk nl; lia) ltac:(rewrite nk; lia)
  ltac:(rewrite nl; lia) herr houts hrun.
exists c, outs'; split => //; split => // j hj hhard hcap.
(* the conditions of the line *)
move: hok; rewrite /ExpCheck.line_ok; cbv zeta.
change ExpCheck.drop with 1%Z.
move=> hok.
destruct hok as (e & _ & _ & _ & _ & hv0 & hvl & (A & hlA & hlB & hA & hB) &
  hT & hE).
set u := bp (uexp ex) in hv0 hvl hA hT hE hhard *.
set v := ExpCheck.bp (ExpCheck.vexp e) in hA hT hE *.
set rho := (exp _ * _ / _)%R in hT hE.
have u0 : (0 < u)%R by apply: Flocq.Core.Raux.bpow_gt_0.
(* x = x0 + j u, and v = vof x *)
have hx : (IZR (S0 + j) * u = IZR S0 * u + IZR j * u)%R.
  by rewrite plus_IZR; ring.
have hvx : ExpHard.vof (IZR (S0 + j) * u) = v.
  apply: (ExpHard.vof_line e _ _ _ hv0 hvl).
  rewrite hx; split.
    have : (0 <= IZR j)%R by apply: IZR_le; lia.
    by move=> hj0; nra.
  have : (IZR j <= IZR (n - 1))%R by apply: IZR_le; lia.
  have -> : (S0 + n - 1 = S0 + (n - 1))%Z by lia.
  by rewrite (plus_IZR S0 (n - 1)) => hjn; nra.
move: hhard; rewrite /ExpHard.hard hvx hx => hz.
(* the hypotheses of search_complete, from the conditions of the line *)
have k9 : ExpCheck.k = 9%nat by [].
have hmap : vcoefs xs 6 9 =
    map (fun i => polyZ A (Z.of_nat i) mod base 6)%Z (seq 0 9).
  rewrite hv; apply: (nth_ext _ _ 0%Z 0%Z).
    by rewrite length_map length_seq hlB.
  move=> i hi; rewrite hlB in hi.
  rewrite hB // (nth_indep _ 0%Z (polyZ A (Z.of_nat 0) mod base 6)%Z).
    by rewrite length_map length_seq.
  by rewrite map_nth seq_nth // Pz_polyZ // beta_l_base.
have hA' : forall i, (i < 9)%coq_nat ->
    (Rabs (IZR (nth i A 0%Z) - IZR (base 6) *
             frac_part (ExpCheck.a (IZR S0 * u) u i / v)) < 1)%R.
  move=> i hi; have [_] := hA i hi.
  by rewrite ExpHard.fracR_frac_part beta_l_base.
have hj0 : (0 <= j)%Z by lia.
have hT' := hT j ltac:(lia).
rewrite -sumR_TaylorReal -(INR_Z2N j hj0) k9 in hT'.
rewrite [in exp _](INR_Z2N j hj0) in hT'.
have nR : INR (Z.to_nat n) = IZR n by apply: INR_Z2N; lia.
rewrite E_err beta_l_base -sumR_TaylorReal -nR k9 in hE.
have := search_complete xs len (Int64.repr 9) (Int64.repr 6)
  (Int64.repr n) (Int64.repr 0x600000) outs cap e1 result A
  (fun i => ExpCheck.a (IZR S0 * u) u i / v)%R rho
  (bp (- ExpCheck.m)) (exp (IZR S0 * u + IZR j * u) / v)%R (Z.to_nat j).
cbv zeta; rewrite nk nl nn.
move=> /(_ hxs ltac:(lia) ltac:(lia) ltac:(lia) herr houts).
move=> /(_ ltac:(by rewrite hlA) hmap hA' hT' hE ltac:(lia) hz hrun).
move=> [c2 [outs2 [hc2 [he2 hin]]]].
(* the same count and the same array *)
have hc' : c = c2 by move: hc; rewrite hc2 => -[].
have houts' : outs' = outs2.
  move: he1; rewrite he2 => -[] h; clear -h.
  by elim: outs' outs2 h => [|x s IH] [|y t] //= [-> /IH ->].
by rewrite hc' houts'; apply: hin; rewrite -hc'.
Qed.

(** ** On a table *)

Theorem search_table ls :
  check_raw ls = true ->
  forall s, In s ls -> exists S0 ex n B,
  parse s = Some (S0, ex, n, B) /\ line_ok S0 ex n B /\
  forall xs len outs cap e1 result,
  (* the array holds B, each B_i in 6 words, the least significant first *)
  length xs = nat_of len -> (54 <= nat_of len)%coq_nat ->
  vcoefs xs 6 9 = B ->
  length outs = nat_of cap ->
  (* the run of search, with k = 9, l = 6 and err = 0x600000 *)
  eval_funcall ge (Internal search46)
    [Varr (map Vint64 xs); Vint64 len; Vint64 (Int64.repr 9);
     Vint64 (Int64.repr 6); Vint64 (Int64.repr n);
     Vint64 (Int64.repr 0x600000); Varr (map Vint64 outs); Vint64 cap]
    e1 (Some result) ->
  exists c outs', result = Vint64 c /\
    e1!(param 6 search46) = Some (Varr (map Vint64 outs')) /\
    forall j, (0 <= j < n)%Z ->
    hard (IZR (S0 + j) * bp (uexp ex)) ->
    (nat_of c <= nat_of cap)%coq_nat ->
    In (Z.to_nat j) (firstn (nat_of c) (map nat_of outs')).
Proof.
move=> /ExpProof.check_rawP [_ hall] s hs.
have [S0 [ex [n [B [hp hok]]]]] := hall s hs.
exists S0, ex, n, B; split => //; split => //.
exact: search_line.
Qed.
