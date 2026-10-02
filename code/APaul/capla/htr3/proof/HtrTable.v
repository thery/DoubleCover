(** * The table check and the Capla search, through [line_ok]

    [check_raw] is the check of a table file (code/exptablekl): when it
    answers [true], every line of the file satisfies [line_ok]
    ([ExpProof.check_rawP]).  Each line has its own number of terms [k]
    and of words [l].  Here, on a line that satisfies [line_ok], the Capla
    [search] of [htr3.b], run with the parameters of the line ([k]
    coefficients of [l] words, the window [err = ERR = 0x600000], the
    inputs [j = 0 .. n-1]), returns every hard-to-round input of the
    line, when their number fits in the output array.  So:
    [check_raw] -> [line_ok] -> no [hard] input is missed. *)

From Stdlib Require Import Reals Lra.
From ExpTableKL Require ExpCheck ExpParse ExpProof ExpHard.
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
Local Notation ERR := ExpCheck.ERR.

(** ** The two descriptions of a line agree *)

(** The sums of [ExpCheck] and of [TaylorReal]. *)
Lemma sumR_TaylorReal (f : nat -> R) (N : nat) :
  TaylorReal.sumR N f = ExpCheck.sumR f N.
Proof. by elim: N => [|N IH] //=; rewrite IH. Qed.

(** The polynomials of [ExpCheck] and of [HtrDefs]. *)
Lemma Pz_polyZ k (A : list Z) j :
  length A = k -> ExpCheck.Pz k A j = polyZ A j.
Proof. by move=> hA; rewrite /ExpCheck.Pz /polyZ hA. Qed.

(** [beta^l] of [ExpCheck] is [base l]. *)
Lemma beta_l_base l : (0 <= l)%Z -> ExpCheck.beta_l l = base (Z.to_nat l).
Proof.
move=> l0; rewrite /ExpCheck.beta_l /ExpCheck.beta /base.
have -> : Z.of_nat (Z.to_nat l) = l by lia.
by rewrite -Z.pow_mul_r //; lia.
Qed.

(** The window [E l] of [ExpCheck] is [err beta^(l-1)], [err = ERR]. *)
Lemma E_err l : (1 <= l)%Z ->
  ExpCheck.E l =
  (Int64.unsigned (Int64.repr ERR) *
   2 ^ (64 * (Z.of_nat (Z.to_nat l) - 1)))%Z.
Proof.
move=> l1; have -> : Z.of_nat (Z.to_nat l) = l by lia.
have -> : Int64.unsigned (Int64.repr ERR) = ERR by vm_compute.
by rewrite /ExpCheck.E /ExpCheck.beta -Z.pow_mul_r //; lia.
Qed.

(** A natural number [j] as a real. *)
Lemma INR_Z2N (j : Z) : (0 <= j)%Z -> INR (Z.to_nat j) = IZR j.
Proof. by move=> j0; rewrite INR_IZR_INZ Z2Nat.id. Qed.

(** The [n] of a line fits in a word. *)
Lemma line_ok_n S0 ex n k l B :
  line_ok S0 ex n k l B -> (1 <= n < 2 ^ 53)%Z.
Proof.
move=> hok; destruct hok as (e & hn & h52 & h53 & hsg & _).
change ExpCheck.drop with 1%Z in *.
have : (0 < S0 /\ 0 < S0 + n - 1 \/ S0 < 0 /\ S0 + n - 1 < 0)%Z by nia.
by lia.
Qed.

(** The [k] and [l] of a line: condition 6. *)
Lemma line_ok_kl S0 ex n k l B :
  line_ok S0 ex n k l B ->
  ((1 <= k)%coq_nat /\ (k <= 13)%coq_nat) /\ (1 <= l <= 8)%Z.
Proof.
move=> hok; destruct hok as (e & _ & _ & _ & _ & _ & _ & _ & _ & _ & hk &
  hl & _).
change ExpCheck.kmax with 13%nat in hk.
by change ExpCheck.lmax with 8%Z in hl; lia.
Qed.

(** ** On one line *)

Theorem search_line S0 ex n k l B :
  line_ok S0 ex n k l B ->
  forall xs len outs cap e1 result,
  (* the array holds B, each B_i in l words, the least significant first *)
  length xs = nat_of len -> (k * Z.to_nat l <= nat_of len)%coq_nat ->
  vcoefs xs (Z.to_nat l) k = B ->
  length outs = nat_of cap ->
  (* the run of search, with the k and l of the line and err = ERR *)
  eval_funcall ge (Internal search46)
    [Varr (map Vint64 xs); Vint64 len; Vint64 (Int64.repr (Z.of_nat k));
     Vint64 (Int64.repr l); Vint64 (Int64.repr n);
     Vint64 (Int64.repr ERR); Varr (map Vint64 outs); Vint64 cap]
    e1 (Some result) ->
  exists c outs', result = Vint64 c /\
    e1!(param 6 search46) = Some (Varr (map Vint64 outs')) /\
    forall j, (0 <= j < n)%Z ->
    hard (IZR (S0 + j) * bp (uexp ex)) ->
    (nat_of c <= nat_of cap)%coq_nat ->
    In (Z.to_nat j) (firstn (nat_of c) (map nat_of outs')).
Proof.
move=> hok xs len outs cap e1 result hxs hlen hv houts hrun.
have [n1 n53] := line_ok_n S0 ex n k l B hok.
have [[k1 k13] [l1 l8]] := line_ok_kl S0 ex n k l B hok.
have nk : nat_of (Int64.repr (Z.of_nat k)) = k.
  rewrite /nat_of Int64.unsigned_repr ?Nat2Z.id //.
  by change Int64.max_unsigned with (2 ^ 64 - 1)%Z; lia.
have nl : nat_of (Int64.repr l) = Z.to_nat l.
  rewrite /nat_of Int64.unsigned_repr //.
  by change Int64.max_unsigned with (2 ^ 64 - 1)%Z; lia.
have nn : nat_of (Int64.repr n) = Z.to_nat n.
  rewrite /nat_of Int64.unsigned_repr //.
  by change Int64.max_unsigned with (2 ^ 64 - 1)%Z; lia.
have herr : (2 * Int64.unsigned (Int64.repr ERR) <=
             Int64.max_unsigned)%Z by vm_compute.
(* the count and the output array, from the run *)
have [c [outs' [hc [he1 _]]]] := search_spec xs len
  (Int64.repr (Z.of_nat k)) (Int64.repr l) (Int64.repr n) (Int64.repr ERR)
  outs cap e1 result hxs ltac:(rewrite nk nl; lia) ltac:(rewrite nk; lia)
  ltac:(rewrite nl; lia) herr houts hrun.
exists c, outs'; split => //; split => // j hj hhard hcap.
(* the conditions of the line *)
move: hok; rewrite /ExpCheck.line_ok; cbv zeta.
change ExpCheck.drop with 1%Z.
move=> hok.
destruct hok as (e & _ & _ & _ & _ & hv0 & hvl & (A & hlA & hlB & hA & hB) &
  hT & hE & _).
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
have hbl := beta_l_base l ltac:(lia).
have hmap : vcoefs xs (Z.to_nat l) k =
    map (fun i => polyZ A (Z.of_nat i) mod base (Z.to_nat l))%Z (seq 0 k).
  rewrite hv; apply: (nth_ext _ _ 0%Z 0%Z).
    by rewrite length_map length_seq hlB.
  move=> i hi; rewrite hlB in hi.
  rewrite hB //.
  rewrite (nth_indep _ 0%Z (polyZ A (Z.of_nat 0) mod base (Z.to_nat l))%Z).
    by rewrite length_map length_seq.
  by rewrite map_nth seq_nth // (Pz_polyZ k) // hbl.
have hA' : forall i, (i < k)%coq_nat ->
    (Rabs (IZR (nth i A 0%Z) - IZR (base (Z.to_nat l)) *
             frac_part (ExpCheck.a (IZR S0 * u) u i / v)) < 1)%R.
  move=> i hi; have [_] := hA i hi.
  by rewrite ExpHard.fracR_frac_part hbl.
have hj0 : (0 <= j)%Z by lia.
have hT' := hT j ltac:(lia).
rewrite -sumR_TaylorReal -(INR_Z2N j hj0) in hT'.
rewrite [in exp _](INR_Z2N j hj0) in hT'.
have nR : INR (Z.to_nat n) = IZR n by apply: INR_Z2N; lia.
rewrite (E_err l l1) hbl -sumR_TaylorReal -nR in hE.
have := search_complete xs len (Int64.repr (Z.of_nat k)) (Int64.repr l)
  (Int64.repr n) (Int64.repr ERR) outs cap e1 result A
  (fun i => ExpCheck.a (IZR S0 * u) u i / v)%R rho
  (bp (- ExpCheck.m)) (exp (IZR S0 * u + IZR j * u) / v)%R (Z.to_nat j).
cbv zeta; rewrite nk nl nn.
move=> /(_ hxs ltac:(lia) ltac:(lia) ltac:(lia) herr houts).
move=> /(_ hlA hmap hA' hT' hE ltac:(lia) hz hrun).
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
  forall s, In s ls -> exists S0 ex n k l B,
  parse s = Some (S0, ex, n, k, l, B) /\ line_ok S0 ex n k l B /\
  forall xs len outs cap e1 result,
  (* the array holds B, each B_i in l words, the least significant first *)
  length xs = nat_of len -> (k * Z.to_nat l <= nat_of len)%coq_nat ->
  vcoefs xs (Z.to_nat l) k = B ->
  length outs = nat_of cap ->
  (* the run of search, with the k and l of the line and err = ERR *)
  eval_funcall ge (Internal search46)
    [Varr (map Vint64 xs); Vint64 len; Vint64 (Int64.repr (Z.of_nat k));
     Vint64 (Int64.repr l); Vint64 (Int64.repr n);
     Vint64 (Int64.repr ERR); Varr (map Vint64 outs); Vint64 cap]
    e1 (Some result) ->
  exists c outs', result = Vint64 c /\
    e1!(param 6 search46) = Some (Varr (map Vint64 outs')) /\
    forall j, (0 <= j < n)%Z ->
    hard (IZR (S0 + j) * bp (uexp ex)) ->
    (nat_of c <= nat_of cap)%coq_nat ->
    In (Z.to_nat j) (firstn (nat_of c) (map nat_of outs')).
Proof.
move=> /ExpProof.check_rawP hall s hs.
have [S0 [ex [n [k [l [B [hp hok]]]]]]] := hall s hs.
exists S0, ex, n, k, l, B; split => //; split => //.
exact: search_line.
Qed.
