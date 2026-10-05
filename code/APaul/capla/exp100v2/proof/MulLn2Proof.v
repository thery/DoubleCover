(** * mul_ln2: q = floor(n LN2 / 2^32), for n < 2^32

    mul_ln2 calls num_mul_small: its statement [num_mul_small_spec] is
    a hypothesis of [mul_ln2_ok], proved in MulSmallProof.v.  The
    product p = LN2 n has 7 limbs; the loop copies its limbs 1 .. 6 into
    q.  The loop invariant is the one of the VST proof (body_mul_ln2 of
    ../../../vst/exp100/Verif_reduce.v): after i rounds, limb j of q is
    limb j + 1 of p for j < i. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpTable.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(* An array of words with one word written, as a function. *)
Lemma setV_ffun n (f : {ffun 'I_n -> int64}) (k : 'I_n) a :
  [ffun j => if j == k then Vint64 a else [ffun x => Vint64 (f x)] j] =
  [ffun x => Vint64 ([ffun j => if j == k then a else f j] x)].
Proof. by apply/ffunP => j; rewrite !ffunE; case: eqP. Qed.

(* A number of 6 limbs made of the limbs 1 .. 6 of a number of 7 limbs. *)
Lemma drop1_val (p : {ffun 'I_NP -> int64}) (qv : numA) :
  limbsA p ->
  (forall j : 'I_NL, exists H : (j.+1 < NP)%nat, qv j = p (Ordinal H)) ->
  limbsA qv /\ valA qv = valA p / 2 ^ limb_bits.
Proof.
move=> Hp Hq.
have Ew : words qv = behead (words p).
{ apply: (@eq_from_nth _ 0); first by rewrite size_behead size_words size_words.
  move=> k; rewrite size_words => Hk.
  rewrite -[k]/(nat_of_ord (Ordinal Hk)) nth_words.
  have [H ->] := Hq (Ordinal Hk).
  by rewrite nth_behead -[k.+1]/(nat_of_ord (Ordinal H)) nth_words. }
split.
- move=> j; have [H ->] := Hq j; exact: Hp.
- rewrite /valA Ew -(valZ_drop1 _ (proj1 (limbsA_Forall p) Hp)).
  by case: (words p).
Qed.

Theorem mul_ln2_ok : num_mul_small_spec -> mul_ln2_spec.
Proof.
move=> MS μ qq L2 nn r rl HL Hn.
have HL2 : limbsA L2.
  by apply/limbsA_Forall; rewrite HL; exact: (proj2 ExpConsts.num_LN2).
enter_func; csteps.
call MS => /(_ HL2 Hn) [p' [-> [Hp Hv]]].
csteps.
inv I := { [:: q; i] } (fun qv iv =>
  (iv:N <= 6)%nat /\
  forall j : 'I_NL, (j < iv:N)%nat -> exists H : (j.+1 < NP)%nat, qv j = p' (Ordinal H)).
enter_loop I.
{ prove_inv; exsp. }
unfold_inv => - [Hi Hq].
csteps.
case END: Int64.ltu => /=.
- csteps; evalf; csteps.
  rewrite setV_ffun.
  cret; split=> // _; split.
  { solve_loop_conditions. }
  prove_inv; exsp.
  { move=> j Hj.
    have Ei : (Int64.add i0 (Int64.repr 1)):N = (i0:N).+1 by clia i0.
    have Hj6 : (j.+1 < NP)%nat by exact: ltn_ord j.
    exists Hj6; rewrite ffunE; case: eqP => [Ej|Nj].
    - congr (fun_of_fin p'); apply: val_inj => /=; rewrite Ei.
      by move: Ej => /(f_equal (@nat_of_ord _)) /= ->.
    - have Hji : (j < i0:N)%nat.
        move: Hj; rewrite Ei ltnS leq_eqVlt => /orP [/eqP Ej|//].
        by case: Nj; apply: val_inj.
      have [H' ->] := Hq j Hji.
      by congr (fun_of_fin p'); apply: val_inj. }
- csteps; cret; split=> //= _; csteps; cret.
  have Hi6 : i0:N = 6%nat by move: END Hi; clia.
  have Hall : forall j : 'I_NL, exists H : (j.+1 < NP)%nat, q0 j = p' (Ordinal H).
    by move=> j; apply: Hq; rewrite Hi6; exact: ltn_ord j.
  have [Hl Hval] := drop1_val p' q0 Hp Hall.
  exists q0; split; [by []|split; first exact: Hl].
  rewrite Hval Hv ExpModel.qE /valA HL; congr (_ / _); ring.
Qed.
