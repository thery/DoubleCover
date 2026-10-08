(** * num_lt: a < b

    The loop runs i = 5 - k from the top limb down.  Its invariant is the
    one of the VST proof (body_num_lt of ../../../vst/exp100/Verif_bits.v):
    after k rounds, the k top limbs of a and b are equal. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** Comparing from the top limb *)

(* Equal limbs above i and a smaller limb i: from limb i on, the low
   limbs of a stand for less than those of b. *)
Lemma pval_lt_top (a b : numA) (i : 'I_NL) k : limbsA a -> limbsA b ->
  (forall j : 'I_NL, (i < j)%nat -> a j = b j) ->
  Int64.unsigned (a i) < Int64.unsigned (b i) ->
  (i < k <= NL)%nat -> pval a k < pval b k.
Proof.
  move=> Ha Hb Ht Hi; elim: k => [|k IH] // /andP [Hik Hk].
  rewrite (pvalS a (Ordinal Hk)) (pvalS b (Ordinal Hk)).
  case: (ltngtP i k) => [lt|gt|eq].
  - rewrite Ht //; have := IH; rewrite lt ltnW //=; lia.
  - by move: Hik; rewrite ltnS leqNgt gt.
  - have -> : Ordinal Hk = i by apply: val_inj.
    have := pval_lt a i Ha (ltnW (ltn_ord i)).
    have := pval_lt b i Hb (ltnW (ltn_ord i)).
    have := limb_base_pos i => Hl.
    have : limb_base i * (Int64.unsigned (a i) + 1) <=
           limb_base i * Int64.unsigned (b i).
    { apply: Z.mul_le_mono_nonneg_l; lia. }
    lia.
Qed.

(* Equal limbs above i and a smaller limb i: a smaller number. *)
Lemma valA_lt_top (a b : numA) (i : 'I_NL) : limbsA a -> limbsA b ->
  (forall j : 'I_NL, (i < j)%nat -> a j = b j) ->
  Int64.unsigned (a i) < Int64.unsigned (b i) -> valA a < valA b.
Proof.
  move=> Ha Hb Ht Hi.
  have := pval_lt_top a b i NL Ha Hb Ht Hi; rewrite ltn_ord leqnn.
  by rewrite !(pval_all (n := NL)); apply.
Qed.

(** ** num_lt *)

Theorem num_lt_ok : num_lt_spec.
Proof.
move=> μ a0 b0 r rl Ha Hb.
start; csteps.
(* the k top limbs of a and b are equal *)
inv I := { [:: k] } (fun (k : int64) =>
  (k:N <= 6)%nat /\ forall j : 'I_NL, (6 - k:N <= j)%nat -> a0 j = b0 j).
enter_loop I.
{ prove_inv; exsp.
  move=> j; have := ltn_ord j; rewrite /NL; clia. }
unfold_inv => - [Hk Ht].
csteps.
case LT: Int64.ltu => /=.
- csteps.
  rewrite !(fffE' _ _ H) /=; csteps.
  have Hi5 : ((Int64.sub (Int64.repr 5) k0):N = 5 - k0:N)%nat.
  { move: LT; clia k0. }
  have Htop : forall j : 'I_NL, (Ordinal H < j)%nat -> a0 j = b0 j.
  { move=> j /= Hj; apply: Ht; move: Hj; rewrite Hi5; clia k0. }
  case L1: Int64.ltu => /=.
  + (* a_i < b_i: true *)
    csteps; cret; split=> // _; csteps; fin.
    rewrite/envC/=; split=> //.
    have Hab : Int64.unsigned (a0 (Ordinal H)) <
      Int64.unsigned (b0 (Ordinal H)).
    { by move: L1; rewrite /Int64.ltu; case: Coqlib.zlt. }
    by have /Z.ltb_lt -> := valA_lt_top a0 b0 (Ordinal H) Ha Hb Htop Hab.
  + csteps.
    rewrite !(fffE' _ _ H) /=; csteps.
    have Hba : Int64.unsigned (b0 (Ordinal H)) <=
      Int64.unsigned (a0 (Ordinal H)).
    { move: L1; rewrite /Int64.ltu; case: Coqlib.zlt => [//|Hn _]; lia. }
    case L2: Int64.ltu => /=.
    * (* a_i > b_i: false *)
      csteps; cret; split=> // _; csteps; fin.
      rewrite/envC/=; split=> //.
      have Hab : Int64.unsigned (b0 (Ordinal H)) <
        Int64.unsigned (a0 (Ordinal H)).
      { by move: L2; rewrite /Int64.ltu; case: Coqlib.zlt. }
      have Htop' : forall j : 'I_NL, (Ordinal H < j)%nat -> b0 j = a0 j.
      { by move=> j Hj; rewrite Htop. }
      have := valA_lt_top b0 a0 (Ordinal H) Hb Ha Htop' Hab.
      by move=> Hlt; case: Z.ltb_spec => //; lia.
    * (* a_i = b_i: the next limb *)
      csteps; cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp.
      { clia k0. }
      have Hab : Int64.unsigned (a0 (Ordinal H)) <=
        Int64.unsigned (b0 (Ordinal H)).
      { move: L2; rewrite /Int64.ltu; case: Coqlib.zlt => [//|Hn _]; lia. }
      have Eab : a0 (Ordinal H) = b0 (Ordinal H).
      { rewrite -(Int64.repr_unsigned (a0 _)) -(Int64.repr_unsigned (b0 _)).
        congr Int64.repr; lia. }
      move=> j Hj.
      have [Ej|Ej] : nat_of_ord j = (Int64.sub (Int64.repr 5) k0):N \/
                     (6 - k0:N <= j)%nat.
      { move: Hj; rewrite Hi5; clia k0. }
      { by have -> : j = Ordinal H by apply: val_inj. }
      by apply: Ht.
- (* all limbs equal: false *)
  csteps; cret; split=> //= _; csteps; fin.
  rewrite/envC/=; split=> //.
  have -> : a0 = b0.
  { apply/ffunP => j; apply: Ht; have := ltn_ord j; rewrite /NL; clia k0. }
  by rewrite Z.ltb_irrefl.
Qed.
