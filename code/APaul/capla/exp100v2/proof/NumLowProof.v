(** * num_low: a = b mod 2^f, for f < 192

    The loop invariant is the one of the VST proof (body_num_low of
    ../../../vst/exp100/Verif_bits.v): after i rounds, the i low words of
    a are those of the target [low_target]: the words of b below limb
    f / 32, the f mod 32 low bits of limb f / 32, then zeros. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpModel.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas Exp100Capla2.NumPow2Proof.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** Words *)

(* The m low bits of a word. *)
Lemma and_low y m : 0 <= m < 64 ->
  Int64.and y (Int64.repr (2 ^ m - 1)) =
  Int64.repr (Int64.unsigned y mod 2 ^ m).
Proof.
  move=> Hm.
  have -> : 2 ^ m - 1 = Z.ones m by rewrite Z.ones_equiv; lia.
  apply: Int64.same_bits_eq => k Hk.
  rewrite Int64.bits_and // !Int64.testbit_repr //.
  rewrite -Z.land_ones; first lia.
  by rewrite Z.land_spec.
Qed.

(* The mask (1 << (f mod 32)) - 1. *)
Lemma mask_eq f :
  Int64.sub (Int64.shl' (Int64.repr 1)
     (Int.modu (Int64.loword (Int64.modu f (Int64.repr 32))) Int64.iwordsize'))
     (Int64.repr 1) = Int64.repr (2 ^ (Int64.unsigned f mod 32) - 1).
Proof.
  rewrite /Int64.sub shl1_mod32; congr Int64.repr.
Qed.

(* y & ((1 << (f mod 32)) - 1) = y mod 2^(f mod 32). *)
Lemma mask_and y f :
  Int64.unsigned (Int64.and y (Int64.sub (Int64.shl' (Int64.repr 1)
     (Int.modu (Int64.loword (Int64.modu f (Int64.repr 32))) Int64.iwordsize'))
     (Int64.repr 1))) = Int64.unsigned y mod 2 ^ (Int64.unsigned f mod 32).
Proof.
  have Hm := Z.mod_pos_bound (Int64.unsigned f) 32 ltac:(lia).
  rewrite mask_eq and_low; first lia.
  have := Z.mod_pos_bound (Int64.unsigned y) (2 ^ (Int64.unsigned f mod 32))
            ltac:(apply: Z.pow_pos_nonneg; lia).
  have : 2 ^ (Int64.unsigned f mod 32) < 2 ^ 32.
  { apply: Z.pow_lt_mono_r; lia. }
  move=> ? ?; rewrite Int64.unsigned_repr //.
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

(* (A + 2^n B) mod 2^(n+m), for A < 2^n. *)
Lemma mod_shift A B n m : 0 <= n -> 0 <= m -> 0 <= A < 2 ^ n ->
  (A + 2 ^ n * B) mod 2 ^ (n + m) = A + 2 ^ n * (B mod 2 ^ m).
Proof.
  move=> Hn Hm HA.
  have Hp : 0 < 2 ^ m by apply: Z.pow_pos_nonneg; lia.
  have HB := Z.mod_pos_bound B (2 ^ m) Hp.
  rewrite Z.pow_add_r //.
  symmetry; apply: (Z.mod_unique _ _ (B / 2 ^ m)); [left|].
  - nia.
  - have EB := Z.div_mod B (2 ^ m) ltac:(lia).
    rewrite {1}EB; ring.
Qed.

Lemma limb_baseD i j : limb_base (i + j) = limb_base i * limb_base j.
Proof.
  rewrite /limb_base Nat2Z.inj_add Z.mul_add_distr_l Z.pow_add_r //;
    rewrite /limb_bits; lia.
Qed.

(** ** The target *)

(* Limbs of b below q, limb q masked by m, then zeros. *)
Definition low_target (b : numA) (q : nat) (m : int64) : numA :=
  [ffun j : 'I_NL => if (j < q)%nat then b j
     else if nat_of_ord j == q then Int64.and (b j) m else Int64.zero].

Lemma low_targetE b q m j : low_target b q m j =
  if (j < q)%nat then b j
  else if nat_of_ord j == q then Int64.and (b j) m else Int64.zero.
Proof. by rewrite ffunE. Qed.

(* A limb masked to its s low bits is a limb. *)
Lemma mod_limb_aux x s : 0 <= s < 32 -> 0 <= x mod 2 ^ s < 2 ^ 32.
Proof.
  move=> Hs.
  have Hp : 0 < 2 ^ s by apply: Z.pow_pos_nonneg; lia.
  have := Z.mod_pos_bound x (2 ^ s) Hp.
  have := Z.pow_le_mono_r 2 s 32 ltac:(lia) ltac:(lia).
  lia.
Qed.

Section Low.

Variables (b : numA) (q : nat) (m : int64) (r : Z).
Hypothesis Hb : limbsA b.
Hypothesis Hq : (q < NL)%nat.
Hypothesis Hr : 0 <= r < 32.
Hypothesis Hm :
  forall x, Int64.unsigned (Int64.and x m) = Int64.unsigned x mod 2 ^ r.

(* The k low limbs of the target. *)
Lemma pval_low k : (k <= NL)%nat ->
  pval (low_target b q m) k =
  if (k <= q)%nat then pval b k
  else pval b q + limb_base q * (Int64.unsigned (b (Ordinal Hq)) mod 2 ^ r).
Proof.
  elim: k => [|k IH] Hk; first by rewrite !pval0.
  rewrite (pvalSn _ _ Hk) (IH (ltnW Hk)) low_targetE /=.
  case: (ltngtP k q) => [Lt|Gt|Eq].
  - by rewrite (pvalSn _ _ Hk).
  - by rewrite Int64.unsigned_zero; ring.
  - have E : Ordinal Hk = Ordinal Hq by apply: val_inj.
    by rewrite E Hm Eq.
Qed.

(* From limb q + 1 on, b adds a multiple of the weight of limb q + 1. *)
Lemma pval_high k : (q < k <= NL)%nat ->
  exists X, pval b k = pval b q.+1 + limb_base q.+1 * X.
Proof.
  elim: k => [|k IH] /andP [Hqk Hk]; first by rewrite ltn0 in Hqk.
  case: (ltngtP q k) => [Lt|Gt|Eq].
  - have [X EX] := IH ltac:(by rewrite Lt ltnW).
    exists (X + limb_base (k - q.+1) * Int64.unsigned (b (Ordinal Hk))).
    rewrite (pvalSn _ _ Hk) EX.
    have -> : limb_base k = limb_base q.+1 * limb_base (k - q.+1).
    { by rewrite -limb_baseD subnKC. }
    ring.
  - by move: Hqk; rewrite ltnS leqNgt Gt.
  - by exists 0%Z; rewrite Eq; ring.
Qed.

(* Every word of the target is a limb. *)
Lemma limbsA_low : limbsA (low_target b q m).
Proof.
  move=> j; rewrite low_targetE.
  case: (j < q)%nat; first exact: Hb.
  case: (nat_of_ord j == q).
  - by rewrite Hm /limb /limb_bits; apply: mod_limb_aux.
  - by rewrite Int64.unsigned_zero.
Qed.

(* The target stands for b mod 2^(32 q + r). *)
Lemma valA_low : valA (low_target b q m) =
  valA b mod 2 ^ (limb_bits * Z.of_nat q + r).
Proof.
  rewrite -!(pval_all (n := NL)) pval_low // leqNgt Hq /=.
  have [X EX] := pval_high NL ltac:(by rewrite Hq leqnn).
  have Hp := pval_lt b q Hb (ltnW Hq).
  have E : pval b NL = pval b q + 2 ^ (limb_bits * Z.of_nat q) *
             (Int64.unsigned (b (Ordinal Hq)) + 2 ^ limb_bits * X).
  { by rewrite EX (pvalSn _ _ Hq) limb_baseS /limb_base; ring. }
  have Hn : 0 <= limb_bits * Z.of_nat q.
  { by apply: Z.mul_nonneg_nonneg; [|apply: Nat2Z.is_nonneg]. }
  rewrite E (mod_shift _ _ _ _ Hn (proj1 Hr) Hp).
  (* lia loops with Hr in the context: Hr is split first *)
  have Hl : 2 ^ limb_bits = 2 ^ (limb_bits - r) * 2 ^ r.
  { case: Hr => H0 H1; rewrite -Z.pow_add_r ?Z.sub_add //.
    rewrite /limb_bits; clear -H1; lia. }
  have Hz : 2 ^ r <> 0 by apply: Z.pow_nonzero; [|case: Hr].
  rewrite Hl -Z.mul_assoc (Z.mul_comm (2 ^ r)) Z.mul_assoc Z.mod_add //.
Qed.

End Low.

(** ** num_low *)

Theorem num_low_ok : num_low_spec.
Proof.
move=> μ a0 b0 f r rl Hb Hf.
have E32 : Int64.eq (Int64.repr 32) Int64.zero = false by [].
pose q := (Int64.divu f (Int64.repr 32)):N.
pose m := Int64.sub (Int64.shl' (Int64.repr 1)
  (Int.modu (Int64.loword (Int64.modu f (Int64.repr 32))) Int64.iwordsize'))
  (Int64.repr 1).
pose T := low_target b0 q m.
enter_func; csteps.
(* the i low words of a are those of the target *)
inv I := { [:: a; i] } (fun (a : numA) (i : int64) =>
  (i:N <= NL)%nat /\ forall j : 'I_NL, (j < i:N)%nat -> a j = T j).
enter_loop I.
{ prove_inv; exsp. }
unfold_inv => - [Hi Ha].
csteps.
case LT: Int64.ltu => /=.
- csteps; rewrite /divu64 E32 /=; csteps.
  case C1: Int64.ltu => /=.
  + (* below limb f / 32: a copy *)
    have Hq : (i0:N < q)%nat by move: C1; rewrite /q; clia.
    csteps; rewrite (fffE' _ _ H) /= setf_map.
    cret; split=> // _; split.
    { solve_loop_conditions. }
    prove_inv; exsp.
    { move: Hi; rewrite /NL; clia i0. }
    move=> j Hj; rewrite (setfP _ _ _ H) low_targetE.
    case: eqP => [Ej|ne].
    { have -> : j = Ordinal H by apply: val_inj.
      by rewrite /= Hq. }
    rewrite -low_targetE; apply: Ha; move: Hi; rewrite /NL; clia i0.
  + csteps; rewrite /divu64 E32 /=; csteps.
    case C2: Int64.eq => /=.
    * (* limb f / 32: its low bits *)
      have Eq : (i0:N = q)%nat.
      { move: C2; rewrite /q; clia. }
      csteps; rewrite /modu64 E32 /=; csteps.
      rewrite (fffE' _ _ H) /=; csteps.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp.
      { move: Hi; rewrite /NL; clia i0. }
      move=> j Hj; rewrite (setfP _ _ _ H) low_targetE.
      case: eqP => [Ej|ne].
      { have -> : j = Ordinal H by apply: val_inj.
        by rewrite /= -Eq ltnn eqxx. }
      rewrite -low_targetE; apply: Ha; move: Hi; rewrite /NL; clia i0.
    * (* above limb f / 32: zero *)
      have Gq : (q < i0:N)%nat.
      { move: C1 C2; rewrite /q; clia. }
      csteps.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp.
      { move: Hi; rewrite /NL; clia i0. }
      move=> j Hj; rewrite (setfP _ _ _ H) low_targetE.
      case: eqP => [Ej|ne].
      { rewrite Ej ltnNge (ltnW Gq) /=.
        by have /negbTE -> : (i0:N != q) by rewrite neq_ltn Gq orbT. }
      rewrite -low_targetE; apply: Ha; move: Hi; rewrite /NL; clia i0.
- (* the end: a is the target *)
  csteps; cret; split=> //= _; csteps; cret.
  rewrite/envC/=.
  have Ei : (i0:N = 6)%nat by move: Hi; rewrite /NL; clia i0.
  have Ea : a1 = T :> numA.
  { apply/ffunP => j; apply: Ha; rewrite Ei; exact: ltn_ord. }
  exists T; split; first by rewrite -Ea.
  have Hf' : 0 <= Int64.unsigned f < 192.
  { have := Int64.unsigned_range f; move: Hf.
    rewrite /ExpModel.num_bits /limb_bits /NL /=; lia. }
  have Hd : 0 <= Int64.unsigned f / 32 < 6.
  { split; [apply: Z.div_pos | apply: Z.div_lt_upper_bound]; lia. }
  have Eq : Z.of_nat q = Int64.unsigned f / 32.
  { by rewrite /q divu32 Z2Nat.id; lia. }
  have Hq : (q < NL)%nat by rewrite /NL; lia.
  have Ef : Int64.unsigned f =
            32 * (Int64.unsigned f / 32) + Int64.unsigned f mod 32.
  { exact: Z.div_mod. }
  have Hr := Z.mod_pos_bound (Int64.unsigned f) 32 ltac:(lia).
  have Hm : forall x, Int64.unsigned (Int64.and x m) =
              Int64.unsigned x mod 2 ^ (Int64.unsigned f mod 32).
  { by move=> x; apply: mask_and. }
  split; first exact: (limbsA_low b0 q m _ Hb Hr Hm).
  rewrite /T (valA_low b0 q m _ Hb Hq Hr Hm) Eq ExpModel.lowE.
  { by case: Hf'. }
  by rewrite /limb_bits -Ef.
Qed.
