(** * num_bitlen: the number of bits of a

    The loop invariants are those of the VST proof (body_num_bitlen of
    ../../../vst/exp100/Verif_bits.v): after i rounds of the outer loop,
    b is the bit length of the i low limbs of a; after k rounds of the
    inner loop, b is the bit length of the i low limbs and of the k low
    bits of limb i. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** Bit lengths *)

(* A number of m bits plus 2^m has m + 1 bits. *)
Lemma bitlen_top Y m : (0 <= m)%Z -> (0 <= Y < 2 ^ m)%Z ->
  ExpModel.bitlen (Y + 2 ^ m) = (m + 1)%Z.
Proof.
move=> Hm HY; rewrite /ExpModel.bitlen.
have H2 : (0 < 2 ^ m)%Z by apply: Z.pow_pos_nonneg; lia.
case: (Z.leb_spec (Y + 2 ^ m) 0) => [|_]; first lia.
rewrite (Z.log2_unique (Y + 2 ^ m) m) //.
rewrite Z.pow_succ_r; lia.
Qed.

(* Scanning bit k of the limb of weight 2^m. *)
Lemma bitlen_step X m w k : (0 <= m)%Z -> (0 <= k)%Z -> (0 <= X < 2 ^ m)%Z ->
  ExpModel.bitlen (X + 2 ^ m * (w mod 2 ^ (k + 1))) =
  if (w / 2 ^ k) mod 2 =? 0 then ExpModel.bitlen (X + 2 ^ m * (w mod 2 ^ k))
  else (m + k + 1)%Z.
Proof.
move=> Hm Hk HX.
have Hk2 : (0 < 2 ^ k)%Z by apply: Z.pow_pos_nonneg; lia.
rewrite Z.pow_add_r ?Z.pow_1_r ?Z.rem_mul_r; try lia.
have Hb := Z.mod_pos_bound (w / 2 ^ k) 2 ltac:(lia).
have Hr := Z.mod_pos_bound w (2 ^ k) Hk2.
case: (Z.eqb_spec ((w / 2 ^ k) mod 2) 0) => [E|E].
- by rewrite E Z.mul_0_r Z.add_0_r.
- have -> : ((w / 2 ^ k) mod 2 = 1)%Z by lia.
  have Emk : (2 ^ (m + k) = 2 ^ m * 2 ^ k)%Z by apply: Z.pow_add_r; lia.
  have -> : (X + 2 ^ m * (w mod 2 ^ k + 2 ^ k * 1) =
             X + 2 ^ m * (w mod 2 ^ k) + 2 ^ (m + k))%Z by rewrite Emk; ring.
  rewrite bitlen_top //.
  all: rewrite ?Emk; nia.
Qed.

(** ** The words of the loop *)

(* Bit k of a limb, as num_bitlen tests it. *)
Lemma bit_test w k : (0 <= Int64.unsigned w < 2 ^ 32)%Z ->
  (Int64.unsigned k < 32)%Z ->
  Int64.eq (Int64.and (Int64.shru' w (Int.modu (Int64.loword k)
                                                Int64.iwordsize'))
                      (Int64.repr 1)) (Int64.repr 1) =
  ((Int64.unsigned w / 2 ^ Int64.unsigned k) mod 2 =? 1)%Z.
Proof.
move=> Hw Hk.
have Hk0 := Int64.unsigned_range k.
have M : Int.max_unsigned = 4294967295%Z by [].
have M64 : Int64.max_unsigned = 18446744073709551615%Z by [].
have Ek : Int.unsigned (Int.modu (Int64.loword k) Int64.iwordsize') =
          Int64.unsigned k.
{ rewrite /Int.modu /Int64.loword /Int64.iwordsize'.
  have R1 : (0 <= Int64.unsigned k <= Int.max_unsigned)%Z by lia.
  have R2 : (0 <= Int64.zwordsize <= Int.max_unsigned)%Z by rewrite M.
  rewrite (Int.unsigned_repr _ R1) (Int.unsigned_repr _ R2).
  change Int64.zwordsize with 64%Z.
  rewrite (Z.mod_small _ 64); first lia.
  by apply: Int.unsigned_repr; lia. }
have H2k : (1 <= 2 ^ Int64.unsigned k)%Z.
  by rewrite -(Z.pow_0_r 2); apply: Z.pow_le_mono_r; lia.
have Hd : (0 <= Int64.unsigned w / 2 ^ Int64.unsigned k <= Int64.max_unsigned)%Z.
{ rewrite M64; split; first by apply: Z.div_pos; lia.
  have := Z.div_le_upper_bound (Int64.unsigned w) (2 ^ Int64.unsigned k)
            (Int64.unsigned w) ltac:(lia) ltac:(nia).
  lia. }
rewrite /Int64.shru' Ek Z.shiftr_div_pow2; first lia.
set d := (Int64.unsigned w / 2 ^ Int64.unsigned k)%Z.
have E1 : Int64.repr 1 = Int64.sub (Int64.repr 2) Int64.one by [].
rewrite {1}E1 -(Int64.modu_and _ _ (Int64.repr 1)) //.
change (Int64.unsigned (Int64.repr 2)) with 2%Z.
rewrite /Int64.modu (Int64.unsigned_repr _ Hd) -/d.
have Hm := Z.mod_pos_bound d 2 ltac:(lia).
have R3 : (0 <= d mod 2 <= Int64.max_unsigned)%Z by rewrite M64; lia.
have R4 : (0 <= 1 <= Int64.max_unsigned)%Z by rewrite M64.
rewrite /Int64.eq (Int64.unsigned_repr _ R3) (Int64.unsigned_repr _ R4).
by case: (Z.eqb_spec (d mod 2) 1); case: Coqlib.zeq.
Qed.

(* The value 32 i + k + 1 that num_bitlen writes in b. *)
Lemma add_mul32 i k : (Int64.unsigned i < 6)%Z -> (Int64.unsigned k < 32)%Z ->
  Int64.add (Int64.add (Int64.mul (Int64.repr 32) i) k) (Int64.repr 1) =
  Int64.repr (32 * Int64.unsigned i + Int64.unsigned k + 1).
Proof. clia. Qed.

Lemma add1_32 k : (Int64.unsigned k < 32)%Z ->
  Int64.unsigned (Int64.add k (Int64.repr 1)) = (Int64.unsigned k + 1)%Z.
Proof. clia. Qed.

(* One more bit of limb i in num_bitlen. *)
Lemma bitlen_inner2 (a : numA) (i : 'I_NL) j k : limbsA a ->
  (0 <= k)%Z -> nat_of_ord i = j ->
  Int64.repr (ExpModel.bitlen (pval a j + limb_base j *
                (Int64.unsigned (a i) mod 2 ^ (k + 1)))) =
  if (Int64.unsigned (a i) / 2 ^ k) mod 2 =? 1
  then Int64.repr (32 * Z.of_nat j + k + 1)
  else Int64.repr (ExpModel.bitlen (pval a j + limb_base j *
                (Int64.unsigned (a i) mod 2 ^ k))).
Proof.
move=> Ha Hk <-.
have HX := pval_lt a i Ha (ltnW (ltn_ord i)).
rewrite /limb_base in HX *.
have Hm : (0 <= limb_bits * Z.of_nat i)%Z by rewrite /limb_bits; lia.
rewrite (bitlen_step _ _ _ _ Hm Hk HX).
have Hb := Z.mod_pos_bound (Int64.unsigned (a i) / 2 ^ k) 2 ltac:(lia).
by case: (Z.eqb_spec ((Int64.unsigned (a i) / 2 ^ k) mod 2) 0) => E0;
  case: (Z.eqb_spec ((Int64.unsigned (a i) / 2 ^ k) mod 2) 1) => E1 //;
  lia.
Qed.

(** ** The proof *)

Theorem num_bitlen_ok : num_bitlen_spec.
Proof.
move=> μ a r rl Ha.
start; csteps.
inv I := { [:: b; i] } (fun bv iv =>
  (iv:N <= 6)%nat /\ bv = Int64.repr (ExpModel.bitlen (pval a iv:N))).
enter_loop I.
{ prove_inv; exsp.
  by have -> : (Int64.repr 0):N = 0%nat by []; rewrite pval0. }
unfold_inv => - [Hi Hb].
csteps.
case END: Int64.ltu => /=.
- csteps.
  have Hi6 : (i0:N < NL)%nat by rewrite /NL; move: END; clia.
  inv J := { [:: b; k] } (fun bv kv =>
    (kv:N <= 32)%nat /\
    bv = Int64.repr (ExpModel.bitlen (pval a i0:N + limb_base i0:N *
           (Int64.unsigned (a (Ordinal Hi6)) mod 2 ^ Int64.unsigned kv)))).
  enter_loop J.
  { prove_inv; exsp.
    change (Int64.unsigned (Int64.repr 0)) with 0%Z.
    by rewrite Hb Z.pow_0_r Z.mod_1_r Z.mul_0_r Z.add_0_r. }
  unfold_inv => - [Hk Hbk].
  csteps.
  case ENDk: Int64.ltu => /=.
  + csteps; evalf; csteps.
    have Hk32 : (Int64.unsigned k1 < 32)%Z by move: ENDk; clia.
    have Hk0 := proj1 (Int64.unsigned_range k1).
    have Ei : Z.of_nat i0:N = Int64.unsigned i0.
      by rewrite Z2Nat.id //; case: (Int64.unsigned_range i0).
    have Hi32 : (Int64.unsigned i0 < 6)%Z by move: END; clia.
    have := bit_test _ _ (Ha (Ordinal Hi6)) Hk32.
    case BIT: Int64.eq => /= Ebit.
    * csteps; evalf; csteps.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp.
      { move: ENDk; clia. }
      rewrite add1_32 // bitlen_inner2 // -Ebit add_mul32 //.
      by rewrite Ei.
    * csteps; evalf; csteps.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp.
      { move: ENDk; clia. }
      by rewrite add1_32 // bitlen_inner2 // -Ebit.
  + csteps; cret; split=> //= _.
    csteps; cret; split=> // _; split.
    { solve_loop_conditions. }
    prove_inv; exsp.
    { move: END; clia. }
    have Ek : Int64.unsigned k1 = 32%Z by move: ENDk Hk; clia.
    have Ei1 : (Int64.add i0 (Int64.repr 1)):N = (i0:N).+1.
      by move: END; clia.
    have Hl := Ha (Ordinal Hi6).
    rewrite Hbk Ek Z.mod_small; first exact: Hl.
    by rewrite Ei1 (pvalSn a _ Hi6).
- csteps; cret; split=> //= _; csteps; fin.
  have Ei : i0:N = NL by rewrite /NL; move: END Hi; clia.
  by rewrite Hb Ei pval_all.
Qed.
