(** * num_mulshr: r = floor(a b / 2^160), when it fits

    The loop invariants are those of the VST proof (body_num_mulshr of
    ../../../vst/exp100/Verif_mulshr.v).  The scratch array p of 12 limbs
    starts at 0.  Outer loop: after i rounds, p stands for the i low limbs
    of a times b, and the limbs from i + 6 on are 0.  Inner loop: after j
    rounds, p and the carry c stand for p at the start of the round plus
    a_i times the j low limbs of b, at weight 2^(32 i).  Last loop: r_k is
    p_(k+5); then r = p / 2^160 since p < 2^352. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** Limbs *)

(* The limbs of an array of zeros stand for 0. *)
Lemma pval_zero {n} (f : {ffun 'I_n -> int64}) k :
  (forall i, f i = Int64.zero) -> (k <= n)%nat -> pval f k = 0%Z.
Proof.
  move=> Hz; elim: k => [|k IH] Hk; first by rewrite pval0.
  by rewrite (pvalSn _ _ Hk) IH ?(ltnW Hk) // Hz Int64.unsigned_zero; lia.
Qed.

Lemma limb_base_add m k : limb_base (m + k) = (limb_base m * limb_base k)%Z.
Proof. rewrite /limb_base -Z.pow_add_r /limb_bits; try lia; f_equal; lia. Qed.

Lemma mulshr_step (V P0 B Bi Bj p m q c ai bj Pb s : Z) :
  B = (Bi * Bj)%Z -> s = (ai * bj + p + c)%Z -> (m + 2 ^ 32 * q = s)%Z ->
  (V + c * B = P0 + ai * Pb * Bi)%Z ->
  (V + (m - p) * B + q * (2 ^ 32 * B) = P0 + ai * (Pb + Bj * bj) * Bi)%Z.
Proof.
  move=> -> -> Hm HV.
  have -> : V = (P0 + ai * Pb * Bi - c * (Bi * Bj))%Z by lia.
  have -> : m = (ai * bj + p + c - 2 ^ 32 * q)%Z by lia.
  ring.
Qed.

Section Mul2.
Transparent Int64.mul.
Lemma mul_add2_word (a b p c : int64) :
  (Int64.unsigned a < 2 ^ 32)%Z -> (Int64.unsigned b < 2 ^ 32)%Z ->
  (Int64.unsigned p < 2 ^ 32)%Z -> (Int64.unsigned c < 2 ^ 32)%Z ->
  Int64.unsigned (Int64.add (Int64.add (Int64.mul a b) p) c) =
  (Int64.unsigned a * Int64.unsigned b + Int64.unsigned p + Int64.unsigned c)%Z.
Proof.
  move=> Ha Hb Hp Hc.
  have := Int64.unsigned_range a; have := Int64.unsigned_range b;
    have := Int64.unsigned_range p; have := Int64.unsigned_range c.
  move=> Rc Rp Rb Ra.
  have Ep : (0 <= Int64.unsigned a * Int64.unsigned b <=
             (2 ^ 32 - 1) * (2 ^ 32 - 1))%Z by nia.
  have M : Int64.max_unsigned = 18446744073709551615%Z by [].
  rewrite !Int64.add_unsigned /Int64.mul.
  rewrite (Int64.unsigned_repr (Int64.unsigned a * Int64.unsigned b)) ?M; lia.
Qed.
End Mul2.

(* Limbs 5 .. 5 + k - 1 of P, copied into R. *)
Lemma pval_shift (P : {ffun 'I_12 -> int64}) (R : {ffun 'I_6 -> int64}) :
  (forall m (H1 : (m < 6)%nat) (H2 : (m + 5 < 12)%nat),
     R (Ordinal H1) = P (Ordinal H2)) ->
  forall k, (k <= 6)%nat ->
  pval P (5 + k) = (pval P 5 + limb_base 5 * pval R k)%Z.
Proof.
  move=> HR; elim=> [|k IH] Hk; first by rewrite addn0 pval0; lia.
  have H2 : (5 + k < 12)%nat by move: Hk; clear; lia.
  have H2' : (k + 5 < 12)%nat by move: Hk; clear; lia.
  rewrite addnS (pvalSn _ _ H2) IH ?(ltnW Hk) // (pvalSn _ _ Hk).
  have -> : P (Ordinal H2) = R (Ordinal Hk).
    by rewrite (HR k Hk H2'); congr (P _); apply: val_inj; rewrite /= addnC.
  rewrite (limb_base_add 5 k); ring.
Qed.

(* r = p / 2^160 when p < 2^352: the result of num_mulshr. *)
Lemma mulshr_final (P : {ffun 'I_12 -> int64}) (R : {ffun 'I_6 -> int64}) X Y :
  limbsA P ->
  (forall m (H1 : (m < 6)%nat) (H2 : (m + 5 < 12)%nat),
     R (Ordinal H1) = P (Ordinal H2)) ->
  valA P = (X * Y)%Z -> (X * Y < 2 ^ (ExpConsts.P + ExpModel.num_bits))%Z ->
  limbsA R /\ valA R = ExpModel.mulshr X Y.
Proof.
  move=> HP HR HV Hfit; split.
  { case=> m H1; have H2 : (m + 5 < 12)%nat by move: H1; clear; lia.
    by rewrite (HR m H1 H2); apply: HP. }
  have H11 : (11 < 12)%nat by [].
  have Ep := pval_shift P R HR 6 (leqnn 6).
  have Eb := pval_lt P 5 HP isT.
  have L11 := HP (Ordinal H11); move: L11; rewrite /limb => L11.
  have G := valA_ge0 R.
  move: HV; rewrite -pval_all (pvalSn _ _ H11) Ep pval_all => HV.
  have B11 : limb_base 11 = (2 ^ (ExpConsts.P + ExpModel.num_bits))%Z by [].
  have B5 : limb_base 5 = (2 ^ ExpConsts.P)%Z by [].
  have Z11 : Int64.unsigned (P (Ordinal H11)) = 0%Z.
  { have := limb_base_pos 5; have := limb_base_pos 11; move: Hfit Eb.
    rewrite -B11; nia. }
  rewrite ExpModel.mulshrE -HV Z11 Z.mul_0_r Z.add_0_r -B5.
  apply: Z.div_unique_pos; first by exact: (pval_lt P 5 HP isT).
  ring.
Qed.

Theorem num_mulshr_ok : num_mulshr_spec.
Proof.
  move=> μ rr a b r rl Ha Hb Hfit.
  start. csteps.

  inv I := { [:: p; i0] } (fun (pp : {ffun 'I_12 -> int64}) ii =>
    (ii:N <= 6)%nat /\ limbsA pp /\
    (forall k : 'I_12, (ii:N + 6 <= k)%nat -> pp k = Int64.zero) /\
    valA pp = (pval a ii:N * valA b)%Z).
  enter_loop I.
  { prove_inv; exsp.
    - by move=> k; rewrite ffunE Int64.unsigned_zero /limb /limb_bits; lia.
    - by move=> k _; rewrite ffunE.
    - change (Int64.repr 0):N with 0%nat; rewrite pval0 Z.mul_0_l -pval_all.
      by apply: pval_zero => // k; rewrite ffunE. }
  unfold_inv => - [Hi0 [Hl0 [Hz0 Hv0]]].
  csteps.
  case END: Int64.ltu => /=.
  - have Hi : (i1:N < NL)%nat by rewrite /NL; clia i1.
    csteps.
    inv J := { [:: p; c; j] } (fun (pp : {ffun 'I_12 -> int64}) cc jj =>
      (jj:N <= 6)%nat /\ limbsA pp /\ limb (Int64.unsigned cc) /\
      (forall k : 'I_12, (i1:N + 6 <= k)%nat -> pp k = Int64.zero) /\
      (valA pp + Int64.unsigned cc * limb_base (i1:N + jj:N) =
       valA p0 + Int64.unsigned (a (Ordinal Hi)) * pval b jj:N *
         limb_base i1:N)%Z).
    enter_loop J.
    { prove_inv; exsp.
      change (Int64.repr 0):N with 0%nat; rewrite pval0 Int64.unsigned_zero.
      by rewrite Z.mul_0_l Z.mul_0_r Z.mul_0_l. }
    unfold_inv => - [Hj1 [Hl1 [Hc1 [Hz1 Hv1]]]].
    csteps.
    case END2: Int64.ltu => /=.
    + csteps; evalf; csteps; evalf; csteps.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp.
      all: have E1 : (Int64.add j1 (Int64.repr 1)):N = (j1:N).+1 by clia j1.
      all: have Eij : (Int64.add i1 j1):N = (i1:N + j1:N)%nat by clia i1, j1.
      all: have Hij : (i1:N + j1:N < 12)%nat by have := Hi; have := H; rewrite /NL; lia.
      all: have Eai : forall H' : (i1:N < NL)%nat, a (Ordinal H') = a (Ordinal Hi)
             by move=> H'; rewrite (bool_irrelevance H' Hi).
      all: rewrite ?Eai ?E1.
      all: have La := Ha (Ordinal Hi).
      all: have Lb := Hb (Ordinal H).
      all: have Lp := Hl1 (Ordinal H0).
      all: move: La Lb Lp Hc1; rewrite /limb /limb_bits => La Lb Lp Hc'.
      all: set ai := a (Ordinal Hi) in La *.
      all: set bj := b (Ordinal H) in Lb *.
      all: set pij := p1 (Ordinal H0) in Lp *.
      all: have Es := mul_add2_word ai bj pij c1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia).
      all: set s := Int64.add (Int64.add (Int64.mul ai bj) pij) c1 in Es *.
      all: have Rs := Int64.unsigned_range s.
      all: rewrite ?Eij.
      * exact: H.
      * move=> k; rewrite (setfP _ _ _ Hij); case: eqP => [_|Ne].
        -- rewrite /limb /limb_bits and_mask.
          by have := Z.mod_pos_bound (Int64.unsigned s) (2 ^ 32); lia.
        -- exact: Hl1.
      * rewrite shru32; split; first by apply: Z.div_pos; lia.
        apply: Z.div_lt_upper_bound; move: Rs; rewrite /Int64.modulus /=; lia.
      * move=> k Hk; rewrite (setfP _ _ _ Hij); case: eqP => [E|_].
        -- by have := H; move: Hk; rewrite E /NL; lia.
        -- exact: Hz1.
      * have Epij : p1 (Ordinal Hij) = pij by rewrite /pij; congr (p1 _); apply: val_inj.
        rewrite -[valA (p1 ↑[_ ← _])]pval_all (pval_setf _ _ _ Hij) // Epij.
        case: ifP => [_|/negP]; last by rewrite Hij.
        rewrite pval_all (pvalSn _ _ H) addnS limb_baseS.
        rewrite !limb_base_add and_mask shru32 /limb_bits.
        rewrite limb_base_add in Hv1.
        apply: (mulshr_step _ _ _ _ _ _ _ _ (Int64.unsigned c1) _ _ _
                  (Int64.unsigned s) erefl Es _ Hv1).
        have := Z.div_mod (Int64.unsigned s) (2 ^ 32) ltac:(lia); lia.
    + csteps; cret; split=> //= _; csteps.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp.
      all: have Ej6 : j1:N = 6%nat by clia j1.
      all: have Ei6 : (Int64.add i1 (Int64.repr 6)):N = (i1:N + 6)%nat by clia i1.
      all: have Ei1 : (Int64.add i1 (Int64.repr 1)):N = (i1:N).+1 by clia i1.
      all: have Hi6 : (i1:N + 6 < 12)%nat by have := Hi; rewrite /NL; lia.
      all: rewrite ?Ei6 ?Ei1.
      * by have := Hi; rewrite /NL.
      * move=> k; rewrite (setfP _ _ _ Hi6); case: eqP => [_|_].
        -- exact: Hc1.
        -- exact: Hl1.
      * move=> k Hk; rewrite (setfP _ _ _ Hi6); case: eqP => [E|_].
        -- by move: Hk; rewrite E; lia.
        -- by apply: Hz1; lia.
      * rewrite -[valA (p1 ↑[_ ← _])]pval_all (pval_setf _ _ _ Hi6) //.
        case: ifP => [_|/negP]; last by rewrite Hi6.
        rewrite pval_all Hz1 // Int64.unsigned_zero (pvalSn _ _ Hi).
        move: Hv1; rewrite Ej6 pval_all Hv0; lia.
  - csteps; cret; split=> //= _; csteps.
    have E6 : i1:N = 6%nat by clia i1.
    rewrite E6 in Hz0 Hv0.
    inv K := { [:: r0; i] } (fun (rv : numA) ii =>
      (ii:N <= 6)%nat /\
      (forall m (H1 : (m < NL)%nat) (H2 : (m + 5 < 12)%nat), (m < ii:N)%nat ->
         rv (Ordinal H1) = p0 (Ordinal H2))).
    enter_loop K.
    { prove_inv; exsp. }
    unfold_inv => - [Hk1 Hr1].
    csteps.
    case END3: Int64.ltu => /=.
    + csteps; rewrite (fffE _ _ H) ffunE setf_map.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp.
      * clia i2.
      * move=> m H1 H2 Hm; rewrite (setfP _ _ _ H0) /=; case: eqP => [Em|Nm].
        -- subst m; congr (p0 _); apply: val_inj => /=; clia i2.
        -- apply: Hr1; move: Hm Nm.
           have -> : (Int64.add i2 (Int64.repr 1)):N = (i2:N).+1 by clia i2.
           lia.
    + csteps; cret; split=> //= _; csteps.
      fin.
      have E6' : i2:N = 6%nat by clia i2.
      exists r1; split; first by rewrite /envC /=.
      apply: (mulshr_final p0 r1 _ _ Hl0 _ _ Hfit).
      * move=> m H1 H2; apply: Hr1; rewrite E6'; exact: H1.
      * by rewrite Hv0 -(pval_all a).
Qed.
