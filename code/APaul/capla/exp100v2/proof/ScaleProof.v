(** * num_scale: a = floor(v 2^e), for v < 2^53 and e < 128

    num_scale calls num_zero: its statement [num_zero_spec] is a
    hypothesis of [num_scale_ok], proved in NumZeroProof.v.  The cases
    are those of the VST proof (body_num_scale of
    ../../../vst/exp100/Verif_bits.v): for e < 0 the word v >> -e (0
    when e <= -64) is written in limbs 0 and 1; for e >= 0 the word
    v 2^(e mod 32) is written in limbs q, q + 1, q + 2, q = e / 32. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** Limbs written in a row of zeros *)

(* The number of limbs all zero. *)
Lemma pval_zero k : (k <= NL)%nat -> pval ([ffun=> Int64.zero] : numA) k = 0%Z.
Proof.
elim: k => [|k IH] Hk; first by rewrite pval0.
by rewrite (pvalSn _ _ Hk) ffunE (IH (ltnW Hk)) Int64.unsigned_zero Z.mul_0_r.
Qed.

(* Writing a limb keeps an array of limbs. *)
Lemma limbsA_setf n (f : {ffun 'I_n -> int64}) k x (H : (k < n)%nat) :
  limbsA f -> limb (Int64.unsigned x) -> limbsA (f ↑[k ← x]).
Proof. by move=> Hf Hx i; rewrite (setfP _ _ _ H); case: eqP. Qed.

(* Two limbs written at k0 and k0 + 1 in a row of zeros. *)
Lemma valA_write2 (k0 k1 : nat) (x0 x1 : int64) (H1 : (k1 < NL)%nat) :
  k1 = k0.+1 ->
  valA (([ffun=> Int64.zero] : numA) ↑[k0 ← x0] ↑[k1 ← x1]) =
  (limb_base k0 * (Int64.unsigned x0 + 2 ^ 32 * Int64.unsigned x1))%Z.
Proof.
move=> E1.
have H0 : (k0 < NL)%nat by rewrite -ltnS -E1 ltnW.
rewrite -pval_all (pval_setf _ _ _ H1 _ (leqnn _)) (pval_setf _ _ _ H0 _ (leqnn _)).
rewrite (setfP _ _ _ H0) ffunE H0 H1 pval_zero // ffunE.
have N : (k1 == k0) = false by rewrite E1 (gtn_eqF (ltnSn k0)).
have L : limb_base k1 = (2 ^ 32 * limb_base k0)%Z by rewrite E1 limb_baseS.
change (nat_of_ord (Ordinal H1) == k0) with (k1 == k0).
rewrite N Int64.unsigned_zero L; ring.
Qed.

(* Three limbs written at k0, k0 + 1 and k0 + 2 in a row of zeros. *)
Lemma valA_write3 (k0 k1 k2 : nat) (x0 x1 x2 : int64) (H1 : (k1 < NL)%nat)
    (H2 : (k2 < NL)%nat) :
  k1 = k0.+1 -> k2 = k0.+2 ->
  valA (([ffun=> Int64.zero] : numA) ↑[k0 ← x0] ↑[k1 ← x1] ↑[k2 ← x2]) =
  (limb_base k0 * (Int64.unsigned x0 + 2 ^ 32 * (Int64.unsigned x1 +
     2 ^ 32 * Int64.unsigned x2)))%Z.
Proof.
move=> E1 E2.
have H0 : (k0 < NL)%nat by rewrite -ltnS -E1 ltnW.
rewrite -pval_all (pval_setf _ _ _ H2 _ (leqnn _)) H2 pval_all.
rewrite (valA_write2 _ _ _ _ H1 E1) (setfP _ _ _ H1) (setfP _ _ _ H0) ffunE.
change (nat_of_ord (Ordinal H2)) with k2.
have L : limb_base k2 = (2 ^ 32 * (2 ^ 32 * limb_base k0))%Z.
  by rewrite E2; rewrite limb_baseS limb_baseS.
have N1 : (k2 == k1) = false.
  by apply/eqP; rewrite E1 E2 => /eqP; rewrite eqSS (gtn_eqF (ltnSn _)).
have N0 : (k2 == k0) = false.
  by apply/eqP; rewrite E2 => /eqP; rewrite gtn_eqF // ltnW.
rewrite N1 N0 Int64.unsigned_zero L; ring.
Qed.

(** ** The words of the two branches *)

(* The tests of the negative branch of num_scale: -64 < e < 0. *)
Lemma neg_amount e : Int64.lt e (Int64.repr 0) = true ->
  Int64.lt (Int64.repr 18446744073709551552) e = true ->
  (-64 < Int64.signed e < 0)%Z.
Proof.
rewrite /Int64.lt.
have -> : Int64.signed (Int64.repr 18446744073709551552) = (-64)%Z by [].
have -> : Int64.signed (Int64.repr 0) = 0%Z by [].
by case: Coqlib.zlt => // ? ; case: Coqlib.zlt.
Qed.

(* The other case of the negative branch: e <= -64. *)
Lemma neg_amount_le e :
  Int64.lt (Int64.repr 18446744073709551552) e = false ->
  (Int64.signed e <= -64)%Z.
Proof.
rewrite /Int64.lt.
have -> : Int64.signed (Int64.repr 18446744073709551552) = (-64)%Z by [].
by case: Coqlib.zlt => // ? _; lia.
Qed.

Lemma neg_amount2 e : (-64 < Int64.signed e < 0)%Z ->
  Int.unsigned (Int.modu (Int64.loword (Int64.neg e)) Int64.iwordsize') =
  (- Int64.signed e)%Z.
Proof.
move=> He.
have M : Int.max_unsigned = 4294967295%Z by [].
have M64 : Int64.max_unsigned = 18446744073709551615%Z by [].
have R : (0 <= - Int64.signed e <= Int64.max_unsigned)%Z by rewrite M64; lia.
rewrite -{1}(Int64.repr_signed e) Int64.neg_repr /Int64.loword (Int64.unsigned_repr _ R).
have R1 : (0 <= - Int64.signed e <= Int.max_unsigned)%Z by rewrite M; lia.
rewrite /Int.modu (Int.unsigned_repr _ R1).
change (Int.unsigned Int64.iwordsize') with 64%Z.
rewrite Z.mod_small; first lia.
apply: Int.unsigned_repr; lia.
Qed.

(* The two limbs of a word below 2^64, as num_scale writes them. *)
Lemma split_word w : (Int64.unsigned w < 2 ^ 64)%Z ->
  let x0 := Int64.and w (Int64.repr 4294967295) in
  let x1 := Int64.shru' w (Int.modu (Int.repr 32) Int64.iwordsize') in
  limb (Int64.unsigned x0) /\ limb (Int64.unsigned x1) /\
  (Int64.unsigned x0 + 2 ^ 32 * Int64.unsigned x1 = Int64.unsigned w)%Z.
Proof.
move=> Hw x0 x1; rewrite /x0 /x1 /limb /limb_bits and_mask shru32.
have Hr := Int64.unsigned_range w.
have := Z.mod_pos_bound (Int64.unsigned w) (2 ^ 32) ltac:(lia).
have := Z.div_mod (Int64.unsigned w) (2 ^ 32) ltac:(lia).
move=> Ed Hm; split; first lia.
split; last lia.
split; first by apply: Z.div_pos; lia.
by apply: Z.div_lt_upper_bound; lia.
Qed.

(* A shift amount below 64, as the 32-bit modulo of Capla gives it. *)
Lemma amount_ok (x : int64) : (Int64.unsigned x < 64)%Z ->
  Int.unsigned (Int.modu (Int64.loword x) Int64.iwordsize') = Int64.unsigned x.
Proof.
move=> Hx; have Hr := Int64.unsigned_range x.
have M : Int.max_unsigned = 4294967295%Z by [].
have R1 : (0 <= Int64.unsigned x <= Int.max_unsigned)%Z by rewrite M; lia.
rewrite /Int.modu /Int64.loword (Int.unsigned_repr _ R1).
change (Int.unsigned Int64.iwordsize') with 64%Z.
rewrite Z.mod_small; first lia.
apply: Int.unsigned_repr; lia.
Qed.
(* e / 32 and e mod 32 on words. *)
Lemma divu32 e : Int64.unsigned (Int64.divu e (Int64.repr 32)) =
  (Int64.unsigned e / 32)%Z.
Proof.
have Hr := Int64.unsigned_range e.
rewrite /Int64.divu (Int64.unsigned_repr 32) //.
apply: Int64.unsigned_repr; split; first by apply: Z.div_pos; lia.
have := Z.div_le_upper_bound (Int64.unsigned e) 32 (Int64.unsigned e) ltac:(lia) ltac:(lia).
have M64 : Int64.max_unsigned = 18446744073709551615%Z by [].
have : (Int64.modulus = 18446744073709551616)%Z by [].
lia.
Qed.
Lemma modu32 e : Int64.unsigned (Int64.modu e (Int64.repr 32)) =
  (Int64.unsigned e mod 32)%Z.
Proof.
rewrite /Int64.modu (Int64.unsigned_repr 32) //.
have := Z.mod_pos_bound (Int64.unsigned e) 32 ltac:(lia).
have M64 : Int64.max_unsigned = 18446744073709551615%Z by [].
move=> H; apply: Int64.unsigned_repr; lia.
Qed.
(* A positive e as a word. *)
Lemma nonneg_e e : Int64.lt e (Int64.repr 0) = false ->
  Int64.unsigned e = Int64.signed e /\ (0 <= Int64.signed e)%Z.
Proof.
move=> H; rewrite Int64.unsigned_signed.
have -> : Int64.zero = Int64.repr 0 by [].
rewrite H; split => //.
move: H; rewrite /Int64.lt.
have -> : Int64.signed (Int64.repr 0) = 0%Z by [].
by case: Coqlib.zlt => // ? _; lia.
Qed.
(* The indices q + 1 and q + 2 of num_scale. *)
Lemma idx1 d : (Int64.unsigned d < 4)%Z -> (Int64.add d (Int64.repr 1)):N = (d:N).+1.
Proof. clia. Qed.
Lemma idx2 d : (Int64.unsigned d < 4)%Z -> (Int64.add d (Int64.repr 2)):N = (d:N).+2.
Proof. clia. Qed.

(* The three limbs that num_scale writes for e >= 0: v 2^m for m < 32. *)
Lemma scale_words v s : (Int64.unsigned v < 2 ^ 53)%Z ->
  (Int.unsigned s < 32)%Z ->
  let s32 := Int.modu (Int.repr 32) Int64.iwordsize' in
  let lo := Int64.shl' (Int64.and v (Int64.repr 4294967295)) s in
  let h2 := Int64.add (Int64.shl' (Int64.shru' v s32) s) (Int64.shru' lo s32) in
  limb (Int64.unsigned (Int64.and lo (Int64.repr 4294967295))) /\
  limb (Int64.unsigned (Int64.and h2 (Int64.repr 4294967295))) /\
  limb (Int64.unsigned (Int64.shru' h2 s32)) /\
  (Int64.unsigned (Int64.and lo (Int64.repr 4294967295)) + 2 ^ 32 *
    (Int64.unsigned (Int64.and h2 (Int64.repr 4294967295)) + 2 ^ 32 *
     Int64.unsigned (Int64.shru' h2 s32)) =
   Int64.unsigned v * 2 ^ Int.unsigned s)%Z.
Proof.
move=> Hv Hs s32 lo h2.
have M64 : Int64.max_unsigned = 18446744073709551615%Z by [].
have Hv0 := Int64.unsigned_range v.
have Hs0 := Int.unsigned_range s.
set m := Int.unsigned s in Hs Hs0 *.
have Hp : (1 <= 2 ^ m <= 2 ^ 31)%Z.
  by split; [rewrite -(Z.pow_0_r 2)|]; apply: Z.pow_le_mono_r; lia.
have Hv1 := Z.mod_pos_bound (Int64.unsigned v) (2 ^ 32) ltac:(lia).
have Hv2 : (0 <= Int64.unsigned v / 2 ^ 32 < 2 ^ 21)%Z.
  by split; [apply: Z.div_pos|apply: Z.div_lt_upper_bound]; lia.
have Hvd := Z.div_mod (Int64.unsigned v) (2 ^ 32) ltac:(lia).
have Ulo : Int64.unsigned lo = (Int64.unsigned v mod 2 ^ 32 * 2 ^ m)%Z.
{ rewrite /lo /Int64.shl' and_mask -/m Z.shiftl_mul_pow2; first lia.
  apply: Int64.unsigned_repr; rewrite M64; nia. }
have Uhi : Int64.unsigned (Int64.shl' (Int64.shru' v s32) s) =
           (Int64.unsigned v / 2 ^ 32 * 2 ^ m)%Z.
{ rewrite /Int64.shl' /s32 shru32 -/m Z.shiftl_mul_pow2; first lia.
  apply: Int64.unsigned_repr; rewrite M64; nia. }
have Hl1 : (0 <= Int64.unsigned lo / 2 ^ 32 < 2 ^ 31)%Z.
  by rewrite Ulo; split; [apply: Z.div_pos|apply: Z.div_lt_upper_bound]; nia.
have Uh2 : Int64.unsigned h2 =
           (Int64.unsigned v / 2 ^ 32 * 2 ^ m + Int64.unsigned lo / 2 ^ 32)%Z.
{ rewrite /h2 /Int64.add Uhi /s32 shru32.
  apply: Int64.unsigned_repr; rewrite M64; nia. }
have Hh2 : (0 <= Int64.unsigned h2 < 2 ^ 53)%Z by rewrite Uh2; nia.
have Hm0 := Z.mod_pos_bound (Int64.unsigned lo) (2 ^ 32) ltac:(lia).
have Hm1 := Z.mod_pos_bound (Int64.unsigned h2) (2 ^ 32) ltac:(lia).
have Hd0 := Z.div_mod (Int64.unsigned lo) (2 ^ 32) ltac:(lia).
have Hd1 := Z.div_mod (Int64.unsigned h2) (2 ^ 32) ltac:(lia).
have Hq1 : (0 <= Int64.unsigned h2 / 2 ^ 32 < 2 ^ 32)%Z.
  by split; [apply: Z.div_pos|apply: Z.div_lt_upper_bound]; lia.
rewrite /limb /limb_bits /s32.
rewrite !and_mask shru32.
split; first lia.
split; first lia.
split; first lia.
have -> : (Int64.unsigned h2 mod 2 ^ 32 + 2 ^ 32 * (Int64.unsigned h2 / 2 ^ 32)
           = Int64.unsigned h2)%Z by lia.
rewrite Uh2.
have -> : (Int64.unsigned lo mod 2 ^ 32 + 2 ^ 32 * (Int64.unsigned v / 2 ^ 32 * 2 ^ m + Int64.unsigned lo / 2 ^ 32)
          = Int64.unsigned lo + 2 ^ 32 * (Int64.unsigned v / 2 ^ 32 * 2 ^ m))%Z by lia.
rewrite Ulo.
have -> : (Int64.unsigned v * 2 ^ m = (2 ^ 32 * (Int64.unsigned v / 2 ^ 32) +
            Int64.unsigned v mod 2 ^ 32) * 2 ^ m)%Z by rewrite -Hvd.
ring.
Qed.

(** ** The proof *)

Theorem num_scale_ok : num_zero_spec -> num_scale_spec.
Proof.
move=> NZ μ a v e r rl Hv He.
start; csteps.
call NZ => ->.
csteps.
have Hv0 := Int64.unsigned_range v.
have M64 : Int64.max_unsigned = 18446744073709551615%Z by [].
have H1 : ((Int64.repr 1):N < NL)%nat by [].
have Hz : limbsA ([ffun=> Int64.zero] : numA) by move=> i; rewrite ffunE.
case NEG: Int64.lt => /=.
- csteps.
  case G64: Int64.lt => /=.
  + csteps; evalf; csteps.
    rewrite -!setfE; fin.
    have He' := neg_amount _ NEG G64.
    set wv := Int64.shru' v _.
    have Hw : Int64.unsigned wv = (Int64.unsigned v / 2 ^ (- Int64.signed e))%Z.
    { have Hp : (1 <= 2 ^ (- Int64.signed e))%Z.
        by rewrite -(Z.pow_0_r 2); apply: Z.pow_le_mono_r; lia.
      have Hd : (0 <= Int64.unsigned v / 2 ^ (- Int64.signed e) <= Int64.max_unsigned)%Z.
      { rewrite M64; split; first by apply: Z.div_pos; lia.
        have := Z.div_le_upper_bound (Int64.unsigned v) (2 ^ (- Int64.signed e))
                  (Int64.unsigned v) ltac:(lia) ltac:(nia).
        rewrite /mant_bits in Hv; lia. }
      rewrite /wv /Int64.shru' (neg_amount2 _ He') Z.shiftr_div_pow2; first lia.
      exact: Int64.unsigned_repr. }
    have [L0 [L1 E01]] := split_word wv ltac:(rewrite Hw; have := Int64.unsigned_range wv; lia).
    eexists; split; first by [].
    split; first by apply: limbsA_setf => //; apply: limbsA_setf.
    rewrite (valA_write2 _ _ _ _ H1) // limb_base0 Z.mul_1_l E01 Hw ExpModel.scaleE.
    by case: Z.leb_spec; first lia.
  + csteps; evalf; csteps.
    rewrite -!setfE; fin.
    have He' := neg_amount_le _ G64.
    have [L0 [L1 E01]] := split_word (Int64.repr 0) ltac:(by []).
    eexists; split; first by [].
    split; first by apply: limbsA_setf => //; apply: limbsA_setf.
    rewrite (valA_write2 _ _ _ _ H1) // limb_base0 Z.mul_1_l E01 ExpModel.scaleE.
    case: Z.leb_spec; first lia.
    move=> _; rewrite Int64.unsigned_repr_eq Z.mod_0_l // Z.div_small //.
    have : (2 ^ 64 <= 2 ^ (- Int64.signed e))%Z by apply: Z.pow_le_mono_r; lia.
    rewrite /mant_bits in Hv.
    have : (2 ^ 53 < 2 ^ 64)%Z by [].
    lia.
- have E32 : Int64.eq (Int64.repr 32) Int64.zero = false by [].
  csteps.
  rewrite [divu64 _ _]/divu64 E32.
  csteps.
  rewrite [modu64 _ _]/modu64 E32.
  csteps; evalf; csteps.
  rewrite -!setfE; fin.
  have [Eu He0] := nonneg_e _ NEG.
  rewrite /scale_emax in He.
  have Hd : (Int64.unsigned (Int64.divu e (Int64.repr 32)) < 4)%Z.
    by rewrite divu32 Eu; apply: Z.div_lt_upper_bound; lia.
  have Hm := Z.mod_pos_bound (Int64.unsigned e) 32 ltac:(lia).
  have Hs : Int.unsigned (Int.modu (Int64.loword (Int64.modu e (Int64.repr 32)))
              Int64.iwordsize') = (Int64.signed e mod 32)%Z.
    by rewrite amount_ok modu32 Eu //; lia.
  set s := Int.modu (Int64.loword (Int64.modu e (Int64.repr 32))) Int64.iwordsize'.
  have Hs32 : (Int.unsigned s < 32)%Z by rewrite /s Hs; lia.
  have [L0 [L1 [L2 Ev]]] := scale_words v s Hv Hs32.
  eexists; split; first by [].
  split.
  { apply: limbsA_setf => //; apply: limbsA_setf => //.
    by apply: limbsA_setf. }
  rewrite (valA_write3 _ _ _ _ _ _ H0 H2 (idx1 _ Hd) (idx2 _ Hd)) Ev Hs.
  rewrite ExpModel.scaleE; case: Z.leb_spec => [_|?]; last lia.
  have Hd0 := Int64.unsigned_range (Int64.divu e (Int64.repr 32)).
  have Ed : Z.of_nat (Int64.divu e (Int64.repr 32)):N = (Int64.signed e / 32)%Z.
    by rewrite Z2Nat.id; [lia|rewrite divu32 Eu].
  have Edm := Z.div_mod (Int64.signed e) 32 ltac:(lia).
  have Hm' := Z.mod_pos_bound (Int64.signed e) 32 ltac:(lia).
  have Ep := Z.pow_add_r 2 (32 * (Int64.signed e / 32)) (Int64.signed e mod 32)
               ltac:(lia) ltac:(lia).
  have Ee : (32 * (Int64.signed e / 32) + Int64.signed e mod 32 =
             Int64.signed e)%Z by lia.
  rewrite Ee in Ep.
  rewrite /limb_base /limb_bits Ed Ep; ring.
Qed.
