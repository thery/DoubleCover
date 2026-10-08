(** * guess_n: the first guess of n, floor(X INV / 2^185)

    guess_n calls num_mul_small: its statement [num_mul_small_spec] is
    a hypothesis of [guess_n_ok], proved in MulSmallProof.v.  The
    product p = X INV has 7 limbs; the result is the number made of the bits
    of p from bit 185 on, read off limbs 5 and 6 (bits185 of ExpLimbs.v). *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpTable.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(* Bits 185 .. 223 of a number of 7 limbs, the word of guess_n. *)
Lemma bits185A (p : {ffun 'I_NP -> int64}) (i5 i6 : 'I_NP) :
  limbsA p -> nat_of_ord i5 = 5%nat -> nat_of_ord i6 = 6%nat ->
  Int64.or (Int64.shru' (p i5) (Int.modu (Int.repr 25) Int64.iwordsize'))
           (Int64.shl' (p i6) (Int.modu (Int.repr 7) Int64.iwordsize')) =
  Int64.repr (valA p / 2 ^ 185).
Proof.
move=> Hp E5 E6.
rewrite /Int64.shru' /Int64.shl'.
change (Int.unsigned (Int.modu (Int.repr 25) Int64.iwordsize')) with 25%Z.
change (Int.unsigned (Int.modu (Int.repr 7) Int64.iwordsize')) with 7%Z.
have := Hp i5; have := Hp i6; rewrite /limb /limb_bits => H6 H5.
have M : Int64.max_unsigned = 18446744073709551615%Z by [].
have R1 : (0 <= Z.shiftr (Int64.unsigned (p i5)) 25 <= Int64.max_unsigned)%Z.
{ rewrite Z.shiftr_div_pow2 // M; split; [apply: Z.div_pos; lia|].
  apply: Z.lt_le_incl; apply: Z.div_lt_upper_bound; lia. }
have R2 : (0 <= Z.shiftl (Int64.unsigned (p i6)) 7 <= Int64.max_unsigned)%Z.
{ rewrite Z.shiftl_mul_pow2 // M; lia. }
rewrite /Int64.or.
rewrite (Int64.unsigned_repr _ R1) (Int64.unsigned_repr _ R2).
congr Int64.repr.
rewrite -(nth_words p i5) -(nth_words p i6) E5 E6.
rewrite 2!(nth_List_nth (words p)).
apply: bits185.
- exact: (size_words p).
- exact: (proj1 (limbsA_Forall p) Hp).
Qed.

(* The multiplier of guess_n is INV. *)
Lemma INV_word : Int64.unsigned (Int64.repr 3098164009) = ExpTable.INV.
Proof. by []. Qed.

Theorem guess_n_ok : num_mul_small_spec -> guess_n_spec.
Proof.
move=> MS μ X r rl HX.
start; csteps.
have Hw : limb (Int64.unsigned (Int64.repr 3098164009)).
  by rewrite INV_word; exact: ExpConsts.limb_INV.
call MS => /(_ HX Hw) [p' [-> [Hp Hv]]].
csteps; evalf; csteps; evalf; csteps.
fin; split=> //.
rewrite /envC /=; evalf.
rewrite bits185A // Hv INV_word ExpModel.guessE.
by [].
Qed.
