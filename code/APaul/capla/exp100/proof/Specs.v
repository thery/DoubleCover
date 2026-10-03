(** * The tables of the Capla exp100, and what every spec shares

    Capla has no globals: [exp_core], [exp_encl_bits] and [maybe_hard_bits]
    take the tables T, C, LN2, RMAX as arguments.  [tables_ok] says that
    the arguments hold the lists of ExpTable.v, word by word.  The lemmas
    below read a table or a row as a number of the model (ExpModel.v). *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers.
Require Import BValues.
Require Import Exp100Capla.ExpBase Exp100Capla.Bridge.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpTable ExpConsts ExpModel.
Require Import WP ZifyIntegers ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(* A list of integers, one word each. *)
Definition words (l : list Z) : list int64 := map Int64.repr l.

(* A table as Capla passes it: an array of arrays of words. *)
Definition vtab (t : list (list int64)) : value :=
  Varr (map (fun r => Varr (map Vint64 r)) t).

(* The four tables of ExpTable.v, as words. *)
Definition Tw : list (list int64) := map words ExpTable.T.
Definition Cw : list (list int64) := map words ExpTable.C.
Definition LN2w : list int64 := words ExpTable.LN2.
Definition RMAXw : list int64 := words ExpTable.RMAX.

(* The table arguments hold the tables of ExpTable.v. *)
Definition tables_ok (Ta Ca L2a RMa : value) : Prop :=
  Ta = vtab Tw /\ Ca = vtab Cw /\
  L2a = Varr (map Vint64 LN2w) /\ RMa = Varr (map Vint64 RMAXw).

(* The number of the table T, of the table C: their lengths. *)
Definition TAB_n : nat := 64.
Definition DEG_n : nat := 16.

(** ** From the lists of Z to the words *)

Lemma length_words l : length (words l) = length l.
Proof. by rewrite /words length_map. Qed.

Lemma val32_words l : Forall limb l -> val32 (words l) = valZ l.
Proof.
  elim: l => [|x l IH] //= /Forall_cons_iff [Hx Hl].
  rewrite IH // Int64.unsigned_repr //.
  move: Hx; rewrite /limb /limb_bits.
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

Lemma limbs_words l : Forall limb l -> limbs (words l).
Proof.
  move=> H; apply/limbs_Forall; apply/Forall_forall => y.
  rewrite /words map_map => /in_map_iff [x [<- Hx]].
  move/Forall_forall: H => /(_ x Hx) Hl.
  rewrite Int64.unsigned_repr //.
  move: Hl; rewrite /limb /limb_bits.
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

(** ** LN2 and RMAX *)

Lemma LN2w_num : length LN2w = 6%nat /\ limbs LN2w /\
  val32 LN2w = ExpModel.LN2v.
Proof.
  have [Hl Hf] := ExpConsts.num_LN2.
  rewrite /LN2w length_words Hl ExpModel.LN2vE val32_words //.
  split => //; split => //; exact: limbs_words.
Qed.

Lemma RMAXw_num : length RMAXw = 6%nat /\ limbs RMAXw /\
  val32 RMAXw = ExpModel.RMAXv.
Proof.
  have [Hl Hf] := ExpConsts.num_RMAX.
  rewrite /RMAXw length_words Hl ExpModel.RMAXvE val32_words //.
  split => //; split => //; exact: limbs_words.
Qed.

(** ** The rows of T and C *)

Lemma length_Tw : length Tw = TAB_n.
Proof. by rewrite /Tw length_map ExpConsts.length_T. Qed.

Lemma length_Cw : length Cw = S DEG_n.
Proof. by rewrite /Cw length_map ExpConsts.length_C. Qed.

(* Row j of T is the number T_j of the model. *)
Lemma Tw_row j : (j < TAB_n)%coq_nat ->
  length (List.nth j Tw []) = 6%nat /\ limbs (List.nth j Tw []) /\
  val32 (List.nth j Tw []) = ExpModel.Tv (Z.of_nat j).
Proof.
  move=> Hj.
  have Hj' : (j < length ExpTable.T)%coq_nat by rewrite ExpConsts.length_T.
  have [Hl Hf] := proj1 (Forall_forall _ _) ExpConsts.num_T _
                    (nth_In _ [] Hj').
  rewrite /Tw (List.nth_indep _ [] (words [])) ?length_map //.
  rewrite List.map_nth length_words Hl ExpModel.TvE Nat2Z.id val32_words //.
  split => //; split => //; exact: limbs_words.
Qed.

(* Row i of C is the number C_i of the model. *)
Lemma Cw_row i : (i <= DEG_n)%coq_nat ->
  length (List.nth i Cw []) = 6%nat /\ limbs (List.nth i Cw []) /\
  val32 (List.nth i Cw []) = ExpModel.Cv i.
Proof.
  move=> Hi.
  have Hi' : (i < length ExpTable.C)%coq_nat
    by rewrite ExpConsts.length_C /DEG_n /ExpConsts.DEG in Hi *; lia.
  have [Hl Hf] := proj1 (Forall_forall _ _) ExpConsts.num_C _
                    (nth_In _ [] Hi').
  rewrite /Cw (List.nth_indep _ [] (words [])) ?length_map //.
  rewrite List.map_nth length_words Hl ExpModel.CvE val32_words //.
  split => //; split => //; exact: limbs_words.
Qed.

(** ** Bounds the statements share *)

(* Bits of a mantissa of a double, with the implicit bit. *)
Definition mant53 : Z := 53.

(* num_scale writes limb e / 32 + 2 of 6: e < 128. *)
Definition scale_emax : Z := 128.

(* A scratch array of 6 words, as a callee leaves it. *)
Definition arr6 (v : option value) : Prop :=
  exists l, v = Some (Varr (map Vint64 l)) /\ length l = 6%nat.
