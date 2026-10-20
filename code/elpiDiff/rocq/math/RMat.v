(* RMat.v — the Stdlib reals as a mathcomp commutative ring, for the
   matrix statements of MainMx.v.

   Extra axiom: mathcomp's choice structure on R is built from
   constructive_indefinite_description (Stdlib.Logic.ClassicalEpsilon),
   with classic and functional extensionality. This axiom is used by the
   matrix layer only (RMat.v, MainMx.v); the rest of the development does
   not depend on it. *)

From HB Require Import structures.
From Stdlib Require Import Reals ClassicalEpsilon FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssralg.

Local Open Scope R_scope.

(* Decidable equality. *)
Definition eqR (x y : R) : bool := if Req_EM_T x y then true else false.

Lemma eqRP : Equality.axiom eqR.
Proof. by move=> x y; rewrite /eqR; case: Req_EM_T => H; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build R eqRP.

(* Choice, by indefinite description. *)
Definition findR (P : pred R) (n : nat) : option R :=
  match excluded_middle_informative (exists x, P x) with
  | left H => Some (proj1_sig (constructive_indefinite_description _ H))
  | right _ => None
  end.

Lemma findR_some (P : pred R) n x : findR P n = Some x -> P x.
Proof.
rewrite /findR; case: excluded_middle_informative => // H [<-].
exact: proj2_sig (constructive_indefinite_description _ H).
Qed.

Lemma findR_ex (P : pred R) : (exists x, P x) -> exists n, findR P n.
Proof.
by move=> H; exists O; rewrite /findR; case: excluded_middle_informative.
Qed.

Lemma findR_ext (P Q : pred R) : P =1 Q -> findR P =1 findR Q.
Proof. by move=> /functional_extensionality ->. Qed.

HB.instance Definition _ := hasChoice.Build R findR_some findR_ex findR_ext.

(* The commutative ring. *)
Lemma RplusA : associative Rplus.
Proof. by move=> x y z; rewrite Rplus_assoc. Qed.

Lemma RmultA : associative Rmult.
Proof. by move=> x y z; rewrite Rmult_assoc. Qed.

HB.instance Definition _ := GRing.isZmodule.Build R
  RplusA Rplus_comm Rplus_0_l Rplus_opp_l.

Lemma R1_neq0 : 1 != 0 :> R.
Proof. by apply/eqP; exact: R1_neq_R0. Qed.

HB.instance Definition _ := GRing.Zmodule_isComRing.Build R
  RmultA Rmult_comm Rmult_1_l Rmult_plus_distr_r R1_neq0.
