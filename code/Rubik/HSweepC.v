(* =========================================================================  *)
(*  HSweepC.v -- the three sweeps obligation C still owes.                    *)
(* =========================================================================  *)

(* The mathematics of C is proved: a turn moves the datum -- where each cubie *)
(* sits and how it lies -- by a rule with no position in it (HEdge.eslot_step,*)
(* HCorner.cplace_step, HCorner.ctwist_step), and the three coordinates read  *)
(* nothing but that datum.  What is left is that the three move tables ARE the*)
(* rankings of those rules, and that is a computation, one per coordinate.    *)
(*                                                                            *)
(* THE SIZES.  The edges are 190080 data, which is 24 * 22 * 20 * 18 and is   *)
(* n_e exactly; the U corners among the eight places are 70; the twists are   *)
(* 2187.  Times twelve turns each.  HEdgeChk.v has RUN the first, outside any *)
(* proof, and it came back true in 254 s.                                     *)
(*                                                                            *)
(* THE TWIST SWEEP HAS A WRINKLE, and it is worth naming before it bites.     *)
(* ctcoordi ranks SEVEN twists, the eighth being determined -- but only for a *)
(* real position, where the eight sum to zero mod three.  ctwist_step moves   *)
(* all eight, so the rule on seven needs the eighth, and where it comes from  *)
(* is that invariant.  Either the sweep carries all eight and the invariant   *)
(* is proved separately, or it carries seven and the eighth is recomputed;    *)
(* the first is honest and the second is what the prototype does.             *)
(*                                                                            *)
(* AND THEY MUST BE INT63.  A sweep the kernel checks cannot count in nat:    *)
(* HEdgeChk took 254 s in nat with vm_compute, and the kernel is slower than  *)
(* vm_compute.  Same reason HSweep.adm walks an int63 with the fuel as its    *)
(* only nat.                                                                  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound HEdge
        HCorner.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

Section Sweeps.

Variable mt_e mt_cl mt_ct : arr.

(* ---- what each sweep has to say ------------------------------------------ *)

(* For each coordinate: the table entry at a value and a turn is the value    *)
(* the rule gives.  Stated on positions, because that is how the step lemmas  *)
(* deliver it and how agree consumes it; the computation behind it ranges     *)
(* over data, of which there are 190080, 70 and 2187.                         *)
Definition sweep_e : Prop :=
  forall (a : arr) m, tabi_ok flast a -> cubt (ti2t flast a) -> (m < nq)%N ->
    ecoordi (inv_tabi flast (comp_tabi flast a (mvq m)))
      = PArray.get mt_e (Uint63.add
          (Uint63.mul (ecoordi (inv_tabi flast a)) nqti) (of_nat m)).

Definition sweep_cl : Prop :=
  forall (a : arr) m, tabi_ok flast a -> cubct (ti2t flast a) -> (m < nq)%N ->
    clcoordi (inv_tabi flast (comp_tabi flast a (mvq m)))
      = PArray.get mt_cl (Uint63.add
          (Uint63.mul (clcoordi (inv_tabi flast a)) nqti) (of_nat m)).

Definition sweep_ct : Prop :=
  forall (a : arr) m, tabi_ok flast a -> cubct (ti2t flast a) -> (m < nq)%N ->
    ctcoordi (inv_tabi flast (comp_tabi flast a (mvq m)))
      = PArray.get mt_ct (Uint63.add
          (Uint63.mul (ctcoordi (inv_tabi flast a)) nqti) (of_nat m)).

(* ---- and what they give -------------------------------------------------- *)

(* The three together are HAgree.agree, which is what HRunS.hsearch_complete  *)
(* takes as stt_step and what HAdmis needs to read the sweep of D through the *)
(* coordinates.  htriple is the three of them side by side.                   *)
Lemma sweeps_agree : sweep_e -> sweep_cl -> sweep_ct ->
  forall (a : arr) m, tabi_ok flast a -> cubt (ti2t flast a) ->
    cubct (ti2t flast a) -> (m < nq)%N ->
    htriple (comp_tabi flast a (mvq m))
      = stepa mt_e mt_cl mt_ct (htriple a) (of_nat m).
Proof.
move=> he hcl hct a m aok ca cca mL.
by rewrite /htriple /stepa (he _ _ aok ca mL) (hcl _ _ aok cca mL)
           (hct _ _ aok cca mL).
Qed.

End Sweeps.
