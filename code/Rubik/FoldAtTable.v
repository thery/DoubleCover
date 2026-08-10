(* =========================================================================  *)
(*  FoldAtTable.v -- the fold at the emitted table.  See fold.md.                 *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        Fold P1Fold FoldTables Sym16 P1FTable P1RTable
        FoldStabiliser FoldChecks FoldRankCert FoldChecksRun FoldAssembly.
Require Import FoldOrbit_00 FoldOrbit_01 FoldOrbit_02 FoldOrbit_03 FoldOrbit_04.
Require Import FoldOrbit_05 FoldOrbit_06 FoldOrbit_07 FoldOrbit_08 FoldOrbit_09.
Require Import FoldOrbit_10 FoldOrbit_11 FoldOrbit_12 FoldOrbit_13 FoldOrbit_14.
Require Import FoldOrbit_15 FoldOrbit_16 FoldOrbit_17 FoldOrbit_18 FoldOrbit_19.
Require Import FoldOrbit_20 FoldOrbit_21 FoldOrbit_22 FoldOrbit_23 FoldOrbit_24.
Require Import FoldOrbit_25 FoldOrbit_26.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* =========================================================================  *)
(*  1.  The three slots                                                       *)
(* =========================================================================  *)

(* slots 5, 6 and 7 hold the folding tables FoldTables.v reads *)

Lemma repslotE : PArray.get p1ftab frepslot = repa.
Proof. Time native_cast_no_check (erefl repa). Qed.

Lemma symslotE : PArray.get p1ftab fsymslot = syma.
Proof. Time native_cast_no_check (erefl syma). Qed.

Lemma twsymslotE : PArray.get p1ftab twsymslot = twsyma.
Proof. Time native_cast_no_check (erefl twsyma). Qed.

Lemma frepE r : Phase1.frep p1ftab r = frepi r.
Proof. by rewrite /Phase1.frep repslotE. Qed.

Lemma fsymE r : Phase1.fsym p1ftab r = fsymi r.
Proof. by rewrite /Phase1.fsym symslotE. Qed.

Lemma twsymE tw s : Phase1.twsym p1ftab tw s = twsymi tw s.
Proof. by rewrite /Phase1.twsym twsymslotE. Qed.

(* =========================================================================  *)
(*  2.  The stabiliser                                                        *)
(* =========================================================================  *)

(* short orbits: every symmetry reaching the representative agrees *)
Lemma stabCP : stabC p1ftab (racti ractab).
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma stabEP tw r u :
  (to_nat tw < ntwist)%N -> (r <? nfsi)%uint63 -> (to_nat u < nsym)%N ->
  racti ractab r u = rrepi frepi repsi r ->
  p1get p1ftab (foldi (frepi r) (twsymi tw u))
  = Dfoldi p1ftab frepi fsymi twsymi tw r.
Proof. by move=> twL rL uL hu; exact: (stabE_of_check stabCP rL uL twL hu). Qed.

(* =========================================================================  *)
(*  3.  The certificate, at the orbits                                        *)
(* =========================================================================  *)

(* the orbit certificate, in twenty seven slices of eighty one twists *)

Definition slices : seq nat :=
  iota 0 81 ++ iota 81 81 ++ iota 162 81 ++ iota 243 81 ++ iota 324 81 ++
  iota 405 81 ++ iota 486 81 ++ iota 567 81 ++ iota 648 81 ++ iota 729 81 ++
  iota 810 81 ++ iota 891 81 ++ iota 972 81 ++ iota 1053 81 ++ iota 1134 81 ++
  iota 1215 81 ++ iota 1296 81 ++ iota 1377 81 ++ iota 1458 81 ++
  iota 1539 81 ++ iota 1620 81 ++ iota 1701 81 ++ iota 1782 81 ++
  iota 1863 81 ++ iota 1944 81 ++ iota 2025 81 ++ iota 2106 81.

Lemma slicesE : slices = iota 0 ntwist.
Proof. Time native_cast_no_check (erefl (iota 0 ntwist)). Qed.

(* foldcheckStep is that all, so the equation is all it takes *)
Lemma foldcheckStep_of_slices (s : seq nat) : s = iota 0 ntwist ->
  all (fun t => foldcheckOrb p1ftab frepi fsymi repsi twsymi actfsr
                              (of_nat t)) s ->
  foldcheckStep p1ftab frepi fsymi repsi twsymi actfsr.
Proof. by move=> -> h; exact: h. Qed.

Lemma foldcheckStepP :
  foldcheckStep p1ftab frepi fsymi repsi twsymi actfsr.
Proof.
apply: (foldcheckStep_of_slices slicesE).
by rewrite /slices !all_cat foldorb_00 foldorb_01 foldorb_02 foldorb_03
   foldorb_04 foldorb_05 foldorb_06 foldorb_07 foldorb_08 foldorb_09
   foldorb_10 foldorb_11 foldorb_12 foldorb_13 foldorb_14 foldorb_15
   foldorb_16 foldorb_17 foldorb_18 foldorb_19 foldorb_20 foldorb_21
   foldorb_22 foldorb_23 foldorb_24 foldorb_25 foldorb_26.
Qed.

(* =========================================================================  *)
(*  4.  The value at the identity                                             *)
(* =========================================================================  *)

(* the value at the identity, one entry *)
Lemma p1check0P : p1check0 p1ftab.
Proof. Time native_cast_no_check (erefl true). Qed.

(* =========================================================================  *)
(*  5.  And the rank certificate Farp1 asks for                               *)
(* =========================================================================  *)

Lemma p1checkSteprP : p1checkStepr p1ftab.
Proof.
exact: (FoldAssembly.p1checkSteprP frepE fsymE twsymE (@frepL)
          fsymLCP smulCP fsymECP ractLCP actrLCP frepSCP ractACP msymRCP
          twsymLCP acttwiLCP twsymACP msymTCP stabEP foldcheckStepP).
Qed.
