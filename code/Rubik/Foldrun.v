(* =========================================================================  *)
(*  Foldrun.v -- the fold at the emitted table.                               *)
(*                                                                            *)
(*  Foldasm.v assembles the fold with the table and the twelve checks as      *)
(*  section hypotheses.  This file supplies them, and gets p1checkStepr for   *)
(*  the table the search actually reads.                                      *)
(*                                                                            *)
(*  Three kinds of thing live here, and none of them is the long run:        *)
(*    - the three slot equations, which say that slots 5, 6 and 7 of the      *)
(*      table hold the folding tables Foldtab.v reads;                        *)
(*    - stabE, from Foldchk.stabE_of_check, and stabC under it;               *)
(*    - the orbit certificate, GLUED from the twenty seven Foldslc slices     *)
(*      so that it runs nine at a time rather than as one process.            *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        Fold P1Fold Foldtab Sym16 P1FTable P1RTable
        Foldchk Foldinst Foldbr Foldcert Foldasm.
Require Import Foldslc_00 Foldslc_01 Foldslc_02 Foldslc_03 Foldslc_04.
Require Import Foldslc_05 Foldslc_06 Foldslc_07 Foldslc_08 Foldslc_09.
Require Import Foldslc_10 Foldslc_11 Foldslc_12 Foldslc_13 Foldslc_14.
Require Import Foldslc_15 Foldslc_16 Foldslc_17 Foldslc_18 Foldslc_19.
Require Import Foldslc_20 Foldslc_21 Foldslc_22 Foldslc_23 Foldslc_24.
Require Import Foldslc_25 Foldslc_26.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* =========================================================================  *)
(*  1.  The three slots                                                       *)
(* =========================================================================  *)

(* The folded table carries the three folding tables in the slots after the
   distance chunks, so a folded read still takes one array.  These say the
   slots hold what Foldtab.v reads, and each is one array comparison.

   native_cast_no_check, not "by vm_compute": the latter reduces in the
   tactic and the kernel then converts the statement again at Qed.
   MEASURED on repslotE under vm: 1.83 s in the tactic and 1.28 s more at
   Qed.  vm_cast_no_check (erefl repa) is the fallback where the native
   compiler is not available. *)

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

(* A rank whose orbit is shorter than sixteen reaches its representative by
   several symmetries; the row has to give the same entry for all of them. *)
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

(* 64 430 orbits x 2187 twists x 18 moves, in place of the same sweep over
   all 1 013 760 ranks.  CUT INTO TWENTY SEVEN SLICES, eighty one twists
   each, exactly as the P1Chk slices cut the rank certificate: as one file
   it is a single process, and the rank certificate it replaces ran nine at
   a time.  The slices are what puts the wall time back. *)

Definition slices : seq nat :=
  iota 0 81 ++ iota 81 81 ++ iota 162 81 ++ iota 243 81 ++ iota 324 81 ++
  iota 405 81 ++ iota 486 81 ++ iota 567 81 ++ iota 648 81 ++ iota 729 81 ++
  iota 810 81 ++ iota 891 81 ++ iota 972 81 ++ iota 1053 81 ++ iota 1134 81 ++
  iota 1215 81 ++ iota 1296 81 ++ iota 1377 81 ++ iota 1458 81 ++
  iota 1539 81 ++ iota 1620 81 ++ iota 1701 81 ++ iota 1782 81 ++
  iota 1863 81 ++ iota 1944 81 ++ iota 2025 81 ++ iota 2106 81.

Lemma slicesE : slices = iota 0 ntwist.
Proof. Time native_cast_no_check (erefl (iota 0 ntwist)). Qed.

(* foldcheckStep IS that all over iota 0 ntwist, so the equation is all it
   takes.  `h' given by name rather than left to done: done would unfold the
   all and evaluate it. *)
Lemma foldcheckStep_of_slices (s : seq nat) : s = iota 0 ntwist ->
  all (fun t => foldcheckOrb p1ftab frepi fsymi repsi twsymi actfsr
                              (of_nat t)) s ->
  foldcheckStep p1ftab frepi fsymi repsi twsymi actfsr.
Proof. by move=> -> h; exact: h. Qed.

Lemma foldcheckStepP :
  foldcheckStep p1ftab frepi fsymi repsi twsymi actfsr.
Proof.
apply: (foldcheckStep_of_slices slicesE).
by rewrite /slices !all_cat foldchk_00 foldchk_01 foldchk_02 foldchk_03
   foldchk_04 foldchk_05 foldchk_06 foldchk_07 foldchk_08 foldchk_09
   foldchk_10 foldchk_11 foldchk_12 foldchk_13 foldchk_14 foldchk_15
   foldchk_16 foldchk_17 foldchk_18 foldchk_19 foldchk_20 foldchk_21
   foldchk_22 foldchk_23 foldchk_24 foldchk_25 foldchk_26.
Qed.

(* =========================================================================  *)
(*  4.  The value at the identity                                             *)
(* =========================================================================  *)

(* One entry, and P1Chk0.v's version of it reads the unfolded table. *)
Lemma p1check0P : p1check0 p1ftab.
Proof. Time native_cast_no_check (erefl true). Qed.

(* =========================================================================  *)
(*  5.  And the rank certificate Farp1 asks for                               *)
(* =========================================================================  *)

Lemma p1checkSteprP : p1checkStepr p1ftab.
Proof.
exact: (Foldasm.p1checkSteprP frepE fsymE twsymE (@frepL)
          fsymLCP smulCP fsymECP ractLCP actrLCP frepSCP ractACP msymRCP
          twsymLCP acttwiLCP twsymACP msymTCP stabEP foldcheckStepP).
Qed.
