(* =========================================================================  *)
(*  Foldrun.v -- the fold at the emitted table.                               *)
(*                                                                            *)
(*  Foldasm.v assembles the fold with the table and the twelve checks as      *)
(*  section hypotheses.  This file supplies them, and gets p1checkStepr for   *)
(*  the table the search actually reads.                                      *)
(*                                                                            *)
(*  Three kinds of thing live here, and only the third is expensive:          *)
(*    - the three slot equations, which say that slots 5, 6 and 7 of the      *)
(*      table hold the folding tables Foldtab.v reads;                        *)
(*    - stabE, from Foldchk.stabE_of_check;                                   *)
(*    - stabC and foldcheckStep, the two computations.                        *)
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

   vm_cast_no_check, not "by vm_compute": the latter reduces in the tactic
   and the kernel then converts the statement again at Qed.  MEASURED on
   repslotE: 1.83 s in the tactic and 1.28 s more at Qed. *)

Lemma repslotE : PArray.get p1ftab frepslot = repa.
Proof. vm_cast_no_check (erefl repa). Qed.

Lemma symslotE : PArray.get p1ftab fsymslot = syma.
Proof. vm_cast_no_check (erefl syma). Qed.

Lemma twsymslotE : PArray.get p1ftab twsymslot = twsyma.
Proof. vm_cast_no_check (erefl twsyma). Qed.

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
   all 1 013 760 ranks. *)
Lemma foldcheckStepP :
  foldcheckStep p1ftab frepi fsymi repsi twsymi actfsr.
Proof. Time native_cast_no_check (erefl true). Qed.

(* =========================================================================  *)
(*  4.  The value at the identity                                             *)
(* =========================================================================  *)

(* One entry, so vm_compute rather than native: this needs no precompiled
   table and P1Chk0.v's version of it reads the unfolded table. *)
Lemma p1check0P : p1check0 p1ftab.
Proof. vm_cast_no_check (erefl true). Qed.

(* =========================================================================  *)
(*  5.  And the rank certificate Farp1 asks for                               *)
(* =========================================================================  *)

Lemma p1checkSteprP : p1checkStepr p1ftab.
Proof.
exact: (Foldasm.p1checkSteprP frepE fsymE twsymE (@frepL)
          fsymLCP smulCP fsymECP ractLCP actrLCP frepSCP ractACP msymRCP
          twsymLCP acttwiLCP twsymACP msymTCP stabEP foldcheckStepP).
Qed.
