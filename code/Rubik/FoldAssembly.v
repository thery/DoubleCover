(* =========================================================================  *)
(*  FoldAssembly.v -- FoldChecks and FoldRankCert together: p1checkStepr,     *)
(*     no data.                                                               *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        Fold Sym16 FoldChecks FoldRankCert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Asm.

(* the folded table, and the four folding tables read off it                  *)
Variable F : PArray.array arr.
Variable ractab : PArray.array arr.
Variables frepi fsymi repsi : int -> int.
Variable twsymi : int -> int -> int.

(* Phase1 reads the folding tables out of slots 5, 6 and 7 of F itself, so
   the assembly needs to know that those slots hold these tables.  Three
   array equalities, discharged where the table is supplied.                  *)
Hypothesis frepE : forall r, Phase1.frep F r = frepi r.
Hypothesis fsymE : forall r, Phase1.fsym F r = fsymi r.
Hypothesis twsymE : forall tw s, Phase1.twsym F tw s = twsymi tw s.

(* every orbit index is below norbi -- FoldTables.frepL, as a hypothesis so
   this file need not require the table it is proved from                     *)
Hypothesis frepLP : forall r, (r <? nfsi)%uint63 -> (frepi r <? norbi)%uint63.

(* the twelve checks                                                          *)
Hypothesis fsymLCP : fsymLC fsymi.
Hypothesis smulCP : smulC.
Hypothesis fsymECP : fsymEC ractab frepi fsymi repsi.
Hypothesis ractLCP : ractLC ractab.
Hypothesis actrLCP : actrLC actfsr.
Hypothesis frepSCP : frepSC ractab frepi.
Hypothesis ractACP : ractAC ractab.
Hypothesis msymRCP : msymRC ractab actfsri.
Hypothesis twsymLCP : twsymLC twsymi.
Hypothesis acttwiLCP : acttwiLC.
Hypothesis twsymACP : twsymAC twsymi.
Hypothesis msymTCP : msymTC twsymi.

(* and that the 288 entry msym table IS Sym16's relabelling.  msymRC is
   stated over the table so its loop stays in int63; this is what ties the
   two together, and it costs 288 values to run.                              *)
Hypothesis msymiCP : msymiC.

(* the stabiliser fact, which FoldStabiliser.stabE_of_check supplies from stabC *)
Hypothesis stabEP : forall tw r u, (to_nat tw < ntwist)%N ->
  (r <? nfsi)%uint63 -> (to_nat u < nsym)%N ->
  racti ractab r u = rrepi frepi repsi r ->
  p1get F (foldi (frepi r) (twsymi tw u))
  = Dfoldi F frepi fsymi twsymi tw r.

(* and the orbit check itself                                                 *)
Hypothesis foldcheckStepP :
  foldcheckStep F frepi fsymi repsi twsymi actfsr.

(* Phase1's read by rank IS Fold's folded read, once the slots are known      *)
Lemma Dp1riE tw r : Dp1ri F tw r = Dfoldi F frepi fsymi twsymi tw r.
Proof. by rewrite /Dp1ri /Dfoldi frepE fsymE twsymE. Qed.

(* THE POINT: the rank sweep, without sweeping the ranks.                     *)
Lemma p1checkSteprP : p1checkStepr F.
Proof.
apply: p1checkStepr_of_step => tw r k twL rL kL.
rewrite !Dp1riE.
exact: (Dfoldi_step_of_check (fsymEn fsymECP) (fsymLn fsymLCP)
          (frepSn frepSCP) (rrepSn repsi frepSCP) (@repsEn frepi repsi)
          frepLP (twsymLn twsymLCP) (ractLn ractLCP) (actrLn actrLCP)
          (twsymAn twsymACP) (ractAn ractACP) (smulLn smulCP) stabEP
          (acttwiLn acttwiLCP) (@msymLn) (msymTn msymTCP)
          (msymRn (actri := actfsri) actfsriE msymiCP msymRCP)
          foldcheckStepP twL rL kL).
Qed.

End Asm.
