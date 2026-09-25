(* =========================================================================  *)
(*  RowFoldSrchIC.v -- RowFoldRunC's run over the int search, and that it is  *)
(*  the same run.                                                             *)
(* =========================================================================  *)

(* The level with the prepass only when the cuts are on, as the OCaml, over   *)
(* the search that carries the depth as an int.  RowFoldSrchIP proves the two *)
(* searches equal, so this is only the level and the run around them.         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask.
Require Import RowFold RowFoldSrch RowFoldSrchI RowFoldSrchIP RowFoldRunC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FSrchIC.

Variable e8num e4bit : arr.
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation wmask := (mmask dnlo dnhi fllo flhi).

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

Variables forb fpop : arr.
Variable ishm : int.

Local Notation fsrk :=
  (fsrchk e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation fsrsk :=
  (fsrchsk e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation flvsk :=
  (flvlsk e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).
Local Notation frnsk :=
  (frunsk e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).

Local Notation fsrki :=
  (fsrchki e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation fsrski :=
  (fsrchski e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation flvski :=
  (flvlski e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).
Local Notation frnski :=
  (frunski e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).

(* two walks that take the same step are the same walk                        *)
Local Notation p1g := (fp1g F frep fsym twsym).
Local Notation wdist := mdist.
Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Local Notation fslvskN :=
  (fslvsk e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).
Local Notation frnskc :=
  (frunskc e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).

Local Notation fsrkL :=
  (fsrchkL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation fsrskL :=
  (fsrchskL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).

(* ---- the int searches with hcoset's last level ---------------------------- *)

(* fsrchki with the last move handed straight to the search at nought        *)
Fixpoint isrchkL (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                 (msk pv : int) (m : rmap) : rmap :=
  if togo is togo'.+1 then
    if togo' is 0 then
      ifold RowRun.nmvn 0
        (fun k m' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
           else if ~~ okmv pv k then m'
           else if cut && ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
           then m'
           else fsrki cut 0 0 (cstep c k) (xstep x k) 0 k m')
        m
    else
    let togoi' := Uint63.sub togoi 1 in
    ifold RowRun.nmvn 0
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
         else if ~~ okmv pv k then m'
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then isrchkL cut togo' togoi' c' (xstep x k)
                        (wmask w (fsslack (Uint63.sub togoi' nd))) k m'
           else m')
      m
  else fsrki cut 0 togoi c x msk pv m.

Fixpoint isrchskL (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                  (msk pv : int) (enough : int) (mn : rmap * int)
                  : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    if togo' is 0 then
      ifold RowRun.nmvn 0
        (fun k a =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
           else if ~~ okmv pv k then a
           else if cut && ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
           then a
           else fsrski cut 0 0 (cstep c k) (xstep x k) 0 k enough a)
        mn
    else
    let togoi' := Uint63.sub togoi 1 in
    ifold RowRun.nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmv pv k then a
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then isrchskL cut togo' togoi' c' (xstep x k)
                         (wmask w (fsslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else fsrski cut 0 togoi c x msk pv enough mn.

Lemma isrchkL_eq cut togo :
  forall togoi c x msk pv m, to_nat togoi = togo -> (togo <= 63)%N ->
  isrchkL cut togo togoi c x msk pv m = fsrkL cut togo c x msk pv m.
Proof.
elim: togo => [|togo ih] togoi c x msk pv m htg hb.
  by rewrite /isrchkL /fsrchkL; apply: fsrchki_eq.
case: togo ih htg hb => [|togo] ih htg hb.
  rewrite /isrchkL /fsrchkL; apply: fifold_eqf => k m'.
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  by apply: fsrchki_eq.
rewrite /isrchkL -/isrchkL /fsrchkL -/fsrchkL.
cbv zeta; apply: fifold_eqf => k m'.
have hbd : (to_nat togoi < nwB)%N := to_nat_bounded togoi.
have h1t : (to_nat 1 <= to_nat togoi)%N by rewrite to_nat_1 htg.
have htg' : to_nat (Uint63.sub togoi 1) = togo.+1.
  by rewrite (to_nat_sub togoi 1 h1t hbd) to_nat_1 htg subn1.
have ht62 : (togo.+1 <= 62)%N by rewrite -ltnS.
case: ifP => _; first by [].
case: ifP => _; first by [].
rewrite andE3; case: ifP => _; first by [].
set w := mdist _.
rewrite (fcondE cut w htg' ht62).
case: ifP => hif; last by [].
have hbd' : (to_nat (Uint63.sub togoi 1) < nwB)%N :=
  to_nat_bounded (Uint63.sub togoi 1).
have hwle : (to_nat w <= to_nat (Uint63.sub togoi 1))%N.
  by rewrite htg'; move: hif => /andP[].
rewrite fmmaskiE (to_nat_sub (Uint63.sub togoi 1) w hwle hbd') htg'.
by apply: ih; [exact: htg' | exact: ltnW].
Qed.

Lemma isrchskL_eq cut togo :
  forall togoi c x msk pv enough mn, to_nat togoi = togo -> (togo <= 63)%N ->
  isrchskL cut togo togoi c x msk pv enough mn
  = fsrskL cut togo c x msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x msk pv enough mn htg hb.
  rewrite /isrchskL /fsrchskL; case: ifP => _; first by [].
  by apply: fsrchski_eq.
rewrite /isrchskL -/isrchskL /fsrchskL -/fsrchskL.
case: ifP => _; first by [].
case: togo ih htg hb => [|togo] ih htg hb.
  apply: fifold_eqf => k a.
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  by apply: fsrchski_eq.
cbv zeta; apply: fifold_eqf => k a.
have hbd : (to_nat togoi < nwB)%N := to_nat_bounded togoi.
have h1t : (to_nat 1 <= to_nat togoi)%N by rewrite to_nat_1 htg.
have htg' : to_nat (Uint63.sub togoi 1) = togo.+1.
  by rewrite (to_nat_sub togoi 1 h1t hbd) to_nat_1 htg subn1.
have ht62 : (togo.+1 <= 62)%N by rewrite -ltnS.
case: ifP => _; first by [].
case: ifP => _; first by [].
rewrite andE3; case: ifP => _; first by [].
set w := mdist _.
rewrite (fcondE cut w htg' ht62).
case: ifP => hif; last by [].
have hbd' : (to_nat (Uint63.sub togoi 1) < nwB)%N :=
  to_nat_bounded (Uint63.sub togoi 1).
have hwle : (to_nat w <= to_nat (Uint63.sub togoi 1))%N.
  by rewrite htg'; move: hif => /andP[].
rewrite fmmaskiE (to_nat_sub (Uint63.sub togoi 1) w hwle hbd') htg'.
by apply: ih; [exact: htg' | exact: ltnW].
Qed.

(* flvlski's body with the map it searches given                              *)
Definition fslvski (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (fsslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (isrchskL cut d di croot sroot msk 18 e (m', n0)).1
      else isrchkL cut d di croot sroot msk 18 m'
    else m'
  else m'.

Fixpoint frunskic (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m' := fslvski true d.+1 (flev m dst) in
      frunskic n1 d.+1 (fcount forb fpop m') m' m
    else
      let m' := fslvski false d.+1 m in
      frunskic n1 d.+1 (fcount forb fpop m') m' dst
  else m.

Lemma fslvski_eq cut d m : (d <= 63)%N -> fslvski cut d m = fslvskN cut d m.
Proof.
move=> hb; rewrite /fslvski /fslvsk; cbv zeta.
case: ifP => _; last by [].
have hdw : (d < nwB)%N.
  by apply: (@ltn_nwB 6); [ | exact: hb].
have hd : to_nat (of_nat d) = d := of_natK d hdw.
set w := mdist _.
rewrite fnleE hd; case: ifP => hle; last by [].
have hbd : (to_nat (of_nat d) < nwB)%N := to_nat_bounded (of_nat d).
have hwle : (to_nat w <= to_nat (of_nat d))%N by rewrite hd; exact: hle.
rewrite fmmaskiE (to_nat_sub (of_nat d) w hwle hbd) hd.
by case: ifP => _; [rewrite isrchskL_eq | rewrite isrchkL_eq].
Qed.

Lemma frunskic_eq n d n0 m dst : (d + n <= 63)%N ->
  frunskic n d n0 m dst = frnskc n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hb; first by [].
have hd1 : (d.+1 <= 63)%N.
  by apply: leq_trans hb; rewrite -addSnnS; exact: leq_addr.
have hb' : (d.+1 + n <= 63)%N by rewrite addSnnS.
rewrite /= -/frunskic -/frunskc.
by case: ifP => _; rewrite fslvski_eq // ih.
Qed.

End FSrchIC.
