(* =========================================================================  *)
(*  RowSrch.v -- the plain row search, with hcoset's cuts and his early stop. *)
(* =========================================================================  *)

(* RowRun.v has the bare search.  This file adds the four things the folded   *)
(* run has had since the start and the plain one had not: the folded phase    *)
(* one table with the moves it names, hcoset's two cuts, Rokicki's early      *)
(* stop, and the count that drives them.  RowSrchP proves them sound.         *)
(*                                                                            *)
(* DEFINITIONS ONLY, NO PROOF, and that is the point: the process that runs   *)
(* for hours loads what it reads and nothing else.  It is RowFoldSrch.v,      *)
(* written for the unfolded map -- and RowSrchP.v is RowFoldRun.v.            *)
(*                                                                            *)
(* IT IS A FILE OF ITS OWN AND NOT AN ADDITION TO RowRun.v.  RowFoldSrch      *)
(* reads RowRun, so a change there rebuilds the folded run -- nine hours -- to *)
(* no purpose.                                                                *)
(*                                                                            *)
(* Every cut is safe the way the ones in RowRun are: what is proved is that   *)
(* the map filled, never that the search was complete, so a cut that loses    *)
(* words can only make the row finish later.                                  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section Srch.

(* ---- the layout, the prepass and the table: RowRun's own ----------------- *)

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place e8num e4bit).
Local Notation unplc := (unplace e8inv e4of par8 par4).

Variable mpg mgr msw mlo mhi : arr.

(* THE PREPASS IS A PARAMETER.  RowMap's is one; RowLvl's prepassD, which     *)
(* reads each page's chunk once and puts it back once, is another and is      *)
(* proved equal to it.  The run takes whichever it is handed.                     *)
Variable prep : rmap -> rmap -> rmap.

(* ---- the phase one table, folded, and the moves it names ----------------- *)

(* THE OTHER FOLD, AND IT IS NOT THE MAP'S.  Rokicki folds the phase one      *)
(* table by the sixteen symmetries and stores one rank of each orbit; beside  *)
(* the distance an entry names which moves bring the state nearer H and which *)
(* at least do not take it further.  A node then offers three or four moves   *)
(* where RowRun's table left it offering eighteen.                            *)
(*                                                                            *)
(* THIS IS THE SAME READ THE FOLDED RUN MAKES.  Only the MAP is unfolded      *)
(* here; the table is folded on both sides, because that fold costs the run   *)
(* nothing and is what makes the search finish.                               *)
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Definition sp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm F frep fsym twsym tw (Uint63.sub c (Uint63.mul tw nfsi)).

Local Notation p1g := sp1g.
Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).
Local Notation nmvn := RowRun.nmvn.

(* ---- what the search carries: RowRun's own ------------------------------- *)

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable posp : pst -> {perm facelet}.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

(* ---- the count, and the mark that counts --------------------------------- *)

(* HOW MANY BITS A HALF WORD HAS, one entry each.  The folded run reads the   *)
(* same table from RowFoldTab; it is built here instead so that the plain     *)
(* chain does not have to load the folded tables to count.                    *)
Definition nlo12 : int := 4096.

Definition popof (v : int) : int :=
  ifold 12 0 (fun i a => Uint63.add a (Uint63.land (Uint63.lsr v i) 1)) 0.

Definition popi : arr := Eval vm_compute in
  ifold (to_nat nlo12) 0 (fun i a => PArray.set a i (popof i))
        (PArray.make nlo12 0).

(* How many members the map holds.  One sweep of the whole map, which the run *)
(* asks for once a level.  The folded count weighs a bit by the size of its   *)
(* orbit; here a page stands for itself, so the bits are simply added up.     *)
Definition mcount (m : rmap) : int :=
  ifold npagen 0
    (fun pg acc =>
       ifold ngroupn 0
         (fun gr b =>
            let v := gget m (grpof pg gr) in
            if Uint63.eqb v 0 then b
            else
              Uint63.add b
                (Uint63.add (PArray.get popi (Uint63.land v lo12))
                            (PArray.get popi
                               (Uint63.land (Uint63.lsr v 12) lo12))))
         acc)
    0.

(* THE SAME MARK, AND A COUNT OF WHAT IT PUTS IN.  The stop has to know how   *)
(* full the map is, and a bit already set is not new.                         *)
Definition mmarkn (mn : rmap * int) (pg gr bt : int) : rmap * int :=
  let: (m, n) := mn in
  let g := grpof pg gr in
  let v := bitof bt in
  let old := gget m g in
  if Uint63.eqb (Uint63.land old v) 0
  then (gset m g (Uint63.lor old v), Uint63.add n 1)
  else mn.

(* ---- the four numbers, which are Rokicki's own --------------------------- *)

(* RowFoldSrch.v has the same four for the folded map.  They are written      *)
(* again rather than shared because that file is proved and its terms must    *)
(* not move.                                                                  *)

Definition enoughb : int := 167000000.          (* his own number             *)
Definition enoughd : int := 3.                  (* and a third of the rest    *)
Definition rcuti : nat := 5.        (* below this a move must go at H         *)
Definition ncutb : int := 6000000.  (* and his threshold on the row's size    *)

(* the moves of H, one bit each                                              *)
Variable ishm : int.

(* ---- hcoset's two cuts --------------------------------------------------- *)

(*   the last move is not in H   a word ending in H is a shorter one          *)
(*                               followed by moves of H, and the prepass has  *)
(*                               already played those                         *)
(*   go straight at H near the   a move that wastes a step down there ends in *)
(*   bottom                      moves of H, so the prepass catches it too    *)
(*                                                                            *)
(* Both come on only once the row is past six million members, which is why   *)
(* they do nothing below depth fourteen.                                      *)
Fixpoint srchk (cut : bool) (togo : nat) (c : int) (x : pst) (msk pv : int)
               (m : rmap) : rmap :=
  if togo is togo'.+1 then
    ifold nmvn 0
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
         else if ~~ okmv pv k then m'
         else if [&& cut, (togo' == 0)%N
                  & ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0]
         then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if [&& (nd <= togo')%N
               & [|| ~~ cut, (nd == togo')%N | (rcuti <= togo' + nd)%N]]
           then srchk cut togo' c' (xstep x k) (wmask w (togo' - nd)) k m'
           else m')
      m
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in mmark m pg gr bt
       else m.

(* ---- and the same search, stopping once the map holds enough ------------- *)

(* THE LAST SEARCH LEVEL NEED NOT BE RUN OUT, only run until the map holds    *)
(* enough for the prepasses above it to finish the row.  Rokicki's rule is    *)
(* 167 million bits plus a third of what the prepass left, and every          *)
(* published time of his was measured with it on.                             *)
Fixpoint srchsk (cut : bool) (togo : nat) (c : int) (x : pst) (msk pv : int)
                (enough : int) (mn : rmap * int) : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    ifold nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmv pv k then a
         else if [&& cut, (togo' == 0)%N
                  & ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0]
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if [&& (nd <= togo')%N
               & [|| ~~ cut, (nd == togo')%N | (rcuti <= togo' + nd)%N]]
           then srchsk cut togo' c' (xstep x k) (wmask w (togo' - nd)) k
                       enough a
           else a)
      mn
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in mmarkn mn pg gr bt
       else mn.

(* ---- one level, and the run ---------------------------------------------- *)

(* the stop on the last level searched, the cuts on every one the caller says *)
Definition levelsk (cut : bool) (d : nat) (m dst : rmap) : rmap :=
  let m' := prep m dst in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then
      if (d == dsrch)%N then
        let n0 := mcount m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (srchsk cut d croot sroot (wmask w (d - nd)) 18 e (m', n0)).1
      else srchk cut d croot sroot (wmask w (d - nd)) 18 m'
    else m'
  else m'.

(* It carries the count of the last level, which is what says whether the     *)
(* cuts are on -- past six million members, hcoset's own rule.                *)
Fixpoint runsk (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    let m' := levelsk (Uint63.ltb ncutb n0) d.+1 m dst in
    runsk n1 d.+1 (mcount m') m' m
  else m.

(* ---- the same search, with the depth left carried as an int -------------- *)

(* srchk makes a unary nat of the table's distance at every expanding node,   *)
(* and then compares, adds and subtracts in unary.  Here the depth left is    *)
(* carried as an int beside the nat and nothing is converted at all: the nat  *)
(* is only what makes the recursion structural.  Neither subtraction wraps.   *)
(* The invariant is togoi = of_nat togo, and it belongs to the proof.  Why,   *)
(* and what it is worth, is in row.md.                                        *)

Definition rcutii : int := 5.       (* rcuti, on the side it is compared on   *)

(* mmask asks its slack whether it is two or more and whether it is one, so   *)
(* an int slack picks one of three nats.  RowMask itself is left alone: the   *)
(* folded run reads it.                                                       *)
Definition sslack (s : int) : nat :=
  if (2 <=? s) then 2%N else if (s =? 1) then 1%N else 0%N.

Fixpoint srchki (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                (msk pv : int) (m : rmap) : rmap :=
  if togo is togo'.+1 then
    let togoi' := Uint63.sub togoi 1 in
    ifold nmvn 0
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
         else if ~~ okmv pv k then m'
         else if [&& cut, (togo' == 0)%N
                  & ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0]
         then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if [&& (nd <=? togoi')
               & [|| ~~ cut, (nd =? togoi')
                   | (rcutii <=? Uint63.add togoi' nd)]]
           then srchki cut togo' togoi' c' (xstep x k)
                       (wmask w (sslack (Uint63.sub togoi' nd))) k m'
           else m')
      m
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in mmark m pg gr bt
       else m.

Fixpoint srchski (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                 (msk pv : int) (enough : int) (mn : rmap * int)
                 : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    let togoi' := Uint63.sub togoi 1 in
    ifold nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmv pv k then a
         else if [&& cut, (togo' == 0)%N
                  & ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0]
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if [&& (nd <=? togoi')
               & [|| ~~ cut, (nd =? togoi')
                   | (rcutii <=? Uint63.add togoi' nd)]]
           then srchski cut togo' togoi' c' (xstep x k)
                        (wmask w (sslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in mmarkn mn pg gr bt
       else mn.

(* ---- the level and the run over that search ------------------------------ *)

(* The level converts its own depth once, which is where of_nat belongs.      *)
Definition levelski (cut : bool) (d : nat) (m dst : rmap) : rmap :=
  let m' := prep m dst in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (sslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let n0 := mcount m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (srchski cut d di croot sroot msk 18 e (m', n0)).1
      else srchki cut d di croot sroot msk 18 m'
    else m'
  else m'.

Fixpoint runski (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    let m' := levelski (Uint63.ltb ncutb n0) d.+1 m dst in
    runski n1 d.+1 (mcount m') m' m
  else m.

End Srch.
