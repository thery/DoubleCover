(* =========================================================================  *)
(*  RowFoldSrch.v -- the row search and run, on the folded map.               *)
(* =========================================================================  *)

(* flvlsk is one level with Rokicki's early stop and hcoset's two cuts;       *)
(* frunsk iterates it.  RowFoldRun proves them sound.                         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowFold RowRun Fold RowMask.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FSrch.

(* ---- the layout, to read a member's place -------------------------------- *)

Variable e8num e4bit : arr.

Local Notation plc := (place e8num e4bit).

(* ---- the fold, and the move on groups and bits --------------------------- *)

Variable fpg fsrc fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.

Local Notation flev := (flevel fsrc fsgr fslo fshi mgr msw mlo mhi).
Local Notation flevg := (flevelg fsrc fsgr fslo fshi mgr msw mlo mhi).
Local Notation fmk := (fmark fpg fsgr fsbt).
Local Notation fmkn := (fmarkn fpg fsgr fsbt).

(* ---- the phase one table, folded ----------------------------------------- *)

(* THE OTHER FOLD.  The sixteen symmetries act on the flip and slice rank     *)
(* too, so only one rank of each orbit is stored: 64 430 against 1 013 760.   *)
(* A read folds the rank to its orbit and carries the twist through the same  *)
(* symmetry, which is Fold.Dfoldi.                                            *)
(*                                                                            *)
(* THE SEARCH CARRIES ONE NUMBER AND THE FOLD WANTS TWO.  RowInst's           *)
(* coordinate is the twist times the number of ranks plus the rank, so the    *)
(* two come back by one division -- the same number the search already steps, *)
(* read the other way round.                                                  *)
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.

(* THE TABLE CARRIES THE MOVES NOW.  RowMask.v's read: the same fold, and    *)
(* beside the distance the moves that bring the state nearer H and the ones  *)
(* that at least do not take it further, named for the KEPT state and        *)
(* renamed back through the four decoding tables.  A node then offers three  *)
(* or four moves where it offered eighteen.                                  *)
Variables dnlo dnhi fllo flhi : arr.

Definition fp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm F frep fsym twsym tw (Uint63.sub c (Uint63.mul tw nfsi)).

Local Notation p1g := fp1g.
Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

(* ---- the search ---------------------------------------------------------- *)

(* RowRun.srch, mark for mark, with fmk at the leaf.                          *)
Fixpoint fsrch (togo : nat) (c : int) (x : pst) (msk : int) (pv : int)
               (m : rmap) : rmap :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then m'
         else if ~~ okmv pv k then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if (nd <= togo')%N
           then fsrch togo' c' (xstep x k) (wmask w (togo' - nd)) k m'
           else m')
      m
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmk m pg gr bt
       else m.

(* NOT PART OF THE RUN.  The same search, counting the leaves it reaches       *)
(* instead of marking them, so that a search which finds nothing can be told  *)
(* from a mark that is lost on the way to the map.                            *)
Fixpoint fsrchn (togo : nat) (c : int) (x : pst) (msk : int) (pv : int)
                (n : int) : int :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else if ~~ okmv pv k then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if (nd <= togo')%N
           then fsrchn togo' c' (xstep x k) (wmask w (togo' - nd)) k a
           else a)
      n
  else if csolved c then Uint63.add n 1 else n.

(* ---- one level, and the run ---------------------------------------------- *)

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

(* The two maps: the level reads m and fills dst, and the caller swaps.       *)
Definition flvl (d : nat) (m dst : rmap) : rmap :=
  let m' := flev m dst in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then fsrch d croot sroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

Fixpoint frun (n : nat) (d : nat) (m dst : rmap) : rmap :=
  if n is n1.+1 then frun n1 d.+1 (flvl d.+1 m dst) m else m.

(* the same run over the guarded level, which never writes a word that is
   already right *)
Definition flvlg (d : nat) (m dst : rmap) : rmap :=
  let m' := flevg m dst in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then fsrch d croot sroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

Fixpoint frung (n : nat) (d : nat) (m dst : rmap) : rmap :=
  if n is n1.+1 then frung n1 d.+1 (flvlg d.+1 m dst) m else m.

(* ---- hcoset's own stop --------------------------------------------------- *)

(* THE LAST SEARCH LEVEL NEED NOT BE RUN OUT, only run until the map holds   *)
(* enough for the prepasses above it to finish the row.  Rokicki's rule is   *)
(* 167 million bits plus a third of what the prepass left, and every         *)
(* published time of his was measured with it on.  It is safe like every     *)
(* other cut here: what is proved is that the map filled, not that the       *)
(* search was complete, so a cut that loses words can only make the row      *)
(* finish later, never call a member covered when it is not.                 *)

Variables forb fpop : arr.

Definition enoughb : int := 167000000%uint63.   (* his own number            *)
Definition enoughd : int := 3%uint63.           (* and a third of the rest   *)

(* the search, carrying the count of what it has put in and stopping when it *)
(* has put in enough                                                         *)
Fixpoint fsrchs (togo : nat) (c : int) (x : pst) (msk : int) (pv : int)
                (enough : int) (mn : rmap * int) : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else if ~~ okmv pv k then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if (nd <= togo')%N
           then fsrchs togo' c' (xstep x k) (wmask w (togo' - nd)) k enough a
           else a)
      mn
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmkn mn pg gr bt
       else mn.

(* the level, with the stop on the last one it searches.  Counting the map   *)
(* costs one sweep and only there.                                           *)
Definition flvls (d : nat) (m dst : rmap) : rmap :=
  let m' := flev m dst in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (fsrchs d croot sroot (wmask w (d - nd)) 18%uint63 e (m', n0)).1
      else fsrch d croot sroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

Fixpoint fruns (n : nat) (d : nat) (m dst : rmap) : rmap :=
  if n is n1.+1 then fruns n1 d.+1 (flvls d.+1 m dst) m else m.


(* ---- hcoset's two remaining cuts ----------------------------------------- *)

(* THESE TWO ARE IN THE PROTOTYPE AND WERE NOT HERE.  Both are switched on    *)
(* only once the row is big -- past six million members -- so below depth     *)
(* fourteen they do nothing, which is why the two sides walked identical      *)
(* trees in everything measured so far.                                       *)
(*                                                                            *)
(*   the last move is not in H   a word ending in H is a shorter one          *)
(*                               followed by moves of H, and the prepass has  *)
(*                               already played those                         *)
(*   go straight at H near the   a move that wastes a step down there ends in *)
(*   bottom                      moves of H, so the prepass catches it too    *)
(*                                                                            *)
(* Both are safe the way the early stop is: what is proved is that the map    *)
(* filled, so a cut that loses words can only make the row finish later,      *)
(* never call a member covered when it is not.                                *)

(* the moves of H, one bit each *)
Variable ishm : int.

(* hcoset's own number: below it a move must go straight at H *)
Definition rcuti : nat := 5.

(* and his threshold on the row's size *)
Definition ncutb : int := 6000000%uint63.

Fixpoint fsrchk (cut : bool) (togo : nat) (c : int) (x : pst) (msk pv : int)
                (m : rmap) : rmap :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then m'
         else if ~~ okmv pv k then m'
         else if [&& cut, (togo' == 0)%N
                  & ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1%uint63 k))
                                  0%uint63]
         then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if [&& (nd <= togo')%N
               & [|| ~~ cut, (nd == togo')%N | (rcuti <= togo' + nd)%N]]
           then fsrchk cut togo' c' (xstep x k) (wmask w (togo' - nd)) k m'
           else m')
      m
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmk m pg gr bt
       else m.

(* the level, with the cuts on or off as the caller says *)
Definition flvlk (cut : bool) (d : nat) (m dst : rmap) : rmap :=
  let m' := flev m dst in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N
    then fsrchk cut d croot sroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

(* ---- and the two together: the stop AND the cuts ------------------------- *)

(* fsrchs stops when the map holds enough; fsrchk refuses the moves hcoset    *)
(* refuses.  Neither has the other, and a run wants both.  This is fsrchs     *)
(* with fsrchk's two tests put in, word for word from each.                   *)
(*                                                                            *)
(* NOTHING HERE IS PROVED.  Like fsrchs and fsrchk it is for measuring; what  *)
(* says it is right is the count.                                             *)

Fixpoint fsrchsk (cut : bool) (togo : nat) (c : int) (x : pst) (msk pv : int)
                 (enough : int) (mn : rmap * int) : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else if ~~ okmv pv k then a
         else if [&& cut, (togo' == 0)%N
                  & ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1%uint63 k))
                                  0%uint63]
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if [&& (nd <= togo')%N
               & [|| ~~ cut, (nd == togo')%N | (rcuti <= togo' + nd)%N]]
           then fsrchsk cut togo' c' (xstep x k) (wmask w (togo' - nd)) k
                        enough a
           else a)
      mn
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmkn mn pg gr bt
       else mn.

(* the level with everything on: the stop on the last one searched, the cuts  *)
(* on every one the caller says                                               *)
Definition flvlsk (cut : bool) (d : nat) (m dst : rmap) : rmap :=
  let m' := flev m dst in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (fsrchsk cut d croot sroot (wmask w (d - nd)) 18%uint63 e (m', n0)).1
      else fsrchk cut d croot sroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

(* the run with everything on.  It carries the count of the last level, which *)
(* is what says whether the cuts are on -- past six million members, hcoset's *)
(* own rule.  RowFoldOptT.fruno is this with the counts kept in a list.       *)
Fixpoint frunsk (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    let m' := flvlsk (Uint63.ltb ncutb n0) d.+1 m dst in
    frunsk n1 d.+1 (fcount forb fpop m') m' m
  else m.

End FSrch.
