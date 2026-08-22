(* =========================================================================  *)
(*  RowMemb.v -- the cube a member names, and the member a cube gives.        *)
(* =========================================================================  *)

(* THIS IS THE ONE PLACE WHERE THREE RANKS MEET FORTY EIGHT FACELETS, and     *)
(* neither half of it is new: the corners are Phase1's -- ctrip is the eight  *)
(* as facelet triples, cpos and cslot say which corner a facelet belongs to   *)
(* and how far round -- and the edges are Coordfs's, eprim and esec, in the   *)
(* order the prototype uses, so the outer eight are the first eight and the   *)
(* middle four the last.                                                      *)
(*                                                                            *)
(* WHAT IS BUILT IS THE INVERSE, because that is the direction that needs no  *)
(* search: at the facelet of slot p, the position's inverse gives the home    *)
(* facelet of whatever cubie sits at p, and the tables say which cubie that   *)
(* is.  The member's own table is that inverted, which Table.inv_tab does.    *)
(*                                                                            *)
(* Nothing here is turned or flipped: a member of H is three permutations and *)
(* nothing else, which is exactly why three ranks are enough.                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the permutation of a rank ------------------------------------------- *)

(* Unranking is a computation and the layout tables are written in terms of   *)
(* it, so the prototype writes it out: eight numbers to a corner rank, four   *)
(* to a middle one.                                                           *)

Definition up8i : arr := Eval vm_compute in
  mkarr 322560%uint63 0%uint63 up8_data.
Definition up4i : arr := Eval vm_compute in
  mkarr 96%uint63 0%uint63 up4_data.

Definition up8 (r : int) (p : nat) : nat :=
  to_nat (PArray.get up8i (Uint63.add (Uint63.mul r 8%uint63) (of_nat p))).

Definition up4 (r : int) (p : nat) : nat :=
  to_nat (PArray.get up4i (Uint63.add (Uint63.mul r 4%uint63) (of_nat p))).

(* ---- the cube a member names --------------------------------------------- *)

(* THE THREE ACT ON DISJOINT FACELETS, so the cube a member names is their    *)
(* composition, and each depends on ONE rank: the corners on the corner rank, *)
(* the outer eight on the outer rank, the middle four on the middle one.      *)
(* That is what makes every one of them a walk Rocq can check -- 40320, 40320 *)
(* and 24 -- where the three together are nineteen billion.                   *)
(*                                                                            *)
(* Each is the identity away from its own facelets, which is what lets them   *)
(* be composed at all.                                                        *)

Definition cpart (r : int) : seq nat :=
  mkseq (fun f =>
     if (f \in cflat) then
       nth 0%N cflat (3 * up8 r (cpos (inord f)) + cslot (inord f))%N
     else f)
   48.

Definition upart (r : int) : seq nat :=
  mkseq (fun f =>
     if (epos (inord f) < 8)%N then
       if (f \in eprim) then nth 0%N eprim (up8 r (epos (inord f)))
       else if (f \in esec) then nth 0%N esec (up8 r (epos (inord f)))
       else f
     else f)
   48.

Definition mpart (r : int) : seq nat :=
  mkseq (fun f =>
     if (8 <= epos (inord f))%N then
       if (f \in eprim) then
         nth 0%N eprim (8 + up4 r (epos (inord f) - 8))%N
       else if (f \in esec) then
         nth 0%N esec (8 + up4 r (epos (inord f) - 8))%N
       else f
     else f)
   48.

(* A MEMBER OUT OF RANGE NAMES THE SOLVED CUBE.  What is wanted above is      *)
(* that every member names a permutation with no premise attached, and a rank *)
(* past the end of a table reads nought and names nothing.  The guard costs   *)
(* one test and everything that cares carries the range anyway.               *)
Definition membrng (x : memb) : bool :=
  [&& (mcp x <? npagei)%uint63, (mud x <? npagei)%uint63 &
      (mmp x <? nbiti)%uint63].

(* the inverse: at the facelet of a place, the home facelet of what sits      *)
(* there                                                                      *)
Definition membinv (x : memb) : seq nat :=
  if ~~ membrng x then id_tab flast
  else comp_tab (comp_tab (cpart (mcp x)) (upart (mud x))) (mpart (mmp x)).

Definition memb2tab (x : memb) : seq nat := inv_tab flast (membinv x).

(* ---- and the member a cube gives ----------------------------------------- *)

(* The three ranks read off a position, which is what the search does at a    *)
(* leaf.  It is only meant for a position of H: outside it the edges are      *)
(* mixed between the outer eight and the middle four and there is no outer    *)
(* permutation to rank.                                                       *)
(* the rank of a permutation, the prototype's own: fold over the places, and *)
(* at each one count how many later places hold something smaller.  It is a  *)
(* computation over eight numbers, so no table is wanted.                    *)
Definition lrank (n : nat) (f : nat -> nat) : nat :=
  foldl (fun r i =>
           (r * (n - i)
            + count (fun j => (f j < f i)%N) (iota i.+1 (n - i.+1)))%N)
        0%N (iota 0 n).

Definition rank8 (f : nat -> nat) : int := of_nat (lrank 8 f).
Definition rank4 (f : nat -> nat) : int := of_nat (lrank 4 f).

(* The search calls this at every leaf, so it reads the INVERSE TABLE and    *)
(* never builds a permutation: Tabi.inv_tabi is the same inverse csrc takes  *)
(* of the position, and at the primary facelet of a place it gives the home  *)
(* facelet of whatever sits there.                                           *)
Definition tomemb (a : arr) : memb :=
  let u := ti2t flast (inv_tabi flast a) in
  (rank8 (fun p => cpos (inord (nth 0%N u (nth 0%N cprim p)))),
   rank8 (fun p => epos (inord (nth 0%N u (nth 0%N eprim p)))),
   rank4 (fun p => (epos (inord (nth 0%N u (nth 0%N eprim (8 + p)))) - 8)%N)).

(* ---- what the unrank tables have to be ----------------------------------- *)

(* A row of up8 is a permutation of the eight, and a row of up4 of the four.  *)
(* That is a walk over 40320 rows and 24, and it is all the tables are asked  *)
(* for -- nothing here cares WHICH permutation a rank names, only that the    *)
(* naming is one to one.                                                      *)

Definition up8ok1 (r : int) : bool :=
  perm_eq [seq up8 r p | p <- iota 0 8] (iota 0 8).
Definition up8ok : bool := iter npagen 0%uint63 up8ok1.

Definition up4ok1 (r : int) : bool :=
  perm_eq [seq up4 r p | p <- iota 0 4] (iota 0 4).
Definition up4ok : bool := iter nbitn 0%uint63 up4ok1.

(* ---- what the three parts owe, and it is three walks --------------------- *)

(* Each part is a permutation of the forty eight facelets.  Over the ranks    *)
(* that is 40320, 40320 and 24 tests, and it is the whole of what the unrank  *)
(* tables are asked for -- nothing cares WHICH permutation a rank names, only *)
(* that each names one.                                                       *)


(* ---- disjoint tables commute --------------------------------------------- *)

(* The three parts of a member act on disjoint facelets, and so do the three  *)
(* halves of a move of H.  That is what lets the composition be rearranged,   *)
(* and it is the one structural fact the prepass proof needs.                 *)

Lemma comp_tabE (s t : seq nat) f : (f < seq.size s)%N ->
  nth 0%N (comp_tab s t) f = nth 0%N t (nth 0%N s f).
Proof. by move=> h; rewrite /comp_tab (nth_map 0%N). Qed.

Lemma tab_ok_size (t : seq nat) : tab_ok flast t -> seq.size t = 48%N.
Proof. by case/and3P => /eqP. Qed.

Lemma tab_eq (s t : seq nat) : tab_ok flast s -> tab_ok flast t ->
  (forall f, (f < 48)%N -> nth 0%N s f = nth 0%N t f) -> s = t.
Proof.
move=> hs ht h; apply: (@eq_from_nth _ 0%N).
  by rewrite (tab_ok_size hs) (tab_ok_size ht).
by move=> i; rewrite (tab_ok_size hs) => hi; apply: h.
Qed.

Lemma comp_disj (S T s t : seq nat) :
  tab_ok flast s -> tab_ok flast t ->
  all (fun f => (f \in S) || (nth 0%N s f == f)) (iota 0 48) ->
  all (fun f => (f \in T) || (nth 0%N t f == f)) (iota 0 48) ->
  all (fun f => (f \in S) ==> (nth 0%N s f \in S)) (iota 0 48) ->
  all (fun f => (f \in T) ==> (nth 0%N t f \in T)) (iota 0 48) ->
  all (fun f => ~~ ((f \in S) && (f \in T))) (iota 0 48) ->
  comp_tab s t = comp_tab t s.
Proof.
move=> hs ht hsid htid hss htt hd.
have hsl f : (f < 48)%N -> (nth 0%N s f < 48)%N.
  by move=> hf; move: (hs) => /and3P[_ /allP hh _]; apply: hh; apply: mem_nth;
     rewrite (tab_ok_size hs).
apply: tab_eq; try by apply: tab_ok_comp.
move=> f hf.
rewrite comp_tabE ?(tab_ok_size hs) // comp_tabE ?(tab_ok_size ht) //.
have hfS := all_iota_lt hsid hf.
have hfT := all_iota_lt htid hf.
have hfD := all_iota_lt hd hf.
case: (boolP (f \in S)) => hS.
  have hsS : nth 0%N s f \in S by move: (all_iota_lt hss hf); rewrite hS.
  have -> : nth 0%N t (nth 0%N s f) = nth 0%N s f.
    move: (all_iota_lt htid (hsl f hf)).
    by move: (all_iota_lt hd (hsl f hf)); rewrite hsS /= => /negbTE -> /= /eqP.
  by move: hfT; move: hfD; rewrite hS /= => /negbTE -> /= /eqP ->.
have hsf : nth 0%N s f = f by move: hfS; rewrite (negbTE hS) /= => /eqP.
rewrite hsf.
have htl f' : (f' < 48)%N -> (nth 0%N t f' < 48)%N.
  by move=> hf'; move: (ht) => /and3P[_ /allP hh _]; apply: hh; apply: mem_nth;
     rewrite (tab_ok_size ht).
case: (boolP (f \in T)) => hT.
  have htT : nth 0%N t f \in T by move: (all_iota_lt htt hf); rewrite hT.
  move: (all_iota_lt hsid (htl f hf)).
  by move: (all_iota_lt hd (htl f hf)); rewrite htT andbT => /negbTE -> /= /eqP.
by move: hfT; rewrite (negbTE hT) /= => /eqP ht2; rewrite ht2 hsf.
Qed.


(* ---- the three halves of a move of H -------------------------------------- *)

(* A move of H sends corner facelets to corner facelets, outer edges to outer *)
(* edges and middle to middle -- that is what being in H MEANS -- so it is    *)
(* the composition of its three halves, and they are disjoint.  restr cuts a  *)
(* table down to one set and leaves the rest alone.                           *)

Definition restr (S t : seq nat) : seq nat :=
  mkseq (fun f => if f \in S then nth 0%N t f else f) 48.

(* the outer eight and the middle four, as facelet sets                       *)
Definition eout : seq nat := take 8 eprim ++ take 8 esec.
Definition emid : seq nat := drop 8 eprim ++ drop 8 esec.

(* the move a place is carried by, undone: membinv is the inverse of the      *)
(* member, so what acts on it is the move the other way round                 *)
Definition hinv (k : int) : seq nat := inv_tab flast (mvt (hmvi k)).

Definition hcT (k : int) : seq nat := restr cflat (hinv k).
Definition huT (k : int) : seq nat := restr eout (hinv k).
Definition hmT (k : int) : seq nat := restr emid (hinv k).

(* ---- what the three tables owe, part by part ------------------------------ *)

(* Each is a walk, and that is the whole point of splitting the member into   *)
(* three: the corners against the page table, the outer eight against the     *)
(* group table, the middle four against btmv.  Over the places together they  *)
(* would be nineteen billion; apart they are 403 200, 403 200 and 240.        *)

Section Move.

Variable mpg mgr btmvt e8invt e4oft : arr.

(* the corner half: the page table is the corner permutation moved            *)
Definition cmvok1 (k : int) : bool :=
  iter npagen 0%uint63 (fun pg =>
    cpart (pgmv mpg k pg) == comp_tab (hcT k) (cpart pg)).
Definition cmvok : bool := iter nhn 0%uint63 cmvok1.

(* the middle half: btmv is the middle permutation moved                      *)
(* mpart takes the middle RANK, which is what e4of reads off a bit, so the    *)
(* check has to go through it or it is checking the wrong thing.              *)
Definition mmvok1 (k : int) : bool :=
  iter nbitn 0%uint63 (fun bt =>
    mpart (PArray.get e4oft (btmv btmvt k bt))
    == comp_tab (hmT k) (mpart (PArray.get e4oft bt))).
Definition mmvok : bool := iter nhn 0%uint63 mmvok1.

(* THE OUTER HALF IS THE ONE WITH A PARITY IN IT.  A group is a PAIR of outer *)
(* permutations and which of the two a place means is settled by the parity   *)
(* of the corners and the middle together, so the moved place's outer         *)
(* permutation depends on the page and the bit as well as the group.  What    *)
(* makes it a walk again is that a move changes each of the three parities by *)
(* a fixed amount, so the pair is carried across whole: the check runs over   *)
(* the group and the parity, 20160 by two by ten.                             *)
Definition umvok1 (k : int) : bool :=
  iter ngroupn 0%uint63 (fun gr =>
    iter 2 0%uint63 (fun p =>
      upart (PArray.get e8invt
               (Uint63.add (Uint63.mul (grmv mgr k gr) 2%uint63) p))
      == comp_tab (huT k)
           (upart (PArray.get e8invt
                     (Uint63.add (Uint63.mul gr 2%uint63) p))))).
Definition umvok : bool := iter nhn 0%uint63 umvok1.


(* ---- and the move itself is its three halves ------------------------------ *)

(* Ten tables, ten checks: undoing a move of H is its corner half, its outer  *)
(* half and its middle half, composed.  It is what being in H means, written  *)
(* down.                                                                      *)
Definition hsplit : bool :=
  iter nhn 0%uint63 (fun k =>
    hinv k == comp_tab (comp_tab (hcT k) (huT k)) (hmT k)).

End Move.

Section Parts.

Definition cpartok : bool :=
  iter npagen 0%uint63 (fun r => tab_ok flast (cpart r)).
Definition upartok : bool :=
  iter npagen 0%uint63 (fun r => tab_ok flast (upart r)).
Definition mpartok : bool :=
  iter nbitn 0%uint63 (fun r => tab_ok flast (mpart r)).

Hypothesis hcp : cpartok.
Hypothesis hup : upartok.
Hypothesis hmp : mpartok.

(* and then a member names a permutation, with no premise at all              *)
Lemma membinv_ok x : tab_ok flast (membinv x).
Proof.
rewrite /membinv; case: ifPn => [_|]; first exact: tab_ok_id.
rewrite negbK => /and3P[hc hu hm].
apply: tab_ok_comp; last by apply: (iter_at hmp (ltn_nbiti hm)).
apply: tab_ok_comp; first by apply: (iter_at hcp (ltn_npagei hc)).
by apply: (iter_at hup (ltn_npagei hu)).
Qed.

Lemma memb2tab_ok x : tab_ok flast (memb2tab x).
Proof. by apply: tab_ok_inv; apply: membinv_ok. Qed.

End Parts.

(* ---- the prepass moves a member ------------------------------------------ *)

Section Prep.

Variable mpg mgr btmvt e8invt e4oft par8t par4t e8numt : arr.

Hypothesis hcmv : cmvok mpg.
Hypothesis hmmv : mmvok btmvt e4oft.
Hypothesis humv : umvok mgr e8invt.
Hypothesis hspl : hsplit.

(* THE STEP THAT IS LEFT, and it is the parity one.  The three ranks of the   *)
(* moved place are the three ranks moved: the page table for the corners, the *)
(* group table WITH ITS PARITY for the outer eight, btmv for the middle.  It  *)
(* is a walk over the page and the bit -- a move changes each parity by a     *)
(* fixed amount -- and it is what carries a pair of outer permutations across *)
(* whole.                                                                     *)
Hypothesis moved_ranks : forall k pg gr bt, (to_nat k < nhn)%N ->
  inrange pg gr bt ->
  unplace e8invt e4oft par8t par4t
    (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)
  = (pgmv mpg k pg,
     PArray.get e8invt
       (Uint63.add (Uint63.mul (grmv mgr k gr) 2%uint63)
          (Uint63.mod (PArray.get e8numt
             (mud (unplace e8invt e4oft par8t par4t pg gr bt))) 2%uint63)),
     btmv btmvt k bt).

End Prep.
