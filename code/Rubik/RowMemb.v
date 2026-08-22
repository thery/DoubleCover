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

(* CPOS AND EPOS AT THE NAT LEVEL, and this is not a nicety: inord does not   *)
(* reduce, so cposn f under a vm_compute does not come back.  Coordfs         *)
(* says the same thing about its own twelve -- every fact there is pushed to  *)
(* nat for exactly this reason.  These are the same functions with the        *)
(* ordinal taken out.                                                         *)
Definition eposn (f : nat) : nat := (index f (eprim ++ esec)) %% nedge.

(* THE TWO SIDES NUMBER THE CORNERS DIFFERENTLY, and nothing else does.  The  *)
(* prototype takes them URF UFL ULB UBR DFR DLF DBL DRB; cflat takes them in  *)
(* the order its facelets come, which reads ULB UBR UFL URF DLF DFR DBL DRB.  *)
(* A rank the prototype wrote names a permutation of ITS eight, so it has to  *)
(* be read in its order.  The edges need nothing of the kind: eprim and esec  *)
(* are already UR UF UL UB DR DF DL DB FR FL BL BR.                           *)
(*                                                                            *)
(* This is the prototype's order written in our own numbers, and it is not a  *)
(* choice: cordok below turns each face and reads the corner every place      *)
(* receives, and only this order gives the prototype's own numbers.           *)
Definition cordn : seq nat := [:: 3; 2; 0; 1; 5; 4; 6; 7]%N.

(* the twenty four facelets again, the corners in the prototype's order       *)
Definition cflatp : seq nat :=
  flatten [seq [seq nth 0%N cflat (3 * c + j)%N | j <- iota 0 3]
          | c <- cordn].

(* the primary facelet of each place, in the same order                       *)
Definition cprimp : seq nat := [seq nth 0%N cflatp (3 * p)%N | p <- iota 0 8].

Definition cposn (f : nat) : nat := (index f cflatp) %/ 3.
Definition cslotn (f : nat) : nat := (index f cflatp) %% 3.

(* AND THE ORDER IS CHECKED, not asserted.  These are the prototype's own six *)
(* cp arrays, copied out of rubik_row.ml's `basic'.  Turn a face, ask which   *)
(* corner each place receives, and the eight numbers have to be its.  The six *)
(* turns move the corners every way there is, so nothing but the right order  *)
(* passes.                                                                    *)
Definition cparr : seq (seq nat) :=
  [:: [:: 3; 0; 1; 2; 4; 5; 6; 7]; [:: 4; 1; 2; 0; 7; 5; 6; 3];
      [:: 1; 5; 2; 3; 0; 4; 6; 7]; [:: 0; 1; 2; 3; 5; 6; 7; 4];
      [:: 0; 2; 6; 3; 4; 1; 5; 7]; [:: 0; 1; 3; 7; 4; 5; 2; 6]]%N.

Definition cordok : bool :=
  all (fun k => [seq cposn (nth 0%N (inv_tab flast (nth [::] mtabs (3 * k)%N))
                                    (nth 0%N cprimp p)) | p <- iota 0 8]
                == nth [::] cparr k) (iota 0 6).

Lemma cordokC : cordok.
Proof. by vm_compute. Qed.

Definition cpart (r : int) : seq nat :=
  mkseq (fun f =>
     if (f \in cflatp) then
       nth 0%N cflatp (3 * up8 r (cposn f) + cslotn f)%N
     else f)
   48.

Definition upart (r : int) : seq nat :=
  mkseq (fun f =>
     if (eposn f < 8)%N then
       if (f \in eprim) then nth 0%N eprim (up8 r (eposn f))
       else if (f \in esec) then nth 0%N esec (up8 r (eposn f))
       else f
     else f)
   48.

Definition mpart (r : int) : seq nat :=
  mkseq (fun f =>
     if (8 <= eposn f)%N then
       if (f \in eprim) then
         nth 0%N eprim (8 + up4 r (eposn f - 8))%N
       else if (f \in esec) then
         nth 0%N esec (8 + up4 r (eposn f - 8))%N
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
(* the rank of a permutation, the prototype's own: fold over the places, and  *)
(* at each one count how many later places hold something smaller.  It is a   *)
(* computation over eight numbers, so no table is wanted.                     *)
Definition lrank (n : nat) (f : nat -> nat) : nat :=
  foldl (fun r i =>
           (r * (n - i)
            + count (fun j => (f j < f i)%N) (iota i.+1 (n - i.+1)))%N)
        0%N (iota 0 n).

Definition rank8 (f : nat -> nat) : int := of_nat (lrank 8 f).
Definition rank4 (f : nat -> nat) : int := of_nat (lrank 4 f).

(* The search calls this at every leaf, so it reads the INVERSE TABLE and     *)
(* never builds a permutation: Tabi.inv_tabi is the same inverse csrc takes   *)
(* of the position, and at the primary facelet of a place it gives the home   *)
(* facelet of whatever sits there.                                            *)
Definition tomemb (a : arr) : memb :=
  let u := ti2t flast (inv_tabi flast a) in
  (rank8 (fun p => cposn (nth 0%N u (nth 0%N cprimp p))),
   rank8 (fun p => eposn (nth 0%N u (nth 0%N eprim p))),
   rank4 (fun p => (eposn (nth 0%N u (nth 0%N eprim (8 + p))) - 8)%N)).

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


(* ---- the three halves of a move of H --------------------------------------*)

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

Definition hcT (k : int) : seq nat := restr cflatp (hinv k).
Definition huT (k : int) : seq nat := restr eout (hinv k).
Definition hmT (k : int) : seq nat := restr emid (hinv k).

(* ---- what any part of a member or of a move owes -------------------------*)

(* Three things, and each is settled facelet by facelet: the part is a        *)
(* permutation of the forty eight, it leaves every facelet outside its own    *)
(* alone, and it keeps its own.  The last two are what let the three parts of *)
(* a member be shuffled past the three halves of a move, which is the whole   *)
(* of the prepass proof.                                                      *)
Definition partok (S t : seq nat) : bool :=
  [&& tab_ok flast t,
      all (fun f => (f \in S) || (nth 0%N t f == f)) (iota 0 48) &
      all (fun f => (f \in S) ==> (nth 0%N t f \in S)) (iota 0 48)].

Lemma partok_tab S t : partok S t -> tab_ok flast t.
Proof. by case/and3P. Qed.

Definition dsj (S T : seq nat) : bool :=
  all (fun f => ~~ ((f \in S) && (f \in T))) (iota 0 48).

(* the three sets of a member are disjoint, and that is a walk over forty     *)
(* eight facelets with no table in it                                         *)
Lemma dsj_cu : dsj cflatp eout.  Proof. by vm_compute. Qed.
Lemma dsj_cm : dsj cflatp emid.  Proof. by vm_compute. Qed.
Lemma dsj_um : dsj eout emid.    Proof. by vm_compute. Qed.

(* and then two parts of disjoint facelets commute, as tables and as          *)
(* permutations.  The permutation form is the one the assembly uses, because  *)
(* multiplication in a group is associative and comp_tab is not.              *)
Lemma partok_comm S T s t : partok S s -> partok T t -> dsj S T ->
  comp_tab s t = comp_tab t s.
Proof.
case/and3P => hs h1 h2; case/and3P => ht h3 h4 hd.
exact: (comp_disj hs ht h1 h3 h2 h4 hd).
Qed.

Lemma pt_comm S T s t : partok S s -> partok T t -> dsj S T ->
  pt flast s * pt flast t = pt flast t * pt flast s.
Proof.
move=> hs ht hd.
by rewrite !ptM ?(partok_tab hs) ?(partok_tab ht) // (partok_comm hs ht hd).
Qed.

(* AND THIS IS THE WHOLE OF THE PREPASS PROOF, with the cube taken out of it. *)
(* Six things in a row, three of them going past three; the three crossings   *)
(* are the three disjointness facts and nothing else is used.                 *)
Lemma six_shuffle (gT : finGroupType) (a b c x y z : gT) :
  x * b = b * x -> x * c = c * x -> y * c = c * y ->
  a * x * (b * y) * (c * z) = a * b * c * (x * y * z).
Proof.
move=> h1 h2 h3.
rewrite -!mulgA; congr (_ * _).
rewrite mulgA h1 -mulgA; congr (_ * _).
by rewrite [y * (c * z)]mulgA h3 -mulgA mulgA h2 -mulgA.
Qed.

(* ---- what the three tables owe, part by part ------------------------------*)

(* Each is a walk, and that is the whole point of splitting the member into   *)
(* three: the corners against the page table, the outer eight against the     *)
(* group table, the middle four against btmv.  Over the places together they  *)
(* would be nineteen billion; apart they are 403 200, 403 200 and 240.        *)

Section Move.

Variable mpg mgr btmvt e8invt e4oft par8t par4t : arr.

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

(* ---- and the parity, which is not carried across ------------------------- *)

(* WHICH OF A PAIR A PLACE MEANS IS SETTLED BY A PARITY, and a move CHANGES   *)
(* that parity.  Eight of the ten do: U, U' and R2 are all odd on the outer   *)
(* eight, and only U2 and D2 are not.  So the moved place does not take the   *)
(* same half of its pair, and a check that used the same one on both sides    *)
(* would simply be false.                                                     *)
(*                                                                            *)
(* What IS fixed is how much the parity moves.  A move changes the corner     *)
(* parity by the same amount at every page and the middle parity by the same  *)
(* amount at every bit, so reading the two at nought gives the whole story    *)
(* and parok is the walk that says so: ten by 40320 and ten by 24.            *)
Definition dcpar (k : int) : int :=
  Uint63.lxor (PArray.get par8t (pgmv mpg k 0%uint63))
              (PArray.get par8t 0%uint63).

Definition dmpar (k : int) : int :=
  Uint63.lxor (PArray.get par4t (PArray.get e4oft (btmv btmvt k 0%uint63)))
              (PArray.get par4t (PArray.get e4oft 0%uint63)).

(* and the outer parity moves by the two together, because a member's three   *)
(* parities always agree                                                      *)
Definition hpar (k : int) : int := Uint63.lxor (dcpar k) (dmpar k).

Definition parok1 (k : int) : bool :=
  iter npagen 0%uint63 (fun pg =>
    (PArray.get par8t (pgmv mpg k pg) =?
     Uint63.lxor (PArray.get par8t pg) (dcpar k))%uint63)
  &&
  iter nbitn 0%uint63 (fun bt =>
    (PArray.get par4t (PArray.get e4oft (btmv btmvt k bt)) =?
     Uint63.lxor (PArray.get par4t (PArray.get e4oft bt)) (dmpar k))%uint63).
Definition parok : bool := iter nhn 0%uint63 parok1.

(* ---- the outer half ------------------------------------------------------ *)

(* A group is a PAIR of outer permutations and the last place of the number   *)
(* says which.  The move carries the pair across whole -- that is what mgr    *)
(* is -- and moves the parity by hpar, so the check runs over the group and   *)
(* the parity, 20160 by two by ten.                                           *)
Definition umvok1 (k : int) : bool :=
  iter ngroupn 0%uint63 (fun gr =>
    iter 2 0%uint63 (fun p =>
      upart (PArray.get e8invt
               (Uint63.add (Uint63.mul (grmv mgr k gr) 2%uint63)
                           (Uint63.lxor p (hpar k))))
      == comp_tab (huT k)
           (upart (PArray.get e8invt
                     (Uint63.add (Uint63.mul gr 2%uint63) p))))).
Definition umvok : bool := iter nhn 0%uint63 umvok1.

(* ---- and the move itself is its three halves ------------------------------*)

(* Ten tables, ten checks: undoing a move of H is its corner half, its outer  *)
(* half and its middle half, composed, and each half is a part of its own set *)
(* of facelets.  It is what being in H means, written down.                   *)
Definition hmvok : bool :=
  iter nhn 0%uint63 (fun k =>
    [&& partok cflatp (hcT k), partok eout (huT k), partok emid (hmT k) &
        hinv k == comp_tab (comp_tab (hcT k) (huT k)) (hmT k)]).

End Move.

Section Parts.

Definition cpartok : bool :=
  iter npagen 0%uint63 (fun r => partok cflatp (cpart r)).
Definition upartok : bool :=
  iter npagen 0%uint63 (fun r => partok eout (upart r)).
Definition mpartok : bool :=
  iter nbitn 0%uint63 (fun r => partok emid (mpart r)).

Hypothesis hcp : cpartok.
Hypothesis hup : upartok.
Hypothesis hmp : mpartok.

(* and then a member names a permutation, with no premise at all              *)
Lemma membinv_ok x : tab_ok flast (membinv x).
Proof.
rewrite /membinv; case: ifPn => [_|]; first exact: tab_ok_id.
rewrite negbK => /and3P[hc hu hm].
apply: tab_ok_comp; last by apply: partok_tab (iter_at hmp (ltn_nbiti hm)).
apply: tab_ok_comp; first by apply: partok_tab (iter_at hcp (ltn_npagei hc)).
by apply: partok_tab (iter_at hup (ltn_npagei hu)).
Qed.

Lemma memb2tab_ok x : tab_ok flast (memb2tab x).
Proof. by apply: tab_ok_inv; apply: membinv_ok. Qed.

End Parts.

(* ---- the prepass moves a member ------------------------------------------ *)

(* AND THIS IS THE BRIDGE: moving the place moves the member by that move of  *)
(* H.  Nothing here is a new fact about the cube -- the four walks above are  *)
(* the facts -- and all that is left is to shuffle six tables into a          *)
(* different order.  The shuffling is done on PERMUTATIONS rather than on     *)
(* tables, because a group is associative and comp_tab is not.                *)

Section Prep.

Variable mpg mgr btmvt : arr.
Variable e8numt e8invt e4bitt e4oft par8t par4t : arr.

Hypothesis he8 : e8ok e8numt e8invt par8t.
Hypothesis he4 : e4ok e4bitt e4oft par4t.
Hypothesis hpgo : pgok mpg.
Hypothesis hgro : grok mgr.
Hypothesis hbto : btok btmvt.
Hypothesis hcp : cpartok.
Hypothesis hup : upartok.
Hypothesis hmp : mpartok.
Hypothesis hcmv : cmvok mpg.
Hypothesis hmmv : mmvok btmvt e4oft.
Hypothesis humv : umvok mpg mgr btmvt e8invt e4oft par8t par4t.
Hypothesis hmvo : hmvok.
Hypothesis hprk : parok mpg btmvt e4oft par8t par4t.

Local Notation unpl := (unplace e8invt e4oft par8t par4t).
Local Notation prty pg bt :=
  (Uint63.lxor (PArray.get par8t pg) (PArray.get par4t (PArray.get e4oft bt))).

(* the three ranks a place names, read straight off unplace                   *)
Lemma unplE pg gr bt :
  unpl pg gr bt =
  (pg, PArray.get e8invt (Uint63.add (Uint63.mul gr 2%uint63) (prty pg bt)),
   PArray.get e4oft bt).
Proof. by []. Qed.

(* a place in range names a member whose three ranks are in range             *)
Lemma membrng_unpl pg gr bt : inrange pg gr bt -> membrng (unpl pg gr bt).
Proof.
(* NOT apply/and3P: what done would evaluate here is the layout tables.       *)
move=> hr; have [/and4P[h1 h2 h3 _] _] := place_unplace he8 he4 hr.
by rewrite /membrng h1 h2 h3.
Qed.

(* a parity is nought or one, whichever table it came from                    *)
Lemma prty_lt2 pg bt : (pg <? npagei)%uint63 -> (bt <? nbiti)%uint63 ->
  (to_nat (prty pg bt) < 2)%N.
Proof.
move=> hp hb; apply: lxor_lt2; first by apply: (par8_lt2 he8).
by apply: (par4_lt2 he4); case/and5P: (e4at he4 hb).
Qed.

(* HOW FAR THE PARITY MOVES, and it is the same everywhere.  parok says the   *)
(* corner parity and the middle parity each shift by a fixed amount, so their *)
(* exclusive or -- which is the outer parity -- shifts by hpar.               *)
Lemma prty_move k pg bt : (to_nat k < nhn)%N ->
  (pg <? npagei)%uint63 -> (bt <? nbiti)%uint63 ->
  prty (pgmv mpg k pg) (btmv btmvt k bt)
  = Uint63.lxor (prty pg bt) (hpar mpg btmvt e4oft par8t par4t k).
Proof.
move=> kL hp hb; have /andP[hc hm] := iter_at hprk kL.
rewrite (eqP (iter_at hc (ltn_npagei hp))) (eqP (iter_at hm (ltn_nbiti hb))).
rewrite /hpar.
have z8 : (to_nat 0%uint63 < npagen)%N by apply: ltn_npagei.
have z4 : (to_nat 0%uint63 < nbitn)%N by apply: ltn_nbiti.
have h1 : (to_nat (PArray.get par8t pg) < 2)%N by apply: (par8_lt2 he8).
have h2 : (to_nat (PArray.get par4t (PArray.get e4oft bt)) < 2)%N.
  by apply: (par4_lt2 he4); case/and5P: (e4at he4 hb).
have hz8 : (0%uint63 <? npagei)%uint63 by [].
have hz4 : (0%uint63 <? nbiti)%uint63 by [].
have h3 : (to_nat (dcpar mpg par8t k) < 2)%N.
  apply: lxor_lt2; apply: (par8_lt2 he8); last by [].
  by apply: (iter_at (iter_at hpgo kL) z8).
have h4 : (to_nat (dmpar btmvt e4oft par4t k) < 2)%N.
  apply: lxor_lt2; apply: (par4_lt2 he4).
  - by case/and5P: (e4at he4 (iter_at (iter_at hbto kL) z4)).
  by case/and5P: (e4at he4 hz4).
by case: (int_lt2 h1) => ->; case: (int_lt2 h2) => ->;
   case: (int_lt2 h3) => ->; case: (int_lt2 h4) => ->; vm_compute.
Qed.

(* ---- the six tables, and the three that have to move past three ---------- *)

Lemma hcT_ok k : (to_nat k < nhn)%N -> partok cflatp (hcT k).
Proof. by move=> kL; case/and4P: (iter_at hmvo kL). Qed.

Lemma huT_ok k : (to_nat k < nhn)%N -> partok eout (huT k).
Proof. by move=> kL; case/and4P: (iter_at hmvo kL). Qed.

Lemma hmT_ok k : (to_nat k < nhn)%N -> partok emid (hmT k).
Proof. by move=> kL; case/and4P: (iter_at hmvo kL). Qed.

Lemma hinvE k : (to_nat k < nhn)%N ->
  hinv k = comp_tab (comp_tab (hcT k) (huT k)) (hmT k).
Proof. by move=> kL; case/and4P: (iter_at hmvo kL) => _ _ _ /eqP. Qed.

Lemma cpart_ok r : (r <? npagei)%uint63 -> partok cflatp (cpart r).
Proof. by move=> h; apply: (iter_at hcp (ltn_npagei h)). Qed.

Lemma upart_ok r : (r <? npagei)%uint63 -> partok eout (upart r).
Proof. by move=> h; apply: (iter_at hup (ltn_npagei h)). Qed.

Lemma mpart_ok r : (r <? nbiti)%uint63 -> partok emid (mpart r).
Proof. by move=> h; apply: (iter_at hmp (ltn_nbiti h)). Qed.

(* the member a place names, as a permutation of the forty eight              *)
Lemma pt_membinv pg gr bt : inrange pg gr bt ->
  pt flast (membinv (unpl pg gr bt))
  = pt flast (cpart (mcp (unpl pg gr bt))) *
    pt flast (upart (mud (unpl pg gr bt))) *
    pt flast (mpart (mmp (unpl pg gr bt))).
Proof.
(* NO /= ANYWHERE HERE.  cpart is an mkseq, so a simpl unfolds it into a      *)
(* forty eight place list and the shape the rewrites look for is gone.        *)
move=> hr; have hb := membrng_unpl hr.
have [/and4P[h1 h2 h3 _] _] := place_unplace he8 he4 hr.
have hC := partok_tab (cpart_ok h1).
have hU := partok_tab (upart_ok h2).
have hM := partok_tab (mpart_ok h3).
rewrite /membinv; case: ifPn => [hn|_]; first by rewrite hb in hn.
by rewrite -(ptM (tab_ok_comp hC hU) hM) -(ptM hC hU).
Qed.

(* ---- and the move, part by part ------------------------------------------ *)

Lemma pt_membinv_move k pg gr bt : (to_nat k < nhn)%N -> inrange pg gr bt ->
  pt flast (membinv (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)))
  = pt flast (hinv k) * pt flast (membinv (unpl pg gr bt)).
Proof.
move=> kL hr; have hr' := prep_range hpgo hgro hbto kL hr.
have /and3P[hp hg hb] := hr.
have /and3P[hp' hg' hb'] := hr'.
rewrite (pt_membinv hr) (pt_membinv hr') !unplE /mcp /mud /mmp.
(* the three walks, one for each part                                         *)
have hc : cpart (pgmv mpg k pg) = comp_tab (hcT k) (cpart pg).
  by apply/eqP; apply: (iter_at (iter_at hcmv kL) (ltn_npagei hp)).
have hm : mpart (PArray.get e4oft (btmv btmvt k bt))
        = comp_tab (hmT k) (mpart (PArray.get e4oft bt)).
  by apply/eqP; apply: (iter_at (iter_at hmmv kL) (ltn_nbiti hb)).
have hu : upart (PArray.get e8invt
            (Uint63.add (Uint63.mul (grmv mgr k gr) 2%uint63)
                        (prty (pgmv mpg k pg) (btmv btmvt k bt))))
        = comp_tab (huT k)
            (upart (PArray.get e8invt
                      (Uint63.add (Uint63.mul gr 2%uint63) (prty pg bt)))).
  rewrite (prty_move kL hp hb); apply/eqP.
  apply: (iter_at (iter_at (iter_at humv kL) (ltn_ngroupi hg))).
  by apply: prty_lt2.
rewrite hc hm hu (hinvE kL).
(* the six tables become six permutations, and from there it is a group       *)
have [/and4P[_ o2 o3 _] _] := place_unplace he8 he4 hr.
have q2 : (PArray.get e8invt
             (Uint63.add (Uint63.mul gr 2%uint63) (prty pg bt))
           <? npagei)%uint63 := o2.
have q3 : (PArray.get e4oft bt <? nbiti)%uint63 := o3.
have hct := partok_tab (hcT_ok kL).
have hut := partok_tab (huT_ok kL).
have hmt := partok_tab (hmT_ok kL).
have hcc := partok_tab (cpart_ok hp).
have huc := partok_tab (upart_ok q2).
have hmc := partok_tab (mpart_ok q3).
rewrite -(ptM hct hcc) -(ptM hut huc) -(ptM hmt hmc).
rewrite -(ptM (tab_ok_comp hct hut) hmt) -(ptM hct hut).
apply: six_shuffle.
- exact: (pt_comm (cpart_ok hp) (huT_ok kL) dsj_cu).
- exact: (pt_comm (cpart_ok hp) (hmT_ok kL) dsj_cm).
exact: (pt_comm (upart_ok q2) (hmT_ok kL) dsj_um).
Qed.

(* ---- and the same thing the other way up, which is what RowInst asks for - *)

(* memb2tab is membinv inverted, so the move that acted on the left acts on   *)
(* the right and the other way round -- and the move undone, undone, is the   *)
(* move.                                                                      *)
Lemma memb2tab_move k pg gr bt : (to_nat k < nhn)%N -> inrange pg gr bt ->
  pt flast (memb2tab (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)))
  = pt flast (memb2tab (unpl pg gr bt)) * hmv k.
Proof.
move=> kL hr; have hr' := prep_range hpgo hgro hbto kL hr.
have hi : (hmvi k < 18)%N.
  by apply: (all_nthP 0%N (_ : all (fun m => (m < 18)%N) hmvn)).
have hmk := mvt_ok hi.
(* the two tables named, not left to be guessed: an underscore here sends the *)
(* unifier into the member itself.                                            *)
have ho1 := membinv_ok hcp hup hmp (unpl pg gr bt).
have ho2 := membinv_ok hcp hup hmp
              (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)).
(* the three inversions are CONVERSIONS, given as terms.  Left to rewrite,    *)
(* the match against memb2tab does not come back.                             *)
have E1 : pt flast (memb2tab (unpl pg gr bt))
        = (pt flast (membinv (unpl pg gr bt)))^-1 := esym (ptV ho1).
have E2 : pt flast (memb2tab
            (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)))
        = (pt flast (membinv
            (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt))))^-1
        := esym (ptV ho2).
have E3 : pt flast (hinv k) = (pt flast (mvt (hmvi k)))^-1 := esym (ptV hmk).
(* AND NO congr HERE.  congr tries to close its side goals by conversion,     *)
(* and the two sides are permutations of the forty eight facelets: what it    *)
(* would evaluate is the tables.  Both sides are brought to the same shape    *)
(* instead, and the last step is reflexivity on equal terms.                  *)
apply: (etrans E2).
rewrite (pt_membinv_move kL hr).
rewrite invMg.
rewrite E1.
rewrite E3.
rewrite invgK.
rewrite /hmv -(mvtE hi).
exact: erefl.
Qed.

End Prep.
