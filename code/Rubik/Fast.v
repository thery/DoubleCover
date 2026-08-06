(* =========================================================================  *)
(*  Fast.v                                                                    *)
(*                                                                            *)
(*  searchz3 with every nat taken out of the inner loop.  NO PROOFS: this is  *)
(*  for measuring only.  searchz3f is not tied to searchz3 by anything yet.   *)
(*                                                                            *)
(*  What it removes, all MEASURED at 100 000 iterations, vm:                  *)
(*                                                                            *)
(*    allowedr p      60.4 us -> 2.55  precomputed, the answer depends only   *)
(*                                    on p, which takes 7 values              *)
(*    nth _ mtis k     8.67 us -> 0.17  an array, not a walk down 18 conses,  *)
(*                                    and it runs once a CHILD                *)
(*    of_nat d         1.57 us -> 0.10  the depth carried as an int as well   *)
(*    step3's two nth over mv3a/mv3b and three of_nat: precomputed with the   *)
(*    move index, so step3i does six array reads and nothing else.            *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Fsparity
        Farp1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the move tables as an array, indexed by an int --------------------- *)
Fixpoint setl (a : PArray.array arr) (i : int) (l : seq arr)
  : PArray.array arr :=
  if l is x :: l' then setl (PArray.set a i x) (Uint63.add i 1) l' else a.

Definition mtisa : PArray.array arr := Eval vm_compute in
  setl (PArray.make 18%uint63 (id_tabi 47)) 0%uint63 mtis.

(* ---- the seven allowed lists, with every index already an int ------------ *)
(* each entry is (k, mv3a k, mv3b k) as ints, and the child's p as a nat --
   p indexes a seven element list, so it is left alone *)
Definition amove := ((int * int) * int)%type.

Definition allowed3 : seq (seq (amove * nat)) := Eval vm_compute in
  [seq [seq (((of_nat k, of_nat (nth 0%N mv3a k)), of_nat (nth 0%N mv3b k)),
             fcpos k)
       | k <- allowedr mtis nfcube oppf fcpos p]
  | p <- iota 0 7].

(* ---- step3 with the indices already int63 -------------------------------- *)
Definition step3i (x : c3) (m : amove) : c3 :=
  let: (x0, x1, x2) := x in
  let: ((k, ka), kb) := m in
  ((acttwii x0.1 k, actfsri x0.2 k),
   (acttwii x1.1 ka, actfsri x1.2 ka),
   (acttwii x2.1 kb, actfsri x2.2 kb)).

(* ---- and the search.  d stays a nat for the recursion to be structural;
   di is the same number as an int, so h3i's test costs nothing. ------------ *)
Fixpoint searchz3f (T : PArray.array arr) (d : nat) (di : int) (a : arr)
                   (x : c3) (p : nat) : bool :=
  if (h3i T x <=? di)%uint63 then
    if eq_tabi 47 a (id_tabi 47) then true
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      (fix go (l : seq (amove * nat)) : bool :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           if searchz3f T d' di' (comp_tabi 47 a (PArray.get mtisa m.1.1))
                          (step3i x m) pk
           then true else go l'
         else false) (nth [::] allowed3 p)
    else false
  else false.

(* =========================================================================  *)
(*  searchz3g: the heuristic tested BEFORE the table is composed              *)
(*                                                                            *)
(*  searchz3f evaluates comp_tabi for every child and then the recursive call *)
(*  rejects most of them on one lookup -- a 48 entry array built to be thrown  *)
(*  away.  Rocq is strict, so there is no laziness to save us.  Testing        *)
(*  h3i on the child's COORDINATES first costs six array reads (step3i) and   *)
(*  one lookup, and only survivors pay for comp_tabi.                          *)
(*                                                                            *)
(*  Same tree, same answer: the test is exactly the one the child would do    *)
(*  first.  Only the order of evaluation changes.                             *)
(* =========================================================================  *)
Fixpoint searchz3g (T : PArray.array arr) (d : nat) (di : int) (a : arr)
                   (x : c3) (p : nat) : bool :=
  if (h3i T x <=? di)%uint63 then
    if eq_tabi 47 a (id_tabi 47) then true
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      (fix go (l : seq (amove * nat)) : bool :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           let x' := step3i x m in
           if (h3i T x' <=? di')%uint63 then
             if searchz3g T d' di' (comp_tabi 47 a (PArray.get mtisa m.1.1))
                            x' pk
             then true else go l'
           else go l'
         else false) (nth [::] allowed3 p)
    else false
  else false.

(* ---- eq_tabi with an early exit ------------------------------------------
   eqi is `(get a i =? get b i) && eqi k' ...'.  andb is a FUNCTION, strict
   under native, so the recursive call runs even when the entries already
   differ -- all 48 are compared every time.  The same trap as the `||' in
   the certificate guards.  `a' is almost never the identity, so this should
   stop at the first or second entry. *)
Fixpoint eqif (k : nat) (i : int) (a b : arr) : bool :=
  if k is k'.+1 then
    if (PArray.get a i =? PArray.get b i)%uint63
    then eqif k' (Uint63.add i 1%uint63) a b
    else false
  else true.

Definition eq_tabif (a b : arr) : bool := eqif 48 0%uint63 a b.

(* searchz3g plus that *)
Fixpoint searchz3h (T : PArray.array arr) (d : nat) (di : int) (a : arr)
                   (x : c3) (p : nat) : bool :=
  if (h3i T x <=? di)%uint63 then
    if eq_tabif a (id_tabi 47) then true
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      (fix go (l : seq (amove * nat)) : bool :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           let x' := step3i x m in
           if (h3i T x' <=? di')%uint63 then
             if searchz3h T d' di' (comp_tabi 47 a (PArray.get mtisa m.1.1))
                            x' pk
             then true else go l'
           else go l'
         else false) (nth [::] allowed3 p)
    else false
  else false.

(* =========================================================================  *)
(*  h3le: the heuristic TEST, short circuited                                 *)
(*                                                                            *)
(*  h3i computes nine table lookups and takes their max; the caller only ever *)
(*  asks `h3i T x <=? di', and max <= di iff every one of them is.  Since the *)
(*  earlier test made most children rejections, the first lookup usually       *)
(*  settles it -- one instead of nine.                                        *)
(*                                                                            *)
(*  h3le T x di is EXACTLY h3i T x <=? di, so the tree does not change.       *)
(* =========================================================================  *)
Definition hv1le (T : PArray.array arr) (tf : int * int) (di : int) : bool :=
  if (Dfsri tf.2 <=? di)%uint63 then
    if (Dtsi tf.1 (slrank tf.2) <=? di)%uint63 then
      (p1get T (p1idxr tf.1 tf.2) <=? di)%uint63
    else false
  else false.

Definition h3le (T : PArray.array arr) (x : c3) (di : int) : bool :=
  let: (x0, x1, x2) := x in
  if hv1le T x0 di then
    if hv1le T x1 di then hv1le T x2 di else false
  else false.

Fixpoint searchz3k (T : PArray.array arr) (d : nat) (di : int) (a : arr)
                   (x : c3) (p : nat) : bool :=
  if h3le T x di then
    if eq_tabif a (id_tabi 47) then true
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      (fix go (l : seq (amove * nat)) : bool :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           let x' := step3i x m in
           if h3le T x' di' then
             if searchz3k T d' di' (comp_tabi 47 a (PArray.get mtisa m.1.1))
                            x' pk
             then true else go l'
           else go l'
         else false) (nth [::] allowed3 p)
    else false
  else false.

(* =========================================================================  *)
(*  searchz3m: the three views computed one at a time                         *)
(*                                                                            *)
(*  step3i still builds all three views' coordinates before h3le gets to      *)
(*  reject on the first.  A child turned away by view 0 never needed views 1  *)
(*  and 2 -- four array reads wasted each time, and most children are turned  *)
(*  away.  Interleaving the two is the same short circuit once more.          *)
(*                                                                            *)
(*  Same tree, same answer: hv1le on all three in order IS h3le.              *)
(* =========================================================================  *)
Definition stepv (v : int * int) (k : int) : int * int :=
  (acttwii v.1 k, actfsri v.2 k).

Fixpoint searchz3m (T : PArray.array arr) (d : nat) (di : int) (a : arr)
                   (x : c3) (p : nat) : bool :=
  if h3le T x di then
    if eq_tabif a (id_tabi 47) then true
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      let: (x0, x1, x2) := x in
      (fix go (l : seq (amove * nat)) : bool :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           let: ((k, ka), kb) := m in
           let y0 := stepv x0 k in
           if hv1le T y0 di' then
             let y1 := stepv x1 ka in
             if hv1le T y1 di' then
               let y2 := stepv x2 kb in
               if hv1le T y2 di' then
                 if searchz3m T d' di'
                      (comp_tabi 47 a (PArray.get mtisa k)) (y0, y1, y2) pk
                 then true else go l'
               else go l'
             else go l'
           else go l'
         else false) (nth [::] allowed3 p)
    else false
  else false.

(* =========================================================================  *)
(*  searchz3n: carry the PATH, not the table                                  *)
(*                                                                            *)
(*  a is used for exactly one thing -- eq_tabif a idi, "is it solved" -- and  *)
(*  maintaining it costs a 48 entry composition for every surviving child.    *)
(*  But a solved cube certainly has solved COORDINATES, and comparing six     *)
(*  ints is nothing.  So test the coordinates, and rebuild the table from the *)
(*  move path only in the case they say it might be solved.                   *)
(*                                                                            *)
(*  Sound because solved => coordinates solved: the coordinate test can only  *)
(*  let through non-solutions, never reject a solution, and the rebuild then  *)
(*  settles it exactly.                                                       *)
(* =========================================================================  *)
Definition solved3 : c3 := Eval vm_compute in init3 (id_tabi 47).

Definition issolved (x : c3) : bool :=
  let: (x0, x1, x2) := x in
  let: (s0, s1, s2) := solved3 in
  if (x0.1 =? s0.1)%uint63 then
    if (x0.2 =? s0.2)%uint63 then
      if (x1.1 =? s1.1)%uint63 then
        if (x1.2 =? s1.2)%uint63 then
          if (x2.1 =? s2.1)%uint63 then (x2.2 =? s2.2)%uint63 else false
        else false
      else false
    else false
  else false.

(* the path is kept newest first, and foldr applies the LAST element of the
   list first -- so folding over `path' itself composes oldest move first,
   which is what is wanted.  An earlier version folded over `rev path' and
   composed them backwards; nothing detected it, because rebuild is only
   ever evaluated in the issolved branch and no search finds a solution, so
   every answer was "no solution" either way.  Found by trying to prove
   rebuild a0 (k :: path) = comp_tabi 47 (rebuild a0 path) (get mtisa k),
   which is now true by foldr's own equation. *)
Definition rebuild (a0 : arr) (path : seq int) : arr :=
  foldr (fun k acc => comp_tabi 47 acc (PArray.get mtisa k)) a0 path.

Fixpoint searchz3n (T : PArray.array arr) (d : nat) (di : int) (a0 : arr)
                   (path : seq int) (x : c3) (p : nat) : bool :=
  if h3le T x di then
    (* a nested if, NOT `&&': andb is strict, so `issolved x && eq_tabif
       (rebuild ...)' would rebuild the table at EVERY node -- the very bug
       this file exists to remove *)
    if (if issolved x then eq_tabif (rebuild a0 path) (id_tabi 47) else false)
    then true
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      let: (x0, x1, x2) := x in
      (fix go (l : seq (amove * nat)) : bool :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           let: ((k, ka), kb) := m in
           let y0 := stepv x0 k in
           if hv1le T y0 di' then
             let y1 := stepv x1 ka in
             if hv1le T y1 di' then
               let y2 := stepv x2 kb in
               if hv1le T y2 di' then
                 if searchz3n T d' di' a0 (k :: path) (y0, y1, y2) pk
                 then true else go l'
               else go l'
             else go l'
           else go l'
         else false) (nth [::] allowed3 p)
    else false
  else false.

(* =========================================================================  *)
(*  the same search, counting the nodes it visits                             *)
(*                                                                            *)
(*  So that the seconds above can be turned into us a node and compared with  *)
(*  the OCaml's 0.6-0.8.  The counter is an int63: a nat one costs O(n) per   *)
(*  increment and would dominate what it measures.                            *)
(* =========================================================================  *)
Fixpoint searchz3nc (T : PArray.array arr) (d : nat) (di : int) (a0 : arr)
                    (path : seq int) (x : c3) (p : nat) : bool * int :=
  if h3le T x di then
    if (if issolved x then eq_tabif (rebuild a0 path) (id_tabi 47) else false)
    then (true, 1%uint63)
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      let: (x0, x1, x2) := x in
      (fix go (l : seq (amove * nat)) (acc : int) : bool * int :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           let: ((k, ka), kb) := m in
           let y0 := stepv x0 k in
           if hv1le T y0 di' then
             let y1 := stepv x1 ka in
             if hv1le T y1 di' then
               let y2 := stepv x2 kb in
               if hv1le T y2 di' then
                 let: (r, c) := searchz3nc T d' di' a0 (k :: path)
                                           (y0, y1, y2) pk in
                 if r then (true, Uint63.add acc c)
                 else go l' (Uint63.add acc c)
               else go l' acc
             else go l' acc
           else go l' acc
         else (false, acc)) (nth [::] allowed3 p) 1%uint63
    else (false, 1%uint63)
  else (false, 1%uint63).

(* =========================================================================  *)
