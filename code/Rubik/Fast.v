(* =========================================================================  *)
(*  Fast.v                                                                    *)
(*                                                                            *)
(*  searchz3 on int63, as the refinements searchz3f to searchz3n.             *)
(*  Definitions only; FastP.v proves searchz3n = searchz3.                    *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Tabi Moves Redun Searchir Phase1 Farp1.

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
(* an entry is (k, mv3a k, mv3b k) as ints, and the child's p as a nat *)
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

(* ---- and the search.  d stays a nat so that the recursion is structural,
   di is the same depth as an int, for the heuristic test. ------------------ *)
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

(* ---- searchz3g: the heuristic is tested on the coordinates after the move,
   before the table is composed --------------------------------------------- *)
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

(* ---- eq_tabi stopping at the first entry that differs -------------------- *)
Fixpoint eqif (k : nat) (i : int) (a b : arr) : bool :=
  if k is k'.+1 then
    if (PArray.get a i =? PArray.get b i)%uint63
    then eqif k' (Uint63.add i 1%uint63) a b
    else false
  else true.

Definition eq_tabif (a b : arr) : bool := eqif 48 0%uint63 a b.

(* ---- searchz3h: searchz3g with eq_tabif ---------------------------------- *)
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

(* ---- h3le T x di is h3i T x <=? di, lookup by lookup --------------------- *)
Definition hv1le (T : PArray.array arr) (tf : int * int) (di : int) : bool :=
  if (Dfsri tf.2 <=? di)%uint63 then
    if (Dtsi tf.1 (slrank tf.2) <=? di)%uint63 then
      (Dp1ri T tf.1 tf.2 <=? di)%uint63
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

(* ---- searchz3m: x holds the cube and its two conj3 conjugates; each of the
   three is moved only if the previous ones passed the test ----------------- *)
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

(* ---- searchz3n: carry the move path instead of the table.  The coordinates
   say whether the position may be solved; the table is rebuilt from the path
   only then -------------------------------------------------------------- *)
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

(* the path is newest first, and foldr takes its last element first, so the
   moves are composed oldest first *)
Definition rebuild (a0 : arr) (path : seq int) : arr :=
  foldr (fun k acc => comp_tabi 47 acc (PArray.get mtisa k)) a0 path.

Fixpoint searchz3n (T : PArray.array arr) (d : nat) (di : int) (a0 : arr)
                   (path : seq int) (x : c3) (p : nat) : bool :=
  if h3le T x di then
    (* nested ifs and not `&&', which is strict and would rebuild the table
       at every position *)
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

(* ---- searchz3nc: searchz3n, also returning how many positions it visited - *)
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
