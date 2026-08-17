(* =========================================================================  *)
(*  HSearch.v -- the quarter-turn search over Reid's table.                    *)
(* =========================================================================  *)

(* The search of ocaml/rubik_h.ml, in the shape Fast.v gave the half-turn one: *)
(* the position is carried as its coset along three axes, the maneuver as the   *)
(* list of moves played, and the facelet table is rebuilt from that list only   *)
(* when the cosets say the position might be solved.                          *)
(*                                                                            *)
(* Everything is a Variable here, so this file compiles with no table at all.  *)
(* A run file supplies the seven small tables that ocaml/rubik_h.ml emits with  *)
(* `make mtabs', and the fifty nine chunks of the folded table with            *)
(* `make hdump'.                                                              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves HRoot HCoord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the constants, as int63 -------------------------------------------- *)

Definition nqti  : int := 12%uint63.        (* the twelve quarter turns      *)
Definition nclti : int := 70%uint63.        (* the cl coordinate             *)
Definition nctti : int := 2187%uint63.      (* the ct coordinate             *)

(* the folded table is packed fifteen four-bit entries to a word, and cut into *)
(* chunks of two million words                                                *)
Definition nper  : int := 15%uint63.
Definition nibs  : int := 4%uint63.
Definition nibm  : int := 15%uint63.
Definition cshft : int := 21%uint63.        (* two million is 2 ^ 21         *)
Definition cmskw : int := 2097151%uint63.

(* ---- the eighteen moves as an array, for rebuilding a maneuver ----------- *)

Fixpoint setl (a : PArray.array arr) (i : int) (l : seq arr)
  : PArray.array arr :=
  if l is x :: l' then setl (PArray.set a i x) (Uint63.add i 1%uint63) l' else a.

Definition mtia : PArray.array arr := Eval vm_compute in
  setl (PArray.make 18%uint63 idi) 0%uint63 mtis.

(* ---- the redundancy rule ------------------------------------------------ *)

(* Here U U is a legitimate pair, being the half turn, so `never the same face *)
(* twice running` would be unsound.  What is true: three turns of a face in a  *)
(* row are one turn the other way, so a run is at most two long; a run of two  *)
(* must be twice the SAME turn, since U U' is nothing; and of the two orders   *)
(* of two opposite faces only one is kept.                                    *)
(*                                                                            *)
(* The state of the rule is the last move and how long its run is.  Class 0 is *)
(* the start, and class 1 + 2 m + (r - 1) is `last move m, run r', r being 1   *)
(* or 2 -- a run of three never arises.                                       *)
Definition nclass := (1 + 2 * 12)%N.

Definition pcode (m r : nat) : nat := (1 + 2 * m + (r - 1))%N.
Definition plast (p : nat) : nat := ((p - 1) %/ 2)%N.
Definition prun  (p : nat) : nat := ((p - 1) %% 2 + 1)%N.

Definition allowedq (p m : nat) : bool :=
  if p == 0%N then true else
  let pm := plast p in
  if (m %/ 2)%N == (pm %/ 2)%N then (m == pm) && (prun p == 1%N)
  else ~~ (((m %/ 2)%N == ((pm %/ 2) + 3) %% 6)%N && ((pm %/ 2) < (m %/ 2))%N).

Definition hclass (p m : nat) : nat :=
  if p == 0%N then pcode m 1
  else if (m %/ 2)%N == (plast p %/ 2)%N then pcode m (prun p + 1)
  else pcode m 1.

(* ---- a move, with everything it costs already an int -------------------- *)

(* A move is played on the three axes at once, each with its own relabelling,  *)
(* and remembered by its index among the eighteen so the maneuver can be       *)
(* rebuilt.                                                                   *)
Definition amv := (int * (int * int * int))%type.

Definition amoves : seq amv := Eval vm_compute in
  [seq (of_nat (qt18 m),
        (of_nat (cmv 0 m), of_nat (cmv 1 m), of_nat (cmv 2 m)))
  | m <- iota 0 12].

Definition anull : amv := (0%uint63, (0%uint63, 0%uint63, 0%uint63)).

(* the moves the rule allows in each class, and the class each one leads to   *)
Definition hmoves : seq (seq (amv * nat)) := Eval vm_compute in
  [seq [seq (nth anull amoves m, hclass p m) | m <- iota 0 12 & allowedq p m]
  | p <- iota 0 nclass].

(* ---- how the run is cut up ---------------------------------------------- *)

(* One job takes some of the pairs of moves the search may play first, and     *)
(* plays every second move the rule allows after its first.  The first move is *)
(* NOT cut down: the reduction of doc/reid-1998-fourspot.md has already fixed  *)
(* the beginning of the maneuver, and asking the rest to be canonical as well  *)
(* would need an argument nobody has made.                                    *)
Definition hpres : seq (seq nat) := Eval vm_compute in
  flatten [seq [seq [:: m1; m2] | m2 <- iota 0 12 & allowedq (pcode m1 1) m2]
          | m1 <- iota 0 12].

(* A first move of U, R or F leaves nine second moves and one of D, L or B     *)
(* leaves eleven, which is 6 * 9 + 6 * 11.                                    *)
Lemma hpres_size : seq.size hpres = 120.
Proof. by vm_compute. Qed.

(* job j of nj, dealt round robin as the prototype deals them                 *)
Definition hslice (j nj : nat) : seq (seq nat) :=
  [seq nth [::] hpres i | i <- iota 0 (seq.size hpres) & i %% nj == j].

(* ---- the state --------------------------------------------------------- *)

(* one coset per axis, each of them a triple *)
Definition hv := (int * int * int)%type.
Definition hst := (hv * hv * hv)%type.

Section Search.

(* The move tables of the three coordinates, row major with twelve columns,   *)
(* and the two maps of the fold: which of the sixteen symmetries takes an e to *)
(* the least of its family, which family that is, and how a symmetry acts on   *)
(* cl and on ct.  `make mtabs' emits all five.                                *)
Variable mt_e mt_cl mt_ct : arr.
Variable which fam : arr.
Variable sym_cl sym_ct : arr.

(* the folded table, as its fifty nine chunks *)
Variable hfold : PArray.array arr.

(* ---- one lookup -------------------------------------------------------- *)

(* The fold: an e is carried to the least member of its family by symmetry i,  *)
(* and cl and ct follow it there.  The entry is the four bits at that place.   *)
Definition hget (v : hv) : int :=
  let: (e, c, t) := v in
  let i := PArray.get which e in
  let k := Uint63.add
             (Uint63.mul (Uint63.add (Uint63.mul (PArray.get fam e) nclti)
                                     (PArray.get sym_cl
                                        (Uint63.add (Uint63.mul i nclti) c)))
                         nctti)
             (PArray.get sym_ct (Uint63.add (Uint63.mul i nctti) t)) in
  let w := Uint63.div k nper in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get hfold (Uint63.lsr w cshft))
                            (Uint63.land w cmskw))
                (Uint63.mul nibs (Uint63.mod k nper)))
    nibm.

(* ---- the test, lookup by lookup ---------------------------------------- *)

(* Each of the three answers is a lower bound on the distance, so all three    *)
(* must fit in what is left.  The second is not read unless the first fits.    *)
Definition hale (v : hv) (di : int) : bool := Uint63.leb (hget v) di.

Definition hle (x : hst) (di : int) : bool :=
  let: (x0, x1, x2) := x in
  if hale x0 di then if hale x1 di then hale x2 di else false else false.

(* ---- one move on one axis ---------------------------------------------- *)

Definition stepa (v : hv) (k : int) : hv :=
  let: (e, c, t) := v in
  (PArray.get mt_e  (Uint63.add (Uint63.mul e nqti) k),
   PArray.get mt_cl (Uint63.add (Uint63.mul c nqti) k),
   PArray.get mt_ct (Uint63.add (Uint63.mul t nqti) k)).

(* ---- the check on the move tables -------------------------------------- *)

(* WHAT WOULD GO WRONG SILENTLY.  The table is indexed by the prototype's      *)
(* numbering of the coordinates, and HCoord.v renumbers the corners to match    *)
(* it.  If that renumbering were wrong, every lookup would read some other      *)
(* coset, the search would still finish, and it would still say there is no     *)
(* maneuver.  Nothing in the run would show it.                                *)
(*                                                                            *)
(* So the two are made to agree here: reading the coset of a position and then  *)
(* stepping it through the table must give the coset of the position with the   *)
(* move played on it.  Since each coordinate is connected under the twelve      *)
(* moves, a map that agrees at the solved cube and commutes with every move is  *)
(* the only one there is, so agreeing on a spread of positions is strong.       *)
Definition veq (v w : hv) : bool :=
  let: (a, b, c) := v in let: (d, e, f) := w in
  if Uint63.eqb a d then
    if Uint63.eqb b e then Uint63.eqb c f else false
  else false.

Definition stepchk (a : arr) : bool :=
  all (fun m => veq (htriple (comp_tabi flast a (mvi (qt18 m))))
                    (stepa (htriple a) (of_nat m)))
      (iota 0 12).

(* the six positions, and everything one and two quarter turns from them      *)
Definition hspread : seq arr :=
  flatten [seq (rooti k)
                :: [seq appw (rooti k) (qtw [:: m]) | m <- iota 0 12]
                ++ flatten [seq [seq appw (rooti k) (qtw [:: m; m'])
                                | m' <- iota 0 12]
                           | m <- iota 0 12]
          | k <- iota 0 npfx].

Definition mtabsok : bool := all stepchk hspread.

(* ---- the solved cube --------------------------------------------------- *)

(* The solved cube is fixed by the three rotations, so its coset is h0 along   *)
(* every axis.  This is only a NECESSARY condition -- a coset holds many        *)
(* positions -- and it is used as the cheap filter in front of the real test.  *)
Definition h0i : hv := Eval vm_compute in h0.

Definition heq (v : hv) : bool :=
  let: (e, c, t) := v in
  let: (e0, c0, t0) := h0i in
  if Uint63.eqb e e0 then
    if Uint63.eqb c c0 then Uint63.eqb t t0 else false
  else false.

Definition hsolved (x : hst) : bool :=
  let: (x0, x1, x2) := x in
  if heq x0 then if heq x1 then heq x2 else false else false.

(* the maneuver, newest move first, applied to the position it started from   *)
Definition rebuild (a0 : arr) (path : seq int) : arr :=
  foldr (fun k acc => comp_tabi flast acc (PArray.get mtia k)) a0 path.

(* ---- the search -------------------------------------------------------- *)

(* d is the depth left as a nat, so the recursion is structural, and di is the *)
(* same number as an int, for the test against the table.                     *)
Fixpoint hsearch (d : nat) (di : int) (a0 : arr) (path : seq int)
                 (x : hst) (p : nat) : bool :=
  if hle x di then
    (* nested ifs and not `&&', which would rebuild the table at every node   *)
    if (if hsolved x then eq_tabi flast (rebuild a0 path) idi else false)
    then true
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      let: (x0, x1, x2) := x in
      (fix go (l : seq (amv * nat)) : bool :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           let: (k18, (k0, k1, k2)) := m in
           let y0 := stepa x0 k0 in
           if hale y0 di' then
             let y1 := stepa x1 k1 in
             if hale y1 di' then
               let y2 := stepa x2 k2 in
               if hale y2 di' then
                 if hsearch d' di' a0 (k18 :: path) (y0, y1, y2) pk
                 then true else go l'
               else go l'
             else go l'
           else go l'
         else false) (nth [::] hmoves p)
    else false
  else false.

(* the same, also counting the positions it visited, for the calibration runs *)
Fixpoint hsearchc (d : nat) (di : int) (a0 : arr) (path : seq int)
                  (x : hst) (p : nat) : bool * int :=
  if hle x di then
    if (if hsolved x then eq_tabi flast (rebuild a0 path) idi else false)
    then (true, 1%uint63)
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      let: (x0, x1, x2) := x in
      (fix go (l : seq (amv * nat)) (acc : int) : bool * int :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           let: (k18, (k0, k1, k2)) := m in
           let y0 := stepa x0 k0 in
           if hale y0 di' then
             let y1 := stepa x1 k1 in
             if hale y1 di' then
               let y2 := stepa x2 k2 in
               if hale y2 di' then
                 let: (r, c) := hsearchc d' di' a0 (k18 :: path)
                                         (y0, y1, y2) pk in
                 if r then (true, Uint63.add acc c) else go l' (Uint63.add acc c)
               else go l' acc
             else go l' acc
           else go l' acc
         else (false, acc)) (nth [::] hmoves p) 1%uint63
    else (false, 1%uint63)
  else (false, 1%uint63).

(* ---- the same search, counting the prototype's way ---------------------- *)

(* hsearchc counts a position when it recurses into it, so a child the table   *)
(* cuts is never counted.  ocaml/rubik_h.ml counts on ENTRY: its dfs adds one  *)
(* and only then asks the table, so every child the rule allows is counted,    *)
(* cut or not.  That is a factor of about ten, and this is the version whose   *)
(* numbers can be compared with the prototype's directly.                     *)
Fixpoint hsearchn (d : nat) (di : int) (a0 : arr) (path : seq int)
                  (x : hst) (p : nat) : bool * int :=
  if hle x di then
    if (if hsolved x then eq_tabi flast (rebuild a0 path) idi else false)
    then (true, 1%uint63)
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      let: (x0, x1, x2) := x in
      (fix go (l : seq (amv * nat)) (acc : int) : bool * int :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           let: (k18, (k0, k1, k2)) := m in
           let: (r, c) := hsearchn d' di' a0 (k18 :: path)
                            (stepa x0 k0, stepa x1 k1, stepa x2 k2) pk in
           if r then (true, Uint63.add acc c) else go l' (Uint63.add acc c)
         else (false, acc)) (nth [::] hmoves p) 1%uint63
    else (false, 1%uint63)
  else (false, 1%uint63).

(* ---- what a run asks for ----------------------------------------------- *)

(* The state at the root of position k: its coset along each of the three     *)
(* axes, read off the position relabelled for that axis.                     *)
Definition hstate (k : nat) : hst :=
  (htriple (rooti_ax 0 k), htriple (rooti_ax 1 k), htriple (rooti_ax 2 k)).

(* A job is one prefix of quarter turns played first, which is how the run is  *)
(* cut up: 120 prefixes of length two.  The prefix is played on the state and  *)
(* remembered in the maneuver, and the class it leaves the rule in is carried  *)
(* on, so no job repeats another's work.                                      *)
Definition hplay (sxp : seq int * hst * nat) (m : nat) : seq int * hst * nat :=
  let: (path, x, p) := sxp in
  let: (x0, x1, x2) := x in
  let: (k18, (k0, k1, k2)) := nth anull amoves m in
  (k18 :: path, (stepa x0 k0, stepa x1 k1, stepa x2 k2), hclass p m).

Definition hprefix (k : nat) (w : seq nat) : seq int * hst * nat :=
  foldl hplay ([::], hstate k, 0%N) w.

(* position k, after the prefix w, searched d turns deep *)
Definition hrun (k : nat) (w : seq nat) (d : nat) : bool :=
  let: (path, x, p) := hprefix k w in
  hsearch d (of_nat d) (rooti k) path x p.

Definition hrunc (k : nat) (w : seq nat) (d : nat) : bool * int :=
  let: (path, x, p) := hprefix k w in
  hsearchc d (of_nat d) (rooti k) path x p.

(* the same, counted as the prototype counts                                  *)
Definition hrunn (k : nat) (w : seq nat) (d : nat) : bool * int :=
  let: (path, x, p) := hprefix k w in
  hsearchn d (of_nat d) (rooti k) path x p.

End Search.
