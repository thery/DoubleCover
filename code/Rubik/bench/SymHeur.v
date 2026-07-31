(* Does a symmetry-reduced heuristic pay off in Rocq?  YES: 19x fewer nodes.

   The search prunes with h g = Dfs (coordfs g), ONE lookup in the flip x
   slice table.  The OCaml reference (../ocaml/rubik_lb.ml) prunes with the
   max over THREE symmetry conjugates of g -- the SAME table, queried three
   times.  A max of admissible heuristics is admissible, and a stronger
   heuristic prunes exponentially more.

   Measured here, depth 9 from the two-move prefix Far.prefixi 0 3, native_
   compute, single threaded:

     views                            nodes    time     nodes    time
     ---------------------------------------------------------------
     1   (what Far.v does today)     94 762   4.16 s      1x      1x
     3   {1, Sy, Sx}                 11 353   1.06 s     8.3x    3.9x
     5   {1, Sy, Sx, Sy.Sx, Sx.Sy}    4 918   0.895 s   19.3x    4.6x

   For comparison, rubik_lb with its heur restricted to one symmetry needs
   24 081 446 nodes at depth 12 against 1 106 390 with three -- 21.8x.  So
   the 19.3x here reproduces the reference's advantage.

   WHY THE TIME GAIN PLATEAUS AT ~4.6x WHILE THE NODE GAIN KEEPS GROWING.
   Each view costs a conjugation (two comp_tabi) plus a full coordi rebuild,
   about 12 us.  OCaml pays almost nothing per view because it STEPS its three
   coordinate triples through move tables instead of recomputing them.  That
   is exactly Far.v's searchz/actf: carry the coordinate rather than rebuild
   it.  Carrying five coordinates and stepping each with actf (~2 us) instead
   of rebuilding (~12 us) should move the wall-clock gain from 4.6x toward the
   full 19x.  The two ideas compose; they are the same idea.

   WHAT IT WOULD TAKE TO MAKE THIS REAL.  No new table -- this is the table we
   already ship.  The certificate obligations are:
     h 1 = 0            the identity is fixed by every symmetry, so this is
                        Far.Dfsd_0 unchanged;
     h g <= (h (g*m)).+1   for each conjugate, (g*m)^s = g^s * m^s and m^s is
                        itself a move, so Far.Dfsd_step applies view-wise and
                        the max of admissible heuristics is admissible.
   The one new fact is that conjugation permutes the eighteen moves, which is
   a vm_compute check of the shape Redun.uniq_mtabs already uses.  Sym.v
   already provides Sy, Sx, SyT, SxT and ptJ.

   NOTHING HERE IS PROVED -- this file only counts nodes and takes times.  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63 Tabi Moves Coordfs Coordfsi Fstab FsTable
        Sym Searchr Redun Searchir.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* defined here rather than imported from Far, so this does not drag in
   Fsmain and the sixteen certificate files *)
Definition Dfsd : int -> nat := Dfs fstab.
Definition Dtid : arr -> nat := Dti Dfsd.

Definition allow (p : nat) : seq nat :=
  [seq k <- iota 0 18 | okfc0 nfcube oppf p (fcpos k)].

(* the symmetries as arrays, with their inverses -- all closed literals, so
   the VM shares them instead of rebuilding them per node *)
Definition syti     : arr := Eval vm_compute in t2ti 47 Sytab.
Definition sxti     : arr := Eval vm_compute in t2ti 47 Sxtab.
Definition syti_inv : arr := Eval vm_compute in inv_tabi 47 syti.
Definition sxti_inv : arr := Eval vm_compute in inv_tabi 47 sxti.

Definition conjy (a : arr) : arr := comp_tabi 47 (comp_tabi 47 syti_inv a) syti.
Definition conjx (a : arr) : arr := comp_tabi 47 (comp_tabi 47 sxti_inv a) sxti.
Definition conjyx (a : arr) : arr := conjy (conjx a).
Definition conjxy (a : arr) : arr := conjx (conjy a).

Definition hsym3 (a : arr) : nat :=
  maxn (Dtid a) (maxn (Dtid (conjy a)) (Dtid (conjx a))).

Definition hsym5 (a : arr) : nat :=
  maxn (maxn (Dtid a) (Dtid (conjy a)))
       (maxn (Dtid (conjx a))
             (maxn (Dtid (conjyx a)) (Dtid (conjxy a)))).

(* the root Far.v searches: superflip after two moves *)
Definition pfx : arr :=
  comp_tabi 47 (comp_tabi 47 sfti (nth (id_tabi 47) mtis 0))
               (nth (id_tabi 47) mtis 3).

(* one lookup -- what Far.v does today *)
Fixpoint cnt1 (d : nat) (a : arr) (p : nat) : int :=
  if Dtid a <= d then
    if eq_tabi 47 a (id_tabi 47) then 1%uint63
    else if d is d'.+1 then
      (fix go (l : seq nat) (acc : int) : int :=
         if l is k :: l' then
           go l' (acc + cnt1 d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                                (fcpos k))%uint63
         else acc) (allow p) 1%uint63
    else 1%uint63
  else 1%uint63.

Fixpoint cnt3 (d : nat) (a : arr) (p : nat) : int :=
  if hsym3 a <= d then
    if eq_tabi 47 a (id_tabi 47) then 1%uint63
    else if d is d'.+1 then
      (fix go (l : seq nat) (acc : int) : int :=
         if l is k :: l' then
           go l' (acc + cnt3 d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                                (fcpos k))%uint63
         else acc) (allow p) 1%uint63
    else 1%uint63
  else 1%uint63.

Fixpoint cnt5 (d : nat) (a : arr) (p : nat) : int :=
  if hsym5 a <= d then
    if eq_tabi 47 a (id_tabi 47) then 1%uint63
    else if d is d'.+1 then
      (fix go (l : seq nat) (acc : int) : int :=
         if l is k :: l' then
           go l' (acc + cnt5 d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                                (fcpos k))%uint63
         else acc) (allow p) 1%uint63
    else 1%uint63
  else 1%uint63.

(* the three views of the root: 7, 7, 6 -- they really do differ *)
Eval vm_compute in (Dtid pfx, Dtid (conjy pfx), Dtid (conjx pfx)).

Time Eval native_compute in cnt1 9 pfx nfcube.
Time Eval native_compute in cnt3 9 pfx nfcube.
Time Eval native_compute in cnt5 9 pfx nfcube.
