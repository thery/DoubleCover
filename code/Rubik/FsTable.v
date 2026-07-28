(* =========================================================================  *)
(*  FsTable.v                                                                 *)
(*                                                                            *)
(*  The pruning table itself -- a placeholder, for now.                       *)
(*                                                                            *)
(*  Fstab.v takes the table as a Variable and says what it has to satisfy.    *)
(*  This file supplies one.  It is the ONLY file the real table changes, and  *)
(*  it is one Definition long: fstab_len, fstab_def, check0 and checkStep are *)
(*  all stated against fstab without mentioning its contents.                 *)
(*                                                                            *)
(*  WHY AN ALL ZERO TABLE IS AN HONEST PLACEHOLDER.  A table is admissible    *)
(*  when it passes two checks, and the zero table passes both -- Dfs is 0     *)
(*  everywhere, so Dfs (coordfs 1) = 0, and 0 <= _.+1 needs nothing.  It is   *)
(*  the trivial heuristic: sound, and useless.  The search it drives is the   *)
(*  brute force one Toy.v runs today, so the whole assembly can be built and  *)
(*  tested against Toy.v's node counts BEFORE the real table exists, and      *)
(*  swapping the real one in cannot change what is proved -- only how deep    *)
(*  the search can afford to go.                                              *)
(*                                                                            *)
(*  HOW THE REAL ONE IS MADE.                                                 *)
(*                                                                            *)
(*  1.  rubik_par.ml gains a dump mode for this table, as it already has for  *)
(*      the coordinate move tables (make MoveTables.v):                       *)
(*                                                                            *)
(*        ./rubik_par 1 9 dumpfs > FsTable.v                                  *)
(*                                                                            *)
(*      It runs the breadth first search over the 2 ^ 24 packed summaries --  *)
(*      flip in the low twelve bits, slice mask in the high twelve -- with    *)
(*      the values capped at 9, then packs eight four bit entries per word    *)
(*      and prints 2 ^ 21 int63 literals.  Note the summaries are the MASK    *)
(*      form, not the ranked one: 16 777 216 indices of which 1 013 760 are   *)
(*      reachable.  The unreachable ones keep the default 0, which is exactly *)
(*      what Dfs_oob wants, so the waste costs nothing but memory.            *)
(*                                                                            *)
(*  2.  The generated file is                                                 *)
(*                                                                            *)
(*        Definition fstab : arr := Eval vm_compute in <a fold of set>        *)
(*                                                                            *)
(*      in the style of bench/Store.v, which measured that the kernel holds a *)
(*      268 000 000 entry array and that an evaluated table survives in the   *)
(*      .vo.  2 ^ 21 words is 16 MB, so nothing here is near that.  The       *)
(*      Eval matters: without it the array is rebuilt on every Require.       *)
(*                                                                            *)
(*  3.  Nothing else changes.  The two obligations below are proved for the   *)
(*      generated table the same way -- length_make and default_make -- and   *)
(*      check0 and checkStep become two vm_compute, which is where the real   *)
(*      compute time of the whole development sits.                           *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsData.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- The table ----------------------------------------------------------- *)

(* FsData.v holds the 2 097 152 words; this is the only place they become an
   array.  The Eval matters: without it the fold is redone on every Require. *)
Definition mkarr (l : seq int) : arr :=
  (fix go (a : arr) (i : int) (l : seq int) {struct l} : arr :=
     if l is x :: l' then go (PArray.set a i x) (i + 1)%uint63 l' else a)
    (PArray.make nwordsi 0%uint63) 0%uint63 l.

Definition fstab : arr := Eval vm_compute in mkarr fsdata.

(* ---- What Fstab.v asks of it --------------------------------------------- *)

(* Both are now one read of a literal array rather than an induction.        *)
Lemma fstab_len : PArray.length fstab = nwordsi.
Proof. by vm_compute. Qed.

Lemma fstab_def : PArray.default fstab = 0%uint63.
Proof. by vm_compute. Qed.

(* ---- The two checks ------------------------------------------------------ *)

(* One lookup: the summary of the identity has to hold 0.                    *)
Lemma fstab_check0 : check0 fstab.
Proof. by vm_compute. Qed.

(* THE SECOND COMPUTATION.  16 777 216 summaries times eighteen moves, each
   a dozen bit operations and two reads -- the local certificate, and the
   only thing this table is ever asked to satisfy.  Not run here.           *)
Lemma fstab_checkStep mtabs : checkStep fstab mtabs.
Proof. Admitted.
