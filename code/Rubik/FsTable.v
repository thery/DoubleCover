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
        Coordfs Coordfsi Fstab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- The table ----------------------------------------------------------- *)

(* PLACEHOLDER.  Replaced verbatim by the generated Definition; the make is   *)
(* what the generated fold starts from anyway, so the shape does not change.  *)
Definition fstab : arr := PArray.make nwordsi 0%uint63.

(* Every entry is the default, so the read is 0 whatever the index: that one
   fact is the whole file.                                                  *)
Lemma Dfsi_fstab x : Dfsi fstab x = 0%uint63.
Proof.
rewrite /Dfsi /fstab get_makeE.
have h0 k : lsr 0%uint63 k = 0%uint63.
  by apply: to_nat_inj; rewrite to_nat_lsr to_nat_0 div0n.
rewrite h0; apply: bit_ext => n; rewrite land_spec.
by rewrite (@bit_false_lt 0%uint63 0 n) ?to_nat_0.
Qed.

(* ---- What Fstab.v asks of it --------------------------------------------- *)

(* length_make, once nwordsi <=? max_length is known -- 2 ^ 21 against       *)
(* 4 194 303, so it holds, but the comparison is a computation and this is a  *)
(* skeleton.                                                                  *)
Lemma fstab_len : PArray.length fstab = nwordsi.
Proof. by rewrite /fstab length_makeE; vm_compute. Qed.

(* default_make, and nothing else                                             *)
Lemma fstab_def : PArray.default fstab = 0%uint63.
Proof. exact: (@PArray.default_make int 0%uint63 nwordsi). Qed.

(* ---- What it is worth ---------------------------------------------------- *)

(* Every entry is the default, so the heuristic is 0 and both checks hold for *)
(* a reason rather than by computation.  With the generated table these three *)
(* go away and check0 and checkStep are proved by vm_compute instead.         *)

Lemma fstab_zero x : Dfs fstab x = 0.
Proof. by rewrite /Dfs Dfsi_fstab to_nat_0. Qed.

Lemma fstab_check0 : check0 fstab.
Proof. by rewrite /check0 Dfsi_fstab. Qed.

Lemma fstab_checkStep mtabs : checkStep fstab mtabs.
Proof.
rewrite /checkStep; apply: all_pow_all => x; apply/allP => d _.
by rewrite !Dfsi_fstab.
Qed.
