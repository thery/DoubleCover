(* A BENCHMARK, not part of any proof, and not in _CoqProject.               *)
(*                                                                            *)
(* What Rocq costs a node against the prototype, which is the one number the   *)
(* whole run is priced from.  It counts from position 0 with no prefix, the     *)
(* same thing `make hcount HPOS=0 HDEPTH=16' counts, so the two are compared   *)
(* directly -- and the prototype's own numbers have to be taken FRESH: the     *)
(* 82 974 159 nodes recorded for depth 16 are from the single-angle search, and *)
(* this one reads three angles.                                               *)
(*                                                                            *)
(*   cd ocaml && make hcount HPOS=0 HDEPTH=16    # the prototype, with H_TBL   *)
(*   cd .. && /usr/bin/time -v coqc -R . Rubik HBench.v                        *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves HRoot HCoord HSearch HTables HFoldAll.

Import GroupScope.

Definition hcnt (d : nat) : bool * int :=
  hrunc h_mt_e h_mt_cl h_mt_ct h_which h_fam h_sym_cl h_sym_ct hfoldall
        0 [::] d.

(* Three depths, because one of them says nothing about how the cost grows.   *)
Eval native_compute in hcnt 12.
Eval native_compute in hcnt 14.
Eval native_compute in hcnt 16.
