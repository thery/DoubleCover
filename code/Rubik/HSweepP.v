(* A PROBE, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* WHAT IT PRICES.  Obligation D is a sweep of the whole table, 190080 x 70 x *)
(* 2187 triples and twelve turns each -- 3.5e11 reads.  Nobody has measured   *)
(* what that costs in Rocq, and a sweep is not a search: it reads the table in*)
(* order rather than at random, so the search's rate says nothing about it.   *)
(* This runs the same sweep over a few e coordinates and is meant to be timed.*)
(*                                                                            *)
(*   cd ocaml && make hbuild JOBS=18 && make mtabs && make hfold              *)
(*   make hdump CHUNK=0 ... (or reuse the HFold_*.vo the run already built)   *)
(*   /usr/bin/time -v coqc -R . Rubik HSweepP.v                               *)
(*                                                                            *)
(* Wanted: the wall time of each of the three, and the resident size.  They   *)
(* are 1, 8 and 64 e coordinates, so the three should be in that ratio once   *)
(* the table is loaded, and 190080 / 64 times the third is the whole sweep.   *)
(* Against it, ocaml/rubik_h.ml `make hadmis' is the same sweep in the same   *)
(* order, so the two numbers are comparable.                                  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Coordfs Phase1 HRoot HCoord HSearch
        HSweep HTables HFoldAll.

Import GroupScope.

Definition admp (n : nat) : bool :=
  adm h_mt_e h_mt_cl h_mt_ct h_which h_fam h_sym_cl h_sym_ct hfoldall
      0%uint63 n.

Time Eval native_compute in admp 1.
Time Eval native_compute in admp 8.
Time Eval native_compute in admp 64.
