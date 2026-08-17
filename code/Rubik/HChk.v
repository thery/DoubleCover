(* =========================================================================  *)
(*  HChk.v -- the move tables against the coordinates.                        *)
(* =========================================================================  *)

(* The one check that has to pass before a run means anything.  HTables.v is    *)
(* indexed by the prototype's numbering and HCoord.v renumbers the corners to   *)
(* match it; if that were wrong the search would read other cosets, finish, and *)
(* report no maneuver just the same.  See mtabsok in HSearch.v for what is      *)
(* compared.                                                                   *)
(*                                                                            *)
(*   cd ocaml && make mtabs                                                   *)
(*   cd .. && coqc -R . Rubik HTables.v && coqc -R . Rubik HChk.v              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Rubik.HSearch Rubik.HTables.

Lemma mtabs_ok : mtabsok h_mt_e h_mt_cl h_mt_ct = true.
Proof. by vm_compute. Qed.
