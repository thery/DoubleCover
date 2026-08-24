(* =========================================================================  *)
(*  RowFoldTab.v -- the fold's tables, made arrays.                           *)
(* =========================================================================  *)

(* RowTabF.v is the numbers, written by ocaml/rubik_row.ml dumptab fold; this *)
(* file makes them arrays.  As in RowTab.v, `Eval vm_compute in' is what      *)
(* makes each body an array VALUE: without it the body IS the cons list, and  *)
(* every read has to walk it.                                                 *)
(*                                                                            *)
(* THE CHECKS ARE NOT HERE YET.  What the prototype checks -- that a renaming *)
(* keeps a parity, keeps a half, sends a page to its orbit and agrees with    *)
(* the conjugation on every member -- is what this side will have to check    *)
(* before a bit of the folded map may stand for sixteen members.              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowFold RowTabF.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

Definition nfpgi  : int := 40320.               (* a page                     *)
Definition nfsrci : int := 27680.               (* a kept page by ten moves   *)
Definition nfsgri : int := 645120.              (* sixteen by two by 20160    *)
Definition nfsloi : int := 65536.               (* sixteen by 4096            *)
Definition nfsbti : int := 384.                 (* sixteen by 24              *)
Definition nfpopi : int := 4096.

Definition fpgi  : arr := Eval vm_compute in mkarr nfpgi 0 fpg_data.
Definition fsrci : arr := Eval vm_compute in mkarr nfsrci 0 fsrc_data.
Definition fsgri : arr := Eval vm_compute in mkarr nfsgri 0 fsgr_data.
Definition fsloi : arr := Eval vm_compute in mkarr nfsloi 0 fslo_data.
Definition fshii : arr := Eval vm_compute in mkarr nfsloi 0 fshi_data.
Definition fsbti : arr := Eval vm_compute in mkarr nfsbti 0 fsbt_data.
Definition forbi : arr := Eval vm_compute in mkarr nrepi 0 forb_data.
Definition frepi : arr := Eval vm_compute in mkarr nrepi 0 frep_data.
Definition fpopi : arr := Eval vm_compute in mkarr nfpopi 0 fpop_data.
