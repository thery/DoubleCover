From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1.
Set Implicit Arguments.
Import GroupScope.

Eval vm_compute in step3 (init3 sfti) 0.
Eval vm_compute in step3 (step3 (init3 sfti) 0) 4.
