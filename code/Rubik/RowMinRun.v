(* =========================================================================  *)
(*  RowMinRun.v -- RowFoldCubDefD's run to thirteen, with Stdlib only loaded. *)
(* =========================================================================  *)

(* A BENCH.  RowMinInst.v's run, to be run where the development was built   *)
(* (roquableu), beside RowBenchCountF.v: fcount48 (rowmapiD 13) must be      *)
(* 14 731 320.                                                                *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMin RowMinTab RowMinInst.

Local Open Scope uint63_scope.

(* ---- the bench ------------------------------------------------------------ *)

(* thrown away: the tables arriving, and the four numbers' tables built       *)
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (mkempty tt).
Time Eval native_compute in
  Uint63.add (Uint63.add (PArray.get ctab 5) (PArray.get etab 5))
    (Uint63.add (PArray.get e8rT 5) (Uint63.add (PArray.get e4rT 5) ishmi)).

(* the run to thirteen: 14 731 320, twice                                     *)
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (rowmapiD 13).
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (rowmapiD 13).
