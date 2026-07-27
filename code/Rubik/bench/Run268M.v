Require Import Big.
From Stdlib Require Import Uint63 PArray.
(* 16384 x 16384 entries; the max must be 268435455 *)
Time Eval vm_compute in build_max 16384 16384%nat.
