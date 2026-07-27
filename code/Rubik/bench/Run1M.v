Require Import Big.
From Stdlib Require Import Uint63 PArray.
(* 1024 x 1024 entries; the max must be 1048575 *)
Time Eval vm_compute in build_max 1024 1024%nat.
