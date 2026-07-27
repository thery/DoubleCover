Require Import Big.
From Stdlib Require Import Uint63 PArray.
(* 32768 x 32768 entries; the max must be 1073741823 *)
Time Eval vm_compute in build_max 32768 32768%nat.
