Require Import Big.
From Stdlib Require Import Uint63 PArray.
(* compute the table once and store the VALUE in the .vo *)
Definition T : array (array int) :=
  Eval vm_compute in fillB 1024%nat 1024%nat 1024 0 (empty 1024 1024%nat).
