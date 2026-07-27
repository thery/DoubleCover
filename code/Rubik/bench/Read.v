Require Import Big Store.
From Stdlib Require Import Uint63 PArray.
(* read the stored table back; the max must be 1048575 *)
Time Eval vm_compute in maxall 1024%nat 1024%nat 0 0 T.
