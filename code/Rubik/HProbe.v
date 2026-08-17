(* A PROBE, not part of any proof, and not in _CoqProject.                   *)
(*                                                                           *)
(* Reid's table folded by the sixteen symmetries of the up-down axis is       *)
(* 1 851 470 460 entries, which at fifteen four bit entries to an int63 word  *)
(* is 123 431 364 words, or 59 chunks of two million.  The folded phase 1     *)
(* table, which the development already carries, is five such chunks.  So     *)
(* the question is whether twelve times that can be loaded at all, and one    *)
(* chunk answers it.                                                         *)
(*                                                                           *)
(* Generate the chunk, then compile this and watch what it costs:             *)
(*                                                                           *)
(*   cd ocaml && make hdump CHUNK=0                                          *)
(*   cd .. && /usr/bin/time -v coqc -R . Rubik HFold_00.v                    *)
(*   ls -la HFold_00.vo                                                      *)
(*   /usr/bin/time -v coqc -R . Rubik HProbe.v                               *)
(*                                                                           *)
(* The three numbers wanted are the maximum resident size of each compile,    *)
(* the size of the `.vo', and the time.  Multiply by 59.                      *)

From Stdlib Require Import Uint63.
From Stdlib Require Import PArray.
Require Import Rubik.HFold_00.

Local Open Scope uint63_scope.

(* One read at each end, so the array is really loaded and not just named.   *)
Definition probe_ends :=
  Eval vm_compute in (h_chunk_00.[0], h_chunk_00.[2097151]).

(* What a lookup costs is one shift and one mask on top of the read: entry k  *)
(* lives in word k / 15 at bit 4 * (k mod 15).  Written out here so the cost  *)
(* of the packing is visible next to the cost of the read.                   *)
Definition entry (k : int) : int :=
  (h_chunk_00.[k / 15] >> (4 * (k mod 15))) land 15.

Definition probe_entry := Eval vm_compute in entry 1000000.
