(* A PROBE, not part of any proof, and not in _CoqProject.                   *)
(*                                                                           *)
(* HProbe.v prices ONE chunk of the folded table, and one chunk cannot say    *)
(* what fifty nine cost: its peak holds whatever is transient in building a   *)
(* single array as well as what stays resident.  Two chunks separate the two, *)
(* because the difference between the two peaks is the marginal cost of a     *)
(* chunk, and that is the number to multiply.                                *)
(*                                                                           *)
(*   cd ocaml && make hdump CHUNK=1                                          *)
(*   cd .. && coqc -native-compiler no -R . Rubik HFold_01.v                 *)
(*   /usr/bin/time -v coqc -native-compiler no -R . Rubik HProbe2.v          *)
(*                                                                           *)
(* Then, with P for the peak of HProbe.v and Q for the peak of this one, a    *)
(* worker holding the whole table needs about Q + 57 * (Q - P).              *)

From Stdlib Require Import Uint63.
From Stdlib Require Import PArray.
Require Import Rubik.HFold_00.
Require Import Rubik.HFold_01.

Local Open Scope uint63_scope.

(* Both ends of both chunks, so neither array can be left unbuilt.           *)
Definition probe_ends_00 :=
  Eval vm_compute in (h_chunk_00.[0], h_chunk_00.[2097151]).
Definition probe_ends_01 :=
  Eval vm_compute in (h_chunk_01.[0], h_chunk_01.[2097151]).

(* A lookup that crosses the two, as the search does: entry k lives in word   *)
(* k / 15 at bit 4 * (k mod 15), and the chunk is the word divided by two     *)
(* million.                                                                  *)
Definition entry (k : int) : int :=
  let w := k / 15 in
  let a := if w <? 2097152 then h_chunk_00 else h_chunk_01 in
  (a.[w land 2097151] >> (4 * (k mod 15))) land 15.

Definition probe_entries :=
  Eval vm_compute in (entry 1000000, entry 40000000).
