(** * Two tactics for the proofs of the functions

    start enters a function with its postcondition hidden in a local
    definition POST, so that the simplifications of the execution leave it
    alone; fin returns and puts the postcondition back. *)

From compcert Require Import CaplaProof.

Ltac start := lazymatch goal with |- _ = Some (?r, ?rl) -> _ =>
  let E := fresh "E" in move=> E; pattern r, rl;
  lazymatch goal with |- ?F _ _ => let Q := fresh "POST" in set Q := F end;
  move: E; enter_func end.

Ltac fin := cret; lazymatch goal with Q := _ |- ?F _ _ => rewrite /F; cbv beta; clear F end.
