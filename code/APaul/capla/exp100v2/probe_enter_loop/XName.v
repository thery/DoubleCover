From compcert Require Import CaplaProof.
Require Import xname.

(* Fails with "No matching clauses for match" at enter_loop.  Renaming the
   local X of xname.b (to Y, x, Z, XX...) makes it pass. *)
Lemma enter_loop_X μ (M : {ffun 'I_3 -> int64}) r rl (P : Prop) :
  eval_func (genv_of_program program) μ f_f [:: M <:: [u64; 3]] = Some (r, rl) -> P.
Proof.
  enter_func; csteps.
  inv I := { [:: i; M0] } (fun (i : int64) (M : {ffun 'I_3 -> int64}) => True).
  enter_loop I.
Abort.
