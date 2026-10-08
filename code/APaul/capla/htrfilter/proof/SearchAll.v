(** * The search of one line, its callees plugged in

    search_correct: search_spec with no hypothesis, from search_ok,
    difftab_ok, tstep_ok, sub_ok and add_ok. *)

From compcert Require Import CaplaProof.
Require Import HtrFilterCapla.Specs HtrFilterCapla.AddProof
  HtrFilterCapla.SubProof HtrFilterCapla.TstepProof
  HtrFilterCapla.DifftabProof HtrFilterCapla.SearchProof.

Theorem search_correct : search_spec.
Proof. exact: (search_ok (difftab_ok sub_ok) (tstep_ok add_ok)). Qed.

Print Assumptions search_correct.
