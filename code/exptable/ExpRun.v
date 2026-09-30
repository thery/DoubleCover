(** * The first lines of [in_lt], checked *)

From ExpTable Require Import ExpCheck ExpData.

Lemma table_okE : table_ok table.
Proof. apply check_tableP; vm_compute; reflexivity. Qed.
