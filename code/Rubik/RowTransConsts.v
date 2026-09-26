(* =========================================================================  *)
(*  RowTransConsts.v -- the four values ocaml/rubik_row_rocq.ml reads off     *)
(*  Rocq, printed in the order it reads them.                                 *)
(* =========================================================================  *)

(*   rocq compile -R . Rubik RowTransConsts.v > rowtrans_consts.txt           *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowCubi RowInst.

Open Scope uint63_scope.

Eval vm_compute in ymvpi.
Eval vm_compute in yrooti.
Eval vm_compute in RowInst.croot.
Eval vm_compute in RowInst.csolvedci.
