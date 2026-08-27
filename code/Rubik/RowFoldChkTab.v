(* =========================================================================  *)
(*  RowFoldChkTab.v -- the fold tables land in range.                         *)
(* =========================================================================  *)

(* The three conditions RowFoldOk asks of the fold: a page folds to a kept    *)
(* page, a group to a group, a bit to one of the twenty four.  Each is one    *)
(* sweep of a generated list.                                                 *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
Require Import Rubik.RowTabF.

Local Open Scope uint63_scope.

(* a page: the kept page it folds to is one of the 2768 *)
Definition fpgB : bool := all (fun w => (Uint63.lsr w 5) <? 2768) fpg_data.
Lemma fpgBP : fpgB. Proof. by vm_compute. Qed.

(* and so is the page each move gathers from *)
Definition fsrcB : bool := all (fun w => (Uint63.lsr w 5) <? 2768) fsrc_data.
Lemma fsrcBP : fsrcB. Proof. by vm_compute. Qed.

(* a group folds to a group *)
Definition fsgrB : bool := all (fun v => v <? 20160) fsgr_data.
Lemma fsgrBP : fsgrB. Proof. by vm_compute. Qed.

(* a bit folds to one of the twenty four *)
Definition fsbtB : bool := all (fun v => v <? 24) fsbt_data.
Lemma fsbtBP : fsbtB. Proof. by vm_compute. Qed.

(* and each half of a word folds to a half of a word *)
Definition fsloB : bool := all (fun v => v <? 4096) fslo_data.
Lemma fsloBP : fsloB. Proof. by vm_compute. Qed.

Definition fshiB : bool := all (fun v => v <? 4096) fshi_data.
Lemma fshiBP : fshiB. Proof. by vm_compute. Qed.
