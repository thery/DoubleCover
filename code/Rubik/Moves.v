(* =========================================================================  *)
(*  Moves.v -- The eighteen moves and the superflip, as tables and int63      *)
(*     arrays.                                                                *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Diameter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the moves, as tables, in the order of Rubik333.moves ---------------- *)

Definition mtabs : seq (seq nat) :=
  flatten [seq [:: t; exp_tab 47 t 2; inv_tab 47 t]
          | t <- [:: cycs_tab 47 Uncyc; cycs_tab 47 Rncyc; cycs_tab 47 Fncyc;
                     cycs_tab 47 Dncyc; cycs_tab 47 Lncyc; cycs_tab 47 Bncyc]].

Lemma mtabs_ok : all (tab_ok 47) mtabs.
Proof. by vm_compute. Qed.

Lemma mtabsE : moves = [seq pt 47 mt | mt <- mtabs].
Proof.
rewrite /moves /faces {1}/map /flatten /foldr /cat.
by rewrite UmoveT RmoveT FmoveT DmoveT LmoveT BmoveT !ptX // !ptV //.
Qed.

(* ---- the superflip, as a table -------------------------------------------*)

Definition sfncyc : seq (seq nat) :=
  [:: [:: 1; 33]; [:: 3; 9]; [:: 4; 25]; [:: 6; 17]; [:: 11; 36];
      [:: 12; 19]; [:: 14; 43]; [:: 20; 27]; [:: 22; 41]; [:: 28; 35];
      [:: 30; 44]; [:: 38; 46]]%N.

Definition sftab : seq nat := cycs_tab 47 sfncyc.

Lemma sftab_ok : tab_ok 47 sftab.
Proof. by vm_compute. Qed.

Lemma sftabE : superflip = pt 47 sftab.
Proof.
rewrite /superflip /Spcyc /sftab.
by have ->// := @cycs_pt 47%N sfncyc.
Qed.

(* ---- the same, on int63 and PArray ---------------------------------------*)
(*                                                                            *)
(*  The Ti copies of the T theorems above.  t2ti is the only conversion, and  *)
(*  ti2t_t2ti reads the list back unchanged, so each Ti lemma is its T lemma  *)
(*  plus one rewrite -- nothing about the cube is proved twice.               *)

(* the two side conditions of Tabi.v, at n = 47.  nwB is 2 ^ 63 and nat is    *)
(* unary, so the first is not a computation but a comparison of exponents.    *)
Lemma n47_small : 47.+1 < nwB.
Proof. by apply: (@ltn_nwB 6). Qed.

Lemma n47_len : (of_nat 47.+1 <=? PArray.max_length)%uint63.
Proof. by vm_compute. Qed.

Definition mtis : seq (PArray.array int) := [seq t2ti 47 mt | mt <- mtabs].
Definition sfti : PArray.array int := t2ti 47 sftab.

Lemma mtis_ok : all (tabi_ok 47) mtis.
Proof.
rewrite /mtis all_map; apply/allP => mt mtM /=.
by apply: (tabi_ok_t2ti n47_small n47_len); apply: (allP mtabs_ok).
Qed.

Lemma sfti_ok : tabi_ok 47 sfti.
Proof. by rewrite /sfti; apply: (tabi_ok_t2ti n47_small n47_len sftab_ok). Qed.

Lemma ti2t_mtis : [seq ti2t 47 mt | mt <- mtis] = mtabs.
Proof.
rewrite /mtis -map_comp -[RHS]map_id; apply/eq_in_map => mt mtM /=.
by apply: (ti2t_t2ti n47_small n47_len); apply: (allP mtabs_ok).
Qed.

Lemma mtisE : moves = [seq pt 47 mt | mt <- [seq ti2t 47 mt | mt <- mtis]].
Proof. by rewrite ti2t_mtis -mtabsE. Qed.

Lemma sftiE : superflip = pt 47 (ti2t 47 sfti).
Proof. by rewrite /sfti (ti2t_t2ti n47_small n47_len sftab_ok) sftabE. Qed.
