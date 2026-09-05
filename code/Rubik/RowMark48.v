(* =========================================================================  *)
(*  RowMark48.v -- the witnesses marked into the map, instead of a map of their *)
(*  own.                                                                      *)
(* =========================================================================  *)

(* RowFinal keeps the witnesses in a SECOND map and asks mfull248 of the two.   *)
(* That map is a whole map -- 812 851 200 words -- made to hold thirty two    *)
(* bits, and the test reads both at every word.  Marking them into the map    *)
(* the run leaves does the same work: the map is already sound at twenty, a   *)
(* witness is a member within twenty, and a mark keeps a map sound.  mfull48    *)
(* alone is then the test, and only one map is ever held.                     *)
(*                                                                            *)
(* IT HAS TO BE AT THE END AND NOT AT THE START.  A map sound at d claims     *)
(* every bit it has set is a member within d; a witness is within TWENTY, so  *)
(* seeding one before the run would make the first level claim its            *)
(* neighbours are within one, and they are not.                               *)
(*                                                                            *)
(* IT IS A FILE OF ITS OWN AND NOT AN ADDITION TO RowFinal.v, for the reason  *)
(* RowSrch is not an addition to RowRun: the folded run reads RowFinal, and a *)
(* change there rebuilds it.  RowFoldFinal.fmark_sound is this lemma for the  *)
(* folded map.                                                                *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowRun RowFinal.
Require Import Row48 RowMap48 RowRun48 RowFinal48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section Mark.

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place48 e8num e4bit par8).
Local Notation unplc := (unplace48 e8inv e4of par4).
Local Notation mok := (membok par8 par4).
Local Notation inrng := inrange48.

Variable ptab : memb -> seq nat.
Hypothesis ptabP : forall x, tab_ok flast (ptab x).

Local Notation pos := (RowFinal.pos ptab).
Local Notation wthn := (RowRun.wthn pos).
Local Notation soundat := (RowRun48.soundat e8inv e4of par4 pos).
Local Notation wgood := (RowFinal48.wgood48 e8inv e4of par4 ptab).

Variable wl : seq (int * int * int * seq nat).

(* the witnesses written into the map they are handed                        *)
Definition wmarkof (l : seq (int * int * int * seq nat)) (m : rmap) : rmap :=
  foldr (fun t m' => let: (pg, gr, bt, _) := t in mmark m' pg gr bt) m l.

(* ---- a mark keeps a map sound -------------------------------------------- *)

Lemma mmark_sound m pg gr bt :
  inrng pg gr bt -> wthn 20 (unplc pg gr bt) ->
  soundat m 20 -> soundat (mmark m pg gr bt) 20.
Proof.
move=> hr hw hm pg' gr' bt' hr' ht'.
by case: (mmark48P hr hr' ht') => [[<- <- <-]|hb]; [exact: hw | exact: hm].
Qed.

Lemma wmark_sound l m : wgood l -> soundat m 20 -> soundat (wmarkof l m) 20.
Proof.
elim: l m => [|[[[pg gr] bt] w] l ih] m //=.
move=> /andP[/and3P[hr hs hw] hg] hm.
by apply: mmark_sound => //;
   [exact: (RowFinal.wokP ptabP hw hs) | exact: ih].
Qed.

(* ---- and the theorem, on one map ----------------------------------------- *)

(* RowFinal.row_within_20, with mfull48 of the marked map where it had mfull248   *)
(* of two.  The witnesses enter through wmark_sound instead of wmap_wit.      *)
Variable mfin : rmap.

Theorem row_within_20_marked :
  soundat mfin 20 ->
  RowFinal48.wgood48 e8inv e4of par4 ptab wl ->
  mfull48 (wmarkof wl mfin) ->
  forall x, mok x -> wthn 20 x.
Proof.
move=> hs hw hf x hx.
case E: (plc x) => [[pg gr] bt].
have hr := place48_range he8 he4 hx E.
have hu := unplace48_place48 he8 he4 hx E.
rewrite -hu.
by apply: (wmark_sound hw hs) => //; exact: (mfull48P hf hr).
Qed.

End Mark.
