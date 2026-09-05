(* =========================================================================  *)
(*  RowFinal48.v -- the same theorem over a map of forty eight bit cells.     *)
(* =========================================================================  *)

(* RowFinal.v assembles the theorem from three things: the run is sound, the  *)
(* map came out full once the witnesses are counted in, and the layout is a   *)
(* bijection.  Only the third mentions how wide a cell is, so only the last   *)
(* few lines are done again here.                                             *)
(*                                                                            *)
(* WHAT A WITNESS IS DOES NOT CHANGE AT ALL: a word, replayed on a forty      *)
(* eight entry table.  wok, wokP, wtr, wp and the rest are RowFinal's own and *)
(* are used as they stand.                                                    *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowRun RowFinal.
Require Import Row48 RowMap48 RowRun48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section Final48.

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place48 e8num e4bit par8).
Local Notation unplc := (unplace48 e8inv e4of par4).
Local Notation mok := (membok par8 par4).

Variable ptab : memb -> seq nat.
Hypothesis ptabP : forall x, tab_ok flast (ptab x).

Local Notation pos := (RowFinal.pos ptab).
Local Notation wthn := (RowRun.wthn pos).
Local Notation soundat := (RowRun48.soundat e8inv e4of par4 pos).

(* ---- the witnesses, at forty eight bits ---------------------------------- *)

Variable wl : seq (int * int * int * seq nat).

Definition wmapof48 (l : seq (int * int * int * seq nat)) : rmap :=
  foldr (fun t m => let: (pg, gr, bt, _) := t in mmark m pg gr bt)
        (mkempty48 tt) l.

Definition wmap48 : rmap := wmapof48 wl.

Definition wgood48 (l : seq (int * int * int * seq nat)) : bool :=
  all (fun t => let: (pg, gr, bt, w) := t in
                [&& inrange48 pg gr bt, (seq.size w <= 20)%N &
                    wok ptab (unplc pg gr bt) w])
      l.

Definition witsok48 : bool := wgood48 wl.

(* a bit the witness map has set has a witness behind it                      *)
Lemma wmap_wit48 (l : seq (int * int * int * seq nat)) pg gr bt :
  inrange48 pg gr bt -> wgood48 l -> mtest (wmapof48 l) pg gr bt ->
  exists w, (seq.size w <= 20)%N /\ wok ptab (unplc pg gr bt) w.
Proof.
move=> hr; elim: l => [|t l ih] /=; first by rewrite mkempty48P.
case: t => [[[p g] b] w] /andP[/and3P[hi hs hw] hl].
case/(mmark48P hi hr) => [[<- <- <-]|]; first by exists w.
by apply: ih.
Qed.

(* an empty map is sound at nought: it has no bit set                        *)
Lemma sound_mempty48 : soundat (mkempty48 tt) 0.
Proof. by move=> pg gr bt _; rewrite mkempty48P. Qed.

(* ---- the theorem --------------------------------------------------------- *)

Variable mfin : rmap.

Theorem row48_within_20 :
  soundat mfin 20 ->
  witsok48 ->
  mfull248 mfin wmap48 ->
  forall x, mok x -> wthn 20 x.
Proof.
move=> hs hw hf x hx.
case E: (plc x) => [[pg gr] bt].
have hr := place48_range he8 he4 hx E.
have hu := unplace48_place48 he8 he4 hx E.
rewrite -hu; case/orP: (mfull248P hf hr) => {}hb; first by apply: hs.
have [w [hsz hok]] := wmap_wit48 hr hw hb.
by apply: (wokP ptabP hok hsz).
Qed.

End Final48.
