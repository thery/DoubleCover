(* =========================================================================  *)
(*  RowFinal.v -- every member of the row is within twenty moves.             *)
(* =========================================================================  *)

(* The theorem is assembled from three things and nothing else:               *)
(*                                                                            *)
(*   the run is SOUND    -- every bit it set is a member within twenty        *)
(*   the map came out FULL, once the witnesses are counted in                 *)
(*   the layout is a BIJECTION -- one bit for each member, and no other       *)
(*                                                                            *)
(* THE WITNESSES ARE THE CHEAP HALF, and in Rocq far cheaper than they are    *)
(* for hcoset.  A member the run leaves clear is settled by exhibiting a word *)
(* and playing it: twenty moves on a forty eight entry table.  Whatever       *)
(* produced the word is never trusted and never mentioned -- it can be any    *)
(* solver at all.  So the search should be stopped as SHALLOW as the witness  *)
(* count allows, not run as deep as it will go: a search level is expensive   *)
(* and a witness is not.  That is the reverse of the lower bound, where a     *)
(* witness proves nothing and only exhaustiveness counts.                     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowRun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section Final.

Variable e8num e8inv e4bit e4of par8 par4 : arr.

(* the two table checks, which is all Row.v asks of the layout                *)
Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place e8num e4bit).
Local Notation unplc := (unplace e8inv e4of par8 par4).
Local Notation mok := (membok par8 par4).
Local Notation inrng := inrange.

(* ---- a word, and what it solves ------------------------------------------ *)

(* A word is a list of move numbers, three to a face, the faces U R F D L B,  *)
(* which is the numbering the whole development uses.  What a word multiplies *)
(* out to is a product of permutations, and it is the same product on tables, *)
(* where it is twenty compositions of a forty eight entry list and nothing    *)
(* more.  That is the whole of what a witness costs.                          *)

Definition flast := 47.

Definition mvt (m : nat) : seq nat := nth [::] mtabs m.

(* a word: every letter is one of the eighteen moves                          *)
Definition wf (w : seq nat) : bool := all (fun m => (m < 18)%N) w.

Definition wp (w : seq nat) : {perm facelet} := \prod_(m <- w) nth 1 moves m.

Definition wtr (w : seq nat) : seq nat :=
  foldr (fun m t => comp_tab (mvt m) t) (id_tab flast) w.

Lemma mvt_ok m : (m < 18)%N -> tab_ok flast (mvt m).
Proof.
move=> mL; rewrite /mvt; apply: (allP mtabs_ok); apply: mem_nth.
by rewrite size_mtabs.
Qed.

Lemma mvtE m : (m < 18)%N -> nth 1 moves m = pt flast (mvt m).
Proof.
by move=> mL; rewrite /mvt mtabsE (nth_map [::]) ?size_mtabs.
Qed.

Lemma wtr_ok w : wf w -> tab_ok flast (wtr w).
Proof.
elim: w => [_|m w ih /andP[mL wL]] /=; first by apply: tab_ok_id.
by apply: tab_ok_comp; [apply: mvt_ok | apply: ih].
Qed.

Lemma wp_wtr w : wf w -> wp w = pt flast (wtr w).
Proof.
elim: w => [_|m w ih]; first by rewrite /wp big_nil pt1.
rewrite /wf /= => /andP[mL wL].
by rewrite /wp big_cons -/(wp w) ih // mvtE // ptM ?mvt_ok ?wtr_ok.
Qed.

(* a word of n moves lands inside the ball of n, which is all the witnesses   *)
(* ever ask of the group                                                      *)
Lemma wp_ball w : wf w -> wp w \in ball Sset (seq.size w).
Proof.
elim/last_ind: w => [_|w m ih]; first by rewrite /wp big_nil; apply: mem1_ball.
rewrite -cats1 /wf all_cat => /andP[hw]; rewrite /= andbT => mL.
rewrite /wp big_cat /= big_seq1 -/(wp w) seq.size_cat /= addn1 /= inE.
by apply/orP; right; apply: mem_mulg; [apply: ih | apply: mv_Sset].
Qed.

Lemma ballW n1 n2 g : (n1 <= n2)%N ->
  g \in ball Sset n1 -> g \in ball Sset n2.
Proof.
elim: n2 => [|n2 ih]; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => h1 h2.
by apply: (subsetP (ball_mono Sset n2)); apply: ih.
Qed.

(* ---- a member, as a table ------------------------------------------------ *)

(* The position a member of the row stands for, as a forty eight entry table. *)
(* It is the only thing a witness ever looks at.                              *)
Variable ptab : memb -> seq nat.
Hypothesis ptabP : forall x, tab_ok flast (ptab x).

Definition pos (x : memb) : {perm facelet} := pt flast (ptab x).

Local Notation wthn := (wthn pos).
Local Notation soundat := (soundat e8inv e4of par8 par4 pos).

(* ---- the witnesses ------------------------------------------------------- *)

(* A witness is a place and a word.  wok is the check: play the word from the *)
(* position that place stands for and see the cube solved.  WHATEVER FOUND    *)
(* THE WORD IS NEVER TRUSTED and never mentioned, so it can be any solver at  *)
(* all -- ours on six axes, or Rokicki's.                                     *)
Definition wok (x : memb) (w : seq nat) : bool :=
  wf w && (comp_tab (ptab x) (wtr w) == id_tab flast).

Lemma wokP x w : wok x w -> (seq.size w <= 20)%N -> wthn 20 x.
Proof.
move=> /andP[hw /eqP hc] hs.
have h1 : pos x * wp w = 1.
  by rewrite /pos wp_wtr // ptM ?ptabP ?wtr_ok // hc pt1.
rewrite /RowRun.wthn.
have -> : pos x = (wp w)^-1.
  by rewrite -[LHS]mulg1 -(mulgV (wp w)) mulgA h1 mul1g.
rewrite mem_ballV ?Sset_inv //.
by apply: ballW hs _; apply: wp_ball.
Qed.

Variable wl : seq (int * int * int * seq nat).

(* the map of the places the witnesses cover                                  *)
Definition wmapof (l : seq (int * int * int * seq nat)) : rmap :=
  foldr (fun t m => let: (pg, gr, bt, _) := t in mmark m pg gr bt) mempty l.

Definition wmap : rmap := wmapof wl.

Definition wgood (l : seq (int * int * int * seq nat)) : bool :=
  all (fun t => let: (pg, gr, bt, w) := t in
                [&& inrng pg gr bt, (seq.size w <= 20)%N &
                    wok (unplc pg gr bt) w])
      l.

(* every witness is in range, at most twenty moves, and solves its member     *)
Definition witsok : bool := wgood wl.

(* a bit the witness map has set has a witness behind it                      *)
Lemma wmap_wit (l : seq (int * int * int * seq nat)) pg gr bt :
  inrng pg gr bt -> wgood l -> mtest (wmapof l) pg gr bt ->
  exists w, (seq.size w <= 20)%N /\ wok (unplc pg gr bt) w.
Proof.
move=> hr; elim: l => [|t l ih] /=; first by rewrite memptyP.
case: t => [[[p g] b] w] /andP[/and3P[hi hs hw] hl].
case/(mmarkP hi hr) => [[<- <- <-]|]; first by exists w.
by apply: ih.
Qed.

(* ---- the theorem --------------------------------------------------------- *)

(* Everything the computation has to say is in these two booleans: the map    *)
(* and the witnesses together leave no bit clear, and every witness word does *)
(* what it claims.                                                            *)

Variable mfin : rmap.

Theorem row_within_20 :
  soundat mfin 20 ->
  witsok ->
  mfull2 mfin wmap ->
  forall x, mok x -> wthn 20 x.
Proof.
move=> hs hw hf x hx.
case E: (plc x) => [[pg gr] bt].
have hr := place_range he8 he4 hx E.
have hu := unplace_place he8 he4 hx E.
(* the side goal must be handed the range, not left to done: done unfolds     *)
(* and evaluates, and what it would evaluate here is the map.                 *)
rewrite -hu; case/orP: (mfull2P hf hr) => {}hb; first by apply: hs.
have [w [hsz hok]] := wmap_wit hr hw hb.
by apply: wokP hok hsz.
Qed.

(* What the two hypotheses of row_within_20 rest on, so that the shape of the *)
(* whole thing is visible from this file alone:                               *)
(*                                                                            *)
(*   soundat mfin 20   is RowRun.run_sound, which is RowRun.prepass_sound and *)
(*                     RowRun.srch_sound -- one move of H, and an induction   *)
(*                     on a word.  Neither asks for completeness.             *)
(*                                                                            *)
(*   mfull (...)       is the computation: 812 851 200 words swept once.      *)
(*                                                                            *)
(*   witsok            is the witnesses, one replay of twenty moves each.     *)
(*                                                                            *)
(*   and the step from `no bit clear' to `every member' is Row.place_unplace  *)
(*                     with Row.place_inj: the layout is a bijection between  *)
(*                     the bits and the members.  THAT IS THE LONG POLE --    *)
(*                     the ranking, the pairing of outer permutations, and    *)
(*                     the parity that lets the last place be dropped.        *)

End Final.
