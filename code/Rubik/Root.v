(* =========================================================================  *)
(*  Root.v -- The first move of a maneuver, up to symmetry.                 *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Ball Rubik333 Sym Search.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* The two moves every face turn is carried to.                               *)
Definition Sroot : seq {perm facelet} := [:: Umove; Umove ^+ 2].

Lemma Sroot_moves : {subset Sroot <= moves}.
Proof.
by move=> m; rewrite /Sroot !inE => /orP[]/eqP->; rewrite eqxx ?orbT.
Qed.

(* ---- 1. Every face is a rotation away from U ----------------------------- *)

(* U is fixed, F and D and B come back along the R-L axis, R and L need one   *)
(* turn about the U-D axis first.                                             *)
Lemma face_root f : f \in faces -> exists2 u, u \in Symg & f ^ u = Umove.
Proof.
have SyS : Sy \in Symg by apply: mem_gen; rewrite !inE eqxx.
have SxS : Sx \in Symg by apply: mem_gen; rewrite !inE eqxx orbT.
have BJ : Bmove ^ Sx^-1 = Umove by rewrite -UmoveJx conjgK.
rewrite /faces !inE =>
  /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]]].
- by exists 1; rewrite ?group1 ?conjg1.
- by exists (Sy * Sx); [rewrite groupM|rewrite conjgM RmoveJy FmoveJx].
- by exists Sx; rewrite ?FmoveJx.
- by exists (Sx * Sx); [rewrite groupM|rewrite conjgM DmoveJx FmoveJx].
- by exists (Sy * Sx^-1); [rewrite groupM ?groupVr|rewrite conjgM LmoveJy BJ].
by exists (Sx^-1); rewrite ?groupVr.
Qed.

(* ---- 2. Every move is a symmetry away from a root move ------------------- *)

(* A face turn and its square go where the face goes; the inverse quarter     *)
(* turn needs the mirror as well, since (U^-1) ^ Sm = U.                      *)
Lemma move_root m : m \in moves -> exists2 u, u \in Symg & m ^ u \in Sroot.
Proof.
have SmS : Sm \in Symg by apply: mem_gen; rewrite !inE eqxx !orbT.
rewrite /moves => /flatten_mapP[f fF].
have [u uS fu] := face_root fF.
rewrite !inE => /or3P[]/eqP->.
- by exists u => //; rewrite fu /Sroot !inE eqxx.
- by exists u => //; rewrite conjXg fu /Sroot !inE eqxx orbT.
exists (u * Sm); first by rewrite groupM.
by rewrite conjgM conjVg fu conjVg UmoveJm invgK /Sroot !inE eqxx.
Qed.

(* ---- 3. The first move may be taken in Sroot ----------------------------- *)

Section Fixed.

(* g is a position fixed by every symmetry -- the superflip is one.           *)
Variable g : {perm facelet}.
Hypothesis gJ : forall u, u \in Symg -> g ^ u = g.

Lemma ball_root d :
  g \in ball Sset d.+1 ->
  g = 1 \/ exists2 m, m \in Sroot & g * m \in ball Sset d.
Proof.
move=> gB.
case: (ball_cons Sset_inv gB) => [->|[m mM gmB]]; first by left.
right; have [u uS mu] := move_root mM.
exists (m ^ u) => //.
by rewrite -(gJ uS) -conjMg (mem_ballJ _ _ (Symg_stab uS)).
Qed.

(* The form the generated files use: one lemma per pair of first moves, with  *)
(* the first taken from Sroot -- two instead of eighteen.                     *)
Lemma ball_root2 d :
  g != 1 ->
  (forall m, m \in moves -> g * m != 1) ->
  (forall m1 m2, m1 \in Sroot -> m2 \in moves ->
     g * m1 * m2 \notin ball Sset d) ->
  g \notin ball Sset d.+2.
Proof.
move=> g1 gm1 gmm; apply/negP => /ball_root[gE|[m1 m1R gm1B]].
  by case/eqP: g1.
case: (ball_cons Sset_inv gm1B) => [gm1E|[m2 m2M gmmB]].
  by case/eqP: (gm1 _ (Sroot_moves m1R)).
by case/negP: (gmm _ _ m1R m2M).
Qed.

End Fixed.
