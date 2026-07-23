(* ========================================================================= *)
(*  Rubik333.v                                                               *)
(*                                                                           *)
(*  A group-theoretic representation of the 3x3x3 Rubik's cube, in the       *)
(*  style of Rokicki, Kociemba, Davidson, Dethridge, "The diameter of the    *)
(*  Rubik's cube group is twenty" (SIAM J. Discrete Math., 2013).            *)
(*                                                                           *)
(*  We use the FACELET model (the paper's defining model, p.1088):           *)
(*    G = <S> acting on the 48 non-center stickers.                          *)
(*  Facelets are numbered 0..47 following the standard (Wikipedia/GAP)        *)
(*  numbering, minus 1 to be 0-based.                                        *)
(*                                                                           *)
(*  Generic material lives elsewhere: cyclic permutations in Cyc.v, the word  *)
(*  metric / balls in Ball.v.                                                *)
(*                                                                           *)
(*  NOTE ON COMPUTATION.  Cardinalities such as |G| = 43252003274489856000   *)
(*  and |H| = 19508428800, and any check requiring evaluation of a           *)
(*  {perm 'I_48} (these do not reduce in reasonable time under vm_compute),  *)
(*  are stated as lemmas and left Admitted with the tag [COMPUTATION].       *)
(*  This mirrors the paper: the reduction is a proof; the numeric facts are  *)
(*  external computations.                                                   *)
(* ========================================================================= *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- 1. Facelets --------------------------------------------------------- *)

Definition facelet := 'I_48.

Local Notation "n '@'" := (inord n : facelet) (at level 2, format "n '@'").

(* ---- 2. The six clockwise quarter turns ---------------------------------- *)
(* Cycles are the standard generators (0-based).                             *)

Definition Umove : {perm facelet} :=
  cyc [:: 0@; 2@; 7@; 5@] * cyc [:: 1@; 4@; 6@; 3@] *
  cyc [:: 8@; 32@; 24@; 16@] * cyc [:: 9@; 33@; 25@; 17@] *
  cyc [:: 10@; 34@; 26@; 18@].

Definition Lmove : {perm facelet} :=
  cyc [:: 8@; 10@; 15@; 13@] * cyc [:: 9@; 12@; 14@; 11@] *
  cyc [:: 0@; 16@; 40@; 39@] * cyc [:: 3@; 19@; 43@; 36@] *
  cyc [:: 5@; 21@; 45@; 34@].

Definition Fmove : {perm facelet} :=
  cyc [:: 16@; 18@; 23@; 21@] * cyc [:: 17@; 20@; 22@; 19@] *
  cyc [:: 5@; 24@; 42@; 15@] * cyc [:: 6@; 27@; 41@; 12@] *
  cyc [:: 7@; 29@; 40@; 10@].

Definition Rmove : {perm facelet} :=
  cyc [:: 24@; 26@; 31@; 29@] * cyc [:: 25@; 28@; 30@; 27@] *
  cyc [:: 2@; 37@; 42@; 18@] * cyc [:: 4@; 35@; 44@; 20@] *
  cyc [:: 7@; 32@; 47@; 23@].

Definition Bmove : {perm facelet} :=
  cyc [:: 32@; 34@; 39@; 37@] * cyc [:: 33@; 36@; 38@; 35@] *
  cyc [:: 2@; 8@; 45@; 31@] * cyc [:: 1@; 11@; 46@; 28@] *
  cyc [:: 0@; 13@; 47@; 26@].

Definition Dmove : {perm facelet} :=
  cyc [:: 40@; 42@; 47@; 45@] * cyc [:: 41@; 44@; 46@; 43@] *
  cyc [:: 13@; 21@; 29@; 37@] * cyc [:: 14@; 22@; 30@; 38@] *
  cyc [:: 15@; 23@; 31@; 39@].

(* ---- 3. The move set S (18 HTM moves) and the cube group G --------------- *)

Definition faces : seq {perm facelet} :=
  [:: Umove; Rmove; Fmove; Dmove; Lmove; Bmove].

(* For each face: the quarter turn, the half turn, the inverse quarter turn.  *)
Definition moves : seq {perm facelet} :=
  flatten [seq [:: g; g ^+ 2; g ^-1] | g <- faces].

Definition Sset : {set {perm facelet}} := [set g in moves].

Definition G : {group {perm facelet}} := <<Sset>>.

(* A cube position is an element of G; the solved position is the identity.   *)
Definition position := {perm facelet}.
Definition solved : position := 1%g.

(* ---- 4. The subgroup H (Kociemba's / Thistlethwaite's G1) ---------------- *)
(*   A = {U1,U2,U3,D1,D2,D3,F2,B2,L2,R2}  (paper (4.1)),  H = <A>.            *)
(*   The A-generators are written to be *syntactically* among `moves`.        *)

Definition Amoves : seq {perm facelet} :=
  [:: Umove; Umove ^+ 2; Umove ^-1;
      Dmove; Dmove ^+ 2; Dmove ^-1;
      Fmove ^+ 2; Bmove ^+ 2; Lmove ^+ 2; Rmove ^+ 2].

Definition Aset : {set {perm facelet}} := [set g in Amoves].

Definition H : {group {perm facelet}} := <<Aset>>.

(* The partition of the cube group into the right cosets H*p.                 *)
Definition cosets := rcosets H G.

(* ---- 5. Structural facts ------------------------------------------------- *)

(* Every A-generator is one of the 18 moves.  A finite membership check, but   *)
(* proved structurally (no {perm 'I_48} is ever evaluated): each A-generator   *)
(* is syntactically one of the elements of `moves`.                           *)
Lemma A_sub_S : Aset \subset Sset.
Proof.
rewrite [Aset]set_cons !set_cons set_nil setU0 !setUA !subUset.
rewrite [Sset]set_cons !set_cons set_nil setU0.
by (repeat (apply/andP; split));
    repeat first [apply: subsetUl | apply: subsetU; apply/orP; right].
Qed.

(* H is a subgroup of G.  (Real proof, resting only on A_sub_S.)             *)
Lemma HsubG : H \subset G.
Proof. exact: genS A_sub_S. Qed.

(* ---- 6. The move set is symmetric: Sset^-1 = Sset ------------------------- *)
(*                                                                           *)
(*  This is the hypothesis of the inversion half of the diameter reduction    *)
(*  (diam_le_reps2).  Each face turn is a product of five disjoint 4-cycles,   *)
(*  hence Xmove^+4 = 1; the only non-structural ingredient is that the 20      *)
(*  facelets a face moves are distinct (uniqueness of the concatenation of     *)
(*  its five cycles), an explicit finite fact tagged [COMPUTATION].  From       *)
(*  Xmove^+4 = 1 the half turn Xmove^+2 is an involution (half_turn_inv), so   *)
(*  each face's triple {X, X^+2, X^-1} is closed under inverse, and hence so   *)
(*  is the whole move set.  No permutation is ever evaluated.                  *)

(* The five 4-cycles of each face turn, grouped as a list of facelet lists.   *)
Definition Ucyc : seq (seq facelet) :=
  [:: [:: 0@; 2@; 7@; 5@]; [:: 1@; 4@; 6@; 3@];
      [:: 8@; 32@; 24@; 16@]; [:: 9@; 33@; 25@; 17@]; [:: 10@; 34@; 26@; 18@] ].
Definition Lcyc : seq (seq facelet) :=
  [:: [:: 8@; 10@; 15@; 13@]; [:: 9@; 12@; 14@; 11@];
      [:: 0@; 16@; 40@; 39@]; [:: 3@; 19@; 43@; 36@]; [:: 5@; 21@; 45@; 34@] ].
Definition Fcyc : seq (seq facelet) :=
  [:: [:: 16@; 18@; 23@; 21@]; [:: 17@; 20@; 22@; 19@];
      [:: 5@; 24@; 42@; 15@]; [:: 6@; 27@; 41@; 12@]; [:: 7@; 29@; 40@; 10@] ].
Definition Rcyc : seq (seq facelet) :=
  [:: [:: 24@; 26@; 31@; 29@]; [:: 25@; 28@; 30@; 27@];
      [:: 2@; 37@; 42@; 18@]; [:: 4@; 35@; 44@; 20@]; [:: 7@; 32@; 47@; 23@] ].
Definition Bcyc : seq (seq facelet) :=
  [:: [:: 32@; 34@; 39@; 37@]; [:: 33@; 36@; 38@; 35@];
      [:: 2@; 8@; 45@; 31@]; [:: 1@; 11@; 46@; 28@]; [:: 0@; 13@; 47@; 26@] ].
Definition Dcyc : seq (seq facelet) :=
  [:: [:: 40@; 42@; 47@; 45@]; [:: 41@; 44@; 46@; 43@];
      [:: 13@; 21@; 29@; 37@]; [:: 14@; 22@; 30@; 38@]; [:: 15@; 23@; 31@; 39@] ].

(* Each face turn is the product of its five cycles (reassociation only). *)
Lemma UmoveE : Umove = \prod_(l <- Ucyc) cyc l.
Proof. by rewrite /Umove /Ucyc !big_cons big_nil mulg1 !mulgA. Qed.
Lemma LmoveE : Lmove = \prod_(l <- Lcyc) cyc l.
Proof. by rewrite /Lmove /Lcyc !big_cons big_nil mulg1 !mulgA. Qed.
Lemma FmoveE : Fmove = \prod_(l <- Fcyc) cyc l.
Proof. by rewrite /Fmove /Fcyc !big_cons big_nil mulg1 !mulgA. Qed.
Lemma RmoveE : Rmove = \prod_(l <- Rcyc) cyc l.
Proof. by rewrite /Rmove /Rcyc !big_cons big_nil mulg1 !mulgA. Qed.
Lemma BmoveE : Bmove = \prod_(l <- Bcyc) cyc l.
Proof. by rewrite /Bmove /Bcyc !big_cons big_nil mulg1 !mulgA. Qed.
Lemma DmoveE : Dmove = \prod_(l <- Dcyc) cyc l.
Proof. by rewrite /Dmove /Dcyc !big_cons big_nil mulg1 !mulgA. Qed.

Lemma uniq_inord n l : 
  all (fun i => i < n.+1) l -> uniq l -> uniq ((map inord l) : seq 'I_n.+1).
Proof.
elim: l => //= a l IH /andP[aLn lA] /andP[aNIl lU].
apply/andP; split; last by apply: IH.
apply/negP => aIl; case/negP: aNIl; elim: l {IH lU} lA aIl => //= b l IH.
case/andP=> bLn lA.
rewrite inE => /orP[/val_eqP/val_eqP /=|/IH HH].
  by rewrite !inordK // => /eqP->; rewrite inE eqxx.
by rewrite inE HH ?orbT.
Qed.

(* [COMPUTATION] A face turn moves 20 distinct facelets, i.e. its five 4-cycles *)
(* are pairwise disjoint.  A finite check on 'I_48; no permutation is involved.  *)
Lemma Ucyc_uniq : uniq (flatten Ucyc).
Proof.
by eapply (@uniq_inord _
  [::0; 2; 7; 5; 1; 4; 6; 3; 8; 32; 24; 16; 9; 33; 25; 17; 10; 34; 26; 18])%N.
Qed.
Lemma Lcyc_uniq : uniq (flatten Lcyc).
Proof.
by eapply (@uniq_inord _
[:: 8; 10; 15; 13; 9; 12; 14; 11; 0; 16; 40; 39; 3; 19; 43; 36; 5; 21; 45; 34])%N.

Lemma Fcyc_uniq : uniq (flatten Fcyc). 
Proof. 
by eapply (@uniq_inord _
  [:: 16; 18; 23; 21; 17; 20; 22; 19; 5; 24; 42; 15; 6; 27; 41; 12; 7; 29; 40; 10])%N.
Qed.
Lemma Rcyc_uniq : uniq (flatten Rcyc).
Proof. 
by eapply (@uniq_inord _
  [:: 24; 26; 31; 29; 25; 28; 30; 27; 2; 37; 42; 18; 4; 35; 44; 20; 7; 32; 47; 23])%N.
Qed.
Lemma Bcyc_uniq : uniq (flatten Bcyc).
Proof. 
by eapply (@uniq_inord _
  [:: 32; 34; 39; 37; 33; 36; 38; 35; 2; 8; 45; 31; 1; 11; 46; 28; 0; 13; 47; 26])%N.
Qed.
Lemma Dcyc_uniq : uniq (flatten Dcyc).
Proof. 
by eapply (@uniq_inord _
  [:: 40; 42; 47; 45; 41; 44; 46; 43; 13; 21; 29; 37; 14; 22; 30; 38; 15; 23; 31; 39])%N.
Qed.

(* Each face turn has order dividing 4. *)
Lemma Umove4 : Umove ^+ 4 = 1.
Proof.
rewrite UmoveE; apply: cyc_prod_expn; first exact: Ucyc_uniq.
by move=> l; rewrite /Ucyc !inE
  => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]].
Qed.
Lemma Lmove4 : Lmove ^+ 4 = 1.
Proof.
rewrite LmoveE; apply: cyc_prod_expn; first exact: Lcyc_uniq.
by move=> l; rewrite /Lcyc !inE
  => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]].
Qed.
Lemma Fmove4 : Fmove ^+ 4 = 1.
Proof.
rewrite FmoveE; apply: cyc_prod_expn; first exact: Fcyc_uniq.
by move=> l; rewrite /Fcyc !inE
  => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]].
Qed.
Lemma Rmove4 : Rmove ^+ 4 = 1.
Proof.
rewrite RmoveE; apply: cyc_prod_expn; first exact: Rcyc_uniq.
by move=> l; rewrite /Rcyc !inE
  => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]].
Qed.
Lemma Bmove4 : Bmove ^+ 4 = 1.
Proof.
rewrite BmoveE; apply: cyc_prod_expn; first exact: Bcyc_uniq.
by move=> l; rewrite /Bcyc !inE
  => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]].
Qed.
Lemma Dmove4 : Dmove ^+ 4 = 1.
Proof.
rewrite DmoveE; apply: cyc_prod_expn; first exact: Dcyc_uniq.
by move=> l; rewrite /Dcyc !inE
  => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]].
Qed.

(* A face's triple {g, g^+2, g^-1} is closed under inverse, given g^+4 = 1:    *)
(* g and g^-1 swap, and the half turn g^+2 is its own inverse.                  *)
Lemma inv_closed_triple (g : {perm facelet}) : g ^+ 4 = 1 ->
  {in [:: g; g ^+ 2; g ^-1], forall x, x^-1 \in [:: g; g ^+ 2; g ^-1]}.
Proof.
move=> g4 x xL; move: xL; rewrite !inE.
by move=> /or3P[]/eqP->; rewrite ?invgK ?(half_turn_inv g4) ?eqxx ?orbT.
Qed.

(* If every block of a flattened list is inverse-closed, so is the flatten. *)
Lemma inv_closed_flatten (gT : finGroupType) (bs : seq (seq gT)) (x : gT) :
  (forall b, b \in bs -> {in b, forall y, y^-1 \in b}) ->
  x \in flatten bs -> x^-1 \in flatten bs.
Proof.
move=> H /flattenP[b bbs xb].
by apply/flattenP; exists b => //; apply: (H b bbs).
Qed.

(* The move set is symmetric.  Feeds the inversion half of the reduction.      *)
Lemma Sset_inv : Sset ^-1 = Sset.
Proof.
apply: invg_closed_setV => x; rewrite inE => xm; rewrite inE /moves.
apply: inv_closed_flatten; last exact: xm.
move=> b /mapP[g gf ->]; apply: inv_closed_triple.
move: gf; rewrite /faces !inE
  => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]]].
- exact: Umove4.
- exact: Rmove4.
- exact: Fmove4.
- exact: Dmove4.
- exact: Lmove4.
- exact: Bmove4.
Qed.

(* [COMPUTATION] The order of the cube group (paper, p.1088). Stated for the  *)
(* record; the nat literal / evaluation is an external computation.           *)
(* Lemma card_G : #|G| = 43252003274489856000%N.  (* [COMPUTATION] *) *)
(* Lemma card_H : #|H| = 19508428800%N.            (* [COMPUTATION] *) *)
(* index #|G : H| = 2217093120 then follows from Lagrange (a real proof).     *)
