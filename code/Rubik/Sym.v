(* =========================================================================  *)
(*  Sym.v                                                                     *)
(*                                                                            *)
(*  The spatial symmetries of the cube, acting on facelets, and the fact      *)
(*  that they stabilise the move set:  Sset :^ u = Sset.                      *)
(*                                                                            *)
(*  This is the hypothesis of the conjugation half of the diameter reduction  *)
(*  (Ball.v, diam_le_reps2); together with Sset^-1 = Sset (Rubik333.v) it     *)
(*  gives the paper's factor of 96 = 48 x 2.                                  *)
(*                                                                            *)
(*  A symmetry is NOT a cube move: it relabels the whole cube in space, so    *)
(*  it has to be given explicitly as a facelet permutation.  Three            *)
(*  generators suffice for the full symmetry group of order 48:               *)
(*     Sy   quarter turn of the whole cube about the U-D axis     (order 4)   *)
(*     Sx   quarter turn of the whole cube about the R-L axis     (order 4)   *)
(*     Sm   mirror image in the plane midway between L and R      (order 2)   *)
(*  Sy and Sx generate the 24 rotations; Sm adds the reflections.  Since      *)
(*  stabilising Sset is preserved by products, checking the generators is     *)
(*  enough -- we never enumerate the 48 symmetries.                           *)
(*                                                                            *)
(*  STRUCTURE.  Everything below is a real proof except fourteen of the       *)
(*  eighteen conjugation facts  Xmove ^ s = Ymove  (six per generator),       *)
(*  which are genuine finite computations on {perm 'I_48}; following the      *)
(*  convention of Rubik333.v those are Admitted and tagged [COMPUTATION].     *)
(*  The other four -- a rotation fixes the two turns of its own axis -- are   *)
(*  proved, by commutation.  The fourteen are all of the same shape, so one   *)
(*  technique discharges them all.                                            *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball Rubik333.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Local Notation "n '@'" := (inord n : facelet) (at level 2, format "n '@'").

(* ---- 1. The three generating symmetries ---------------------------------- *)
(*                                                                            *)
(*  A whole-cube quarter turn is the three parallel layers turning together,  *)
(*  which is the cubist's  y = U M D'  and  x = R M L' : the near face turns  *)
(*  on itself, the middle slice follows it, and the far layer turns the same  *)
(*  way in space, hence the other way as seen on its own face -- whence the   *)
(*  inverse.  Writing the rotations this way (rather than as their twelve     *)
(*  4-cycles) is not just shorter: it makes them visibly commute with the     *)
(*  turns of their own axis, which settles four of the conjugation facts of   *)
(*  section 3 outright.  Only the middle slices have to be spelt out.         *)

(*  The middle slice about the U-D axis, turning with U.                      *)
Definition Midycyc : seq (seq facelet) :=
  [:: [:: 11@; 35@; 27@; 19@]; [:: 12@; 36@; 28@; 20@] ].

Definition Midy : {perm facelet} := \prod_(l <- Midycyc) cyc l.

(*  Sy : quarter turn of the whole cube about the U-D axis, in the sense of U.*)
Definition Sy : {perm facelet} := Umove * Midy * Dmove ^-1.

(*  The middle slice about the R-L axis, turning with R.                      *)
Definition Midxcyc : seq (seq facelet) :=
  [:: [:: 1@; 38@; 41@; 17@]; [:: 6@; 33@; 46@; 22@] ].

Definition Midx : {perm facelet} := \prod_(l <- Midxcyc) cyc l.

(*  Sx : quarter turn of the whole cube about the R-L axis, in the sense of R.*)
Definition Sx : {perm facelet} := Rmove * Midx * Lmove ^-1.

(*  Sm is the mirror image in the plane parallel to the L and R faces: it     *)
(*  exchanges L and R and reverses each of the other four faces left-right.   *)
(*  Being orientation reversing, it turns a clockwise quarter turn into a     *)
(*  counterclockwise one -- which is why the move set has to contain the      *)
(*  inverse quarter turns for this to be a symmetry of it.                    *)

Definition Smcyc : seq (seq facelet) :=
  [:: [:: 0@; 2@];
      [:: 3@; 4@];
      [:: 5@; 7@];
      [:: 8@; 26@];
      [:: 9@; 25@];
      [:: 10@; 24@];
      [:: 11@; 28@];
      [:: 12@; 27@];
      [:: 13@; 31@];
      [:: 14@; 30@];
      [:: 15@; 29@];
      [:: 16@; 18@];
      [:: 19@; 20@];
      [:: 21@; 23@];
      [:: 32@; 34@];
      [:: 35@; 36@];
      [:: 37@; 39@];
      [:: 40@; 42@];
      [:: 43@; 44@];
      [:: 45@; 47@] ].

Definition Sm : {perm facelet} := \prod_(l <- Smcyc) cyc l.

(* ---- 2. The three layers of an axis are disjoint --------------------------*)
(*                                                                            *)
(*  The near face, the middle slice and the far face of one axis partition    *)
(*  the 48 facelets.  As in Rubik333.v this is uniqueness of the              *)
(*  concatenation, proved structurally through uniq_inord -- no permutation   *)
(*  is evaluated.  Everything about the rotations is read off it: the three   *)
(*  layers commute, so the rotation has order 4 and fixes the turns of its    *)
(*  own axis.                                                                 *)

Lemma UMDcyc_uniq : uniq (flatten (Ucyc ++ Midycyc ++ Dcyc)).
Proof.
by eapply (@uniq_inord _
  [:: 0; 2; 7; 5; 1; 4; 6; 3; 8; 32; 24; 16; 9; 33; 25; 17; 10; 34; 26; 18;
      11; 35; 27; 19; 12; 36; 28; 20;
      40; 42; 47; 45; 41; 44; 46; 43; 13; 21; 29; 37; 14; 22; 30; 38;
      15; 23; 31; 39])%N.
Qed.

Lemma RMLcyc_uniq : uniq (flatten (Rcyc ++ Midxcyc ++ Lcyc)).
Proof.
by eapply (@uniq_inord _
  [:: 24; 26; 31; 29; 25; 28; 30; 27; 2; 37; 42; 18; 4; 35; 44; 20;
      7; 32; 47; 23; 1; 38; 41; 17; 6; 33; 46; 22;
      8; 10; 15; 13; 9; 12; 14; 11; 0; 16; 40; 39; 3; 19; 43; 36;
      5; 21; 45; 34])%N.
Qed.

Lemma Midycyc_uniq : uniq (flatten Midycyc).
Proof. by eapply (@uniq_inord _ [:: 11; 35; 27; 19; 12; 36; 28; 20])%N. Qed.

Lemma Midxcyc_uniq : uniq (flatten Midxcyc).
Proof. by eapply (@uniq_inord _ [:: 1; 38; 41; 17; 6; 33; 46; 22])%N. Qed.

Lemma Smcyc_uniq : uniq (flatten Smcyc).
Proof.
by eapply (@uniq_inord _
  [:: 0; 2; 3; 4; 5; 7; 8; 26; 9; 25; 10; 24; 11; 28; 12; 27;
      13; 31; 14; 30; 15; 29; 16; 18; 19; 20; 21; 23; 32; 34; 35; 36;
      37; 39; 40; 42; 43; 44; 45; 47])%N.
Qed.

(* The three layers of an axis commute, being supported on disjoint points.   *)

Lemma commute_UMy : commute Umove Midy.
Proof.
rewrite UmoveE /Midy; apply: commute_cyc_cat.
by have [] := cat3_uniq_disj UMDcyc_uniq.
Qed.

Lemma commute_UD : commute Umove Dmove.
Proof.
rewrite UmoveE DmoveE; apply: commute_cyc_cat.
by have [] := cat3_uniq_disj UMDcyc_uniq.
Qed.

Lemma commute_MyD : commute Midy Dmove.
Proof.
rewrite /Midy DmoveE; apply: commute_cyc_cat.
by have [] := cat3_uniq_disj UMDcyc_uniq.
Qed.

Lemma commute_RMx : commute Rmove Midx.
Proof.
rewrite RmoveE /Midx; apply: commute_cyc_cat.
by have [] := cat3_uniq_disj RMLcyc_uniq.
Qed.

Lemma commute_RL : commute Rmove Lmove.
Proof.
rewrite RmoveE LmoveE; apply: commute_cyc_cat.
by have [] := cat3_uniq_disj RMLcyc_uniq.
Qed.

Lemma commute_MxL : commute Midx Lmove.
Proof.
rewrite /Midx LmoveE; apply: commute_cyc_cat.
by have [] := cat3_uniq_disj RMLcyc_uniq.
Qed.

(* The middle slices are two disjoint 4-cycles, so they too have order 4;     *)
(* a rotation, a product of three commuting such, therefore has order 4.      *)

Lemma Midy4 : Midy ^+ 4 = 1.
Proof. by apply: cyc_prod_expn; [exact: Midycyc_uniq | apply: all_sizeP]. Qed.

Lemma Midx4 : Midx ^+ 4 = 1.
Proof. by apply: cyc_prod_expn; [exact: Midxcyc_uniq | apply: all_sizeP]. Qed.

Lemma Sy4 : Sy ^+ 4 = 1.
Proof.
rewrite /Sy; apply: expgMn1; last by rewrite expVgn Dmove4 invg1.
  by apply/esym/commuteM; apply/esym;
     [exact: commuteV commute_UD | exact: commuteV commute_MyD].
by apply: expgMn1; [exact: commute_UMy | exact: Umove4 | exact: Midy4].
Qed.

Lemma Sx4 : Sx ^+ 4 = 1.
Proof.
rewrite /Sx; apply: expgMn1; last by rewrite expVgn Lmove4 invg1.
  by apply/esym/commuteM; apply/esym;
     [exact: commuteV commute_RL | exact: commuteV commute_MxL].
by apply: expgMn1; [exact: commute_RMx | exact: Rmove4 | exact: Midx4].
Qed.

Lemma Sm2 : Sm ^+ 2 = 1.
Proof. by apply: cyc_prod_expn; [exact: Smcyc_uniq | apply: all_sizeP]. Qed.

(* ---- 3. How the symmetries permute the face turns ------------------------ *)
(*                                                                            *)
(*  The eighteen facts below are the whole computational content of this      *)
(*  file -- but four of them are not computational at all: a rotation fixes   *)
(*  the two turns of its own axis, and that is a commutation, proved.  The    *)
(*  fourteen [COMPUTATION] leaves are the ones that move a face elsewhere.    *)
(*  Each says that conjugating a face turn by a                               *)
(*  symmetry is again a face turn -- the face it names is the one the         *)
(*  symmetry moves that face to, and for the mirror the sense is reversed.    *)
(*                                                                            *)
(*  They are equalities of elements of {perm 'I_48}, i.e. finite checks on    *)
(*  48 points, but neither vm_compute nor native_compute can do them here:    *)
(*  a cyc is a product of tperm, and a single 48-image evaluation of such a   *)
(*  product does not reduce in reasonable time (see the note in Rubik333.v).  *)
(*  Two routes to discharging them, neither taken yet:                        *)
(*   - symbolic: cycJ (Cyc.v) turns Xmove ^ s into a product of cycles with   *)
(*     the point lists mapped through s; evaluating s on a point is then      *)
(*     rewriting with cyc_succ / cyc_notin, and what is left is matching the  *)
(*     two products up to rotation of each cycle (cyc_nth) and reordering of  *)
(*     the factors (cyc_comm);                                                *)
(*   - tabular: represent a facelet permutation by its 48-entry image table,  *)
(*     with generic lemmas for the product and the inverse; then each fact    *)
(*     below is one equality of two literal lists of nat, which does compute. *)
(*  Since all fourteen have the same shape, one technique settles them all.   *)

(* -- Sy : U and D fixed, L -> B -> R -> F -> L.                              *)

(* The two turns of the ROTATION'S OWN AXIS are real proofs, no computation:  *)
(* U, the middle slice and D commute pairwise, hence each of U and D          *)
(* commutes with their product Sy, and conjugation by something one commutes  *)
(* with does nothing.                                                         *)
Lemma UmoveJy : Umove ^ Sy = Umove.
Proof.
apply: conjg_commute; rewrite /Sy.
apply: commuteM; last by apply: commuteV; exact: commute_UD.
by apply: commuteM; last exact: commute_UMy.
Qed.

Lemma DmoveJy : Dmove ^ Sy = Dmove.
Proof.
apply: conjg_commute; rewrite /Sy.
apply: commuteM; last by apply: commuteV.
by apply: commuteM; [exact/esym/commute_UD | exact/esym/commute_MyD].
Qed.

(* The other four move a face somewhere else, so no commutation argument      *)
(* reaches them.                                                              *)
Lemma RmoveJy : Rmove ^ Sy = Fmove.  Admitted.  (* [COMPUTATION]              *)
Lemma FmoveJy : Fmove ^ Sy = Lmove.  Admitted.  (* [COMPUTATION]              *)
Lemma LmoveJy : Lmove ^ Sy = Bmove.  Admitted.  (* [COMPUTATION]              *)
Lemma BmoveJy : Bmove ^ Sy = Rmove.  Admitted.  (* [COMPUTATION]              *)

(* -- Sx : R and L fixed, F -> U -> B -> D -> F.                              *)

Lemma RmoveJx : Rmove ^ Sx = Rmove.
Proof.
apply: conjg_commute; rewrite /Sx.
apply: commuteM; last by apply: commuteV; exact: commute_RL.
by apply: commuteM; last exact: commute_RMx.
Qed.

Lemma LmoveJx : Lmove ^ Sx = Lmove.
Proof.
apply: conjg_commute; rewrite /Sx.
apply: commuteM; last by apply: commuteV.
by apply: commuteM; [exact/esym/commute_RL | exact/esym/commute_MxL].
Qed.

Lemma UmoveJx : Umove ^ Sx = Bmove.  Admitted.  (* [COMPUTATION]              *)
Lemma FmoveJx : Fmove ^ Sx = Umove.  Admitted.  (* [COMPUTATION]              *)
Lemma DmoveJx : Dmove ^ Sx = Fmove.  Admitted.  (* [COMPUTATION]              *)
Lemma BmoveJx : Bmove ^ Sx = Dmove.  Admitted.  (* [COMPUTATION]              *)

(* -- Sm : L and R exchanged, every face turn reversed.                       *)
Lemma UmoveJm : Umove ^ Sm = Umove ^-1.  Admitted.  (* [COMPUTATION]          *)
Lemma RmoveJm : Rmove ^ Sm = Lmove ^-1.  Admitted.  (* [COMPUTATION]          *)
Lemma FmoveJm : Fmove ^ Sm = Fmove ^-1.  Admitted.  (* [COMPUTATION]          *)
Lemma DmoveJm : Dmove ^ Sm = Dmove ^-1.  Admitted.  (* [COMPUTATION]          *)
Lemma LmoveJm : Lmove ^ Sm = Rmove ^-1.  Admitted.  (* [COMPUTATION]          *)
Lemma BmoveJm : Bmove ^ Sm = Bmove ^-1.  Admitted.  (* [COMPUTATION]          *)

(* ---- 4. A symmetry of the faces is a symmetry of the move set ------------ *)
(*                                                                            *)
(*  The move set is closed under a conjugation that permutes the six face     *)
(*  turns, up to inverses.  The three moves a face contributes go to the      *)
(*  three moves of the image face: the quarter turns swap when the sense is   *)
(*  reversed, and the half turn is fixed either way, being an involution.     *)
(*  Equality then comes for free from the inclusion, conjugation preserving   *)
(*  cardinality.                                                              *)

Lemma Sset_conj u :
  (forall g, g \in faces ->
     exists2 h, h \in faces & (g ^ u == h) || (g ^ u == h ^-1)) ->
  Sset :^ u = Sset.
Proof.
move=> Hu; apply/eqP; rewrite eqEcard cardJg leqnn andbT.
apply/subsetP => x; rewrite /Sset conj_set_seq inE.
case/mapP=> g gm ->{x}; move: gm; rewrite /moves.
case/flattenP=> b /mapP[f ff ->{b}].
case: (Hu f ff) => h hf /orP[] /eqP fE; rewrite mem_seq3 => /or3P[] /eqP->.
- by rewrite fE; apply: face_mem_Sset.
- by rewrite conjXg fE; apply: face2_mem_Sset.
- by rewrite conjVg fE; apply: faceV_mem_Sset.
- by rewrite fE; apply: faceV_mem_Sset.
- rewrite conjXg fE expVgn (half_turn_inv (face_order4 hf)).
  by apply: face2_mem_Sset.
by rewrite conjVg fE invgK; apply: face_mem_Sset.
Qed.

(* The six faces, split on which one g is.  The membership is decomposed in   *)
(* the hypothesis only: unfolding `faces` in the goal as well would also      *)
(* expose the `h \in faces` under the existential.                            *)
Ltac face_case gf :=
  rewrite /faces !inE in gf;
  case/orP: gf =>
    [/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]]].

(* Witness h, then: h is a face, and the conjugate is h (or h^-1).            *)
Ltac face_wit h J :=
  by exists h; [rewrite /faces !inE eqxx ?orTb ?orbT | rewrite J ?eqxx ?orbT].

Lemma Sset_Jy : Sset :^ Sy = Sset.
Proof.
apply: Sset_conj => g gf; face_case gf.
- face_wit Umove UmoveJy.
- face_wit Fmove RmoveJy.
- face_wit Lmove FmoveJy.
- face_wit Dmove DmoveJy.
- face_wit Bmove LmoveJy.
face_wit Rmove BmoveJy.
Qed.

Lemma Sset_Jx : Sset :^ Sx = Sset.
Proof.
apply: Sset_conj => g gf; face_case gf.
- face_wit Bmove UmoveJx.
- face_wit Rmove RmoveJx.
- face_wit Umove FmoveJx.
- face_wit Fmove DmoveJx.
- face_wit Lmove LmoveJx.
face_wit Dmove BmoveJx.
Qed.

Lemma Sset_Jm : Sset :^ Sm = Sset.
Proof.
apply: Sset_conj => g gf; face_case gf.
- face_wit Umove UmoveJm.
- face_wit Lmove RmoveJm.
- face_wit Fmove FmoveJm.
- face_wit Dmove DmoveJm.
- face_wit Rmove LmoveJm.
face_wit Bmove BmoveJm.
Qed.

(* ---- 5. The symmetry group ----------------------------------------------- *)
(*                                                                            *)
(*  Symg is the group of the 48 symmetries of the cube, acting on facelets.   *)
(*  Its order is not needed anywhere: what the reduction uses is that every   *)
(*  one of its elements stabilises the move set, and that follows from the    *)
(*  three generators by the normaliser being a group.                         *)
(*  [COMPUTATION] #|Symg| = 48.                                               *)

Definition Symset : {set {perm facelet}} := [set Sy; Sx; Sm].

Definition Symg : {group {perm facelet}} := <<Symset>>.

Lemma Symg_stab u : u \in Symg -> Sset :^ u = Sset.
Proof.
suff /subsetP H : Symg \subset 'N(Sset) by move=> /H/normP.
rewrite gen_subG; apply/subsetP => x xS; apply/normP.
move: xS; rewrite !inE; case/orP=> [/orP[]|] /eqP->.
- exact: Sset_Jy.
- exact: Sset_Jx.
exact: Sset_Jm.
Qed.
