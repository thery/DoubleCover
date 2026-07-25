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
(*  STRUCTURE.  Everything below is a real proof except the eighteen          *)
(*  conjugation facts  Xmove ^ s = Ymove  (six per generator), which are      *)
(*  genuine finite computations on {perm 'I_48}.  Following the convention    *)
(*  of Rubik333.v they are Admitted and tagged [COMPUTATION].  They are all   *)
(*  of the same shape, so one technique discharges all eighteen.              *)
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
(*  Sy is the quarter turn of the whole cube about the U-D axis, in the same  *)
(*  sense as the U move: the U face turns on itself, each side face is taken  *)
(*  to the next one (L -> B -> R -> F -> L) with its eight facelets in the    *)
(*  same order, and the D face turns on itself the other way.                 *)

Definition Sycyc : seq (seq facelet) :=
  [:: [:: 0@; 2@; 7@; 5@];
      [:: 1@; 4@; 6@; 3@];
      [:: 8@; 32@; 24@; 16@];
      [:: 9@; 33@; 25@; 17@];
      [:: 10@; 34@; 26@; 18@];
      [:: 11@; 35@; 27@; 19@];
      [:: 12@; 36@; 28@; 20@];
      [:: 13@; 37@; 29@; 21@];
      [:: 14@; 38@; 30@; 22@];
      [:: 15@; 39@; 31@; 23@];
      [:: 40@; 45@; 47@; 42@];
      [:: 41@; 43@; 46@; 44@] ].

Definition Sy : {perm facelet} := \prod_(l <- Sycyc) cyc l.

(*  Sx is the quarter turn of the whole cube about the R-L axis, in the same  *)
(*  sense as the R move: F -> U -> B -> D -> F, R turning on itself.          *)

Definition Sxcyc : seq (seq facelet) :=
  [:: [:: 0@; 39@; 40@; 16@];
      [:: 1@; 38@; 41@; 17@];
      [:: 2@; 37@; 42@; 18@];
      [:: 3@; 36@; 43@; 19@];
      [:: 4@; 35@; 44@; 20@];
      [:: 5@; 34@; 45@; 21@];
      [:: 6@; 33@; 46@; 22@];
      [:: 7@; 32@; 47@; 23@];
      [:: 8@; 13@; 15@; 10@];
      [:: 9@; 11@; 14@; 12@];
      [:: 24@; 26@; 31@; 29@];
      [:: 25@; 28@; 30@; 27@] ].

Definition Sx : {perm facelet} := \prod_(l <- Sxcyc) cyc l.

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

(* ---- 2. The generators really are symmetries of the right order ---------- *)
(*                                                                            *)
(*  Each of Sy, Sx is a product of twelve disjoint 4-cycles covering all 48   *)
(*  facelets, and Sm of twenty disjoint transpositions.  As in Rubik333.v     *)
(*  the disjointness is uniqueness of the concatenation, proved structurally  *)
(*  through uniq_inord -- no permutation is evaluated.                        *)

Lemma Sycyc_uniq : uniq (flatten Sycyc).
Proof.
by eapply (@uniq_inord _
  [:: 0; 2; 7; 5; 1; 4; 6; 3; 8; 32; 24; 16; 9; 33; 25; 17;
      10; 34; 26; 18; 11; 35; 27; 19; 12; 36; 28; 20; 13; 37; 29; 21;
      14; 38; 30; 22; 15; 39; 31; 23; 40; 45; 47; 42; 41; 43; 46; 44])%N.
Qed.

Lemma Sxcyc_uniq : uniq (flatten Sxcyc).
Proof.
by eapply (@uniq_inord _
  [:: 0; 39; 40; 16; 1; 38; 41; 17; 2; 37; 42; 18; 3; 36; 43; 19;
      4; 35; 44; 20; 5; 34; 45; 21; 6; 33; 46; 22; 7; 32; 47; 23;
      8; 13; 15; 10; 9; 11; 14; 12; 24; 26; 31; 29; 25; 28; 30; 27])%N.
Qed.

Lemma Smcyc_uniq : uniq (flatten Smcyc).
Proof.
by eapply (@uniq_inord _
  [:: 0; 2; 3; 4; 5; 7; 8; 26; 9; 25; 10; 24; 11; 28; 12; 27;
      13; 31; 14; 30; 15; 29; 16; 18; 19; 20; 21; 23; 32; 34; 35; 36;
      37; 39; 40; 42; 43; 44; 45; 47])%N.
Qed.

Lemma Sy4 : Sy ^+ 4 = 1.
Proof. by apply: cyc_prod_expn; [exact: Sycyc_uniq | apply: all_sizeP]. Qed.

Lemma Sx4 : Sx ^+ 4 = 1.
Proof. by apply: cyc_prod_expn; [exact: Sxcyc_uniq | apply: all_sizeP]. Qed.

Lemma Sm2 : Sm ^+ 2 = 1.
Proof. by apply: cyc_prod_expn; [exact: Smcyc_uniq | apply: all_sizeP]. Qed.

(* ---- 3. How the symmetries permute the face turns ------------------------ *)
(*                                                                            *)
(*  [COMPUTATION]  The eighteen facts below are the whole computational       *)
(*  content of this file.  Each says that conjugating a face turn by a        *)
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
(*  Since all eighteen have the same shape, one technique settles them all.   *)

(* -- Sy : U and D fixed, L -> B -> R -> F -> L.                              *)
Lemma UmoveJy : Umove ^ Sy = Umove.  Admitted.  (* [COMPUTATION]              *)
Lemma RmoveJy : Rmove ^ Sy = Fmove.  Admitted.  (* [COMPUTATION]              *)
Lemma FmoveJy : Fmove ^ Sy = Lmove.  Admitted.  (* [COMPUTATION]              *)
Lemma DmoveJy : Dmove ^ Sy = Dmove.  Admitted.  (* [COMPUTATION]              *)
Lemma LmoveJy : Lmove ^ Sy = Bmove.  Admitted.  (* [COMPUTATION]              *)
Lemma BmoveJy : Bmove ^ Sy = Rmove.  Admitted.  (* [COMPUTATION]              *)

(* -- Sx : R and L fixed, F -> U -> B -> D -> F.                              *)
Lemma UmoveJx : Umove ^ Sx = Bmove.  Admitted.  (* [COMPUTATION]              *)
Lemma RmoveJx : Rmove ^ Sx = Rmove.  Admitted.  (* [COMPUTATION]              *)
Lemma FmoveJx : Fmove ^ Sx = Umove.  Admitted.  (* [COMPUTATION]              *)
Lemma DmoveJx : Dmove ^ Sx = Fmove.  Admitted.  (* [COMPUTATION]              *)
Lemma LmoveJx : Lmove ^ Sx = Lmove.  Admitted.  (* [COMPUTATION]              *)
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
