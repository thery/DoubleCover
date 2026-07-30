(* =========================================================================  *)
(*  Redun.v                                                                   *)
(*                                                                            *)
(*  Searchr.v's face structure, instantiated for the cube.                     *)
(*                                                                            *)
(*  Searchr.v proves the move redundancy rules from two facts about the move   *)
(*  set and nothing about the cube.  This file supplies them for the six       *)
(*  faces, so that searchrN becomes usable on Rubik333.moves.                  *)
(*                                                                            *)
(*    fc m   the face of a move, 0..5 in the order of Rubik333.faces           *)
(*    opp f  the opposite face, U<->D, R<->L, F<->B                            *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Searchr Rubik333 Sym Diameter Moves.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- 1. The missing commutation ------------------------------------------- *)

(* Sym.v built the U-D and R-L axes because Sy and Sx needed them; the F-B
   pair was never required.  Same proof: the two layers are supported on
   disjoint facelets, so uniq_inord settles it without evaluating a
   permutation.                                                             *)
Lemma FBcyc_uniq : uniq (flatten (Fcyc ++ Bcyc)).
Proof.
by eapply (@uniq_inord _
  [:: 16; 18; 23; 21; 17; 20; 22; 19; 5; 24; 42; 15; 6; 27; 41; 12; 7; 29; 40; 10;
      32; 34; 39; 37; 33; 36; 38; 35; 2; 8; 45; 31; 1; 11; 46; 28; 0; 13; 47; 26])%N.
Qed.

Lemma commute_FB : commute Fmove Bmove.
Proof.
rewrite FmoveE BmoveE; apply: commute_cyc_cat.
by have := FBcyc_uniq; rewrite flatten_cat cat_uniq => /and3P[_ ->].
Qed.

(* ---- 2. One face closes ---------------------------------------------------*)

(* the conversion, factored: every power of an order-4 element is one of the
   four powers below 4.  Note this cannot collapse the nine cases of
   face_closeP into one tactic -- in mathcomp neither addn nor modn reduces
   under /=, so the exponent stays a stuck (1 + 1) %% 4 and nothing matches
   without a per-case conversion anyway.                                   *)
Lemma expg_mod4 (g : {perm facelet}) k : g ^+ 4 = 1 -> g ^+ k = g ^+ (k %% 4).
Proof.
by move=> g4; rewrite {1}(divn_eq k 4) mulnC expgD expgnA g4 expg1n mul1g.
Qed.

(* The three non-trivial powers of an order-4 element are closed under
   product, falling back on the identity.  This is fc_close's content; all
   six faces have order 4 (Umove4 .. Dmove4), so it is proved once.
   Stated in uniform powers g^+1, g^+2, g^+3 rather than g, g^+2, g^-1 so
   that every one of the nine products goes through a single expgD.        *)
Lemma face_closeP (g m1 m2 : {perm facelet}) :
  g ^+ 4 = 1 ->
  m1 \in [:: g ^+ 1; g ^+ 2; g ^+ 3] -> m2 \in [:: g ^+ 1; g ^+ 2; g ^+ 3] ->
  m1 * m2 = 1 \/ m1 * m2 \in [:: g ^+ 1; g ^+ 2; g ^+ 3].
Proof.
move=> g4.
have gk k : g ^+ (4 + k) = g ^+ k by rewrite (expg_mod4 _ g4) modnDl -(expg_mod4 _ g4).
rewrite !inE => /or3P[/eqP->|/eqP->|/eqP->] /or3P[/eqP->|/eqP->|/eqP->];
  rewrite -expgD /=.
- by right; have -> : g ^+ (1 + 1) = g ^+ 2 by []; rewrite eqxx orbT.
- by right; have -> : g ^+ (1 + 2) = g ^+ 3 by []; rewrite eqxx !orbT.
- by left; exact: g4.
- by right; have -> : g ^+ (2 + 1) = g ^+ 3 by []; rewrite eqxx !orbT.
- by left; exact: g4.
- right; have -> : g ^+ (2 + 3) = g ^+ 1.
    by rewrite -[(2+3)%N]/(4+1)%N gk.
  by rewrite eqxx.
- by left; exact: g4.
- right; have -> : g ^+ (3 + 2) = g ^+ 1.
    by rewrite -[(3+2)%N]/(4+1)%N gk.
  by rewrite eqxx.
right; have -> : g ^+ (3 + 3) = g ^+ 2.
  by rewrite -[(3+3)%N]/(4+2)%N gk.
by rewrite eqxx orbT.
Qed.

(* ---- 3. moves is duplicate free -------------------------------------------*)

(* fcube below is index m moves, so it only names the intended face if moves
   has no repeats.  Comparing eighteen permutations pairwise would be a
   nightmare; going through the TABLES makes it a list computation, which is
   the trick this development uses everywhere.  Measured: 145 ms.        *)
Lemma uniq_mtabs : uniq mtabs.
Proof. by vm_compute. Qed.

Lemma pt_inj_in t1 t2 :
  tab_ok 47 t1 -> tab_ok 47 t2 -> pt 47 t1 = pt 47 t2 -> t1 = t2.
Proof.
move=> ok1 ok2 ptE12.
have [/eqP sz1 /allP lt1 _] := and3P ok1.
have [/eqP sz2 /allP lt2 _] := and3P ok2.
apply: (@eq_from_nth _ 0%N); first by rewrite sz1 sz2.
move=> i; rewrite sz1 => iL.
have b1 : nth 0%N t1 i < 47.+1 by apply: lt1; rewrite mem_nth // sz1.
have b2 : nth 0%N t2 i < 47.+1 by apply: lt2; rewrite mem_nth // sz2.
have := congr1 (fun p : {perm facelet} => (p (inord i) : nat)) ptE12.
by rewrite !ptE // !inordK.
Qed.

Lemma uniq_moves : uniq moves.
Proof.
rewrite mtabsE map_inj_in_uniq ?uniq_mtabs //.
move=> t1 t2 t1M t2M; apply: pt_inj_in; exact: (allP mtabs_ok).
Qed.

(* ---- 4. The face structure -------------------------------------------------*)

Definition nfcube := 6.                 (* six faces                          *)
Definition oppf (f : nat) : nat := (f + 3) %% nfcube.

(* moves is flatten [seq [:: g; g^+2; g^-1] | g <- faces], so the moves of
   face f sit at indices 3f, 3f+1, 3f+2.                                    *)
Definition fcube (m : {perm facelet}) : nat := index m moves %/ 3.

(* oppf_lt and oppf_neq used to live here, to discharge Searchr's opp_lt and
   opp_neq.  Those hypotheses turned out to be unused, so both are gone --
   two lines to restore if ever wanted.                                   *)
Lemma fcube_lt m : m \in Sset -> fcube m < nfcube.
Proof.
rewrite inE => mM; rewrite /fcube /nfcube ltn_divLR //.
(* seq.size, not size: Uint63 shadows it with the word width 63 *)
have h : index m moves < seq.size moves by rewrite index_mem.
by apply: leq_trans h _; rewrite /moves /faces.
Qed.

(* ---- 5. Reading a move's face off the list --------------------------------*)

(* nth on the concrete eighteen element list reduces by pure list computation
   -- NO permutation is ever evaluated.  That is what makes all of this cheap,
   and it is worth knowing before assuming otherwise: the whole block below
   is mechanical because of it.                                            *)
Definition gf (f : nat) : {perm facelet} := nth 1 faces f.

Lemma faces_ord4 f : f < 6 -> (gf f) ^+ 4 = 1.
Proof.
rewrite /gf /faces; case: f => [|[|[|[|[|[|f]]]]]] //= _.
- exact: Umove4.
- exact: Rmove4.
- exact: Fmove4.
- exact: Dmove4.
- exact: Lmove4.
exact: Bmove4.
Qed.

Lemma invg_pow3 (g : {perm facelet}) : g ^+ 4 = 1 -> g ^-1 = g ^+ 3.
Proof.
move=> g4; apply: (mulgI g); rewrite mulgV -{1}(expg1 g) -expgD.
exact: (esym g4).
Qed.

Lemma moves_size : seq.size moves = 18.
Proof. by rewrite /moves /faces. Qed.

(* the block structure: face q occupies indices 3q, 3q+1, 3q+2, holding
   g, g^+2 and g^-1 -- the last being g^+3 since g has order 4.  Eighteen
   cases, all closed by list reduction.                                    *)
Lemma nth_moves q r : q < 6 -> r < 3 -> nth 1 moves (3 * q + r) = (gf q) ^+ r.+1.
Proof.
move=> q6 r3.
have g4 := faces_ord4 q6.
move: q6 r3; rewrite /moves /faces /gf in g4 *.
case: q g4 => [|[|[|[|[|[|q]]]]]] g4 //= _;
  case: r => [|[|[|r]]] //= _; rewrite ?expg1 //; exact: (invg_pow3 g4).
Qed.

Lemma moves_faceE m : m \in moves ->
  m \in [:: (gf (fcube m)) ^+ 1; (gf (fcube m)) ^+ 2; (gf (fcube m)) ^+ 3].
Proof.
move=> mM.
have iL : index m moves < 18.
  have h : index m moves < seq.size moves by rewrite index_mem.
  by move: h; rewrite moves_size.
have qL : index m moves %/ 3 < 6 by rewrite ltn_divLR.
have rL : index m moves %% 3 < 3 by rewrite ltn_mod.
have mE : m = (gf (index m moves %/ 3)) ^+ (index m moves %% 3).+1.
  by rewrite -(nth_moves qL rL) mulnC -divn_eq nth_index.
rewrite /fcube {1}mE.
by case: (index m moves %% 3) rL mE => [|[|[|r]]] // _ _; rewrite !inE eqxx ?orbT.
Qed.

(* ---- 6. What is left ------------------------------------------------------ *)

(* the converse of moves_faceE, and the two facts Searchr.v asks for.  All
   three are now mechanical: nth_moves gives the member, mem_nth puts it in
   moves, and index_uniq (via uniq_moves) reads its index back exactly.
   [EASY] triple_moves: m' = gf f ^+ k for k in 1..3 is nth 1 moves (3f+k-1),
   so mem_nth gives m' \in moves and index_uniq gives fcube m' = f.
   [EASY] fcube_close: moves_faceE on m1 gives the triple, fcube m1 = fcube m2
   puts m2 in the same one, face_closeP does the algebra, triple_moves maps
   the answer back.
   [EASY] fcube_comm: needs commute (gf f) (gf (oppf f)) -- six cases from
   commute_UD, commute_RL, commute_FB and their commute_sym -- then commuteX2
   lifts it from the generators to their powers.                            *)
Lemma triple_moves f m' : f < 6 ->
  m' \in [:: (gf f) ^+ 1; (gf f) ^+ 2; (gf f) ^+ 3] ->
  m' \in moves /\ fcube m' = f.
Proof.
move=> f6 m'M.
have [r [r3 m'E]] : exists r, r < 3 /\ m' = (gf f) ^+ r.+1.
  by move: m'M; rewrite !inE => /or3P[/eqP->|/eqP->|/eqP->];
     [exists 0%N | exists 1%N | exists 2%N].
have iL : 3 * f + r < 18.
  by rewrite -[18]/(3 * 6)%N; apply: leq_trans (_ : 3 * f + 3 <= 3 * 6)%N;
     [rewrite ltn_add2l | rewrite -mulnSr leq_mul2l /=].
rewrite m'E -(nth_moves f6 r3); split.
  by rewrite mem_nth // moves_size.
have szi : 3 * f + r < seq.size moves by rewrite moves_size.
by rewrite /fcube (index_uniq 1 szi uniq_moves) mulnC divnMDl //
           (divn_small r3) addn0.
Qed.

(* fcube_lt again, but stated at 6 rather than nfcube so it composes *)
Lemma fcube_ltS m : m \in Sset -> fcube m < 6.
Proof.
rewrite inE => mM; rewrite /fcube ltn_divLR //.
have h : index m moves < seq.size moves by rewrite index_mem.
by move: h; rewrite moves_size.
Qed.

(* Sset membership, folded.  rewrite inE on a GOAL mentioning Sset expands it
   into an eighteen way disjunction over permutations and the proof hangs;
   proved once here on a small goal and used as a rewrite rule instead.   *)
Lemma fcube_close m1 m2 : m1 \in Sset -> m2 \in Sset -> fcube m1 = fcube m2 ->
  (m1 * m2 = 1) \/
  (exists2 m3, m3 \in Sset & fcube m3 = fcube m1 /\ m1 * m2 = m3).
Proof.
have SsetE (x : {perm facelet}) : (x \in Sset) = (x \in moves).
  by rewrite inE.
move=> m1S m2S fE.
have m1M : m1 \in moves by rewrite -SsetE.
have m2M : m2 \in moves by rewrite -SsetE.
have f6 : fcube m1 < 6 by exact: fcube_ltS.
have t1 := moves_faceE m1M.
have t2 := moves_faceE m2M; rewrite -fE in t2.
case: (face_closeP (faces_ord4 f6) t1 t2) => [->|inT]; first by left.
right; have [m3M f3E] := triple_moves f6 inT.
exists (m1 * m2).
- by rewrite SsetE.
by split.
Qed.

Lemma faces_comm f : f < 6 -> commute (gf f) (gf (oppf f)).
Proof.
case: f => [|[|[|[|[|[|f]]]]]] // _.
- exact: commute_UD.
- exact: commute_RL.
- exact: commute_FB.
- exact: (commute_sym commute_UD).
- exact: (commute_sym commute_RL).
exact: (commute_sym commute_FB).
Qed.

Lemma fcube_comm m1 m2 : m1 \in Sset -> m2 \in Sset ->
  fcube m2 = oppf (fcube m1) -> m1 * m2 = m2 * m1.
Proof.
have SsetE (x : {perm facelet}) : (x \in Sset) = (x \in moves).
  by rewrite inE.
move=> m1S m2S fE.
have m1M : m1 \in moves by rewrite -SsetE.
have m2M : m2 \in moves by rewrite -SsetE.
have f6 : fcube m1 < 6 by exact: fcube_ltS.
have t1 := moves_faceE m1M.
have t2 := moves_faceE m2M; rewrite fE in t2.
move: t1 t2; rewrite !inE => t1 t2.
(* x and y must be ABSTRACT here: substituting m1 while the goal still
   mentions fcube m1 builds fcube (gf (fcube m1) ^+ 1) and diverges. *)
have key : forall f (x y : {perm facelet}), f < 6 ->
    x \in [:: (gf f) ^+ 1; (gf f) ^+ 2; (gf f) ^+ 3] ->
    y \in [:: (gf (oppf f)) ^+ 1; (gf (oppf f)) ^+ 2; (gf (oppf f)) ^+ 3] ->
    x * y = y * x.
  move=> f x y f6'; rewrite !inE.
  move=> /or3P[/eqP->|/eqP->|/eqP->] /or3P[/eqP->|/eqP->|/eqP->];
    by apply: commuteX2; exact: (faces_comm f6').
by apply: (key (fcube m1)) => //; rewrite !inE.
Qed.
