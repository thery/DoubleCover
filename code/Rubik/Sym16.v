(* =========================================================================  *)
(*  Sym16.v -- The sixteen symmetries the phase 1 table folds by.             *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Diameter Moves Far.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- 1. The sixteen, as facelet tables ----------------------------------  *)

Definition sym16_00 : seq nat :=
  [:: 45; 43; 40; 46; 41; 47; 44; 42; 39; 38; 37; 36; 35; 34; 33; 32;
      31; 30; 29; 28; 27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 17; 16;
      15; 14; 13; 12; 11; 10; 9; 8; 2; 4; 7; 1; 6; 0; 3; 5]%N.

Definition sym16_01 : seq nat :=
  [:: 7; 4; 2; 6; 1; 5; 3; 0; 18; 17; 16; 20; 19; 23; 22; 21;
      10; 9; 8; 12; 11; 15; 14; 13; 34; 33; 32; 36; 35; 39; 38; 37;
      26; 25; 24; 28; 27; 31; 30; 29; 40; 43; 45; 41; 46; 42; 44; 47]%N.

Definition sym16_02 : seq nat :=
  [:: 0; 3; 5; 1; 6; 2; 4; 7; 34; 33; 32; 36; 35; 39; 38; 37;
      26; 25; 24; 28; 27; 31; 30; 29; 18; 17; 16; 20; 19; 23; 22; 21;
      10; 9; 8; 12; 11; 15; 14; 13; 47; 44; 42; 46; 41; 45; 43; 40]%N.

Definition sym16_03 : seq nat :=
  [:: 47; 44; 42; 46; 41; 45; 43; 40; 37; 38; 39; 35; 36; 32; 33; 34;
      13; 14; 15; 11; 12; 8; 9; 10; 21; 22; 23; 19; 20; 16; 17; 18;
      29; 30; 31; 27; 28; 24; 25; 26; 0; 3; 5; 1; 6; 2; 4; 7]%N.

Definition sym16_04 : seq nat :=
  [:: 42; 41; 40; 44; 43; 47; 46; 45; 29; 30; 31; 27; 28; 24; 25; 26;
      37; 38; 39; 35; 36; 32; 33; 34; 13; 14; 15; 11; 12; 8; 9; 10;
      21; 22; 23; 19; 20; 16; 17; 18; 2; 1; 0; 4; 3; 7; 6; 5]%N.

Definition sym16_05 : seq nat :=
  [:: 5; 3; 0; 6; 1; 7; 4; 2; 16; 17; 18; 19; 20; 21; 22; 23;
      24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39;
      8; 9; 10; 11; 12; 13; 14; 15; 42; 44; 47; 41; 46; 40; 43; 45]%N.

Definition sym16_06 : seq nat :=
  [:: 5; 6; 7; 3; 4; 0; 1; 2; 10; 9; 8; 12; 11; 15; 14; 13;
      34; 33; 32; 36; 35; 39; 38; 37; 26; 25; 24; 28; 27; 31; 30; 29;
      18; 17; 16; 20; 19; 23; 22; 21; 45; 46; 47; 43; 44; 40; 41; 42]%N.

Definition sym16_07 : seq nat :=
  [:: 45; 46; 47; 43; 44; 40; 41; 42; 13; 14; 15; 11; 12; 8; 9; 10;
      21; 22; 23; 19; 20; 16; 17; 18; 29; 30; 31; 27; 28; 24; 25; 26;
      37; 38; 39; 35; 36; 32; 33; 34; 5; 6; 7; 3; 4; 0; 1; 2]%N.

Definition sym16_08 : seq nat :=
  [:: 40; 41; 42; 43; 44; 45; 46; 47; 15; 14; 13; 12; 11; 10; 9; 8;
      39; 38; 37; 36; 35; 34; 33; 32; 31; 30; 29; 28; 27; 26; 25; 24;
      23; 22; 21; 20; 19; 18; 17; 16; 0; 1; 2; 3; 4; 5; 6; 7]%N.

Definition sym16_09 : seq nat :=
  [:: 42; 44; 47; 41; 46; 40; 43; 45; 23; 22; 21; 20; 19; 18; 17; 16;
      15; 14; 13; 12; 11; 10; 9; 8; 39; 38; 37; 36; 35; 34; 33; 32;
      31; 30; 29; 28; 27; 26; 25; 24; 5; 3; 0; 6; 1; 7; 4; 2]%N.

Definition sym16_10 : seq nat :=
  [:: 2; 4; 7; 1; 6; 0; 3; 5; 32; 33; 34; 35; 36; 37; 38; 39;
      8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23;
      24; 25; 26; 27; 28; 29; 30; 31; 45; 43; 40; 46; 41; 47; 44; 42]%N.

Definition sym16_11 : seq nat :=
  [:: 7; 6; 5; 4; 3; 2; 1; 0; 24; 25; 26; 27; 28; 29; 30; 31;
      32; 33; 34; 35; 36; 37; 38; 39; 8; 9; 10; 11; 12; 13; 14; 15;
      16; 17; 18; 19; 20; 21; 22; 23; 47; 46; 45; 44; 43; 42; 41; 40]%N.

Definition sym16_12 : seq nat :=
  [:: 2; 1; 0; 4; 3; 7; 6; 5; 26; 25; 24; 28; 27; 31; 30; 29;
      18; 17; 16; 20; 19; 23; 22; 21; 10; 9; 8; 12; 11; 15; 14; 13;
      34; 33; 32; 36; 35; 39; 38; 37; 42; 41; 40; 44; 43; 47; 46; 45]%N.

Definition sym16_13 : seq nat :=
  [:: 47; 46; 45; 44; 43; 42; 41; 40; 31; 30; 29; 28; 27; 26; 25; 24;
      23; 22; 21; 20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8;
      39; 38; 37; 36; 35; 34; 33; 32; 7; 6; 5; 4; 3; 2; 1; 0]%N.

Definition sym16_14 : seq nat :=
  [:: 40; 43; 45; 41; 46; 42; 44; 47; 21; 22; 23; 19; 20; 16; 17; 18;
      29; 30; 31; 27; 28; 24; 25; 26; 37; 38; 39; 35; 36; 32; 33; 34;
      13; 14; 15; 11; 12; 8; 9; 10; 7; 4; 2; 6; 1; 5; 3; 0]%N.

Definition sym16_15 : seq nat :=
  [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15;
      16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31;
      32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47]%N.

Definition sym16ts : seq (seq nat) :=
  [:: sym16_00; sym16_01; sym16_02; sym16_03; sym16_04; sym16_05;
      sym16_06; sym16_07; sym16_08; sym16_09; sym16_10; sym16_11;
      sym16_12; sym16_13; sym16_14; sym16_15].

Lemma sym16ts_ok : all (tab_ok 47) sym16ts.
Proof. by vm_compute. Qed.

(* ---- 2. The move relabellings -------------------------------------------- *)

(* Conjugating move k by the i-th symmetry gives move symmove i k.  Read off  *)
(* with Far.v's sigma, exactly as Far.v reads off its own sg0 .. sg4, and     *)
(* checked against the moves by sym16C below.                                 *)
Definition symmovet : seq (seq nat) :=
  Eval vm_compute in [seq [seq sigma s k | k <- iota 0 18] | s <- sym16ts].

Definition symmove (i k : nat) : nat := nth 0%N (nth [::] symmovet i) k.

(* THE FACT THE FOLD RESTS ON: conjugation by each of the sixteen permutes    *)
(* the eighteen moves, by the relabelling.                                    *)
Definition sym16C : bool :=
  all (fun i =>
         all (fun k => conjt (nth [::] sym16ts i) (nth [::] mtabs k)
                         == nth [::] mtabs (symmove i k))
             (iota 0 18))
      (iota 0 16).

Lemma sym16CP : sym16C.
Proof. by vm_compute. Qed.

(* the equation, so that allP is applied to a visible all and never has to    *)
(* unfold the certificate                                                     *)
Lemma sym16CE :
  sym16C =
  all (fun i =>
         all (fun k => conjt (nth [::] sym16ts i) (nth [::] mtabs k)
                         == nth [::] mtabs (symmove i k))
             (iota 0 18))
      (iota 0 16).
Proof. by []. Qed.

(* the relabellings land in range, so the conjugated move really is a move    *)
Definition symmoveB : bool :=
  all (fun i => all (fun k => (symmove i k < 18)%N) (iota 0 18)) (iota 0 16).

Lemma symmoveBP : symmoveB.
Proof. by vm_compute. Qed.

Lemma symmoveBE :
  symmoveB =
  all (fun i => all (fun k => (symmove i k < 18)%N) (iota 0 18)) (iota 0 16).
Proof. by []. Qed.

(* ---- 3. The sixteen are a group ------------------------------------------ *)

(* Sixteen distinct tables, the identity among them, closed under inverse and *)
(* under the 256 products.                                                    *)
Definition sym16G : bool :=
  [&& uniq sym16ts,
      id_tab 47 \in sym16ts,
      all (fun s => inv_tab 47 s \in sym16ts) sym16ts
    & all (fun s => all (fun t => comp_tab s t \in sym16ts) sym16ts) sym16ts].

Lemma sym16GP : sym16G.
Proof. by vm_compute. Qed.

Lemma sym16GE :
  sym16G =
  [&& uniq sym16ts,
      id_tab 47 \in sym16ts,
      all (fun s => inv_tab 47 s \in sym16ts) sym16ts
    & all (fun s => all (fun t => comp_tab s t \in sym16ts) sym16ts) sym16ts].
Proof. by []. Qed.

(* ---- 4. The usable forms ------------------------------------------------- *)

(* the small facts the proofs below need, kept local because Farp1.v already  *)
(* carries its own copies of the first two                                    *)
Local Lemma mem_iota0 n k : (k < n)%N -> k \in iota 0 n.
Proof. by move=> kL; rewrite mem_iota add0n leq0n kL. Qed.

Local Lemma size_mtabs18 : seq.size mtabs = 18%N.
Proof. by vm_compute. Qed.

Local Lemma size_sym16ts : seq.size sym16ts = 16%N.
Proof. by vm_compute. Qed.

Lemma symmove_lt i k : (i < 16)%N -> (k < 18)%N -> (symmove i k < 18)%N.
Proof.
move=> iL kL; have h := symmoveBP; rewrite symmoveBE in h.
exact: (allP (allP h _ (mem_iota0 iL)) _ (mem_iota0 kL)).
Qed.

Lemma sym16_conj i k : (i < 16)%N -> (k < 18)%N ->
  conjt (nth [::] sym16ts i) (nth [::] mtabs k) = nth [::] mtabs (symmove i k).
Proof.
move=> iL kL; apply/eqP.
have h := sym16CP; rewrite sym16CE in h.
exact: (allP (allP h _ (mem_iota0 iL)) _ (mem_iota0 kL)).
Qed.

(* so each of the sixteen sends a move to a move -- Far.v's view_move, for    *)
(* these views                                                                *)
Lemma sym16_move i k : (i < 16)%N -> (k < 18)%N ->
  conjt (nth [::] sym16ts i) (nth [::] mtabs k) \in mtabs.
Proof.
move=> iL kL; rewrite (sym16_conj iL kL); apply: mem_nth.
rewrite size_mtabs18; exact: (symmove_lt iL kL).
Qed.

Lemma sym16_tab_ok i : (i < 16)%N -> tab_ok 47 (nth [::] sym16ts i).
Proof.
by move=> iL; apply: (all_nthP [::] sym16ts_ok); rewrite size_sym16ts.
Qed.

Local Lemma mtabs_nth_ok k : (k < 18)%N -> tab_ok 47 (nth [::] mtabs k).
Proof.
by move=> kL; apply: (all_nthP [::] mtabs_ok); rewrite size_mtabs18.
Qed.

Local Lemma ptJt s t : tab_ok 47 s -> tab_ok 47 t ->
  (pt 47 t) ^ (pt 47 s) = pt 47 (conjt s t).
Proof. move=> sok tok; exact: (ptJ tok sok). Qed.

(* the same fact about the permutations: the k-th move conjugated by the i-th *)
(* symmetry IS the symmove i k-th move                                        *)
Lemma sym16_ptJ i k : (i < 16)%N -> (k < 18)%N ->
  (pt 47 (nth [::] mtabs k)) ^ (pt 47 (nth [::] sym16ts i))
  = pt 47 (nth [::] mtabs (symmove i k)).
Proof.
move=> iL kL.
by rewrite (ptJt (sym16_tab_ok iL) (mtabs_nth_ok kL)) (sym16_conj iL kL).
Qed.

Local Lemma nth_moves k :
  (k < 18)%N -> nth 1 moves k = pt 47 (nth [::] mtabs k).
Proof.
move=> kL; have kM : (k < seq.size mtabs)%N by rewrite size_mtabs18.
rewrite mtabsE (set_nth_default (pt 47 [::]) 1); last by rewrite seq.size_map.
exact: (nth_map [::] (pt 47 [::]) (pt 47) kM).
Qed.

(* and again over Rubik333's moves, which is the list the reduction speaks    *)
(* about                                                                      *)
Lemma sym16_movesJ i k : (i < 16)%N -> (k < 18)%N ->
  (nth 1 moves k) ^ (pt 47 (nth [::] sym16ts i)) = nth 1 moves (symmove i k).
Proof.
move=> iL kL.
rewrite (nth_moves kL) (nth_moves (symmove_lt iL kL)).
exact: (sym16_ptJ iL kL).
Qed.

(* ---- 5. The group facts, as membership ----------------------------------- *)

Lemma sym16_uniq : uniq sym16ts.
Proof. by have := sym16GP; rewrite sym16GE => /and4P[h _ _ _]. Qed.

Lemma sym16_id : id_tab 47 \in sym16ts.
Proof. by have := sym16GP; rewrite sym16GE => /and4P[_ h _ _]. Qed.

Lemma sym16_inv s : s \in sym16ts -> inv_tab 47 s \in sym16ts.
Proof.
move=> sM; have := sym16GP; rewrite sym16GE => /and4P[_ _ h _].
exact: (allP h _ sM).
Qed.

Lemma sym16_comp s t : s \in sym16ts -> t \in sym16ts ->
  comp_tab s t \in sym16ts.
Proof.
move=> sM tM; have := sym16GP; rewrite sym16GE => /and4P[_ _ _ h].
exact: (allP (allP h _ sM) _ tM).
Qed.

Lemma sym16_mem i : (i < 16)%N -> nth [::] sym16ts i \in sym16ts.
Proof. by move=> iL; apply: mem_nth; rewrite size_sym16ts. Qed.
