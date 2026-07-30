(* =========================================================================  *)
(*  Searchir.v                                                                *)
(*                                                                            *)
(*  The reduced search on tables and on int63 arrays, and the bridges down to  *)
(*  Searchr.searchr.  SKELETON -- the transfer lemmas are admitted, the        *)
(*  definitions and statements are settled.                                    *)
(*                                                                            *)
(*  Chain, mirroring the unreduced one:                                        *)
(*                                                                            *)
(*    searchir (arrays) --searchirE--> searchtr (seq nat)                      *)
(*             --searchtrE--> searchr (perms) --searchrN--> \notin ball        *)
(*                                                                            *)
(*  THE DESIGN DECISION worth knowing.  searchr guards each move by            *)
(*  okfc0 nfc opp p (fc m), where fc is a function on PERMUTATIONS.  Computing  *)
(*  that on a table or an array would mean carrying Redun's `index m moves`    *)
(*  down two levels, which is absurd: the move list is fixed and ordered, so    *)
(*  the face of the move at position k is simply k %/ 3.  Both reduced          *)
(*  searches therefore iterate over POSITIONS, not over moves, and the whole    *)
(*  content of the bridges is that position k really carries face k %/ 3.      *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Searchr Rubik333 Sym
        Diameter Moves Redun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- 0. Faces by position -------------------------------------------------- *)

Definition fcpos (k : nat) : nat := k %/ 3.

(* THE ONE CUBE FACT the bridges rest on: position k carries face k %/ 3.
   [EASY] nth 1 moves k is the k-th move, and index_uniq with
   Redun.uniq_moves reads its index back as k -- exactly the step already
   used in Redun.triple_moves.                                            *)
Lemma fcpos_moves k : k < 18 -> fcube (nth 1 moves k) = fcpos k.
Proof.
move=> k18.
have szk : k < seq.size moves by rewrite moves_size.
by rewrite /fcube (index_uniq 1 szk uniq_moves).
Qed.

(* has over a list = has over its positions.  Pure seq, and the missing
   ingredient of searchtrE.
   NOTE the predicate is written A -> bool and NOT pred A: with pred A the
   statement does not even elaborate here, it tries to unify A with int. *)
Lemma has_nth_iota (A : Type) (p : A -> bool) (s : seq A) (x0 : A) :
  has p s = has (fun k => p (nth x0 s k)) (iota 0 (seq.size s)).
Proof.
elim: s => [//|x s IH] /=; congr (_ || _).
by rewrite -add1n iotaDl has_map IH.
Qed.

(* ---- 1. The reduced search on tables --------------------------------------*)

Section TableR.

Variable n : nat.
Variable mts : seq (seq nat).
Hypothesis mtsok : all (tab_ok n) mts.
Variable Dt : seq nat -> nat.

(* the face structure, abstract here: nfc faces, opp pairs them, and fcp
   gives the face of a POSITION in mts *)
Variable nfc : nat.
Variable opp : nat -> nat.
Variable fcp : nat -> nat.

Fixpoint searchtr (d : nat) (t : seq nat) (p : nat) : bool :=
  (Dt t <= d) &&
  ((t == id_tab n) ||
   (if d is d'.+1
    then has (fun k => okfc0 nfc opp p (fcp k) &&
                       searchtr d' (comp_tab t (nth [::] mts k)) (fcp k))
             (iota 0 (seq.size mts))
    else false)).

Lemma searchtrS d t p :
  searchtr d.+1 t p =
  (Dt t <= d.+1) &&
  ((t == id_tab n) ||
   has (fun k => okfc0 nfc opp p (fcp k) &&
                 searchtr d (comp_tab t (nth [::] mts k)) (fcp k))
       (iota 0 (seq.size mts))).
Proof. by []. Qed.

(* ---- 2. The bridge to searchr ----------------------------------------------*)

Variable h : {perm 'I_n.+1} -> nat.
Hypothesis hE : forall t, tab_ok n t -> h (pt n t) = Dt t.
Variable fc : {perm 'I_n.+1} -> nat.

(* the position/move identification, supplied by fcpos_moves at the cube *)
Hypothesis fcE : forall k, k < seq.size mts ->
  fc (pt n (nth [::] mts k)) = fcp k.

(* [HARD] the analogue of Tsearch.searchtE, and the ONLY place where the
   position/move identification actually happens -- do this one first, the
   array level is then a copy of Tabi.searchiE.
   SKELETON: induction on d as in searchtE; rewrite hE and pt_eq1, then
   congr (_ && (_ || _)).  The pointwise step is now between a has over
   POSITIONS and a has over MOVES, so it is NOT eq_in_has directly:
     has f (iota 0 (size mts))  =  has g [seq pt n mt | mt <- mts]
   Go through has_map and then `has_nth`-style reasoning -- k <-> nth mts k
   is a bijection of positions onto the list, so
     has g (map F mts) = has (fun k => g (F (nth [::] mts k))) (iota 0 (size mts))
   is the general lemma to prove first (call it has_iota_map); it is about
   seq only and belongs next to prodcat in Searchr.v or in a seq preamble.
   Then fcE turns fcp k into fc of the move and the two guards coincide. *)
Lemma searchtrE d t p :
  tab_ok n t ->
  searchtr d t p = searchr [seq pt n mt | mt <- mts] h nfc fc opp d (pt n t) p.
Proof. Admitted.

End TableR.

(* ---- 3. The reduced search on arrays --------------------------------------*)

(* [MEDIUM] a copy of Tabi.searchi with the guard added.  Not written yet
   because it must be written ONCE, correctly:
     KEEP THE `if ... then` SHAPE.  && and has are strict under vm_compute, so
     spelling this with && evaluates both branches and loses all the pruning.
     That is the bug that cost 185 s at depth 5 before it was found, and the
     guard adds a second place to get it wrong -- the okfc0 test must
     short-circuit before the recursive call, not be &&-ed with it.
   Then searchirE mirrors Tabi.searchiE (rewrite searchirS, DtiE,
   eq_tabi_id, congr, pointwise), and searchirN composes searchirE,
   searchtrE and Searchr.searchrN.                                        *)

(* ---- 4. What the assembly then needs --------------------------------------*)

(* Far.v and the eighteen Far_??.v switch from searchi to searchir.  ONE
   THING THERE IS NOT A RENAME: Far.v splits the root with ball_split2,
   which quantifies the first two moves independently
     (forall m1 m2, m1 \in Sseq -> m2 \in Sseq -> g * m1 * m2 \notin ball S d)
   whereas the reduced search requires m2 to respect the guard against m1.
   So either ball_split2 gains that hypothesis (and the eighteen generated
   files gain the guard in their statement), or the split is taken at depth
   one instead of two.  Decide this before generating the files -- it
   changes what the Far_??.v say, and they are expensive to redo.
   Note also that the factor being bought here is largest at the TOP of the
   search, so a root split that ignores the guard wastes part of it.       *)
