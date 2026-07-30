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

(* the analogue of Tsearch.searchtE, and the only place where the
   position/move identification happens.  The pointwise step is between a
   has over POSITIONS and a has over MOVES: has_map strips the map on the
   right, then has_nth_iota turns that list into its positions.  It has to
   be AIMED at the right hand side -- has_nth_iota's pattern also matches
   the left, where the body mentions k outside the nth, so an untargeted
   rewrite goes the wrong way.                                            *)
Lemma searchtrE d t p :
  tab_ok n t ->
  searchtr d t p = searchr [seq pt n mt | mt <- mts] h nfc fc opp d (pt n t) p.
Proof.
elim: d t p => [t p tok|d IH t p tok] /=; rewrite hE // pt_eq1 //.
congr (_ && (_ || _)).
rewrite has_map [X in _ = X](has_nth_iota _ _ [::]).
apply: eq_in_has => k; rewrite mem_iota => /andP[_ kL] /=.
rewrite fcE //; congr (_ && _).
have mtok : tab_ok n (nth [::] mts k) by apply: (allP mtsok); rewrite mem_nth.
by rewrite (IH _ (fcp k) (tab_ok_comp tok mtok)) (ptM tok mtok).
Qed.

End TableR.

(* ---- 3. The reduced search on arrays --------------------------------------*)

(* has over a filtered list is has over the list with the filter conjoined *)
Lemma has_filter_and (A : Type) (P f : A -> bool) (s : seq A) :
  has f [seq x <- s | P x] = has (fun x => P x && f x) s.
Proof. by elim: s => [//|x s IH] /=; case: (P x) => //=; rewrite IH. Qed.

Section ArrayR.

Variable n : nat.
(* eq_tabi_id needs these two, exactly as Tabi's section does *)
Hypothesis n_small : n.+1 < nwB.
Hypothesis n_len : (of_nat n.+1 <=? PArray.max_length)%uint63.
Variable mtis : seq (PArray.array int).
Hypothesis mtis_ok : all (tabi_ok n) mtis.
Variable Dti : PArray.array int -> nat.
Variable Dt : seq nat -> nat.
Hypothesis DtiE : forall a, tabi_ok n a -> Dti a = Dt (ti2t n a).
Variable nfc : nat.
Variable opp : nat -> nat.
Variable fcp : nat -> nat.

(* THE POSITIONS ALLOWED AFTER A MOVE OF FACE p, filtered ONCE per p rather
   than tested per move.  That is not cosmetic: it keeps the inner loop the
   SAME SHAPE as Tabi.searchi, so the laziness carries over for free and
   searchirS stays definitional.  && and has are strict under vm_compute, so
   a guard spelled `okfc0 ... && searchir ...` inside the loop would run the
   recursive call even when the guard fails -- the 185 s bug all over again. *)
Definition allowedr (p : nat) : seq nat :=
  [seq k <- iota 0 (seq.size mtis) | okfc0 nfc opp p (fcp k)].

Fixpoint searchir (d : nat) (a : PArray.array int) (p : nat) : bool :=
  if Dti a <= d then
    if eq_tabi n a (id_tabi n) then true
    else if d is d'.+1 then
      (fix go (l : seq nat) : bool :=
         if l is k :: l' then
           if searchir d' (comp_tabi n a (nth (id_tabi n) mtis k)) (fcp k)
           then true else go l'
         else false) (allowedr p)
    else false
  else false.

Lemma searchirS d a p :
  searchir d.+1 a p =
  (Dti a <= d.+1) &&
  (eq_tabi n a (id_tabi n) ||
   has (fun k => searchir d (comp_tabi n a (nth (id_tabi n) mtis k)) (fcp k))
       (allowedr p)).
Proof.
rewrite {1}/searchir -/searchir.
by case: (Dti a <= d.+1) => //=; case: (eq_tabi n a (id_tabi n)) => //=.
Qed.

Lemma searchirE d a p :
  tabi_ok n a ->
  searchir d a p =
  searchtr n [seq ti2t n mt | mt <- mtis] Dt nfc opp fcp d (ti2t n a) p.
Proof.
(* p must be generalised: the recursive call changes it to fcp k *)
move=> aok; move: a p aok; elim: d => [|d IH] a p aok.
  by rewrite /= DtiE // eq_tabi_id //.
rewrite searchirS searchtrS DtiE // eq_tabi_id //.
congr (_ && (_ || _)).
rewrite /allowedr has_filter_and seq.size_map.
apply: eq_in_has => k; rewrite mem_iota => /andP[_ kL].
congr (_ && _).
have mtok : tabi_ok n (nth (id_tabi n) mtis k).
  by apply: (all_nthP (id_tabi n) mtis_ok).
by rewrite (nth_map (id_tabi n)) // -ti2t_comp // IH // tabi_ok_comp.
Qed.

(* ---- 3bis. The same search, CARRYING the coordinate ----------------------- *)

(* WHY.  searchir spends ~84% of a node rebuilding the coordinate from the
   permutation: comp_tabi composes 48 entries, then Dti inverts the array and
   repacks all 24 bits from scratch.  Measured (fresh coqc, two sizes,
   differenced): 66.2 us/node against 5.4 us for the composition alone.  But
   the coordinate has its own transition function -- Fstab's actf -- so it can
   be carried alongside the array and updated in one step instead of
   recomputed.  Same measurement with actf: 19.8 us/node, a 3.35x.

   The array itself is still needed, for the goal test eq_tabi a (id_tabi n);
   only the heuristic stops going through it.

   NOTE the guard gd (cubti at the cube) does NOT appear in searchic's body,
   only in the proof below.  Dti a is `if cubti a then Dfs (coordi a) else 0`,
   and cubti holds all along a real search, so the fast loop can read the
   heuristic straight off the coordinate and pay nothing per node for it.   *)

Variable Dc : int -> nat.                    (* the heuristic, on coordinates *)
Variable coord : PArray.array int -> int.
Variable gd : PArray.array int -> bool.      (* the validity guard, cubti     *)
Variable actc : int -> nat -> int.           (* the coordinate transition     *)

(* tabi_ok is needed as well as the guard: at the cube, reading the coordinate
   off a table (coordiE) presupposes the array is a well formed one.  Both
   travel down the search together, tabi_ok by tabi_ok_comp and gd by
   gd_comp.                                                                 *)
Hypothesis DtiE2 : forall a, tabi_ok n a -> gd a -> Dti a = Dc (coord a).
Hypothesis gd_comp : forall a k, k < seq.size mtis -> tabi_ok n a -> gd a ->
  gd (comp_tabi n a (nth (id_tabi n) mtis k)).
Hypothesis actcE : forall a k, k < seq.size mtis -> tabi_ok n a -> gd a ->
  coord (comp_tabi n a (nth (id_tabi n) mtis k)) = actc (coord a) k.

Fixpoint searchic (d : nat) (a : PArray.array int) (x : int) (p : nat) : bool :=
  if Dc x <= d then
    if eq_tabi n a (id_tabi n) then true
    else if d is d'.+1 then
      (fix go (l : seq nat) : bool :=
         if l is k :: l' then
           if searchic d' (comp_tabi n a (nth (id_tabi n) mtis k))
                          (actc x k) (fcp k)
           then true else go l'
         else false) (allowedr p)
    else false
  else false.

Lemma searchicS d a x p :
  searchic d.+1 a x p =
  (Dc x <= d.+1) &&
  (eq_tabi n a (id_tabi n) ||
   has (fun k => searchic d (comp_tabi n a (nth (id_tabi n) mtis k))
                            (actc x k) (fcp k))
       (allowedr p)).
Proof.
rewrite {1}/searchic -/searchic.
by case: (Dc x <= d.+1) => //=; case: (eq_tabi n a (id_tabi n)) => //=.
Qed.

(* the two agree as long as the guard holds, which it does along a real
   search -- gd_comp is what carries it down                                *)
Lemma searchicE d a p : tabi_ok n a -> gd a ->
  searchic d a (coord a) p = searchir d a p.
Proof.
move: a p; elim: d => [|d IH] a p aok ga.
  by rewrite /searchic /searchir DtiE2.
rewrite searchicS searchirS DtiE2 //; congr (_ && (_ || _)).
apply: eq_in_has => k; rewrite mem_filter mem_iota => /andP[_ /andP[_ kL]].
have mtok : tabi_ok n (nth (id_tabi n) mtis k).
  by apply: (all_nthP (id_tabi n) mtis_ok).
by rewrite -actcE // IH ?tabi_ok_comp // gd_comp.
Qed.

End ArrayR.



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
