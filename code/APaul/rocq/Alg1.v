(******************************************************************************)
(*                                                                            *)
(*   Lefevre's original lower-bound algorithm                                 *)
(*                                                                            *)
(*   Algorithm 1 of doc/mourad.pdf (hal-00751446, 4.1), the algorithm         *)
(*    Alg2.v's Algorithm 2 was designed to replace.  Same specification:      *)
(*    with [a = A/M], [b = B/M], a lower bound on                             *)
(*    [inf { b - a*x mod 1 | x < N }].                                        *)
(*                                                                            *)
(*   The two differ in what they branch on.  Algorithm 2 tests [p < q],       *)
(*    which is a plain Euclidean test on the configuration.  Algorithm 1      *)
(*    tests [d < p], which the paper states is exactly "[b] lies in an        *)
(*    interval of length [p]" -- so its control flow depends on where [b]     *)
(*    sits, not only on the two lengths.  That is the one genuinely new       *)
(*    obligation here; see [half1_inf_lt] and [half1_inf_ge] below.                    *)
(*                                                                            *)
(*   One turn of Algorithm 1 is TWO Euclidean steps, a division one then a    *)
(*    subtraction one, with the exit test BETWEEN them (lines 7 and 14).      *)
(*    That is why the loop cannot be written as a [step] plus a check, the    *)
(*    way Alg2.run is.                                                        *)
(*                                                                            *)
(*      branch [d < p]   q -= (q %/ p) * p, u += k*v  | exit | p -= q, v += u *)
(*      branch [p <= d]  d -= p, p -= (p %/ q) * q, v += k*u | exit |         *)
(*                                                          q -= p, u += v    *)
(*                                                                            *)
(*   NOTE ON THE SOURCE.  Line 13 of the paper's listing prints as            *)
(*    [q <- p - k*q].  That has to be a typo for [p <- p - k*q]: as           *)
(*    printed it leaves [p] at its old, larger value and line 15's            *)
(*    [q <- q - p] would go negative.  The counter update on the same line,   *)
(*    [v <- v + k*u], is the one that goes with reducing [p] by [k*q]         *)
(*    (compare Alg2.step's second branch).  The [Example]s below are what     *)
(*    check that reading: they are the same figures Alg2.v checks.            *)
(*                                                                            *)
(*   NOTE ON eps.  The paper's lines 2 and 11 return Failure early when       *)
(*    [d < eps].  That is an optimisation, not part of the bound: [d] never   *)
(*    increases, so an early Failure and a final [d < eps] agree.  The loop   *)
(*    below therefore returns [d], as Alg2.run does, and the test is the      *)
(*    corollary [lefevre1_test].  Relating the two is [run1_decr], left       *)
(*    open below.                                                             *)
(*                                                                            *)
(*   Companion notes: doc/mourad-notes.md (the six cases and Property 3),     *)
(*    doc/lefevre-these-notes.md (what the variables mean).                   *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From APaulRocq Require Import Dist Alg2.

(** ** Algorithm 1 *)

(*  The loop.  [fuel] is a structural bound; [M] suffices, as [p + q]         *)
(*    decreases from [M] -- each turn does two Euclidean reductions, so it    *)
(*    decreases at least as fast as Alg2's.                                   *)
Fixpoint run1 (fuel p q d u v N : nat) : nat :=
  if fuel is fuel1.+1 then
    if d < p then
      (* [b] is in an interval of length [p]: no point enters its gap, so
         [d] is untouched by this turn. *)
      let k  := q %/ p in
      let q1 := q - k * p in
      let u1 := u + k * v in
      if N <= u1 + v then d
      else run1 fuel1 (p - q1) q1 d u1 (v + u1) N
    else
      (* [b] is in an interval of length [q]: one point enters to its left,
         so [d] loses exactly [p]. *)
      let d1 := d - p in
      let k  := p %/ q in
      let p1 := p - k * q in
      let v1 := v + k * u in
      if N <= u + v1 then d1
      else run1 fuel1 p1 (q - p1) d1 (u + v1) v1 N
  else d.

(*  The algorithm: start from the two-point configuration and run.  As in     *)
(*    Alg2.lefevre, the initial [q] is [1 - {a}] rather than [1].             *)
Definition lefevre1 (M A B N : nat) : nat :=
  run1 M (A %% M) (M - A %% M) (B %% M) 1 1 N.

(*  Sanity checks (computed).  These are what validate the transcription      *)
(*    of the listing, in particular the line 13 reading above.  They are      *)
(*    the same figures Alg2.v checks, so the two algorithms can be compared   *)
(*    on them directly.                                                       *)
(*                                                                            *)
(*   [a = 17/45] is the example of Figure 4 of the paper.                     *)

Example lefevre1_fig4 : lefevre1 45 17 30 5 = 7.
Proof. by vm_compute. Qed.

(*  Alg2.lefevre_strict's case, where Algorithm 2 returns 1 and the true      *)
(*    infimum is 2.  Algorithm 1 is exact here -- it is the sharper of the    *)
(*    two, see [leq_lefevre_1_2] at the bottom of the file.                   *)
Example lefevre1_sharper : (lefevre1 32 23 12 8, lefevre 32 23 12 8) = (2, 1).
Proof. by vm_compute. Qed.

(*  But not exact in general: here both return 0 and the infimum is 1.  This  *)
(*    is the smallest counterexample; see the note on [invd] below.           *)
Example lefevre1_strict : (lefevre1 5 2 3 4, inf_dst 5 2 3 4) = (0, 1).
Proof. by vm_compute. Qed.

(******************************************************************************)
(* The theory                                                                 *)
(******************************************************************************)

Section Theory.

(*  The same setting as Alg2.v's [Section Theory], so that its [inv],         *)
(*    [invd] and [invx] can be reused verbatim: those three records describe  *)
(*    the CONFIGURATION, not the algorithm walking it.  Only the [*_step]     *)
(*    lemmas are specific to Alg2.step and have to be redone here.            *)

Variable M : nat.
Hypothesis M_gt0 : 0 < M.

Variables A B : nat.
Hypothesis ltn_A : A < M.
Hypothesis ltn_B : B < M.

Variable N : nat.
Local Notation g := (gcdn A M).

Hypothesis N_gt0 : 0 < N.
Hypothesis N_lt_Mg : N < M %/ g.

Local Notation pt := (pt M A).
Local Notation dst := (dst M A B).
Local Notation inf := (inf_dst M A B).

(*  Alg2's three records, at this section's parameters.                       *)
Local Notation inv := (inv M A).
Local Notation invd := (invd M A B).
Local Notation invx := (invx M A B).

(*  The two halves of a turn, named so the lemmas below can speak about       *)
(*    each separately.  [half1] is lines 5-6 resp. 10-13, [half2] lines 8     *)
(*    resp. 15.  [run1] inlines both; these are for the proofs.               *)

Definition half1 (p q d u v : nat) : nat * nat * nat * nat * nat :=
  if d < p then
    let k := q %/ p in (p, q - k * p, d, u + k * v, v)
  else
    let k := p %/ q in (p - k * q, q, d - p, u, v + k * u).

(*  [half2] must know which branch was taken.  After [half1] the state does   *)
(*    not always say: [b] is a boolean argument rather than a test on         *)
(*    [p, q], so that no case is silently merged.                             *)
Definition half2 (b : bool) (p q d u v : nat) : nat * nat * nat * nat * nat :=
  if b then (p - q, q, d, u, v + u) else (p, q - p, d, u + v, v).

(******************************************************************************)
(* What is new: the branch invariant                                          *)
(******************************************************************************)

(*  REFUTED, DO NOT RETRY.  4.1 says "the variable d contains the distance    *)
(*    between {b} and the closest point to its left", which reads as          *)
(*    [d = inf (u + v)] -- an invariant strictly stronger than Alg2's         *)
(*    [invd], and one that would make the test [d < p] immediately            *)
(*    meaningful.  It is FALSE.  Measured over all [M <= 24], all             *)
(*    [A, B < M] and all [3 <= N < M %/ gcdn A M]:                            *)
(*                                                                            *)
(*      [lefevre1 <= inf_dst]         true   (so Algorithm 1 is sound)        *)
(*      [lefevre1 == inf_dst]         FALSE  (smallest: M=5 A=2 B=3 N=4,      *)
(*                                            [lefevre1_strict] above)        *)
(*      [lefevre <= lefevre1]         true   (Algorithm 1 is the sharper)     *)
(*                                                                            *)
(*    So Algorithm 1 returns a lower bound too, and Alg2's [invd] is the      *)
(*    invariant to carry -- unchanged, which is more reuse, not less.         *)

(*  What is genuinely new is the branch test.  Alg2 branches on [p < q],      *)
(*    decidable from the configuration alone; Algorithm 1 branches on         *)
(*    [d < p], which the paper justifies as "[b] lies in an interval of       *)
(*    length [p]".  Rather than formalise "the gap containing [b]", which     *)
(*    the existing vocabulary does not name, state the two consequences the   *)
(*    proof actually uses: in the [d < p] branch no point enters [b]'s gap,   *)
(*    so [inf] does not move; in the other branch exactly one does, and [d]   *)
(*    loses exactly [p].                                                      *)
(*                                                                            *)
(*  SETTLE THESE TWO FIRST.  They are the one place this development can      *)
(*    fail the way the [d] side of Alg2 failed; everything after is           *)
(*    bookkeeping.  Both are decidable at fixed [M, A, B, N] -- measure       *)
(*    before proving.                                                         *)
(*  MEASURED TRUE on every state reachable along a run, for all [M <= 20],    *)
(*    all [A, B < M] and all [3 <= N < M %/ gcdn A M] (Alg1wip.chk_lt).       *)
Lemma half1_inf_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> d < p ->
  let: (_, _, _, u', v') := half1 p q d u v in inf (u' + v') = inf (u + v).
Proof. Admitted.

(*  MEASURED FALSE, DO NOT RETRY (Alg1wip.chk_ge, same range).  The reading   *)
(*    of 4.1 that "exactly one point enters to the left of [b], so [d] loses  *)
(*    exactly [p]" does NOT come out as [inf] dropping by exactly [p] across  *)
(*    [half1].  Kept, stated, and marked, so the next attempt starts from     *)
(*    the refutation rather than from the paper's prose.                      *)
(*                                                                            *)
(*  WHAT TO TRY NEXT.  The division half of this branch reduces [p] by        *)
(*    [k * q], not by [q] once, so more than one point can enter; the drop    *)
(*    is presumably by a multiple, or is only an inequality                   *)
(*    [inf (u' + v') + p <= inf (u + v)].  Measure those two variants first   *)
(*    -- Alg1wip.v is set up for exactly that -- before proving anything.     *)
Lemma half1_inf_ge p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p <= d ->
  let: (_, _, _, u', v') := half1 p q d u v in
  inf (u' + v') + p = inf (u + v).
Proof. Admitted.

(******************************************************************************)
(* The step lemmas, one per record per half                                   *)
(******************************************************************************)

(*  [inv] through the two halves.  The division half is Alg2.inv_step with    *)
(*    the branches selected differently; the subtraction half is its [k = 1]  *)
(*    case.  Both should follow the shape of Alg2.inv_step closely.           *)
Lemma inv_half1 p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', d', u', v') := half1 p q d u v in inv p' q' d' u' v'.
Proof. Admitted.

Lemma inv_half2 p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', d', u', v') := half2 (d < p) p q d u v in inv p' q' d' u' v'.
Proof. Admitted.

(*  [invx] through the two halves.  This is the bulk of Alg2.v (the           *)
(*    [gap_*], [inf_new_*] and [invx_step_*] families, some 1500 lines) and   *)
(*    it is where the reuse should pay: those lemmas are about what a         *)
(*    Euclidean reduction does to a two-length configuration, which is the    *)
(*    same operation here.  Expect to instantiate rather than reprove.        *)
Lemma invx_half1 p q d u v :
  inv p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', _, u', v') := half1 p q d u v in invx p' q' u' v'.
Proof. Admitted.

Lemma invx_half2 p q d u v :
  inv p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', _, u', v') := half2 (d < p) p q d u v in invx p' q' u' v'.
Proof. Admitted.

(*  [invd] through the two halves: the six cases of 4.1, which is what       *)
(*    doc/mourad-notes.md tabulates.  The division half is where [d] moves    *)
(*    ([d - p] in the second branch, unchanged in the first); the             *)
(*    subtraction half leaves [d] alone but changes [u + v], so it is         *)
(*    [inf (u + v)] that has to be shown not to move.                         *)
Lemma invd_half1 p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', d', u', v') := half1 p q d u v in invd p' q' d' u' v'.
Proof. Admitted.

Lemma invd_half2 p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', d', u', v') := half2 (d < p) p q d u v in invd p' q' d' u' v'.
Proof. Admitted.

(*  The measure: one turn strictly decreases [p + q].  Two reductions per     *)
(*    turn, so this should be easier than Alg2.step_measure, not harder.      *)
Lemma run1_measure p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p1, q1, d1, u1, v1) := half1 p q d u v in
  let: (p', q', _, _, _) := half2 (d < p) p1 q1 d1 u1 v1 in
  p' + q' < p + q.
Proof. Admitted.

(*  [d] never increases along the loop.  This is what makes the paper's       *)
(*    early Failure exits (lines 2 and 11) equivalent to testing the          *)
(*    returned [d], and so justifies dropping eps from [run1].                *)
Lemma run1_decr fuel p q d u v :
  inv p q d u v -> run1 fuel p q d u v N <= d.
Proof. Admitted.

(******************************************************************************)
(* Soundness                                                                  *)
(******************************************************************************)

(*  The initial state.  [Alg2.inv_init] and [Alg2.invx_init] transfer         *)
(*    unchanged -- they are about the configuration, and the two algorithms   *)
(*    start from the same one.  Only [invd] at the start is new, and unlike  *)
(*    Alg2's [invd_first] it should be immediate: before any step, [u+v = 2]  *)
(*    and [d = B %% M] is the distance in the two-point configuration.        *)
Lemma invd_init : invd (A %% M) (M - A %% M) (B %% M) 1 1.
Proof. Admitted.

(*  The loop returns a lower bound on the infimum.  Mirrors Alg2.run_sound,   *)
(*    with two exits per turn instead of one.                                 *)
Lemma run1_sound fuel p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  p + q <= fuel -> run1 fuel p q d u v N <= inf N.
Proof. Admitted.

(*  The algorithm returns a lower bound on the infimum.                       *)
Theorem lefevre1_sound : 2 < N -> lefevre1 M A B N <= inf N.
Proof. Admitted.

(*  The form the search uses: if the returned bound clears the threshold,     *)
(*    there is no hard-to-round case in this sub-interval.  Once              *)
(*    [lefevre1_sound] is in place this is Alg2.lefevre_test verbatim.        *)
Corollary lefevre1_test eps :
  2 < N -> eps < lefevre1 M A B N -> forall x, x < N -> eps < dst x.
Proof.
move=> N_gt2 epsL x xLN.
apply: leq_trans epsL _.
by apply: leq_trans (lefevre1_sound N_gt2) _; apply: leq_inf_dst xLN.
Qed.

End Theory.

(******************************************************************************)
(* Comparison with Algorithm 2                                                *)
(******************************************************************************)

(*  Both algorithms bound the same quantity, so they can be compared.        *)
(*    Neither is exact ([lefevre1_strict]), but Algorithm 1 is the sharper   *)
(*    of the two: measured true over all [M <= 24], all [A, B < M] and all   *)
(*    [3 <= N < M %/ gcdn A M], with [lefevre1_sharper] a witness that the   *)
(*    inequality is strict somewhere.  Not proved.                           *)
(*                                                                           *)
(*  This is a statement about the two algorithms only, with no [inf] in it,  *)
(*    so it needs neither soundness proof and could be attacked first.       *)

(* TODO: proof.
Lemma leq_lefevre_1_2 M A B N : lefevre M A B N <= lefevre1 M A B N.
*)
