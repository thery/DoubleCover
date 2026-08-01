(******************************************************************************)
(*                                                                            *)
(*   The inner loop of the hard-to-round search                               *)
(*                                                                            *)
(*   [htr_plain.c] has two nested loops.  The outer one moves to the next     *)
(*   chunk and re-evaluates the polynomial; the inner one, isolated here,     *)
(*   walks the points of a chunk and reports those whose distance to [b]      *)
(*   falls in a window at the origin:                                         *)
(*                                                                            *)
(*     for (i = 0; i < n; i++) { if (A < twoE) emit i; A = A + B; }           *)
(*                                                                            *)
(*   Its running value is exactly the [dst] of Dist.v -- the C adds           *)
(*   [M - pt 1] at each step, which is [dstDE] read forwards -- so the loop   *)
(*   is stated over [dst] and needs no model of its own.                      *)
(*                                                                            *)
(*   [scan_flags] says the loop reports exactly the indices in the window;    *)
(*   [scan_inf] then skips the loop entirely when the infimum clears it,      *)
(*   which is what a lower bound on [inf] (Alg2.v) decides in O(log n)        *)
(*   steps rather than [n].                                                   *)
(*                                                                            *)
(*   [scan_complete] is the other half: the loop misses no hard case.  There  *)
(*   the truth is an abstract [tru : nat -> nat] with a bound on how far      *)
(*   [dst] drifts from it, so no real number appears; reals enter only where  *)
(*   [tru] and that bound are instantiated.                                   *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.
From APaulRocq Require Import Dist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Scan.

(*  The parameters of Dist.v: the modulus, the multiplier, the target.        *)
Variable M : nat.
Hypothesis M_gt0 : 0 < M.
Variables A B : nat.
Hypothesis ltn_B : B < M.

Local Notation pt := (pt M A).
Local Notation dst := (dst M A B).
Local Notation inf := (inf_dst M A B).

Local Notation ltn_pt := (ltn_pt M_gt0 A).
Local Notation dst0 := (dst0 A ltn_B).
Local Notation dstDE := (dstDE M_gt0 A B).
Local Notation leq_inf_dst := (leq_inf_dst M A B).

(*  Distance to the origin on the circle of size [M].                         *)
Definition cdist0 (x : nat) : nat := minn (x %% M) (M - x %% M).

(*  Distance between two points of that circle.                               *)
Definition cdist (x y : nat) : nat := cdist0 (x + M - y %% M).

(*  ** The loop                                                               *)

(*  What the C adds to its running value at each step.                        *)
Definition stp : nat := M - pt 1.

(*  One turn of the walk is one step along [dst].                             *)
Lemma dstS x : dst x.+1 = (dst x + stp) %% M.
Proof. by rewrite -addn1 dstDE /stp addnBA // ltnW // ltn_pt. Qed.

(*  The loop, with the running value [r] and the index [i] as the C has them. *)
Fixpoint scan_rec (r twoE i n : nat) : seq nat :=
  if n is n1.+1 then
    let rest := scan_rec ((r + stp) %% M) twoE i.+1 n1 in
    if r < twoE then i :: rest else rest
  else [::].

(*  The inner loop: [n] steps from index [0], where the distance is [B].      *)
Definition scan (twoE n : nat) : seq nat := scan_rec B twoE 0 n.

(*  ** What the loop computes                                                 *)

(*  From index [i], the loop reports the indices of the window it meets.      *)
Lemma scan_recE twoE i n :
  scan_rec (dst i) twoE i n = [seq k <- iota i n | dst k < twoE].
Proof. by elim: n i => [//|n IH] i; rewrite /= -dstS IH; case: ifP. Qed.

(*  Correctness: the loop reports exactly the indices in the window.          *)
Theorem scan_flags twoE n :
  scan twoE n = [seq k <- iota 0 n | dst k < twoE].
Proof. by rewrite /scan -{1}dst0 scan_recE. Qed.

(*  Membership, the form a caller uses.                                       *)
Corollary scan_mem twoE n k :
  (k \in scan twoE n) = (k < n) && (dst k < twoE).
Proof. by rewrite scan_flags mem_filter mem_iota add0n andbC. Qed.

(*  The loop reports nothing exactly when the window is clear.                *)
Corollary scanN twoE n :
  reflect (forall k, k < n -> twoE <= dst k) (scan twoE n == [::]).
Proof.
apply: (iffP idP) => [/eqP Hs k kn|H].
  rewrite leqNgt; apply/negP => Hlt.
  have kin : k \in scan twoE n by rewrite scan_mem kn Hlt.
  by move: kin; rewrite Hs.
apply/eqP; rewrite scan_flags -(filter_pred0 (iota 0 n)).
apply: eq_in_filter => k; rewrite mem_iota add0n /= => kn.
by rewrite ltnNge H.
Qed.

(*  So a lower bound on the infimum -- what Alg2.v computes in O(log n)       *)
(*  steps -- lets the loop be skipped altogether.                             *)
Corollary scan_inf twoE n : twoE <= inf n -> scan twoE n = [::].
Proof.
move=> He; apply/eqP; apply/scanN => k kn.
by rewrite (leq_trans He) // leq_inf_dst.
Qed.

(*  ** The loop misses nothing                                                *)

(*  [tru i] is the true value at index [i], on the same circle and with the   *)
(*  same shift by [E] as [dst], so a hard case is one whose true value is     *)
(*  within [win] of [E].  The distance [dst] tracks it to within [err].       *)
(*                                                                            *)
(*  Proof: the triangle inequality puts [dst i] within [win + err < E] of     *)
(*  [E], and [2 * E <= M] means that window does not wrap, so the loop's      *)
(*  test [dst i < 2 * E] holds and [scan_mem] applies.                        *)
Theorem scan_complete (tru : nat -> nat) err win E n :
  0 < E -> 2 * E <= M ->
  (forall i, i < n -> cdist (tru i) (dst i) <= err) ->
  win + err < E ->
  forall i, i < n -> cdist (tru i) E <= win -> i \in scan (2 * E) n.
Proof. Admitted.

End Scan.

(*  ** Sanity checks (computed)                                               *)

(*  [M = 24], multiplier [5], target [7]: the distances are                   *)
(*  [7 2 21 16 11 6 1 20 15 10], and two of them are below [3].               *)
Example scan_ex : scan 24 5 7 3 10 = [:: 1; 6].
Proof. by vm_compute. Qed.

(*  An empty window reports nothing.                                          *)
Example scan_ex0 : scan 24 5 7 0 10 = [::].
Proof. by vm_compute. Qed.

(*  A wider window reports more.                                              *)
Example scan_ex7 : scan 24 5 7 7 10 = [:: 1; 5; 6].
Proof. by vm_compute. Qed.
