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

(*  [cdist0] only sees its argument modulo [M].                               *)
Lemma cdist0_mod x y : x = y %[mod M] -> cdist0 x = cdist0 y.
Proof. by move=> H; rewrite /cdist0 H. Qed.

(*  It is subadditive.                                                        *)
Lemma cdist0D x y : cdist0 (x + y) <= cdist0 x + cdist0 y.
Proof.
rewrite /cdist0 -modnDm.
set a := x %% M; set b := y %% M.
have aM : a < M by rewrite ltn_mod.
have bM : b < M by rewrite ltn_mod.
have aM' : a <= M := ltnW aM.
have bM' : b <= M := ltnW bM.
case: (ltnP (a + b) M) => [ab|ab].
  rewrite (modn_small ab).
  case: (leqP a (M - a)) => ha; case: (leqP b (M - b)) => hb.
  - by rewrite geq_minl.
  - rewrite (leq_trans (geq_minr _ _)) //.
    by rewrite (leq_trans (leq_sub2l M (leq_addl a b))) // leq_addl.
  - rewrite (leq_trans (geq_minr _ _)) //.
    by rewrite (leq_trans (leq_sub2l M (leq_addr b a))) // leq_addr.
  rewrite (leq_trans (geq_minr _ _)) //.
  by rewrite (leq_trans (leq_sub2l M (leq_addr b a))) // leq_addr.
have abM : a + b < M + M.
  by rewrite (leq_ltn_trans (leq_add aM' (leqnn b))) // ltn_add2l.
have cE : (a + b) %% M = a + b - M.
  by rewrite -{1}(subnK ab) modnDr modn_small // ltn_subLR.
rewrite cE.
case: (leqP a (M - a)) => ha; case: (leqP b (M - b)) => hb.
- by rewrite (leq_trans (geq_minl _ _)) // leq_subr.
- rewrite (leq_trans (geq_minl _ _)) // leq_subLR.
  by rewrite addnCA leq_add2l (leq_trans bM') // leq_addr.
- rewrite (leq_trans (geq_minl _ _)) // leq_subLR.
  by rewrite addnA leq_add2r (leq_trans aM') // leq_addr.
have -> : M - (a + b - M) = M + M - (a + b) by rewrite subnBA.
have -> : M - a + (M - b) = M + M - (a + b).
  by rewrite addnBAC // addnBA // subnDA subnAC.
by rewrite geq_minr.
Qed.

(*  Hence the triangle inequality.                                            *)
Lemma cdistD x y z : cdist x z <= cdist x y + cdist y z.
Proof.
have yM : y %% M <= M by rewrite ltnW // ltn_mod.
have zM : z %% M <= M by rewrite ltnW // ltn_mod.
have yMx : y %% M <= x + M by rewrite (leq_trans yM) // leq_addl.
have yy : y %% M <= y by rewrite leq_mod.
have yD : y - y %% M = y %/ M * M by rewrite {1}(divn_eq y M) addnK.
have step1 : x + M - y %% M + y = x + M + (y %/ M * M).
  by rewrite -yD addnBAC // addnBA.
have key : (x + M - y %% M) + (y + M - z %% M)
         = (x + M - z %% M) + (y %/ M * M + M).
  rewrite addnBA; last by rewrite (leq_trans zM) // leq_addl.
  by rewrite addnA step1 addnBAC ?(leq_trans zM) ?leq_addl // !addnA.
rewrite /cdist -(cdist0_mod (x := (x + M - y %% M) + (y + M - z %% M))).
  exact: cdist0D.
by rewrite key [y %/ M * M + M]addnC -mulSn addnC modnMDl.
Qed.

(*  Within [E] of [E] means inside the window [[0, 2E)].                      *)
Lemma cdist_win x E :
  x < M -> 2 * E <= M -> cdist x E < E -> x < 2 * E.
Proof.
move=> xM EM2 Hlt.
case: (ltnP x E) => [xE|Ex]; first by rewrite (leq_trans xE) // leq_pmull.
have E_gt0 : 0 < E by case: (posnP E) Hlt => [->|//]; rewrite ltn0.
have EM : E < M by rewrite (leq_trans _ EM2) // ltn_Pmull.
have xEM : x - E < M by rewrite (leq_ltn_trans (leq_subr _ _)).
move: Hlt; rewrite /cdist (modn_small EM).
have -> : x + M - E = (x - E) + M by rewrite addnBAC.
rewrite /cdist0 modnDr (modn_small xEM).
case: (leqP (x - E) (M - (x - E))) => h.
  by move=> H; rewrite -(subnK Ex) mul2n -addnn ltn_add2r.
rewrite ltn_subLR; last exact: ltnW xEM.
rewrite (subnK Ex) => H.
by move: (ltn_trans xM H); rewrite ltnn.
Qed.


(*  [tru i] is the true value at index [i], on the same circle and with the   *)
(*  same shift by [E] as [dst], so a hard case is one whose true value is     *)
(*  within [win] of [E].  The distance [dst] tracks it to within [err].       *)
(*                                                                            *)
(*  Proof: the triangle inequality puts [dst i] within [win + err < E] of     *)
(*  [E], and [2 * E <= M] means that window does not wrap, so the loop's      *)
(*  test [dst i < 2 * E] holds and [scan_mem] applies.                        *)
Theorem scan_complete (tru : nat -> nat) err win E n :
  0 < E -> 2 * E <= M ->
  (forall i, i < n -> cdist (dst i) (tru i) <= err) ->
  win + err < E ->
  forall i, i < n -> cdist (tru i) E <= win -> i \in scan (2 * E) n.
Proof.
move=> E_gt0 EM2 Herr Hwin i iLn Hhard.
rewrite scan_mem iLn /=.
apply: cdist_win => //; first by rewrite ltn_dst.
apply: leq_ltn_trans (cdistD _ (tru i) _) _.
apply: leq_ltn_trans (leq_add (Herr i iLn) Hhard) _.
by rewrite addnC.
Qed.

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
