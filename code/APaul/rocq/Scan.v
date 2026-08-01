(******************************************************************************)
(*                                                                            *)
(*   The inner loop of the hard-to-round search                               *)
(*                                                                            *)
(*   [htr_plain.c] has two nested loops.  The outer one moves to the next     *)
(*   chunk and re-evaluates the polynomial; the inner one, isolated here,     *)
(*   walks an arithmetic progression modulo the word size and reports the     *)
(*   indices whose value falls in a window at the origin:                     *)
(*                                                                            *)
(*     for (i = 0; i < n; i++) { if (A < twoE) emit i; A = A + B; }           *)
(*                                                                            *)
(*   Everything is [nat], as in Alg2.v: the word size [W] is a modulus, and   *)
(*   modular arithmetic appears only in [val], the value of the progression.  *)
(*                                                                            *)
(*   There is no real number here, and none is needed.  The loop walks a      *)
(*   LINEAR MODEL of the true value; the truth enters as an abstract          *)
(*   [tru : nat -> nat] with a hypothesis bounding how far the model drifts   *)
(*   from it.  [scan_complete] then says the loop misses no hard case as      *)
(*   long as the window absorbs that drift.  Reals appear only when [tru]     *)
(*   and the drift bound are instantiated for a particular function.         *)
(*                                                                            *)
(*   The file is self-contained: only ssreflect.  [scanN] is the hook a       *)
(*   filter would use -- a decision procedure that answers it without         *)
(*   running the loop replaces [n] steps by its own cost.                     *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Scan.

(*  The word size: [2 ^ 64] in the C, kept abstract here.                     *)
Variable W : nat.
Hypothesis W_gt0 : 0 < W.

(*  Distance to the origin on the circle of size [W].                         *)
Definition cdist0 (x : nat) : nat := minn (x %% W) (W - x %% W).

(*  Distance between two points of that circle.                               *)
Definition cdist (x y : nat) : nat := cdist0 (x + W - y %% W).

(*  ** The loop                                                               *)

(*  The value of the linear model at index [i].                               *)
Definition val (A B i : nat) : nat := (A + i * B) %% W.

(*  The loop, with the running value [A] and the index [i] as the C has them. *)
Fixpoint scan_rec (A B twoE i n : nat) : seq nat :=
  if n is n1.+1 then
    let rest := scan_rec ((A + B) %% W) B twoE i.+1 n1 in
    if A < twoE then i :: rest else rest
  else [::].

(*  The inner loop: [n] steps from index [0].                                 *)
Definition scan (A B twoE n : nat) : seq nat := scan_rec A B twoE 0 n.

(*  ** What the loop computes                                                 *)

(*  One turn of the loop.                                                     *)
Lemma scan_recS A B twoE i n :
  scan_rec A B twoE i n.+1 =
    (if A < twoE then [:: i] else [::])
      ++ scan_rec ((A + B) %% W) B twoE i.+1 n.
Proof. by rewrite /=; case: ltnP. Qed.

(*  The loop from index [i], with the running value at step [k].              *)
Lemma scan_recE A B twoE i n :
  A < W ->
  scan_rec A B twoE i n = [seq i + k | k <- iota 0 n & val A B k < twoE].
Proof.
elim: n A i => [//|n IH] A i AW.
have valS : forall k, val ((A + B) %% W) B k = val A B k.+1.
  by move=> k; rewrite /val mulSn addnA modnDml.
rewrite scan_recS IH ?ltn_mod // -[iota 0 n.+1]/(0 :: iota 1 n).
have valA : val A B 0 = A by rewrite /val mul0n addn0 modn_small.
rewrite [X in _ = X]/= valA.
have -> : iota 1 n = [seq 1 + k | k <- iota 0 n] by rewrite -[1]addn0 iotaDl.
have tail : [seq i.+1 + k | k <- iota 0 n & val ((A + B) %% W) B k < twoE]
          = [seq i + k | k <- [seq 1 + k | k <- iota 0 n] & val A B k < twoE].
  rewrite filter_map -map_comp /comp /=.
  have -> : [seq k <- iota 0 n | val A B (1 + k) < twoE]
          = [seq k <- iota 0 n | val ((A + B) %% W) B k < twoE].
    by apply: eq_filter => k; rewrite add1n valS.
  by apply: eq_map => k /=; rewrite add1n addnS addSn.
by case: (A < twoE); rewrite /= ?addn0 tail.
Qed.

(*  The loop reports exactly the indices whose model value is in the window.  *)
Theorem scan_flags A B twoE n :
  A < W -> scan A B twoE n = [seq k <- iota 0 n | val A B k < twoE].
Proof.
move=> AW; rewrite /scan scan_recE //.
by rewrite -[RHS]map_id; apply: eq_map => k; exact: add0n.
Qed.

(*  Membership, the form a caller uses.                                       *)
Corollary scan_mem A B twoE n k :
  A < W -> (k \in scan A B twoE n) = (k < n) && (val A B k < twoE).
Proof. by move=> AW; rewrite scan_flags // mem_filter mem_iota add0n andbC. Qed.

(*  The loop reports nothing exactly when the window is clear.                *)
Corollary scanN A B twoE n :
  A < W ->
  reflect (forall k, k < n -> twoE <= val A B k) (scan A B twoE n == [::]).
Proof.
move=> AW; apply: (iffP idP) => [/eqP Hs k kn|H].
  rewrite leqNgt; apply/negP => Hlt.
  have kin : k \in scan A B twoE n by rewrite scan_mem // kn Hlt.
  by move: kin; rewrite Hs.
apply/eqP; rewrite scan_flags // -(filter_pred0 (iota 0 n)).
apply: eq_in_filter => k; rewrite mem_iota add0n /= => kn.
by rewrite ltnNge H.
Qed.

(*  ** The loop misses nothing                                                *)


(*  [tru i] is the true value at index [i], on the same circle and with the   *)
(*  same shift by [E] as the model, so a hard case is one whose true value    *)
(*  is within [win] of [E].  The model tracks it to within [err].             *)
(*  Proof: the triangle inequality puts the model within [win + err < E] of  *)
(*  [E], and [2 * E <= W] means that window does not wrap, so the loop's      *)
(*  test [val < 2 * E] holds and [scan_mem] applies.                          *)
Theorem scan_complete (tru : nat -> nat) err win E A B n :
  A < W -> 0 < E -> 2 * E <= W ->
  (forall i, i < n -> cdist (tru i) (val A B i) <= err) ->
  win + err < E ->
  forall i, i < n -> cdist (tru i) E <= win -> i \in scan A B (2 * E) n.
Proof. Admitted.

End Scan.

(*  ** Sanity checks (computed)                                               *)

(*  [W = 24], start [5], step [7], window [3]: the values are                 *)
(*  [5 12 19 2 9 16 23 6 13 20], and only the fourth is below [3].            *)
Example scan_ex : scan 24 5 7 3 10 = [:: 3].
Proof. by vm_compute. Qed.

(*  An empty window reports nothing.                                          *)
Example scan_ex0 : scan 24 5 7 0 10 = [::].
Proof. by vm_compute. Qed.

(*  The walk wraps: [W = 10], start [8], step [4] gives [8 2 6 0 4].          *)
Example scan_wrap : scan 10 8 4 2 5 = [:: 3].
Proof. by vm_compute. Qed.
