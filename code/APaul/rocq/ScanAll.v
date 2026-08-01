(******************************************************************************)
(*                                                                            *)
(*   The outer loop of the hard-to-round search                               *)
(*                                                                            *)
(*   [htr_plain.c] has two nested loops.  The inner one is [Scan.v]; the      *)
(*   outer one, here, cuts the interval into chunks of [n] points, takes      *)
(*   fresh data from the polynomial at each chunk start and runs one inner    *)
(*   scan there:                                                              *)
(*                                                                            *)
(*     while (X < X1NUM) { seeds from poly_eval (X - CCNUM); scan; X += n; }  *)
(*                                                                            *)
(*   The seeds are the abstract [Ac], [Bc], [Ec], one triple per chunk:       *)
(*   nothing in the loop depends on how the polynomial produces them.  An     *)
(*   index is global, [j = k * n + i] for the point [i] of chunk [k].         *)
(*                                                                            *)
(*   [scanAll_flags] says the loop reports exactly the indices whose          *)
(*   distance falls in the window of their own chunk, [scanAll_complete]      *)
(*   that it misses no hard case.  As in [Scan.v] the truth is an abstract    *)
(*   [tru : nat -> nat] and the drift a [nat] bound, so no real number        *)
(*   appears; reals enter only where [tru] and that bound are instantiated.   *)
(*                                                                            *)
(*   [chunks d] is the number of turns the C takes over [d] points.  They     *)
(*   cover the interval ([leq_chunks]), the last one running past its end     *)
(*   by fewer than [n] points ([ltn_chunks]), which only adds candidates.     *)
(*                                                                            *)
(*   The C screens each candidate on the spot rather than accumulating a      *)
(*   chunk's worth of them; [scanAll_with] is the loop with that screen,      *)
(*   and [scanAll_with_complete] says completeness survives it as long as     *)
(*   the screen keeps the hard cases of the chunk it is given.                *)
(*                                                                            *)
(*   [scanAll_coh] reads the reindexing the other way: when the seeds         *)
(*   continue one and the same walk -- the shape the polynomial ones are      *)
(*   meant to have -- the whole run IS the flat inner scan over [c * n]       *)
(*   points.                                                                  *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.
From APaulRocq Require Import Dist Scan.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ScanAll.

(*  The modulus: the word in which the C keeps its running value.             *)
Variable M : nat.
Hypothesis M_gt0 : 0 < M.

(*  One chunk is [n] consecutive points of the grid.                          *)
Variable n : nat.
Hypothesis n_gt0 : 0 < n.

(*  What the polynomial gives at the start of chunk [k]: the multiplier,      *)
(*  the target and the half-window.                                           *)
Variables Ac Bc Ec : nat -> nat.
Hypothesis ltn_Bc : forall k, Bc k < M.

(*  ** The loop                                                               *)

(*  The chunk a global index belongs to.                                      *)
Definition chk (j : nat) : nat := j %/ n.

(*  Its position inside that chunk.                                           *)
Definition fne (j : nat) : nat := j %% n.

(*  The test the C applies at the global index [j].                           *)
Definition hit (j : nat) : bool :=
  dst M (Ac (chk j)) (Bc (chk j)) (fne j) < 2 * Ec (chk j).

(*  The candidates of chunk [k], as global indices.                           *)
Definition chunk (k : nat) : seq nat :=
  [seq k * n + i | i <- scan M (Ac k) (Bc k) (2 * Ec k) n].

(*  The loop, with the chunk index [k] and the number [c] of turns left.      *)
Fixpoint scanAll_rec (k c : nat) : seq nat :=
  if c is c1.+1 then chunk k ++ scanAll_rec k.+1 c1 else [::].

(*  The outer loop: [c] chunks, from the first one.                           *)
Definition scanAll (c : nat) : seq nat := scanAll_rec 0 c.

(*  ** What the loop computes                                                 *)

(*  A point of chunk [k] has [k] for chunk...                                 *)
Lemma chkE k i : i < n -> chk (k * n + i) = k.
Proof. by move=> iLn; rewrite /chk divnMDl // divn_small // addn0. Qed.

(*  ...and its offset for position.                                           *)
Lemma fneE k i : i < n -> fne (k * n + i) = i.
Proof. by move=> iLn; rewrite /fne modnMDl modn_small. Qed.

(*  So on chunk [k] the global test is that chunk's own test.                 *)
Lemma hitE k i : i < n -> hit (k * n + i) = (dst M (Ac k) (Bc k) i < 2 * Ec k).
Proof. by move=> iLn; rewrite /hit chkE // fneE. Qed.

(*  One turn reports exactly the indices of its own window.                   *)
Lemma chunkE k : chunk k = [seq j <- iota (k * n) n | hit j].
Proof.
rewrite /chunk (scan_flags M_gt0 _ (ltn_Bc k)).
rewrite -{2}[k * n]addn0 iotaDl filter_map.
congr (map _ _); apply: eq_in_filter => i.
by rewrite mem_iota add0n /= => iLn; rewrite /preim /= hitE.
Qed.

(*  From chunk [k], the loop reports the indices of the windows it meets.     *)
Lemma scanAll_recE k c :
  scanAll_rec k c = [seq j <- iota (k * n) (c * n) | hit j].
Proof.
elim: c k => [k|c IH k]; first by rewrite mul0n.
rewrite /= chunkE IH [c.+1 * n]mulSn iotaD filter_cat.
by rewrite [k.+1 * n]mulSn addnC.
Qed.

(*  Correctness: the loop reports exactly the indices in their windows.       *)
Theorem scanAll_flags c : scanAll c = [seq j <- iota 0 (c * n) | hit j].
Proof. by rewrite /scanAll scanAll_recE mul0n. Qed.

(*  Membership, the form a caller uses.                                       *)
Corollary scanAll_mem c j : (j \in scanAll c) = (j < c * n) && hit j.
Proof. by rewrite scanAll_flags mem_filter mem_iota add0n andbC. Qed.

(*  A single turn is the inner loop itself: the reindexing is the identity.   *)
Lemma scanAll1 : scanAll 1 = scan M (Ac 0) (Bc 0) (2 * Ec 0) n.
Proof.
rewrite /scanAll /= /chunk cats0 -[RHS]map_id.
by apply: eq_map => i; rewrite mul0n.
Qed.

(*  The loop reports nothing exactly when every window is clear.              *)
Corollary scanAllN c :
  reflect (forall j, j < c * n -> ~~ hit j) (scanAll c == [::]).
Proof.
apply: (iffP idP) => [/eqP Hs j jLcn|H].
  apply/negP => Hlt.
  have jin : j \in scanAll c by rewrite scanAll_mem jLcn Hlt.
  by move: jin; rewrite Hs.
apply/eqP; rewrite scanAll_flags -(filter_pred0 (iota 0 (c * n))).
apply: eq_in_filter => j; rewrite mem_iota add0n /= => jLcn.
by apply/negbTE/H.
Qed.

(*  So a lower bound on each chunk's infimum -- what Alg2.v computes in       *)
(*  O(log n) steps -- lets every turn of the loop be skipped.                 *)
Corollary scanAll_inf c :
  (forall k, k < c -> 2 * Ec k <= inf_dst M (Ac k) (Bc k) n) ->
  scanAll c = [::].
Proof.
move=> Hinf; apply/eqP; apply/scanAllN => j jLcn.
have kLc : chk j < c by rewrite /chk ltn_divLR.
rewrite /hit -leqNgt (leq_trans (Hinf _ kLc)) // leq_inf_dst //.
by rewrite /fne ltn_mod.
Qed.

(*  ** The loop misses nothing                                                *)

(*  [tru j] is the true value at the global index [j], read as [Scan.v]       *)
(*  reads it: on the circle of size [M] and shifted by the window, so a       *)
(*  hard case is one whose true value is within [win] of its own chunk's      *)
(*  [Ec].  Each chunk tracks it to within [err].                              *)
(*                                                                            *)
(*  Proof: a global index splits as [chk j * n + fne j] with [chk j] a        *)
(*  chunk of the run and [fne j] a point of it, so the chunk's own            *)
(*  [Scan.scan_complete] applies and [scanAll_mem] lifts it.                  *)
Theorem scanAll_complete (tru : nat -> nat) err win c :
  (forall k, k < c -> 0 < Ec k) ->
  (forall k, k < c -> 2 * Ec k <= M) ->
  (forall k, k < c -> win + err < Ec k) ->
  (forall k i, k < c -> i < n ->
     cdist M (dst M (Ac k) (Bc k) i) (tru (k * n + i)) <= err) ->
  forall j, j < c * n -> cdist M (tru j) (Ec (chk j)) <= win ->
  j \in scanAll c.
Proof.
move=> HE HEM Hwin Herr j jLcn Hhard.
have kLc : chk j < c by rewrite /chk ltn_divLR.
have iLn : fne j < n by rewrite /fne ltn_mod.
have jE : chk j * n + fne j = j by rewrite /chk /fne -divn_eq.
have Hhard' : cdist M (tru (chk j * n + fne j)) (Ec (chk j)) <= win.
  by rewrite jE.
have Hin := scan_complete M_gt0 (ltn_Bc (chk j))
  (tru := fun i => tru (chk j * n + i)) (win := win)
  (HE _ kLc) (HEM _ kLc) (fun i iLn' => Herr _ i kLc iLn') (Hwin _ kLc)
  iLn Hhard'.
move: Hin; rewrite (scan_mem M_gt0 _ (ltn_Bc (chk j))) => /andP[_ Hlt].
by rewrite scanAll_mem jLcn /hit.
Qed.

(*  ** Screening inside the loop                                              *)

(*  The C does not accumulate the candidates of a chunk: it screens each on   *)
(*  the spot.  [post] is that screen, run on one chunk's candidates.          *)
Fixpoint scanAll_with_rec (post : seq nat -> seq nat) (k c : nat) : seq nat :=
  if c is c1.+1 then post (chunk k) ++ scanAll_with_rec post k.+1 c1
  else [::].

(*  The screened outer loop.                                                  *)
Definition scanAll_with (post : seq nat -> seq nat) (c : nat) : seq nat :=
  scanAll_with_rec post 0 c.

(*  Screening by the identity is the plain loop.                              *)
Lemma scanAll_with_id c : scanAll_with id c = scanAll c.
Proof.
by rewrite /scanAll_with /scanAll; elim: c 0 => //= c IH k; rewrite IH.
Qed.

(*  A chunk reports an index iff that index is its own and passes the test.   *)
Lemma chunk_mem k j : (j \in chunk k) = (chk j == k) && hit j.
Proof.
rewrite chunkE mem_filter mem_iota andbC; congr (_ && _).
have -> : (chk j == k) = (k <= chk j) && (chk j < k.+1).
  by rewrite ltnS -eqn_leq eq_sym.
by rewrite /chk leq_divRL // ltn_divLR // mulSn addnC.
Qed.

(*  From chunk [k], an index is reported iff some chunk screens it in.        *)
Lemma scanAll_with_recE post k c j :
  (j \in scanAll_with_rec post k c) = has (fun i => j \in post (chunk i))
                                          (iota k c).
Proof. by elim: c k => [//|c IH] k; rewrite /= mem_cat IH. Qed.

(*  Membership, the form a caller uses.                                       *)
Lemma scanAll_with_mem post c j :
  (j \in scanAll_with post c) = has (fun k => j \in post (chunk k)) (iota 0 c).
Proof. exact: scanAll_with_recE. Qed.

(*  A screen that only removes reports nothing the plain loop would not.      *)
Lemma scanAll_with_sub post c :
  (forall l, {subset post l <= l}) -> {subset scanAll_with post c <= scanAll c}.
Proof.
move=> Hpost j; rewrite scanAll_with_mem => /hasP[k]; rewrite mem_iota add0n.
move=> /andP[_ kLc] /Hpost; rewrite chunk_mem => /andP[/eqP kE Hh].
move: kLc; rewrite -kE /chk ltn_divLR // => jLcn.
by rewrite scanAll_mem jLcn.
Qed.

(*  Completeness survives the screen: if [post] keeps every hard case of the  *)
(*  chunk it is given, the screened loop still misses none.                   *)
Theorem scanAll_with_complete post (tru : nat -> nat) err win c :
  (forall k, k < c -> 0 < Ec k) ->
  (forall k, k < c -> 2 * Ec k <= M) ->
  (forall k, k < c -> win + err < Ec k) ->
  (forall k i, k < c -> i < n ->
     cdist M (dst M (Ac k) (Bc k) i) (tru (k * n + i)) <= err) ->
  (forall k j, k < c -> j \in chunk k -> cdist M (tru j) (Ec (chk j)) <= win ->
     j \in post (chunk k)) ->
  forall j, j < c * n -> cdist M (tru j) (Ec (chk j)) <= win ->
  j \in scanAll_with post c.
Proof.
move=> HE HEM Hwin Herr Hpost j jLcn Hhard.
have kLc : chk j < c by rewrite /chk ltn_divLR.
have jin : j \in chunk (chk j).
  rewrite chunk_mem eqxx /=.
  by have := scanAll_complete HE HEM Hwin Herr jLcn Hhard;
     rewrite scanAll_mem jLcn.
rewrite scanAll_with_mem; apply/hasP; exists (chk j); last exact: Hpost.
by rewrite mem_iota add0n.
Qed.

(*  ** How many turns the loop takes                                          *)

(*  The C moves the chunk start by [n] until it passes the end of the         *)
(*  interval, so over [d] points it takes [ceil (d / n)] turns.               *)
Definition chunks (d : nat) : nat := (d + n - 1) %/ n.

(*  Those turns cover the interval...                                         *)
Lemma leq_chunks d : d <= chunks d * n.
Proof.
case: d => [//|d].
rewrite /chunks addSn subn1 /= addnC.
rewrite -[X in (X + d) %/ n]mul1n divnMDl // mulnDl mul1n.
by rewrite -mulSn ltn_ceil.
Qed.

(*  ...and the last one runs past its end, by fewer than [n] points.          *)
Lemma ltn_chunks d : chunks d * n < d + n.
Proof.
rewrite /chunks; case: d => [|d].
  by rewrite add0n divn_small ?mul0n // -{2}(subn0 n) ltn_sub2l.
rewrite addSn subn1 /=.
by rewrite (leq_ltn_trans (leq_divM _ _)) // addSn.
Qed.

(*  So the run over an interval of [d] points misses no hard case in it.      *)
Corollary scanAll_cover (tru : nat -> nat) err win d :
  (forall k, k < chunks d -> 0 < Ec k) ->
  (forall k, k < chunks d -> 2 * Ec k <= M) ->
  (forall k, k < chunks d -> win + err < Ec k) ->
  (forall k i, k < chunks d -> i < n ->
     cdist M (dst M (Ac k) (Bc k) i) (tru (k * n + i)) <= err) ->
  forall j, j < d -> cdist M (tru j) (Ec (chk j)) <= win ->
  j \in scanAll (chunks d).
Proof.
move=> HE HEM Hwin Herr j jLd Hhard.
apply: scanAll_complete HE HEM Hwin Herr _ _ Hhard.
by apply: leq_trans jLd (leq_chunks d).
Qed.

End ScanAll.

(*  ** Chunks of one and the same walk                                        *)

(*  Restarting the walk at the distance it has reached at [x] gives the same  *)
(*  distances from there on.                                                  *)
Lemma dst_restart M (M_gt0 : 0 < M) A B x y :
  dst M A (dst M A B x) y = dst M A B (x + y).
Proof. by rewrite dstE dstDE. Qed.

(*  So seeds that continue one and the same walk -- each chunk restarted at   *)
(*  the distance the previous ones reached -- make the outer loop the flat    *)
(*  inner loop over all [c * n] points: the reindexing loses and invents      *)
(*  nothing.  This is the shape the polynomial seeds are meant to have.       *)
Theorem scanAll_coh M n A B E c : 0 < M -> 0 < n -> B < M ->
  scanAll M n (fun _ => A) (fun k => dst M A B (k * n)) (fun _ => E) c
  = scan M A B (2 * E) (c * n).
Proof.
move=> M_gt0 n_gt0 ltn_B.
rewrite (scanAll_flags M_gt0 n_gt0 _ _ (fun k => ltn_dst M_gt0 A B (k * n))).
rewrite (scan_flags M_gt0 _ ltn_B).
apply: eq_filter => j.
rewrite /hit /chk /fne dst_restart //.
by rewrite -divn_eq.
Qed.

(*  ** Sanity checks (computed)                                               *)

(*  [M = 24], multiplier [5], target [7], chunks of [5] points: each chunk    *)
(*  restarts the walk at [7], so both report their index [1].                 *)
Example scanAll_ex :
  scanAll 24 5 (fun _ => 5) (fun _ => 7) (fun _ => 2) 2 = [:: 1; 6].
Proof. by vm_compute. Qed.

(*  A window of [0] reports nothing.                                          *)
Example scanAll_ex0 :
  scanAll 24 5 (fun _ => 5) (fun _ => 7) (fun _ => 0) 2 = [::].
Proof. by vm_compute. Qed.

(*  The window may differ from chunk to chunk: here only the second turn      *)
(*  has one wide enough.                                                      *)
Example scanAll_exk :
  scanAll 24 5 (fun _ => 5) (fun _ => 7) (fun k => k * 2) 2 = [:: 6].
Proof. by vm_compute. Qed.

(*  The same run with a screen that drops the first report.                   *)
Example scanAll_with_ex :
  scanAll_with 24 5 (fun _ => 5) (fun _ => 7) (fun _ => 2)
    (fun l => [seq j <- l | 1 < j]) 2 = [:: 6].
Proof. by vm_compute. Qed.

(*  Chunks of [5] points: [10] points take two turns, [11] take three.        *)
Example chunks_ex10 : chunks 5 10 = 2.
Proof. by vm_compute. Qed.

Example chunks_ex11 : chunks 5 11 = 3.
Proof. by vm_compute. Qed.
