(** * Zimmermann's search (doc/htr.md): the scan of one subrange

    On a subrange of [n] consecutive doubles [x0 + j u], the note replaces
    [exp(x0 + j u) / v] by an integer polynomial in [j],
      [P j = A_0 + A_1 j + ... + A_(k-1) j^(k-1)],
    whose coefficients are the [A_i] of the note, and walks it with the
    table of differences of [Shift.v].  A [j] is a candidate when
    [(P j + E) mod M <= 2 E], with [M = beta^l].

    This file states the algorithm over the integers and proves the
    part that does not depend on [exp]:
    - [scanE]: the walk returns exactly the [j < n] passing the test;
    - [scan_complete]: every [j] with [P j] within [E] of a multiple of
      [M] is returned.
    The link to [exp] is in [TaylorReal.v] and [TaylorLink.v]. *)

From mathcomp Require Import all_ssreflect all_algebra.
From APaulRocq Require Import Shift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Scan.

(** The data of a subrange: the [A_i], least significant first, the
    modulus [M = beta^l], the window [E], and the number of doubles. *)
Variables (A : seq int) (M E : int) (n : nat).

(** The polynomial, in Horner form. *)
Definition P : nat -> int := hpoly A.

(** Its degree is at most [size A], so a table of [size A + 1] entries walks
    it exactly (the note uses [size A] entries: the last one here is [0]). *)
Definition dg := size A.

Lemma is_polyCb_P : is_poly C_basis dg P.
Proof. exact: is_polyCb_hpoly. Qed.

(** The test on the first entry of the table: steps 5 and 6 of the note. *)
Definition hit (b : int) : bool := ((b + E) %% M)%Z <= E *+ 2.

(** The main loop, step 6: test the first entry, then shift the table. *)
Fixpoint walk (j : nat) (t : seq int) (c : nat) : seq nat :=
  if c is c'.+1 then
    let rest := walk j.+1 (tstep t) c' in
    if hit (nth 0 t 0) then j :: rest else rest
  else [::].

(** The search: the table at [0], steps 3 and 4, then the walk. *)
Definition scan : seq nat := walk 0 (dtab dg P 0) n.

(** The walk returns exactly the [j] in [[i, i + c)] whose [P j] passes
    the test. *)
Lemma walkE i c : walk i (dtab dg P i) c = [seq j <- iota i c | hit (P j)].
Proof.
elim: c i => [//|c IH] i /=.
rewrite tstepE; last exact: is_polyCb_P.
by rewrite IH.
Qed.

Lemma scanE : scan = [seq j <- iota 0 n | hit (P j)].
Proof. exact: walkE. Qed.

(** If [b] is within [E] of a multiple [M w] of [M], and [2 E < M], then
    [b] passes the test: [(b + E) mod M] is [b - M w + E], in [[0, 2 E]]. *)
Lemma hitP (b w : int) : E *+ 2 < M -> `|b - M * w| <= E -> hit b.
Proof.
move=> EM; rewrite ler_norml => /andP[l r].
have lo : 0 <= b - M * w + E by rewrite -lerBlDr sub0r.
have hi : b - M * w + E < M.
  by apply: Order.POrderTheory.le_lt_trans EM; rewrite mulr2n lerD2r.
rewrite /hit.
have -> : b + E = w * M + (b - M * w + E).
  by rewrite [w * M]mulrC addrA [M * w + _]addrC subrK.
rewrite modzMDl modz_small ?lo ?hi //.
by rewrite mulr2n lerD2r.
Qed.

(** The completeness of the scan, with no reference to [exp]. *)
Theorem scan_complete j (w : int) :
  E *+ 2 < M -> (j < n)%N -> `|P j - M * w| <= E -> j \in scan.
Proof.
move=> EM jn Pw.
by rewrite scanE mem_filter (hitP EM Pw) /= mem_iota /= add0n.
Qed.

End Scan.

(** The step from [exp] to the hypothesis of [scan_complete] is
    [TaylorReal.real_lemma]; [TaylorLink.scan_exp] puts the two
    together. *)
