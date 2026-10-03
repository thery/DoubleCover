(** * What exp100.c computes, on the reals

    [exp_encl_Z] and [maybe_hard_Z] are exp100.c as functions on Z
    (ExpModel.v); [xreal xb] is the double of the bits [xb]. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From ExpTableKL Require Import ExpCheck ExpHard.
From Exp100 Require Import ExpConsts ExpModel ExpBits ExpBound ExpFilter.

Open Scope R_scope.

(** [exp_encl_bits] returns 0: an enclosure of exp x. *)
Theorem exp_encl_ok xb M s : (0 <= xb < 2 ^ 64)%Z ->
  exp_encl_Z xb = inr (M, s) ->
  Rabs (exp (xreal xb) - IZR M * bpow radix2 s) <= IZR D * bpow radix2 s.
Proof.
intros Hxb; unfold exp_encl_Z.
destruct (core_Z xb) as [rc|[y hN]] eqn:Hc; [discriminate|].
intros Heq.
apply (f_equal (fun t : Z + Z * Z =>
  match t with inl _ => (0%Z, 0%Z) | inr p => p end)) in Heq.
cbv beta iota in Heq; apply pair_equal_spec in Heq; destruct Heq as [<- <-].
apply (core_bound xb); auto.
apply xreal_is_x; auto.
destruct (Z.leb_spec be_big (xbexp xb)) as [Hb|Hb]; auto.
unfold core_Z in Hc; rewrite (proj2 (Z.leb_le _ _) Hb) in Hc; discriminate.
Qed.

(** [maybe_hard_bits] returns 0: x is not hard. *)
Theorem maybe_hard_ok xb : (0 <= xb < 2 ^ 64)%Z ->
  maybe_hard_Z xb = 0%Z -> ~ hard (xreal xb).
Proof.
intros Hxb; unfold maybe_hard_Z.
destruct (core_Z xb) as [rc|[y hN]] eqn:Hc; [discriminate|].
intros Hd [k Hk].
assert (Hbe : (xbexp xb < be_big)%Z).
{ destruct (Z.leb_spec be_big (xbexp xb)) as [Hb|Hb]; auto.
  unfold core_Z in Hc; rewrite (proj2 (Z.leb_le _ _) Hb) in Hc;
  discriminate. }
pose proof (core_bound xb y hN (xreal xb) Hxb Hc (xreal_is_x xb Hxb Hbe))
  as Hb.
pose proof (decide_ok y hN _ Hd Hb k) as Hk'.
unfold vof in Hk; lra.
Qed.
