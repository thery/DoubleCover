(** * tstep: one step of the table

    The loop invariant is the one of the VST proof (tstep_inv of
    ../../../vst/Verif_tstep.v): after t rounds, coefficients 0 .. t-1
    are the sums of two neighbours of the start, modulo 2^(64 l), and
    the words from t l on are those of the start.  add is used through
    its statement. *)

From APaulRocq Require Import HtrDefs.
From compcert Require Import CaplaProof.
Require Import HtrFilterCapla.htr_filter HtrFilterCapla.HtrWords.
Require Import HtrFilterCapla.WordLemmas HtrFilterCapla.Specs.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(* One round: coefficient t becomes the sum of t and t + 1. *)
Lemma tstep_round (n : nat) (B0 B1 B2 : {ffun 'I_n -> int64}) (L K t : nat) :
  (t.+1 < K)%nat ->
  (forall p, (p < t)%nat -> coefA B1 L p =
     (coefA B0 L p + coefA B0 L p.+1) mod baseZ (Z.of_nat L)) ->
  (forall q : 'I_n, (t * L <= q)%nat -> B1 q = B0 q) ->
  segv B2 (t * L) L =
    (segv B1 (t * L) L + segv B1 (t.+1 * L) L) mod baseZ (Z.of_nat L) ->
  (forall q : 'I_n, (q < t * L \/ t * L + L <= q)%nat -> B2 q = B1 q) ->
  (forall p, (p < t.+1)%nat -> coefA B2 L p =
     (coefA B0 L p + coefA B0 L p.+1) mod baseZ (Z.of_nat L)) /\
  (forall q : 'I_n, (t.+1 * L <= q)%nat -> B2 q = B0 q).
Proof.
  move=> Ht Hc Hfr Hs Hf; split; last first.
  { move=> q Hq; rewrite Hf; [by right; nia | by apply: Hfr; nia]. }
  move=> p; rewrite ltnS leq_eqVlt => /orP [/eqP ->|Hp].
  - rewrite /coefA Hs.
    have -> : segv B1 (t * L) L = coefA B0 L t.
      by apply: (coefA_ext B0 B1) => q Hq; apply: Hfr; lia.
    have -> : segv B1 (t.+1 * L) L = coefA B0 L t.+1.
      by apply: (coefA_ext B0 B1) => q Hq; apply: Hfr; nia.
    by [].
  - rewrite -Hc //; apply: coefA_ext => q Hq; apply: Hf; left.
    have : (p.+1 * L <= t * L)%nat by rewrite leq_mul2r Hp orbT.
    lia.
Qed.

(* At the end, t = k - 1: the coefficients of tstepZ. *)
Lemma tstep_final (n : nat) (B0 B1 : {ffun 'I_n -> int64}) (L K : nat) :
  (0 < K)%nat ->
  (forall p, (p < K.-1)%nat -> coefA B1 L p =
     (coefA B0 L p + coefA B0 L p.+1) mod baseZ (Z.of_nat L)) ->
  (forall q : 'I_n, (K.-1 * L <= q)%nat -> B1 q = B0 q) ->
  coefsA B1 L K =
    [seq z mod baseZ (Z.of_nat L) | z <- tstepZ (coefsA B0 L K)].
Proof.
  move=> HK Hc Hfr.
  apply: (@eq_from_nth _ 0); first by rewrite size_map size_tstepZ; rewrite !size_coefsA.
  rewrite size_coefsA => p Hp.
  rewrite (nth_map 0) ?size_tstepZ ?size_coefsA // nth_coefsA //.
  case: (ltnP p.+1 K) => Hp1.
  - rewrite nth_tstepZ ?size_coefsA //; rewrite !nth_coefsA //; rewrite Hc //; lia.
  - have Ep : p = K.-1 by lia.
    rewrite nth_tstepZ_last; first by rewrite size_coefsA; lia.
    rewrite nth_coefsA //; rewrite Zmod_small; first exact: coefA_bound.
    apply: coefA_ext => q Hq; apply: Hfr; rewrite -Ep; lia.
Qed.

(* The indices of round t. *)
Lemma tstep_idx (t K L m : nat) : (t.+1 < K)%nat -> (K * L <= m)%nat ->
  (0 < L)%nat ->
  (t < m)%nat /\ (t * L <= m)%nat /\ (t.+1 * L <= m)%nat /\
  (t * L + L <= m)%nat /\ (t.+1 * L + L <= m)%nat /\
  (t * L + L <= t.+1 * L)%nat.
Proof. move=> H1 H2 H3; repeat split; nia. Qed.

Theorem tstep_ok : add_spec -> tstep_spec.
Proof.
  move=> AS μ mm m Hm B0 k l r rl K L HK HL HKL.
  subst mm.
  have Hm : (Z.of_nat m:N <= Int64.max_unsigned)%Z.
    by have := Int64.unsigned_range_2 m; lia.
  enter_func. csteps.
  inv I := { [:: B; t; _t_hi] } (fun (b : {ffun 'I_(m:N) -> int64}) (tt hi : int64) =>
    hi = Int64.sub k (Int64.repr 1) /\ (tt:N < K)%nat /\
    (forall p, (p < tt:N)%nat -> coefA b L p =
       (coefA B0 L p + coefA B0 L p.+1) mod baseZ (Z.of_nat L)) /\
    (forall q : 'I_(m:N), (tt:N * L <= q)%nat -> b q = B0 q)).
  enter_loop I.
  { prove_inv; exsp. }
  unfold_inv => - [_ [Ht [Hc Hfr]]].
  csteps.
  have Ek1 := sub1_nat k HK.
  case END: Int64.ltu => /=; move: (END); rewrite ltu_nat Ek1 => END'.
  - (* one round *)
    have Ht1 : ((t0:N).+1 < K)%nat by move: END'; rewrite /K; lia.
    have [I1 [I2 [I3 [I4 [I5 I6]]]]] := tstep_idx _ _ _ _ Ht1 HKL HL.
    have Et1 : (Int64.add t0 (Int64.repr 1)):N = (t0:N).+1.
      by apply: (add1_nat _ (m:N)).
    have Emt : (Int64.mul t0 l):N = (t0:N * L)%nat.
      by apply: (mul_nat _ _ (m:N)).
    have Emt1 : (Int64.mul (Int64.add t0 (Int64.repr 1)) l):N = ((t0:N).+1 * L)%nat.
      by rewrite (mul_nat _ _ (m:N)); rewrite ?Et1.
    csteps.
    call AS; rewrite Emt Emt1 => /(_ erefl I4 I5 (or_introl I6)).
    move=> [B2 [-> [Hs Hf]]].
    have [R1 R2] := tstep_round _ B0 B1 B2 L K _ Ht1 Hc Hfr Hs Hf.
    csteps; cret; split=> // _; split.
    { solve_loop_conditions. }
    prove_inv; exsp; rewrite ?Et1 //.
  - (* the loop ends with t = k - 1 *)
    csteps; cret; split=> //= _; csteps; cret.
    have Et : t0:N = K.-1 by move: END' Ht; rewrite /K; lia.
    exists B1; split; first by rewrite/envC/=.
    rewrite Et in Hc Hfr; split; first exact: tstep_final.
    by move=> q Hq; apply: Hfr; apply: leq_trans Hq; rewrite leq_mul2r leq_pred orbT.
Qed.
