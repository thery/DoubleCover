(** * difftab: the table of differences

    The loop invariants are those of the VST proof (body_difftab of
    ../../../vst/Verif_difftab.v), with [stage] of DiffPure.v.  Outer
    loop: after the passes 1 .. i-1, coefficient p is stage (i-1) p
    modulo 2^(64 l).  Inner loop (pass i, j going down from k-1):
    coefficient p is stage i p when p > j, stage (i-1) p otherwise.  The
    words from k l on are those of the start.  sub is used through its
    statement. *)

From APaulRocq Require Import HtrDefs.
From HtrFilterCapla Require Import DiffPure.
From compcert Require Import CaplaProof.
Require Import HtrFilterCapla.htr_filter HtrFilterCapla.HtrWords.
Require Import HtrFilterCapla.WordLemmas HtrFilterCapla.Specs.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(* mathcomp's map and iota are Stdlib's map and seq. *)
Lemma map_iota_seq (f : nat -> Z) s n :
  [seq f p | p <- iota s n] = List.map f (List.seq s n).
Proof. by elim: n s => [|n IH] s //=; rewrite IH. Qed.

(* The indices of the round j of pass i. *)
Lemma difftab_idx (i j K L m : nat) : (0 < i)%nat -> (i <= j)%nat ->
  (j < K)%nat -> (K * L <= m)%nat ->
  (j * L + L <= m)%nat /\ (j.-1 * L + L <= m)%nat /\
  (j.-1 * L + L <= j * L)%nat /\ (j * L <= m)%nat /\ (j.-1 * L <= m)%nat /\
  (j < m \/ L = 0)%nat.
Proof. move=> H1 H2 H3 H4; repeat split; nia. Qed.

(* One round of the inner loop: coefficient j becomes stage i j. *)
Lemma difftab_round (n : nat) (B1 B2 : {ffun 'I_n -> int64}) (x : nat -> Z)
    (L K i j : nat) :
  (0 < i)%nat -> (i <= j)%nat -> (j < K)%nat ->
  (forall p, (p < K)%nat -> coefA B1 L p =
     (if (j < p)%nat then stage x i p else stage x i.-1 p)
       mod baseZ (Z.of_nat L)) ->
  segv B2 (j * L) L =
    (segv B1 (j * L) L - segv B1 (j.-1 * L) L) mod baseZ (Z.of_nat L) ->
  (forall q : 'I_n, (q < j * L \/ j * L + L <= q)%nat -> B2 q = B1 q) ->
  forall p, (p < K)%nat -> coefA B2 L p =
     (if (j.-1 < p)%nat then stage x i p else stage x i.-1 p)
       mod baseZ (Z.of_nat L).
Proof.
  move=> Hi Hij Hj Hc Hs Hf p Hp.
  case: (ltngtP p j) => Epj.
  - (* p < j: coefficient p is left alone *)
    have Hm : (p.+1 * L <= j * L)%nat by rewrite leq_mul2r Epj orbT.
    rewrite (coefA_ext B1 B2).
      by move=> q Hq; apply: Hf; left; lia.
    rewrite (Hc p Hp).
    have -> : (j < p)%nat = false by apply/negbTE; rewrite -leqNgt ltnW.
    by have -> : (j.-1 < p)%nat = false by apply/negbTE; rewrite -leqNgt; lia.
  - (* p > j *)
    have Hm : (j.+1 * L <= p * L)%nat by rewrite leq_mul2r Epj orbT.
    rewrite (coefA_ext B1 B2).
      by move=> q Hq; apply: Hf; right; lia.
    rewrite (Hc p Hp) Epj.
    by have -> : (j.-1 < p)%nat by lia.
  - (* p = j: the difference *)
    subst p.
    have E : coefA B2 L j =
      (coefA B1 L j - coefA B1 L j.-1) mod baseZ (Z.of_nat L) by exact: Hs.
    have H1 := Hc j Hj.
    have H2 := Hc j.-1 (leq_ltn_trans (leq_pred j) Hj).
    have F1 : (j < j)%nat = false by rewrite ltnn.
    have F2 : (j < j.-1)%nat = false by apply/negbTE; rewrite -leqNgt leq_pred.
    have T3 : (j.-1 < j)%nat by rewrite prednK //; apply: leq_trans Hij.
    rewrite F1 in H1; rewrite F2 in H2; rewrite E H1 H2 T3.
    rewrite -Zminus_mod.
    have Hl : (i.-1 < j)%nat by move: Hij; case: (i) Hi.
    have Es := stage_step x i.-1 j (elimT ltP Hl).
    rewrite Nat.sub_1_r in Es.
    by rewrite Es (ltn_predK Hi).
Qed.

(* The end of the inner loop, j = i - 1: every coefficient is stage i. *)
Lemma difftab_pass (n : nat) (B1 : {ffun 'I_n -> int64}) (x : nat -> Z)
    (L K i : nat) :
  (0 < i)%nat ->
  (forall p, (p < K)%nat -> coefA B1 L p =
     (if (i.-1 < p)%nat then stage x i p else stage x i.-1 p)
       mod baseZ (Z.of_nat L)) ->
  forall p, (p < K)%nat -> coefA B1 L p = stage x i p mod baseZ (Z.of_nat L).
Proof.
  move=> Hi Hc p Hp; rewrite (Hc p Hp); case: ifP => [//|Hpi].
  rewrite -{2}(ltn_predK Hi) stage_low //.
  by move: Hpi => /negbT; rewrite -leqNgt => /leP.
Qed.

(* The end: the forward differences. *)
Lemma difftab_final (n : nat) (B0 B1 : {ffun 'I_n -> int64}) (L K a : nat) :
  (K <= a.+1)%nat ->
  (forall p, (p < K)%nat -> coefA B1 L p =
     stage (fun p => coefA B0 L p) a p mod baseZ (Z.of_nat L)) ->
  coefsA B1 L K =
    [seq fdiff (coefsA B0 L K) j mod baseZ (Z.of_nat L) | j <- iota 0 K].
Proof.
  move=> HK Hc.
  apply: (@eq_from_nth _ 0); first by rewrite size_map size_iota size_coefsA.
  rewrite size_coefsA => p Hp.
  rewrite (nth_map 0%nat) ?size_iota //; rewrite nth_iota //; rewrite (nth_coefsA _ _ _ _ Hp) (Hc p Hp).
  rewrite stage_end; first by apply/leP; lia.
  rewrite add0n /coefsA map_iota_seq fdiff_dif //; exact/ltP.
Qed.

Theorem difftab_ok : sub_spec -> difftab_spec.
Proof.
  move=> SS μ mm m Hm B0 k l r rl K L HKL.
  subst mm.
  have Hm : (Z.of_nat m:N <= Int64.max_unsigned)%Z.
    by have := Int64.unsigned_range_2 m; lia.
  enter_func. csteps.
  pose x := fun p => coefA B0 L p.
  inv I := { [:: B; i; _i_hi] } (fun (b : {ffun 'I_(m:N) -> int64}) (ii hi : int64) =>
    hi = k /\ (1 <= ii:N)%nat /\ (ii:N <= maxn 1 K)%nat /\
    (forall p, (p < K)%nat -> coefA b L p = stage x (ii:N).-1 p mod baseZ (Z.of_nat L)) /\
    (forall q : 'I_(m:N), (K * L <= q)%nat -> b q = B0 q)).
  enter_loop I.
  { prove_inv; exsp.
    - by rewrite leq_max.
    - move=> p Hp; rewrite stage0 Zmod_small //; exact: coefA_bound. }
  unfold_inv => - [hv [Ehv [Ehl [Hi1 [Hi2 [Hc Hfr]]]]]].
  csteps.
  case END: Int64.ltu => /=; move: (END); rewrite ltu_nat => END'.
  - (* pass i *)
    have HK : (0 < K)%nat by lia.
    have Ek1 := sub1_nat k HK.
    csteps.
    inv J := { [:: B; j] } (fun (b : {ffun 'I_(m:N) -> int64}) (jj : int64) =>
      (i0:N <= (jj:N).+1)%nat /\ (jj:N < K)%nat /\
      (forall p, (p < K)%nat -> coefA b L p =
         (if (jj:N < p)%nat then stage x i0:N p else stage x (i0:N).-1 p)
           mod baseZ (Z.of_nat L)) /\
      (forall q : 'I_(m:N), (K * L <= q)%nat -> b q = B0 q)).
    enter_loop J.
    { prove_inv; exsp; rewrite ?Ek1.
      - lia.
      - lia.
      - move=> p Hp; rewrite (Hc p Hp).
        by have -> : (K.-1 < p)%nat = false by apply/negbTE; rewrite -leqNgt; lia. }
    unfold_inv => - [Hj1 [Hj2 [Hjc Hjfr]]].
    csteps.
    have HKmax : (Z.of_nat K <= Int64.max_unsigned)%Z.
      by have := Int64.unsigned_range_2 k; rewrite /K; lia.
    case END2: (Int64.ltu j1 i0) => /=; move: (END2); rewrite ltu_nat => END2'.
    + (* j = i - 1: the pass is over *)
      have Ej : j1:N = (i0:N).-1 by move: Hj1 END2'; lia.
      have Ei1 : (Int64.add i0 (Int64.repr 1)):N = (i0:N).+1.
        by apply: (add1_nat _ K) => //; lia.
      rewrite Ej in Hjc.
      have Hp := difftab_pass _ B2 x L K _ Hi1 Hjc.
      csteps; cret; split=> //= _; csteps.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp; rewrite ?Ei1 //.
      * by rewrite leq_max; apply/orP; right; move: END'; rewrite /K.
    + (* one round: B_j -= B_(j-1) *)
      have Hij : (i0:N <= j1:N)%nat by rewrite leqNgt END2'.
      have [I1 [I2 [I3 [I4 [I5 _]]]]] := difftab_idx _ _ _ _ _ Hi1 Hij Hj2 HKL.
      have Hj0 : (0 < j1:N)%nat by apply: leq_trans Hij.
      have Esj := sub1_nat j1 Hj0.
      have Emj : (Int64.mul j1 l):N = (j1:N * L)%nat.
        by apply: (mul_nat _ _ (m:N)).
      have Emj1 : (Int64.mul (Int64.sub j1 (Int64.repr 1)) l):N = ((j1:N).-1 * L)%nat.
        by rewrite (mul_nat _ _ (m:N)); rewrite ?Esj.
      have Hj3 : (i0:N <= (j1:N).-1.+1)%nat by rewrite prednK.
      have Hj4 : ((j1:N).-1 < K)%nat by apply: leq_ltn_trans (leq_pred _) Hj2.
      have HKj : (j1:N * L + L <= K * L)%nat by rewrite addnC -mulSn leq_mul2r Hj2 orbT.
      csteps.
      call SS; rewrite Emj Emj1 => /(_ erefl I1 I2 (or_intror I3)).
      move=> [B3 [-> [Hs Hf]]].
      have Hr := difftab_round _ B2 B3 x L K _ _ Hi1 Hij Hj2 Hjc Hs Hf.
      csteps; cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp; rewrite ?Esj //.
      * move=> q Hq; rewrite Hf; first by right; apply: leq_trans HKj Hq.
        exact: Hjfr.
  - (* the loop ends: i = max 1 k *)
    csteps; cret; split=> //= _; csteps; cret.
    exists B1; split; first by rewrite/envC/=.
    split; last exact: Hfr.
    apply: (difftab_final _ B0 B1 L K (i0:N).-1) => //.
    move: END' Hi1; lia.
Qed.
