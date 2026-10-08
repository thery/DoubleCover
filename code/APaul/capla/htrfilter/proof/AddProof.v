(** * add: B_ia <- B_ia + B_ib mod 2^(64 l)

    The loop invariant is the one of the VST proof (body_add of
    ../../../vst/Verif_add.v): after i rounds, the i low words of B_ia
    and the carry cy stand for the sum of the i low words of B_ia and
    B_ib, the other words of B are those of the start, and the carry is 0
    or 1. *)

From APaulRocq Require Import HtrDefs.
From compcert Require Import CaplaProof.
Require Import HtrFilterCapla.htr_filter HtrFilterCapla.HtrWords.
Require Import HtrFilterCapla.WordLemmas HtrFilterCapla.Specs.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(* One round of the loop: word i of B_ia, written at ka = IA + i, and the
   carry c'. *)
Lemma add_round (n : nat) (B0 B1 : {ffun 'I_n -> int64}) (IA IB L i ka kb : nat)
    (Ha : (ka < n)%nat) (Hb : (kb < n)%nat) (c c' : int64) :
  ka = (IA + i)%nat -> kb = (IB + i)%nat -> (i < L)%nat ->
  (IA + L <= IB \/ IB + L <= IA)%nat ->
  (forall q : 'I_n, (q < IA \/ IA + i <= q)%nat -> B1 q = B0 q) ->
  (segv B1 IA i + Int64.unsigned c * baseZ (Z.of_nat i) =
   segv B0 IA i + segv B0 IB i)%Z ->
  let s := Int64.add (B1 (Ordinal Ha)) (Int64.add (B1 (Ordinal Hb)) c) in
  (Int64.unsigned s + 2 ^ wbits * Int64.unsigned c' =
   Int64.unsigned (B1 (Ordinal Ha)) + Int64.unsigned (B1 (Ordinal Hb)) +
   Int64.unsigned c)%Z ->
  let B2 := [ffun j => if j == Ordinal Ha then s else B1 j] in
  (forall q : 'I_n, (q < IA \/ IA + i.+1 <= q)%nat -> B2 q = B0 q) /\
  (segv B2 IA i.+1 + Int64.unsigned c' * baseZ (Z.of_nat i.+1) =
   segv B0 IA i.+1 + segv B0 IB i.+1)%Z.
Proof.
  move=> Eka Ekb Hi Hd Hfr HV s Hs B2.
  have Fa : B1 (Ordinal Ha) = B0 (Ordinal Ha) by apply: Hfr => /=; lia.
  have Fb : B1 (Ordinal Hb) = B0 (Ordinal Hb) by apply: Hfr => /=; lia.
  split.
  { move=> q Hq; rewrite /B2 ffunE; case: eqP => [Eq|_]; last by apply: Hfr; lia.
    by move: Hq; rewrite Eq /=; lia. }
  have E2 : segv B2 IA i = segv B1 IA i.
  { apply: segv_ext => q Hq; apply: wd_eq => Hq'.
    rewrite /B2 ffunE; case: eqP => // /(f_equal val) /=; lia. }
  have W2 : wd B2 (IA + i) = Int64.unsigned s.
    by rewrite -Eka (wdE _ _ Ha) /B2 ffunE eqxx.
  have Wa : wd B0 (IA + i) = Int64.unsigned (B1 (Ordinal Ha)).
    by rewrite -Eka (wdE _ _ Ha) Fa.
  have Wb : wd B0 (IB + i) = Int64.unsigned (B1 (Ordinal Hb)).
    by rewrite -Ekb (wdE _ _ Hb) Fb.
  rewrite !segvS E2 W2 Wa Wb baseZS.
  have Bp := baseZ_pos i.
  nia.
Qed.

Theorem add_ok : add_spec.
Proof.
  move=> μ mm m Hm B0 ia ib l r rl IA IB L HA HB Hd.
  subst mm.
  enter_func. csteps.
  inv I := { [:: B; cy; i; _i_hi] }
    (fun (b : {ffun 'I_(m:N) -> int64}) (c ii hi : int64) =>
    hi = l /\ (ii:N <= L)%nat /\ Int64.unsigned c <= 1 /\
    (forall q : 'I_(m:N), (q < IA \/ IA + ii:N <= q)%nat -> b q = B0 q) /\
    segv b IA ii:N + Int64.unsigned c * baseZ (Z.of_nat ii:N) =
    segv B0 IA ii:N + segv B0 IB ii:N).
  enter_loop I.
  { prove_inv; exsp. }
  unfold_inv => - [hv [Ehv [Ehl [Hi [Hc [Hfr HV]]]]]].
  csteps.
  case END: Int64.ltu => /=.
  - (* one round *)
    have Hlt : (i0:N < L)%nat by move: END; rewrite /L; clia.
    have Hm : (Z.of_nat m:N <= Int64.max_unsigned)%Z.
      by have := Int64.unsigned_range_2 m; lia.
    have Ei : (Int64.add i0 (Int64.repr 1)):N = (i0:N).+1 by clia i0.
    csteps; evalf; csteps; evalf; csteps.
    have Eka : (Int64.add ia i0):N = (IA + i0:N)%nat.
      by apply: (add_nat _ _ (m:N)) => //; lia.
    have Ekb : (Int64.add ib i0):N = (IB + i0:N)%nat.
      by apply: (add_nat _ _ (m:N)) => //; lia.
    have Hcy := add_carry (B1 (Ordinal H0)) (B1 (Ordinal H)) cy0 Hc.
    case C1: Int64.ltu => /=; csteps; evalf; csteps; cret; split=> // _.
    all: rewrite C1 in Hcy.
    all: have [R1 R2] := add_round _ B0 B1 IA IB L _ _ _ H0 H _ _ Eka Ekb Hlt Hd Hfr HV Hcy.
    all: split; first solve_loop_conditions.
    all: prove_inv; exsp; rewrite ?eqxx ?Ei //.
    all: try lia.
    all: by case: Int64.ltu.
  - (* the loop ends with i = l *)
    csteps; cret; split=> //= _; csteps; cret.
    have Ei : i0:N = L by move: END Hi; rewrite /L; clia.
    exists B1; split; first by rewrite/envC/=.
    rewrite Ei in Hfr HV; split; last exact: Hfr.
    exact: segv_mod HV.
Qed.
