(** * The two entry points of exp100, on the reals

    A run of [exp_encl_bits] that returns 0 gives an enclosure of exp x;
    a run of [maybe_hard_bits] that returns 0 says that x is not hard to
    round, x being the double of the bits [xb].  The pieces:
    [exp_encl_bits_spec] and [maybe_hard_bits_spec] (what the program
    computes, Specs.v) and [exp_encl_ok] and [maybe_hard_ok] (the reals,
    ExpSpec.v).

    The theorems are stated twice: on the interpreter [eval_func] of
    Capla, and on its small-step semantics, through
    [starN_interp_eval_func] (L1SemProofHelpers.v).  They are proved in
    the section [Final] from the two statements; the closed theorems, with
    no hypothesis, are at the end of the file. *)

From compcert Require Import CaplaProof.
From Stdlib Require Import Reals.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds ExpBits ExpHard ExpSpec.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Exp100Capla2.NumZeroProof Exp100Capla2.NumAddProof
  Exp100Capla2.NumSubProof Exp100Capla2.NumCopyProof Exp100Capla2.NumPow2Proof
  Exp100Capla2.NumLtProof Exp100Capla2.NumLowProof Exp100Capla2.GuessProof
  Exp100Capla2.MulLn2Proof Exp100Capla2.BitlenProof Exp100Capla2.ScaleProof
  Exp100Capla2.MulSmallProof Exp100Capla2.MulshrProof
  Exp100Capla2.ExpCoreProof Exp100Capla2.DecideProof
  Exp100Capla2.ExpEnclProof Exp100Capla2.MaybeHardProof.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** The return codes of the model *)

Lemma exp_encl_Z_rc xb rc :
  ExpModel.exp_encl_Z xb = inl rc -> (1 <= rc <= 3)%Z.
Proof.
rewrite /ExpModel.exp_encl_Z.
case Hc: (ExpModel.core_Z xb) => [r|[y hN]] // [<-].
exact: ExpModelBounds.core_Z_rc Hc.
Qed.

Lemma maybe_hard_Z_range xb : (0 <= ExpModel.maybe_hard_Z xb <= 1)%Z.
Proof.
rewrite /ExpModel.maybe_hard_Z.
case: (ExpModel.core_Z xb) => [r|[y hN]]; first lia.
rewrite /ExpModel.decide_Z; cbv zeta.
by repeat match goal with |- context [if ?b then _ else _] => case: b end;
  lia.
Qed.

Lemma xb_range (xb : int64) : (0 <= Int64.unsigned xb < 2 ^ 64)%Z.
Proof.
by have := Int64.unsigned_range xb; change Int64.modulus with (2 ^ 64)%Z.
Qed.

(* |exp x - M 2^s| <= D 2^s, x being the double of the bits xb *)
Definition encl (xb M s : Z) : Prop :=
  Rle (Rabs (Rminus (Rtrigo_def.exp (ExpBits.xreal xb))
          (Rmult (IZR M) (Raux.bpow Zaux.radix2 s))))
      (Rmult (IZR ExpModel.D) (Raux.bpow Zaux.radix2 s)).

(* The parameters M and s of exp_encl_bits, its two mutable arrays. *)
Definition M_id : ident := nth xH (fd_params f_exp_encl_bits) 1.
Definition s_id : ident := nth xH (fd_params f_exp_encl_bits) 2.

(** ** The theorems, from the two statements *)

Section Final.

Hypothesis maybe_hard_bits_full : maybe_hard_bits_spec.
Hypothesis exp_encl_bits_full : exp_encl_bits_spec.

(* returns 0 only when x is not hard to round *)
Theorem maybe_hard_bits_real μ xb Ta Ca L2 RM r rl :
  tables_ok Ta Ca L2 RM ->
  eval_func ge μ f_maybe_hard_bits
    [:: xb <:: u64; Ta <:: [[u64; NL]; TABn]; Ca <:: [[u64; NL]; CLn];
        L2 <:: [u64; NL]; RM <:: [u64; NL]] = Some (r, rl) ->
  exists rc, r = Vint64 rc /\ (0 <= Int64.unsigned rc <= 1)%Z /\
    (Int64.unsigned rc = 0%Z ->
       ~ ExpHard.hard (ExpBits.xreal (Int64.unsigned xb))).
Proof.
move=> Ht /(maybe_hard_bits_full _ _ _ _ _ _ _ _ Ht) [-> _].
have Hr := maybe_hard_Z_range (Int64.unsigned xb).
have Hu : Int64.unsigned
            (Int64.repr (ExpModel.maybe_hard_Z (Int64.unsigned xb))) =
          ExpModel.maybe_hard_Z (Int64.unsigned xb).
  by apply: Int64.unsigned_repr; change Int64.max_unsigned with
    (2 ^ 64 - 1)%Z; lia.
eexists; split; first reflexivity.
rewrite Hu; split => // H0.
exact: ExpSpec.maybe_hard_ok (xb_range xb) H0.
Qed.

(* returns 0 only with an enclosure of exp x on (M, s) *)
Theorem exp_encl_bits_real μ xb M s Ta Ca L2 RM r rl :
  tables_ok Ta Ca L2 RM ->
  eval_func ge μ f_exp_encl_bits
    [:: xb <:: u64; M <:: [u64; NM]; s <:: [i64; 1];
        Ta <:: [[u64; NL]; TABn]; Ca <:: [[u64; NL]; CLn];
        L2 <:: [u64; NL]; RM <:: [u64; NL]] = Some (r, rl) ->
  exists rc (M' : {ffun 'I_NM -> int64}) (s' : {ffun 'I_1 -> int64}),
    r = Vint64 rc /\ rl = [:: M' <:: [u64; NM]; s' <:: [i64; 1]] /\
    (0 <= Int64.unsigned rc <= 3)%Z /\
    (Int64.unsigned rc = 0%Z ->
       encl (Int64.unsigned xb) (valW (words M')) (Int64.signed (s' ord0))).
Proof.
move=> Ht /(exp_encl_bits_full _ _ _ _ _ _ _ _ _ _ Ht).
move=> [rc [M' [s' [-> [-> [Hnz Hz]]]]]].
exists rc, M', s'; do 2 (split => //); split.
  case: (Z.eq_dec (Int64.unsigned rc) 0) => [->|Hn]; first lia.
  by have := exp_encl_Z_rc _ _ (Hnz Hn); lia.
by move=> /Hz He; exact: ExpSpec.exp_encl_ok (xb_range xb) He.
Qed.

(** The same on the small-step semantics of Capla: a run from the call
    to the return, on arguments [args] that the values of the
    interpreter stand for. *)

(* returns 0 only when x is not hard to round *)
Theorem maybe_hard_bits_sem n xb Ta Ca L2 RM args e se v :
  tables_ok Ta Ca L2 RM ->
  List.Forall2 match_value args
    [:: xb <:: u64; Ta <:: [[u64; NL]; TABn]; Ca <:: [[u64; NL]; CLn];
        L2 <:: [u64; NL]; RM <:: [u64; NL]] ->
  StarN (L1Sem.semantics program) n (Callstate f_maybe_hard_bits args Kstop)
    E0 (Returnstate e se f_maybe_hard_bits v Kstop) ->
  exists rc, v = BValues.Vint64 rc /\ (0 <= Int64.unsigned rc <= 1)%Z /\
    (Int64.unsigned rc = 0%Z ->
       ~ ExpHard.hard (ExpBits.xreal (Int64.unsigned xb))).
Proof.
move=> Ht Ha /starN_interp_eval_func /(_ _ Ha) [v' [rl [Hv [Hrun _]]]].
have [rc [Hr H]] := maybe_hard_bits_real _ _ _ _ _ _ _ _ Ht Hrun.
by exists rc; move: Hv; rewrite Hr => /[invc].
Qed.

(* returns 0 only with an enclosure of exp x on (M, s), M and s being
   the final values of the parameters M and s *)
Theorem exp_encl_bits_sem n xb M s Ta Ca L2 RM args e se v :
  tables_ok Ta Ca L2 RM ->
  List.Forall2 match_value args
    [:: xb <:: u64; M <:: [u64; NM]; s <:: [i64; 1];
        Ta <:: [[u64; NL]; TABn]; Ca <:: [[u64; NL]; CLn];
        L2 <:: [u64; NL]; RM <:: [u64; NL]] ->
  StarN (L1Sem.semantics program) n (Callstate f_exp_encl_bits args Kstop)
    E0 (Returnstate e se f_exp_encl_bits v Kstop) ->
  exists rc (M' : {ffun 'I_NM -> int64}) (s' : {ffun 'I_1 -> int64}),
    v = BValues.Vint64 rc /\
    (forall a, e ! M_id = Some a -> match_value a (M' <:: [u64; NM])) /\
    (forall a, e ! s_id = Some a -> match_value a (s' <:: [i64; 1])) /\
    (0 <= Int64.unsigned rc <= 3)%Z /\
    (Int64.unsigned rc = 0%Z ->
       encl (Int64.unsigned xb) (valW (words M')) (Int64.signed (s' ord0))).
Proof.
move=> Ht Ha /starN_interp_eval_func /(_ _ Ha) [v' [rl [Hv [Hrun Hmut]]]].
have [rc [M' [s' [Hr [Hrl H]]]]] :=
  exp_encl_bits_real _ _ _ _ _ _ _ _ _ _ Ht Hrun.
exists rc, M', s'.
move: Hv Hmut; rewrite Hr Hrl => /[invc] Hmut.
have -> : [seq i <- fd_params f_exp_encl_bits |
            permission_beq Mutable (option_get (Ρ(f_exp_encl_bits)) ! i Shared)]
          = [:: M_id; s_id] by [].
by move=> /= /List.Forall2_cons_iff [H1 /List.Forall2_cons_iff [H2 _]].
Qed.

End Final.

Print Assumptions maybe_hard_bits_real.
Print Assumptions exp_encl_bits_real.
Print Assumptions maybe_hard_bits_sem.
Print Assumptions exp_encl_bits_sem.

(** ** The closed theorems

    Each statement of Specs.v from the proofs of the functions, the
    statements of the callees given in turn. *)

Lemma num_zero_full : num_zero_spec.
Proof. exact: NumZeroProof.num_zero_ok. Qed.
Lemma num_copy_full : num_copy_spec.
Proof. exact: NumCopyProof.num_copy_ok. Qed.
Lemma num_add_full : num_add_spec.
Proof. exact: NumAddProof.num_add_ok. Qed.
Lemma num_sub_full : num_sub_spec.
Proof. exact: NumSubProof.num_sub_ok. Qed.
Lemma num_lt_full : num_lt_spec.
Proof. exact: NumLtProof.num_lt_ok. Qed.
Lemma num_pow2_full : num_pow2_spec.
Proof. exact: NumPow2Proof.num_pow2_ok. Qed.
Lemma num_low_full : num_low_spec.
Proof. exact: NumLowProof.num_low_ok. Qed.
Lemma num_bitlen_full : num_bitlen_spec.
Proof. exact: BitlenProof.num_bitlen_ok. Qed.
Lemma num_mul_small_full : num_mul_small_spec.
Proof. exact: MulSmallProof.num_mul_small_ok. Qed.
Lemma num_mulshr_full : num_mulshr_spec.
Proof. exact: MulshrProof.num_mulshr_ok. Qed.
Lemma num_scale_full : num_scale_spec.
Proof. exact: ScaleProof.num_scale_ok num_zero_full. Qed.
Lemma guess_n_full : guess_n_spec.
Proof. exact: GuessProof.guess_n_ok num_mul_small_full. Qed.
Lemma mul_ln2_full : mul_ln2_spec.
Proof. exact: MulLn2Proof.mul_ln2_ok num_mul_small_full. Qed.

(* All the statements of the callees, as hypotheses: the proof of a
   function then takes the ones it needs, in any order. *)
Ltac callees :=
  have := num_zero_full; have := num_copy_full; have := num_add_full;
  have := num_sub_full; have := num_lt_full; have := num_pow2_full;
  have := num_low_full; have := num_bitlen_full; have := num_mul_small_full;
  have := num_mulshr_full; have := num_scale_full; have := guess_n_full;
  have := mul_ln2_full; move=> *.

(** ** The closed theorems, no hypothesis left *)

Lemma exp_core_full : exp_core_spec.
Proof. by callees; apply: ExpCoreProof.exp_core_ok. Qed.
Lemma decide_full : decide_spec.
Proof. by callees; apply: DecideProof.decide_ok. Qed.
Lemma exp_encl_bits_full : exp_encl_bits_spec.
Proof. exact: ExpEnclProof.exp_encl_bits_ok exp_core_full. Qed.
Lemma maybe_hard_bits_full : maybe_hard_bits_spec.
Proof. exact: MaybeHardProof.maybe_hard_bits_ok exp_core_full decide_full. Qed.

Definition maybe_hard_bits_correct :=
  maybe_hard_bits_real maybe_hard_bits_full.
Definition exp_encl_bits_correct :=
  exp_encl_bits_real exp_encl_bits_full.
Definition maybe_hard_bits_sem_correct :=
  maybe_hard_bits_sem maybe_hard_bits_full.
Definition exp_encl_bits_sem_correct :=
  exp_encl_bits_sem exp_encl_bits_full.

Check maybe_hard_bits_correct.
Check exp_encl_bits_correct.
Check maybe_hard_bits_sem_correct.
Check exp_encl_bits_sem_correct.

Print Assumptions maybe_hard_bits_correct.
Print Assumptions exp_encl_bits_correct.
Print Assumptions maybe_hard_bits_sem_correct.
Print Assumptions exp_encl_bits_sem_correct.
