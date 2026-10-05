(** * The 16 functions of exp100.c together, and what they compute on the reals

    exp100.c has no [main], so there is no whole program to prove; what
    VST checks instead is [semax_func]: each of the 16 bodies meets its
    statement of Spec.v in the global environment of exp100.c, every call
    inside them being read through the statements of the same list
    [Gprog].  Then the two entry points are restated on the reals, with
    the theorems of ExpSpec.v: [exp_encl_bits] returns 0 only with an
    enclosure of exp x, [maybe_hard_bits] returns 0 only when x is not
    hard to round, x being the double of the bits [xb]. *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.
Require Import E.Verif_simple E.Verif_bits E.Verif_mulshr E.Verif_reduce.
Require Import E.Verif_core E.TopLemmas E.Verif_top.
Require Exp100.ExpModel Exp100.ExpBits Exp100.ExpHard Exp100.ExpSpec.
Require Flocq.Core.Core.
From Stdlib Require Import Rdefinitions.

(** No input or output: the oracle of the C program is empty. *)
#[export] Existing Instance NullExtension.Espec.

(** ** The 16 functions, with the statements of Spec.v *)

Lemma exp100_funcs_correct :
  semax_func Vprog Gprog (Genv.globalenv prog)
    [(_num_zero, Internal f_num_zero); (_num_copy, Internal f_num_copy);
     (_num_add, Internal f_num_add); (_num_sub, Internal f_num_sub);
     (_num_lt, Internal f_num_lt); (_num_mul_small, Internal f_num_mul_small);
     (_num_mulshr, Internal f_num_mulshr);
     (_num_bitlen, Internal f_num_bitlen); (_num_pow2, Internal f_num_pow2);
     (_num_low, Internal f_num_low); (_num_scale, Internal f_num_scale);
     (_mul_ln2, Internal f_mul_ln2); (_guess_n, Internal f_guess_n);
     (_exp_core, Internal f_exp_core);
     (_exp_encl_bits, Internal f_exp_encl_bits);
     (_maybe_hard_bits, Internal f_maybe_hard_bits)] Gprog.
Proof.
  unfold Gprog.
  prove_semax_prog_setup_globalenv.
  semax_func_cons body_num_zero.
  semax_func_cons body_num_copy.
  semax_func_cons body_num_add.
  semax_func_cons body_num_sub.
  semax_func_cons body_num_lt.
  semax_func_cons body_num_mul_small.
  semax_func_cons body_num_mulshr.
  semax_func_cons body_num_bitlen.
  semax_func_cons body_num_pow2.
  semax_func_cons body_num_low.
  semax_func_cons body_num_scale.
  semax_func_cons body_mul_ln2.
  semax_func_cons body_guess_n.
  semax_func_cons body_exp_core.
  semax_func_cons body_exp_encl_bits.
  semax_func_cons body_maybe_hard_bits.
Qed.

(** ** The two entry points on the reals *)

(** |exp x - M 2^s| <= D 2^s, x being the double of the bits xb. *)
Definition encl (xb M s : Z) : Prop :=
  (Rbasic_fun.Rabs (Rtrigo_def.exp (Exp100.ExpBits.xreal xb) -
     IZR M * Flocq.Core.Raux.bpow Flocq.Core.Zaux.radix2 s) <=
   IZR Exp100.ExpModel.D * Flocq.Core.Raux.bpow Flocq.Core.Zaux.radix2 s)%R.

(* returns 0 only with an enclosure of exp x on (M, s) *)
Definition exp_encl_bits_real_spec : ident * funspec :=
 DECLARE _exp_encl_bits
 WITH gv : globals, shM : share, shs : share, xb : Z, pM : val, ps : val
 PRE [ tulong, tptr tulong, tptr tlong ]
   PROP (writable_share shM; writable_share shs;
         (0 <= xb <= Int64.max_unsigned)%Z)
   PARAMS (Vlong (Int64.repr xb); pM; ps) GLOBALS (gv)
   SEP (data_at_ shM (tarray tulong NM) pM; data_at_ shs tlong ps; consts gv)
 POST [ tint ]
   EX rc : Z, EX ms : list Z, EX s : Z,
   PROP ((0 <= rc <= 3)%Z;
         (rc = 0)%Z -> encl xb (valW ms) s /\
                       Zlength ms = NM /\ Forall word ms)
   RETURN (Vint (Int.repr rc))
   SEP (if rc =? 0
        then (data_at shM (tarray tulong NM) (vwords ms) pM *
              data_at shs tlong (Vlong (Int64.repr s)) ps)%logic
        else (data_at_ shM (tarray tulong NM) pM *
              data_at_ shs tlong ps)%logic;
        consts gv).

(* returns 0 only when x is not hard to round *)
Definition maybe_hard_bits_real_spec : ident * funspec :=
 DECLARE _maybe_hard_bits
 WITH gv : globals, xb : Z
 PRE [ tulong ]
   PROP ((0 <= xb <= Int64.max_unsigned)%Z)
   PARAMS (Vlong (Int64.repr xb)) GLOBALS (gv)
   SEP (consts gv)
 POST [ tint ]
   EX r : Z,
   PROP ((0 <= r <= 1)%Z;
         (r = 0)%Z -> ~ Exp100.ExpHard.hard (Exp100.ExpBits.xreal xb))
   RETURN (Vint (Int.repr r))
   SEP (consts gv).

(** The return codes of the model. *)
Lemma exp_encl_Z_rc xb rc :
  Exp100.ExpModel.exp_encl_Z xb = inl rc -> (1 <= rc <= 3)%Z.
Proof.
  unfold Exp100.ExpModel.exp_encl_Z.
  destruct (Exp100.ExpModel.core_Z xb) as [r|[y hN]] eqn:Hc;
    [|discriminate].
  intros H; injection H as <-; exact (core_Z_rc xb r Hc).
Qed.

Lemma maybe_hard_Z_range xb : (0 <= Exp100.ExpModel.maybe_hard_Z xb <= 1)%Z.
Proof.
  unfold Exp100.ExpModel.maybe_hard_Z.
  destruct (Exp100.ExpModel.core_Z xb) as [r|[y hN]]; [lia|].
  unfold Exp100.ExpModel.decide_Z; cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    lia.
Qed.

(* entailer! must not look inside the tables *)
Local Opaque consts.

Lemma exp_encl_bits_sub :
  funspec_sub (snd exp_encl_bits_spec) (snd exp_encl_bits_real_spec).
Proof.
  do_funspec_sub.
  destruct w as [[[[[gv shM] shs] xb] pM] ps]; simpl in H |- *.
  Intros; Exists (gv, shM, shs, xb, pM, ps) emp; entailer!.
  intros rho' _ Hr.
  match goal with
  | H1 : ?r = 0 -> _, H2 : ?r <> 0 -> _ |- _ =>
      rename r into rc; rename H1 into Hz; rename H2 into Hnz
  end.
  match goal with |- context [data_at _ _ (vwords ?m) _] => rename m into ms end.
  match goal with |- context [Vlong (Int64.repr ?t)] => rename t into s end.
  Exists rc ms s; entailer!; split.
  - destruct (Z.eq_dec rc 0) as [->|Hn]; [lia|].
    pose proof (exp_encl_Z_rc xb rc (Hnz Hn)); lia.
  - intros ->; destruct (Hz eq_refl) as (He & Hl & Hf).
    split; [|auto]; unfold encl.
    apply (Exp100.ExpSpec.exp_encl_ok xb); [rep_lia|exact He].
Qed.

Lemma maybe_hard_bits_sub :
  funspec_sub (snd maybe_hard_bits_spec) (snd maybe_hard_bits_real_spec).
Proof.
  do_funspec_sub.
  destruct w as [gv xb]; simpl in H |- *.
  Intros; Exists (gv, xb) emp; entailer!.
  intros rho' _ Hr.
  Exists (Exp100.ExpModel.maybe_hard_Z xb); entailer!.
  split; [apply maybe_hard_Z_range|].
  apply Exp100.ExpSpec.maybe_hard_ok; rep_lia.
Qed.

(** The bodies of the two entry points meet their statements on the reals. *)
Lemma body_exp_encl_bits_real :
  semax_body Vprog Gprog f_exp_encl_bits exp_encl_bits_real_spec.
Proof.
  exact (semax_body_funspec_sub body_exp_encl_bits exp_encl_bits_sub
           ltac:(apply compute_list_norepet_e; reflexivity)).
Qed.

Lemma body_maybe_hard_bits_real :
  semax_body Vprog Gprog f_maybe_hard_bits maybe_hard_bits_real_spec.
Proof.
  exact (semax_body_funspec_sub body_maybe_hard_bits maybe_hard_bits_sub
           ltac:(apply compute_list_norepet_e; reflexivity)).
Qed.

(** ** The final statement

    The 16 functions of exp100.c, every call inside them read through the
    statements of Spec.v, meet the statements [Gprog_real]: those of
    Spec.v for the 14 helpers, those on the reals above for the two entry
    points. *)

Definition Gprog_real : funspecs := [
  num_zero_spec; num_copy_spec; num_add_spec; num_sub_spec; num_lt_spec;
  num_mul_small_spec; num_mulshr_spec; num_bitlen_spec; num_pow2_spec;
  num_low_spec; num_scale_spec; mul_ln2_spec; guess_n_spec;
  exp_core_spec; exp_encl_bits_real_spec; maybe_hard_bits_real_spec].

Theorem exp100_correct :
  semax_func Vprog Gprog (Genv.globalenv prog)
    [(_num_zero, Internal f_num_zero); (_num_copy, Internal f_num_copy);
     (_num_add, Internal f_num_add); (_num_sub, Internal f_num_sub);
     (_num_lt, Internal f_num_lt); (_num_mul_small, Internal f_num_mul_small);
     (_num_mulshr, Internal f_num_mulshr);
     (_num_bitlen, Internal f_num_bitlen); (_num_pow2, Internal f_num_pow2);
     (_num_low, Internal f_num_low); (_num_scale, Internal f_num_scale);
     (_mul_ln2, Internal f_mul_ln2); (_guess_n, Internal f_guess_n);
     (_exp_core, Internal f_exp_core);
     (_exp_encl_bits, Internal f_exp_encl_bits);
     (_maybe_hard_bits, Internal f_maybe_hard_bits)] Gprog_real.
Proof.
  unfold Gprog_real.
  prove_semax_prog_setup_globalenv.
  semax_func_cons body_num_zero.
  semax_func_cons body_num_copy.
  semax_func_cons body_num_add.
  semax_func_cons body_num_sub.
  semax_func_cons body_num_lt.
  semax_func_cons body_num_mul_small.
  semax_func_cons body_num_mulshr.
  semax_func_cons body_num_bitlen.
  semax_func_cons body_num_pow2.
  semax_func_cons body_num_low.
  semax_func_cons body_num_scale.
  semax_func_cons body_mul_ln2.
  semax_func_cons body_guess_n.
  semax_func_cons body_exp_core.
  semax_func_cons body_exp_encl_bits_real.
  semax_func_cons body_maybe_hard_bits_real.
Qed.

Print Assumptions exp100_funcs_correct.
Print Assumptions exp100_correct.
