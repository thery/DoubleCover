(** * The whole program: exp100.c with a main

    exp100_main.c is exp100.c with [main], so VST can prove it as a whole
    program ([semax_prog]): [main] starts with the globals initialized,
    which gives [consts gv] (InitConsts.v), the hypothesis every statement
    of Spec.v makes.  The two wrappers on doubles, [exp_encl] and
    [maybe_hard], are stated on the real value of their argument.  The 16
    body proofs of exp100.c are reused as they are: the function bodies
    of exp100_main_clight.v are the same terms as those of
    exp100_clight.v. *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.
Require Import E.Verif_simple E.Verif_bits E.Verif_mulshr E.Verif_reduce.
Require Import E.Verif_core E.TopLemmas E.Verif_top E.Verif_all E.InitConsts.
Require E.exp100_main_clight.
Require Exp100.ExpModel Exp100.ExpBits Exp100.ExpHard Exp100.ExpSpec.
Require Flocq.Core.Core Flocq.IEEE754.Binary.
From Stdlib Require Import Rdefinitions.

(** No input or output: the oracle of the C program is empty. *)
#[export] Existing Instance NullExtension.Espec.

(** ** The real value of a double *)

(** The real number of the double [x] (0 for an infinity or a NaN). *)
Definition dreal (x : float) : R := Binary.B2R 53 1024 x.

(** The bits of [x] read as an unsigned integer stand for [x]. *)
Lemma xreal_bits x :
  Exp100.ExpBits.xreal (Int64.unsigned (Float.to_bits x)) = dreal x.
Proof.
  unfold Exp100.ExpBits.xreal, dreal.
  change (Flocq.IEEE754.Bits.b64_of_bits (Int64.unsigned (Float.to_bits x)))
    with (Float.of_bits (Float.to_bits x)).
  rewrite Float.of_to_bits; reflexivity.
Qed.

(** |exp x - M 2^s| <= D 2^s, for a real x. *)
Definition encl_real (x : R) (M s : Z) : Prop :=
  (Rbasic_fun.Rabs (Rtrigo_def.exp x -
     IZR M * Flocq.Core.Raux.bpow Flocq.Core.Zaux.radix2 s) <=
   IZR Exp100.ExpModel.D * Flocq.Core.Raux.bpow Flocq.Core.Zaux.radix2 s)%R.

(** ** The two wrappers on doubles *)

(* returns 0 only with an enclosure of exp x on (M, s) *)
Definition exp_encl_spec : ident * funspec :=
 DECLARE _exp_encl
 WITH gv : globals, shM : share, shs : share, x : float, pM : val, ps : val
 PRE [ tdouble, tptr tulong, tptr tlong ]
   PROP (writable_share shM; writable_share shs)
   PARAMS (Vfloat x; pM; ps) GLOBALS (gv)
   SEP (data_at_ shM (tarray tulong NM) pM; data_at_ shs tlong ps; consts gv)
 POST [ tint ]
   EX rc : Z, EX ms : list Z, EX s : Z,
   PROP ((0 <= rc <= 3)%Z;
         (rc = 0)%Z -> encl_real (dreal x) (valW ms) s /\
                       Zlength ms = NM /\ Forall word ms)
   RETURN (Vint (Int.repr rc))
   SEP (if rc =? 0
        then (data_at shM (tarray tulong NM) (vwords ms) pM *
              data_at shs tlong (Vlong (Int64.repr s)) ps)%logic
        else (data_at_ shM (tarray tulong NM) pM *
              data_at_ shs tlong ps)%logic;
        consts gv).

(* returns 0 only when x is not hard to round *)
Definition maybe_hard_spec : ident * funspec :=
 DECLARE _maybe_hard
 WITH gv : globals, x : float
 PRE [ tdouble ]
   PROP () PARAMS (Vfloat x) GLOBALS (gv)
   SEP (consts gv)
 POST [ tint ]
   EX r : Z,
   PROP ((0 <= r <= 1)%Z; (r = 0)%Z -> ~ Exp100.ExpHard.hard (dreal x))
   RETURN (Vint (Int.repr r))
   SEP (consts gv).

(* entailer! must not look inside the tables *)
Local Opaque consts.

Lemma body_maybe_hard :
  semax_body Vprog Gprog f_maybe_hard maybe_hard_spec.
Proof.
  start_function.
  forward.
  forward.
  set (xb := Int64.unsigned (Float.to_bits x)).
  assert (Hx : Vlong (Float.to_bits x) = Vlong (Int64.repr xb))
    by (unfold xb; rewrite Int64.repr_unsigned; reflexivity).
  rewrite Hx.
  forward_call (gv, xb).
  forward.
  Exists (Exp100.ExpModel.maybe_hard_Z xb).
  entailer!.
  split; [apply maybe_hard_Z_range|].
  rewrite <- xreal_bits; fold xb.
  apply Exp100.ExpSpec.maybe_hard_ok; unfold xb; rep_lia.
Qed.

Lemma body_exp_encl :
  semax_body Vprog Gprog f_exp_encl exp_encl_spec.
Proof.
  start_function.
  forward.
  forward.
  set (xb := Int64.unsigned (Float.to_bits x)).
  assert (Hx : Vlong (Float.to_bits x) = Vlong (Int64.repr xb))
    by (unfold xb; rewrite Int64.repr_unsigned; reflexivity).
  rewrite Hx.
  forward_call (gv, shM, shs, xb, pM, ps).
  Intros vret; destruct vret as [[rc ms] s]; simpl fst in *; simpl snd in *.
  forward.
  Exists rc ms s.
  entailer!.
  split.
  - destruct (Z.eq_dec rc 0) as [->|Hn]; [lia|].
    pose proof (exp_encl_Z_rc xb rc (H0 Hn)); lia.
  - intros ->; destruct (H eq_refl) as (He & Hl & Hf).
    split; [|auto]; unfold encl_real; rewrite <- xreal_bits; fold xb.
    apply (Exp100.ExpSpec.exp_encl_ok xb); [unfold xb; rep_lia|exact He].
Qed.

(** ** main *)

(** The double 1.0 of [main]. *)
Definition one : float := Float.of_bits (Int64.repr 4607182418800017408).

Local Transparent Float.of_bits.

Lemma dreal_one : dreal one = 1%R.
Proof.
  unfold dreal, one, Float.of_bits.
  rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia).
  vm_compute Flocq.IEEE754.Bits.b64_of_bits.
  simpl Binary.B2R; unfold Flocq.Core.Defs.F2R; simpl.
  change 4503599627370496%Z with (2 ^ 52)%Z.
  change (Z.pow_pos 2 52) with (2 ^ 52)%Z.
  apply RIneq.Rinv_r; apply RIneq.not_0_IZR; lia.
Qed.

Local Opaque Float.of_bits.

(* main: maybe_hard(1.0), with the globals initialized *)
Definition main_spec : ident * funspec :=
 DECLARE _main
 WITH gv : globals
 PRE [] main_pre E.exp100_main_clight.prog tt gv
 POST [ tint ]
   EX r : Z,
   PROP ((0 <= r <= 1)%Z; (r = 0)%Z -> ~ Exp100.ExpHard.hard 1%R)
   RETURN (Vint (Int.repr r))
   SEP (consts gv; TT).

Lemma body_main :
  semax_body Vprog [maybe_hard_spec] E.exp100_main_clight.f_main main_spec.
Proof.
  start_function1.
  start_function2.
  (* the initial globals are the constants: done here, before
     start_function3, which would split them into one mapsto per word *)
  rewrite main_pre_start_old.
  change (prog_vars E.exp100_main_clight.prog) with
    [(_T, v_T); (_C, v_C); (_LN2, v_LN2); (_RMAX, v_RMAX); (_INV, v_INV)].
  eapply semax_pre with
    (P' := (PROP () LOCAL (gvars gv) SEP (has_ext tt; consts gv) *
            stackframe_of E.exp100_main_clight.f_main)%logic).
  { apply andp_left2; apply sepcon_derives; [|apply derives_refl].
    intro rho; unfold PROPx, LOCALx, SEPx, local, lift1, liftx; simpl.
    unfold lift; normalize.
    apply sepcon_derives; [apply derives_refl|].
    apply globvars_consts; intros i.
    hnf in H; subst gv; unfold globals_of_env.
    destruct (Map.get (ge_of rho) i); [right; eauto|left; reflexivity]. }
  start_function3.
  forward_call (gv, one).
  Intros r.
  forward.
  Exists r; entailer!.
  rewrite dreal_one in H0; exact (H0 eq_refl H1).
Qed.
