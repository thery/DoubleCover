(** * exp_core: the spec (task T12) *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Import Exp100Capla.ExpBase Exp100Capla.Bridge Exp100Capla.Specs.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Require Import Exp100Capla.NumAddProof Exp100Capla.NumBasicProof.
Require Import Exp100Capla.NumSubProof Exp100Capla.NumLtProof.
Require Import Exp100Capla.NumBitsProof Exp100Capla.NumMulProof.
Require Import Exp100Capla.ReduceProof.

(** ** Symbolic execution one statement at a time

    simplWP on the whole body of exp_core unfolds WP along the whole
    sequence and does not finish: WPc hides the rest of a sequence, and
    wpstep runs its first statement only. *)

(* WP, kept folded by simpl. *)
Definition WPc := WP.
Arguments WPc : simpl never.

(* The first statement of a sequence, with the rest hidden. *)
Lemma WP_seq_c p f s1 s2 Q e se :
  WP p f s1 (fun out => match out with
    | Out_normal => WPc p f s2 Q
    | Out_error => fun _ _ => True
    | Out_exit n => Q (Out_exit n)
    | Out_return r => Q (Out_return r)
    end) e se ->
  WP p f (Sseq s1 s2) Q e se.
Proof. by []. Qed.

Lemma WPcE : WPc = WP.
Proof. by []. Qed.

(* hnf must not unfold it either *)
Opaque WPc.

(* the rest of the body is not printed *)
Notation "'WPc' ..." := (WPc _ _ _ _ _ _) (at level 100, only printing).


(** ** The function exp_core and its body, as constants *)

Definition core_fun : function :=
  Eval cbv beta delta [exp_core138 extract_res] in exp_core138.

Lemma exp_core138E : exp_core138 = core_fun.
Proof. by []. Qed.

Definition core_body : stmt :=
  Eval cbv beta delta [core_fun fn_body] iota in fn_body core_fun.

Lemma core_bodyE : fn_body core_fun = core_body.
Proof. by []. Qed.

(** ** The rest of the body as a suffix of core_body, never unfolded *)

(* the first statement of a sequence, and the others *)
Definition shd (s : stmt) : stmt := match s with Sseq a _ => a | _ => s end.
Definition srest (s : stmt) : stmt := match s with Sseq _ r => r | _ => Sskip end.
Definition sis_seq (s : stmt) : bool :=
  match s with Sseq _ _ => true | _ => false end.

(* the body without its first k statements *)
Fixpoint tl (k : nat) (s : stmt) : stmt :=
  match k with O => s | S k => srest (tl k s) end.
Arguments tl : simpl never.

Lemma seq_split s : sis_seq s = true -> s = Sseq (shd s) (srest s).
Proof. by case: s. Qed.

(* expose the first statement of the rest, the others stay folded *)
Ltac open_tl := lazymatch goal with
  | |- WPc _ _ (tl ?k ?b) _ _ _ =>
      let h := eval cbv beta iota delta [shd srest tl core_body] in (shd (tl k b)) in
      lazymatch eval cbv beta iota delta [sis_seq srest tl core_body] in
        (sis_seq (tl k b)) with
      | true =>
          rewrite (seq_split (tl k b) (erefl true));
          change (shd (tl k b)) with h; change (srest (tl k b))
            with (tl (S k) b)
      | false => change (tl k b) with h
      end
  end.

(* a statement that calls no function and tests nothing *)
Ltac nocall a :=
  lazymatch a with
  | context [Scall _ _ _] => fail
  | context [Sifthenelse _ _ _] => fail
  | _ => idtac
  end.

(* run the next statement when it calls no function and tests nothing *)
Ltac wpone := try open_tl; lazymatch goal with
  | |- WPc _ _ (Sseq ?a _) _ _ _ =>
      nocall a; rewrite {1}WPcE -?lock; apply: WP_seq_c; simplWP
  | |- WPc _ _ ?a _ _ _ => nocall a; rewrite {1}WPcE -?lock; simplWP
  | |- WP _ _ (Sseq ?a _) _ _ _ =>
      nocall a; rewrite -?lock; apply: WP_seq_c; simplWP
  end.

(* run the statements up to a call or a test *)
Ltac wpauto := repeat (wpone; repeat prog).

(* enter the next statement, whatever it is *)
Ltac wpenter := try open_tl; lazymatch goal with
  | |- WPc _ _ (Sseq _ _) _ _ _ =>
      rewrite {1}WPcE -?lock; apply: WP_seq_c; simplWP; repeat prog
  | |- WPc _ _ _ _ _ _ => rewrite {1}WPcE -?lock; simplWP; repeat prog
  end.

(* split on the first test of the goal *)
Ltac wpcase B :=
  match goal with |- context [if ?b then _ else _] => case B: b end;
  rewrite -?lock; simplWP; repeat prog.

(* the shape of each goal *)
Ltac summ := lazymatch goal with
  | |- WPc _ _ (Sseq ?a _) _ _ _ => idtac "WPc-seq" a
  | |- WPc _ _ ?a _ _ _ => idtac "WPc" a
  | |- WP _ _ ?a _ _ _ => idtac "WP"
  | |- (if ?b then _ else _) => idtac "IF" b
  | |- ?a -> _ => idtac "ARROW" a
  | |- ?g => idtac "OTHER"
  end.

(** ** The words of exp_core *)

Section CoreWords.
Transparent Int64.repr Int64.unsigned Int.repr Int.unsigned Int.modu.

Lemma max_unsigned64 : Int64.max_unsigned = 18446744073709551615%Z.
Proof. by []. Qed.

(* c >> k, for a shift amount below 64 *)
Lemma shru_k (c : int64) k : (0 <= k < 64)%Z ->
  Int64.unsigned (Int64.shru' c (Int.modu (Int.repr k) Int64.iwordsize')) =
  (Int64.unsigned c / 2 ^ k)%Z.
Proof.
  move=> Hk.
  have Ek : Int.unsigned (Int.repr k) = k.
  { rewrite Int.unsigned_repr //; change Int.max_unsigned with 4294967295%Z; lia. }
  have -> : Int.modu (Int.repr k) Int64.iwordsize' = Int.repr k.
  { rewrite /Int.modu Ek; f_equal; apply: Z.mod_small.
    change (Int.unsigned Int64.iwordsize') with 64%Z; lia. }
  rewrite /Int64.shru' Ek Z.shiftr_div_pow2; first lia.
  have := Int64.unsigned_range c; have := Z.pow_pos_nonneg 2 k ltac:(lia) (proj1 Hk).
  move=> H2 Hc.
  have := Z.div_le_upper_bound (Int64.unsigned c) (2 ^ k) (Int64.unsigned c) H2
    ltac:(nia).
  have := Z.div_pos (Int64.unsigned c) (2 ^ k) ltac:(lia) H2.
  move=> ? ?; rewrite Int64.unsigned_repr // max_unsigned64.
  change Int64.modulus with 18446744073709551616%Z in Hc; lia.
Qed.

(* c & (2^k - 1) *)
Lemma and_low (c : int64) k : (0 <= k < 64)%Z ->
  Int64.unsigned (Int64.and c (Int64.repr (2 ^ k - 1))) =
  (Int64.unsigned c mod 2 ^ k)%Z.
Proof.
  move=> Hk.
  have := Int64.zero_ext_and k c (proj1 Hk); rewrite two_p_equiv => <-.
  rewrite Int64.zero_ext_mod ?two_p_equiv //.
Qed.

(* m | 2^52, for m < 2^52 *)
Lemma or_top (m : int64) : (Int64.unsigned m < 2 ^ 52)%Z ->
  Int64.unsigned (Int64.or m (Int64.repr 4503599627370496)) =
  (Int64.unsigned m + 2 ^ 52)%Z.
Proof.
  move=> Hm.
  have Ec : Int64.unsigned (Int64.repr 4503599627370496) = (1 * 2 ^ 52)%Z by [].
  have R := Int64.unsigned_range m.
  rewrite /Int64.or Ec lor_add; [lia|lia|].
  rewrite Int64.unsigned_repr; first (rewrite max_unsigned64; lia).
  lia.
Qed.

End CoreWords.

(* The sign, the biased exponent and the stored mantissa of xb. *)
Lemma neg_val (xb : int64) :
  Int64.unsigned (Int64.shru' xb (Int.modu (Int.repr 63) Int64.iwordsize')) =
  ExpModel.xsign (Int64.unsigned xb).
Proof. by rewrite shru_k // ExpModel.xsignE. Qed.

Lemma be_val (xb : int64) :
  Int64.unsigned (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) = ExpModel.xbexp (Int64.unsigned xb).
Proof.
  have -> : Int64.repr 2047 = Int64.repr (2 ^ 11 - 1) by [].
  by rewrite and_low // shru_k // ExpModel.xbexpE.
Qed.

(* A failure: the return code is that of core_Z. *)
Lemma rc_fail (x k : Z) (P : Prop) : (1 <= k <= 3)%Z ->
  ExpModel.core_Z x = inl k ->
  exists rc, Vint64 (Int64.repr k) = Vint64 rc /\
    (Int64.unsigned rc <> 0 -> ExpModel.core_Z x = inl (Int64.unsigned rc)) /\
    (Int64.unsigned rc = 0 -> P).
Proof.
  move=> Hk Hc; exists (Int64.repr k).
  rewrite Int64.unsigned_repr; first by rewrite max_unsigned64; lia.
  by split=> //; split=> // H; lia.
Qed.

(* be < 1033 *)
Lemma core_small (xb : int64) :
  ~~ Int64.ltu (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) (Int64.repr 1033) = false ->
  (ExpModel.xbexp (Int64.unsigned xb) < ExpModel.be_big)%Z.
Proof.
  move/negbFE; rewrite -be_val /Int64.ltu; case: zlt => // + _.
  rewrite /ExpModel.be_big Int64.unsigned_repr; first by rewrite max_unsigned64.
  lia.
Qed.

(* The arguments of num_scale: X = floor(|x| 2^P). *)
Lemma scale_args (x : Z) : (ExpModel.xbexp x < ExpModel.be_big)%Z ->
  (Int64.unsigned (Int64.repr (ExpModel.xmant x)) < 2 ^ mant53)%Z /\
  (Int64.signed (Int64.sub (Int64.repr (ExpModel.xexpo x)) (Int64.repr 915))
     < scale_emax)%Z /\
  ExpModel.scale (Int64.unsigned (Int64.repr (ExpModel.xmant x)))
    (Int64.signed (Int64.sub (Int64.repr (ExpModel.xexpo x)) (Int64.repr 915))) =
  ExpModel.xfix x.
Proof.
  move=> Hb.
  have Bm := ExpModelBounds.xmant_bound x.
  have Be := ExpModelBounds.xexpo_bound x Hb.
  move: Bm Be; rewrite /ExpModel.be_big /mant53 /scale_emax => Bm Be.
  have Em : Int64.unsigned (Int64.repr (ExpModel.xmant x)) = ExpModel.xmant x.
  { rewrite Int64.unsigned_repr // max_unsigned64; lia. }
  have Ee : Int64.signed (Int64.sub (Int64.repr (ExpModel.xexpo x)) (Int64.repr 915)) =
            (ExpModel.xexpo x - 915)%Z.
  { have H1 : Int64.unsigned (Int64.repr (ExpModel.xexpo x)) = ExpModel.xexpo x.
    { rewrite Int64.unsigned_repr // max_unsigned64; lia. }
    rewrite Int64.sub_signed !Int64.signed_repr.
    all: change Int64.min_signed with (-9223372036854775808)%Z.
    all: change Int64.max_signed with 9223372036854775807%Z.
    all: try lia.
    rewrite Int64.signed_repr //.
    change Int64.min_signed with (-9223372036854775808)%Z.
    change Int64.max_signed with 9223372036854775807%Z; lia. }
  rewrite Em Ee ExpModelBounds.xfixE; split; [lia|split; [lia|]].
  by f_equal; lia.
Qed.

(* be >= 1033: |x| >= 1024 *)
Lemma core_big (xb : int64) :
  Int64.ltu (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) (Int64.repr 1033) = false ->
  ExpModel.core_Z (Int64.unsigned xb) = inl ExpModel.rc_big.
Proof.
  move=> H; apply: ExpModelBounds.core_Z_big; rewrite -be_val.
  move: H; rewrite /Int64.ltu; case: zlt => // + _.
  rewrite /ExpModel.be_big Int64.unsigned_repr; first by rewrite max_unsigned64.
  lia.
Qed.

Lemma mx_val (xb : int64) :
  Int64.unsigned (Int64.and xb (Int64.repr 4503599627370495)) =
  ExpModel.xmant0 (Int64.unsigned xb).
Proof.
  have -> : Int64.repr 4503599627370495 = Int64.repr (2 ^ 52 - 1) by [].
  by rewrite and_low // ExpModel.xmant0E.
Qed.

(* be = 0: a subnormal x, exponent 1, no implicit bit *)
Lemma be_merge0 (xb : int64) :
  Int64.eq (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) (Int64.repr 0) = true ->
  Vint64 (Int64.repr 1) =
    Vint64 (Int64.repr (ExpModel.xexpo (Int64.unsigned xb))) /\
  Vint64 (Int64.and xb (Int64.repr 4503599627370495)) =
    Vint64 (Int64.repr (ExpModel.xmant (Int64.unsigned xb))).
Proof.
  move=> H.
  have E0 : ExpModel.xbexp (Int64.unsigned xb) = 0%Z.
  { rewrite -be_val; move: H; rewrite /Int64.eq; case: zeq => // -> _.
  }
  have [-> ->] := ExpModelBounds.xexpo_0 _ E0.
  by rewrite -mx_val Int64.repr_unsigned.
Qed.

(* be <> 0: a normal x, the implicit bit is set *)
Lemma be_merge1 (xb : int64) :
  Int64.eq (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) (Int64.repr 0) = false ->
  Vint64 (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) =
    Vint64 (Int64.repr (ExpModel.xexpo (Int64.unsigned xb))) /\
  Vint64 (Int64.or (Int64.and xb (Int64.repr 4503599627370495))
    (Int64.repr 4503599627370496)) =
    Vint64 (Int64.repr (ExpModel.xmant (Int64.unsigned xb))).
Proof.
  move=> H.
  have N0 : ExpModel.xbexp (Int64.unsigned xb) <> 0%Z.
  { rewrite -be_val; move: H; rewrite /Int64.eq; case: zeq => // + _.
  }
  have [E1 E2] := ExpModelBounds.xexpo_n _ N0.
  rewrite E1 E2.
  have Bm := ExpModelBounds.xmant0_bound (Int64.unsigned xb).
  split; first by rewrite -be_val Int64.repr_unsigned.
  rewrite -(Int64.repr_unsigned (Int64.or _ _)) or_top ?mx_val //; lia.
Qed.




(* The return code and, on success, y and hN as core_Z gives them; the
   scratch X q q1 r are left as arrays of 6 words. *)
Theorem exp_core_spec xb ys hs Xs qs q1s rs hhs ts Ta Ca L2a RMa e1 result :
  tables_ok Ta Ca L2a RMa ->
  length ys = 6%nat -> length hs = 1%nat ->
  length Xs = 6%nat -> length qs = 6%nat -> length q1s = 6%nat ->
  length rs = 6%nat -> length hhs = 6%nat -> length ts = 6%nat ->
  eval_funcall ge (Internal exp_core138)
    [Vint64 xb; Varr (map Vint64 ys); Varr (map Vint64 hs);
     Varr (map Vint64 Xs); Varr (map Vint64 qs); Varr (map Vint64 q1s);
     Varr (map Vint64 rs); Varr (map Vint64 hhs); Varr (map Vint64 ts);
     Ta; Ca; L2a; RMa] e1 (Some result) ->
  exists rc, result = Vint64 rc /\
    (Int64.unsigned rc <> 0%Z ->
       ExpModel.core_Z (Int64.unsigned xb) = inl (Int64.unsigned rc)) /\
    (Int64.unsigned rc = 0%Z ->
       exists ys' hN,
         e1!(param 1 exp_core138) = Some (Varr (map Vint64 ys')) /\
         length ys' = 6%nat /\ limbs ys' /\
         e1!(param 2 exp_core138) = Some (Varr [Vint64 hN]) /\
         ExpModel.core_Z (Int64.unsigned xb) =
           inr (val32 ys', Int64.signed hN) /\
         arr6 (e1!(param 3 exp_core138)) /\ arr6 (e1!(param 4 exp_core138)) /\
         arr6 (e1!(param 5 exp_core138)) /\ arr6 (e1!(param 6 exp_core138))).
Proof.
  move=> Hok Hy Hh HX Hq Hq1 Hr Hhh Ht.
  Opaque ExpModel.guess ExpModel.q ExpModel.mulshr ExpModel.scale ExpModel.xfix
    ExpModel.Cv ExpModel.Tv ExpModel.rarg ExpModel.Nu ExpModel.jidx ExpModel.hidx
    ExpModel.horner_from ExpModel.horner ExpModel.xexpo ExpModel.xmant
    ExpModel.xsign ExpModel.xbexp ExpModel.reduce ExpModel.core_Z ExpModel.low
    ExpModel.shr ExpModel.pow2 ExpModel.LN2v ExpModel.RMAXv.
  rewrite exp_core138E.
  case/eval_funcall_internal_OK_inv => ?? out se1 ? [<-] [<-] exec; intros ??.
  hide_envs E value in exec.
  hide_envs SE (list (list nat)) in exec.
  match goal with H : Some result = outcome_result_value out |- _ =>
    have := H end.
  pattern out, e1, se1.
  apply: (WP_sound _ _ _ _ _ _ _ _ _ _ _ _ exec); first (by destruct out).
  rewrite core_bodyE.
  clear exec.
  change core_body with (tl 0 core_body).
  rewrite -[WP]WPcE.
  wpauto.
  try clear E SE.
  (* |x| >= 1024 *)
  wpenter; wpcase B1.
  all: try wpenter.
  1: by move=> ->; apply: rc_fail => //; exact: core_big (negbTE B1).
  (* be = 0 or not: the two paths meet with be = xexpo, mx = xmant *)
  open_tl.
  match goal with |- WPc ?p ?f (Sseq _ ?R) ?Q ?E ?SE =>
    assert (HG : forall vt vbe vmx,
      vbe = Vint64 (Int64.repr (ExpModel.xexpo (Int64.unsigned xb))) ->
      vmx = Vint64 (Int64.repr (ExpModel.xmant (Int64.unsigned xb))) ->
      WPc p f R Q (PTree.set 193%positive vt (PTree.set 116%positive vbe
        (PTree.set 117%positive vmx E))) (PTree.set 193%positive [] SE)) end.
  2: wpenter; wpcase B2.
  2: { have [E1 E2] := be_merge0 xb B2.
       apply: HG; [exact E1 | exact E2]. }
  2: { have [E1 E2] := be_merge1 xb B2.
       apply: HG; [exact E1 | exact E2]. }
  move=> vt vbe vmx -> ->.
Admitted.
