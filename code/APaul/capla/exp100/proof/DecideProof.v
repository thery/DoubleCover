(** * decide: the spec (task T12) *)

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
Require Import Exp100Capla.GroupALemmas.
Require Import Exp100Capla.NumAddProof Exp100Capla.NumBasicProof.
Require Import Exp100Capla.NumSubProof Exp100Capla.NumLtProof.
Require Import Exp100Capla.NumBitsProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(** ** Symbolic execution one statement at a time (as in ExpCoreProof.v) *)

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

(* WPc unfolded, by rewriting *)
Lemma WPcE : WPc = WP.
Proof. by []. Qed.

(* hnf must not unfold it either *)
Opaque WPc.

(* the rest of the body is not printed *)
Notation "'WPc' ..." := (WPc _ _ _ _ _ _) (at level 100, only printing).

(* a statement that calls no function and tests nothing *)
Ltac nocall a :=
  lazymatch a with
  | context [Scall _ _ _] => fail
  | context [Sifthenelse _ _ _] => fail
  | _ => idtac
  end.

(* run the next statement when it calls no function and tests nothing *)
Ltac wpone := lazymatch goal with
  | |- WPc _ _ (Sseq ?a _) _ _ _ =>
      nocall a; rewrite {1}WPcE -?lock; apply: WP_seq_c; simplWP
  | |- WPc _ _ ?a _ _ _ => nocall a; rewrite {1}WPcE -?lock; simplWP
  | |- WP _ _ (Sseq ?a _) _ _ _ =>
      nocall a; rewrite -?lock; apply: WP_seq_c; simplWP
  end.

(* run the statements up to a call or a test *)
Ltac wpauto := repeat (wpone; repeat prog).

(* enter the next statement, whatever it is *)
Ltac wpenter := lazymatch goal with
  | |- WPc _ _ (Sseq _ _) _ _ _ =>
      rewrite {1}WPcE -?lock; apply: WP_seq_c; simplWP; repeat prog
  | |- WPc _ _ _ _ _ _ => rewrite {1}WPcE -?lock; simplWP; repeat prog
  end.

(** ** The function decide and its body, as constants *)

Definition decide_fun : function :=
  Eval cbv beta delta [decide176 extract_res] in decide176.

Lemma decide176E : decide176 = decide_fun.
Proof. by []. Qed.

Definition decide_body : stmt :=
  Eval cbv beta delta [decide_fun fn_body] iota in fn_body decide_fun.

Lemma decide_bodyE : fn_body decide_fun = decide_body.
Proof. by []. Qed.

(** ** The numbers of decide *)

(* The number D = 16 on six words. *)
Definition Dw : list int64 :=
  [Int64.repr 16; Int64.zero; Int64.zero; Int64.zero; Int64.zero; Int64.zero].

Section DecideWords.
Transparent Int64.repr Int64.unsigned Z.to_nat.

(* Writing 16 in limb 0 of six zero words gives D. *)
Lemma Dw_replace :
  replace (Z.to_nat (Int64.unsigned (Int64.repr 0)))
    [Vint64 Int64.zero; Vint64 Int64.zero; Vint64 Int64.zero;
     Vint64 Int64.zero; Vint64 Int64.zero; Vint64 Int64.zero]
    (Vint64 (Int64.repr 16)) = map Vint64 Dw.
Proof. by []. Qed.

(* D as an array value *)
Lemma Dw_lit :
  [Vint64 (Int64.repr 16); Vint64 Int64.zero; Vint64 Int64.zero;
   Vint64 Int64.zero; Vint64 Int64.zero; Vint64 Int64.zero] = map Vint64 Dw.
Proof. by []. Qed.

Lemma Dw_num : length Dw = 6%nat /\ limbs Dw /\ val32 Dw = 16%Z.
Proof.
  split => //; split => //.
  apply/limbs_Forall; repeat constructor; rewrite /limb /limb_bits /=; lia.
Qed.

End DecideWords.

(* A number of six limbs is below 2^192. *)
Lemma val6 l : length l = 6%nat -> limbs l -> (0 <= val32 l < 2 ^ 192)%Z.
Proof.
  move=> Hl Ll; split; first exact: val32_nonneg.
  by have := val32_bound l Ll; rewrite Hl.
Qed.

(** ** Words of the exponent computation *)

(* A signed word of a value: the value modulo 2^64. *)
Lemma eqm_signed_repr x : Int64.eqm (Int64.signed (Int64.repr x)) x.
Proof.
  apply: Int64.eqm_trans; first exact: Int64.eqm_signed_unsigned.
  exact/Int64.eqm_sym/Int64.eqm_unsigned_repr.
Qed.

Lemma sub_repr x y :
  Int64.sub (Int64.repr x) (Int64.repr y) = Int64.repr (x - y).
Proof.
  rewrite Int64.sub_signed; apply: Int64.eqm_samerepr.
  by apply: Int64.eqm_sub; apply: eqm_signed_repr.
Qed.

Lemma add_repr x y :
  Int64.add (Int64.repr x) (Int64.repr y) = Int64.repr (x + y).
Proof.
  rewrite Int64.add_signed; apply: Int64.eqm_samerepr.
  by apply: Int64.eqm_add; apply: eqm_signed_repr.
Qed.

(* The bound of the small values of decide. *)
Definition small64 (x : Z) : Prop := (- 2 ^ 62 <= x <= 2 ^ 62)%Z.

Lemma signed_small x : small64 x -> Int64.signed (Int64.repr x) = x.
Proof.
  rewrite /small64 => H; apply: Int64.signed_repr.
  change Int64.min_signed with (-9223372036854775808)%Z.
  change Int64.max_signed with 9223372036854775807%Z.
  have E : (2 ^ 62 = 4611686018427387904)%Z by [].
  lia.
Qed.

Lemma small64_le x : (- 10000 <= x <= 10000)%Z -> small64 x.
Proof.
  rewrite /small64 => H; have E : (2 ^ 62 = 4611686018427387904)%Z by [].
  lia.
Qed.

(* e = hN - 160 + b - 1 *)
Lemma e_word hN b :
  Int64.sub (Int64.add (Int64.sub hN (Int64.repr 160)) (Int64.repr b))
    (Int64.repr 1) = Int64.repr (Int64.signed hN - 160 + b - 1).
Proof.
  by rewrite -{1}(Int64.repr_signed hN) sub_repr add_repr sub_repr.
Qed.

(* fs = ve - 53 - (hN - 160) *)
Lemma fs_word V hN :
  Int64.sub (Int64.sub (Int64.repr V) (Int64.repr 53))
    (Int64.sub hN (Int64.repr 160)) =
  Int64.repr (V - 53 - (Int64.signed hN - 160)).
Proof.
  by rewrite -{1}(Int64.repr_signed hN) sub_repr sub_repr sub_repr.
Qed.

Lemma lt_small x y : small64 x -> small64 y ->
  Int64.lt (Int64.repr x) (Int64.repr y) = (x <? y)%Z.
Proof.
  move=> Hx Hy; rewrite /Int64.lt (signed_small x Hx) (signed_small y Hy).
  case: zlt => H; symmetry; [apply/Z.ltb_lt | apply/Z.ltb_ge]; lia.
Qed.

(* A small value read back as unsigned. *)
Lemma unsigned_small x : (0 <= x <= 192)%Z ->
  Int64.unsigned (Int64.repr x) = x.
Proof.
  move=> H; apply: Int64.unsigned_repr.
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

(* Two bit lengths are equal as words exactly when they are equal. *)
Lemma eq_bits x y : (0 <= x <= 192)%Z -> (0 <= y <= 192)%Z ->
  Int64.eq (Int64.repr x) (Int64.repr y) = (x =? y)%Z.
Proof.
  move=> Hx Hy; rewrite /Int64.eq (unsigned_small x Hx) (unsigned_small y Hy).
  case: zeq => H; symmetry; [apply/Z.eqb_eq | apply/Z.eqb_neq]; lia.
Qed.

Section DecideConst.
Transparent Int64.repr.

(* The constant -1022 as Capla writes it. *)
Lemma repr_m1022 : Int64.repr 18446744073709550594 = Int64.repr (-1022).
Proof. by apply: Int64.eqm_samerepr; exists 1%Z. Qed.

End DecideConst.

(** ** The numbers of decide, in Z *)

(* The bit length of a number of six limbs. *)
Lemma bitlen192 v : (0 <= v < 2 ^ 192)%Z ->
  (0 <= ExpModel.bitlen v <= 192)%Z.
Proof. exact: ExpModelBounds.bitlen_bound. Qed.

(* lo = y mod 2^f is below 2^f. *)
Lemma low_lt y f : (0 <= f)%Z ->
  (0 <= ExpModel.low y f < ExpModel.pow2 f)%Z.
Proof.
  move=> Hf; rewrite ExpModel.lowE // ExpModel.pow2E //.
  apply: Z.mod_pos_bound; lia.
Qed.

(* 2^(f-43) + D fits in six limbs. *)
Lemma pow2_add_D k : (0 <= k <= 141)%Z -> (ExpModel.pow2 k + 16 < 2 ^ 192)%Z.
Proof.
  move=> Hk; rewrite (ExpModel.pow2E k (proj1 Hk)).
  have := Z.pow_le_mono_r 2 k 141 ltac:(lia) ltac:(lia).
  have : (2 ^ 141 + 16 < 2 ^ 192)%Z by apply/Z.ltb_lt.
  generalize (2 ^ k)%Z (2 ^ 141)%Z (2 ^ 192)%Z; lia.
Qed.

(* The decision once the binade is known and f is in its range. *)
Lemma decide_end y s f :
  ExpModel.bitlen (y - 16) = ExpModel.bitlen y ->
  ExpModel.bitlen (y + 16) = ExpModel.bitlen y ->
  f = (Z.max (s - 160 + ExpModel.bitlen y - 1) (-1022) - 53 - (s - 160))%Z ->
  (64 <= f <= 184)%Z ->
  ExpModel.decide_Z y s =
  (if ExpModel.pow2 (f - 43) + 16 <?
      (if ExpModel.low y f <? ExpModel.pow2 f - ExpModel.low y f
       then ExpModel.low y f else ExpModel.pow2 f - ExpModel.low y f)
   then 0 else 1)%Z.
Proof.
  move=> H1 H2 Hf Rf.
  rewrite (ExpModelBounds.decide_f y s f H1 H2 Hf).
  have Ef : ((f <? ExpModel.f_min) || (ExpModel.f_max <? f))%Z = false.
  { have -> : ExpModel.f_max = 184%Z by [].
    rewrite /ExpModel.f_min.
    by apply/negbTE/negP => /orP [] /Z.ltb_lt; lia. }
  by rewrite Ef.
Qed.

(* f out of its range: hard. *)
Lemma decide_out y s f :
  ExpModel.bitlen (y - 16) = ExpModel.bitlen y ->
  ExpModel.bitlen (y + 16) = ExpModel.bitlen y ->
  f = (Z.max (s - 160 + ExpModel.bitlen y - 1) (-1022) - 53 - (s - 160))%Z ->
  (f < 64 \/ 184 < f)%Z ->
  ExpModel.decide_Z y s = 1%Z.
Proof.
  move=> H1 H2 Hf Rf.
  rewrite (ExpModelBounds.decide_f y s f H1 H2 Hf).
  have Ef : ((f <? ExpModel.f_min) || (ExpModel.f_max <? f))%Z = true.
  { have -> : ExpModel.f_max = 184%Z by [].
    rewrite /ExpModel.f_min.
    by case: Rf => H; apply/orP; [left | right]; apply/Z.ltb_lt. }
  by rewrite Ef.
Qed.

(* The decision of decide_Z, on y and hN in the ranges core_Z gives
   (ExpModelBounds.core_bounds). *)
Theorem decide_spec ys hN los his ds ts e1 result :
  length ys = 6%nat -> limbs ys ->
  (2 ^ ExpConsts.P <= val32 ys < 2 ^ ExpModelBounds.y_bits)%Z ->
  (- 2 ^ ExpModelBounds.hN_bits <= Int64.signed hN <=
     2 ^ ExpModelBounds.hN_bits)%Z ->
  length los = 6%nat -> length his = 6%nat -> length ds = 6%nat ->
  length ts = 6%nat ->
  eval_funcall ge (Internal decide176)
    [Varr (map Vint64 ys); Vint64 hN; Varr (map Vint64 los);
     Varr (map Vint64 his); Varr (map Vint64 ds); Varr (map Vint64 ts)]
    e1 (Some result) ->
  result = Vint64 (Int64.repr (ExpModel.decide_Z (val32 ys) (Int64.signed hN))).
Proof.
  move=> Hy Ly Ry RhN Hlo Hhi Hd Ht.
  have [HDl [LD VD]] := Dw_num.
  have Vy := val6 _ Hy Ly.
  have H16 : (16 <= val32 ys)%Z.
  { have : (16 <= 2 ^ ExpConsts.P)%Z by apply/Z.leb_le. lia. }
  have Hy16 : (val32 ys + 16 < 2 ^ 192)%Z.
  { have : (2 ^ ExpModelBounds.y_bits + 16 <= 2 ^ 192)%Z by apply/Z.leb_le.
    lia. }
  have Rs : (- 4096 <= Int64.signed hN <= 4096)%Z.
  { by move: RhN; have -> : (2 ^ ExpModelBounds.hN_bits = 4096)%Z by []. }
  rewrite decide176E.
  case/eval_funcall_internal_OK_inv => ?? out se1 ? [<-] [<-] exec; intros ??.
  hide_envs E value in exec.
  hide_envs SE (list (list nat)) in exec.
  match goal with H : Some result = outcome_result_value out |- _ =>
    have := H end.
  pattern out, e1, se1.
  apply: (WP_sound _ _ _ _ _ _ _ _ _ _ _ _ exec); first (by destruct out).
  rewrite decide_bodyE /decide_body.
  clear exec.
  name_var "y" Y. name_var "lo" LO. name_var "hi" HI.
  name_var "d" DD. name_var "t" TT.
  wpauto.
  wpenter.
  move=> _ _ CALL.
  (* d = D *)
  have E1 := num_zero_spec _ _ _ Hd CALL; clear CALL.
  change (param 0 num_zero6) with (VAR 1%positive "a") in E1.
  repeat prog.
  try clear E SE.
  rewrite E1; clear E1.
  wpauto.
  rewrite Dw_replace.
  wpenter.
  move=> _ _ CALL.
  (* lo = y - D, hi = y + D *)
  have E1 := num_copy_spec _ _ _ _ Hlo Hy CALL; clear CALL.
  change (param 0 num_copy12) with (VAR 1%positive "a") in E1.
  repeat prog.
  rewrite E1; clear E1.
  wpauto.
  wpenter.
  move=> _ _ CALL.
  rewrite Dw_lit in CALL.
  have [lo1 [E1 [Hlo1 [Llo1 Vlo1]]]] := num_sub_spec _ _ _ _ Hy HDl Ly LD
    ltac:(rewrite VD; lia) CALL; clear CALL.
  change (param 0 num_sub27) with (VAR 1%positive "a") in E1.
  repeat prog.
  rewrite E1; clear E1.
  wpauto.
  wpenter.
  rewrite VD in Vlo1.
  move=> _ _ CALL.
  have E1 := num_copy_spec _ _ _ _ Hhi Hy CALL; clear CALL.
  change (param 0 num_copy12) with (VAR 1%positive "a") in E1.
  repeat prog.
  rewrite E1; clear E1.
  wpauto.
  wpenter.
  move=> _ _ CALL.
  rewrite Dw_lit in CALL.
  have [hi1 [E1 [Hhi1 [Lhi1 Vhi1]]]] := num_add_spec _ _ _ _ Hy HDl Ly LD
    ltac:(rewrite VD; lia) CALL; clear CALL.
  change (param 0 num_add18) with (VAR 1%positive "a") in E1.
  rewrite VD in Vhi1.
  repeat prog.
  rewrite E1; clear E1.
  wpauto.
  wpenter.
  move=> _ _ CALL.
  (* the bit lengths of y, lo, hi *)
  move: (num_bitlen_spec _ _ _ Hy Ly CALL) => {CALL} ->.
  repeat prog.
  wpauto.
  wpenter.
  move=> _ _ CALL.
  move: (num_bitlen_spec _ _ _ Hlo1 Llo1 CALL) => {CALL} ->.
  repeat prog.
  wpauto.
  wpenter.
  move=> _ _ CALL.
  move: (num_bitlen_spec _ _ _ Hhi1 Lhi1 CALL) => {CALL} ->.
  repeat prog.
  wpauto.
  have Rb := bitlen192 _ Vy.
  have Rbl := bitlen192 _ (val6 _ Hlo1 Llo1).
  have Rbh := bitlen192 _ (val6 _ Hhi1 Lhi1).
  wpenter.
  (* y - D or y + D out of the binade of y: hard *)
  rewrite (eq_bits _ _ Rbl Rb).
  case B1: (ExpModel.bitlen (val32 lo1) =? ExpModel.bitlen (val32 ys))%Z;
    rewrite -?lock; simplWP; repeat prog.
  all: try wpenter.
  2: { move=> ->; rewrite ExpModelBounds.decide_bits //; left.
       change (ExpModel.bitlen (val32 ys - 16) <> ExpModel.bitlen (val32 ys)).
       rewrite -Vlo1; exact/Z.eqb_neq. }
  rewrite (eq_bits _ _ Rbh Rb).
  case B2: (ExpModel.bitlen (val32 hi1) =? ExpModel.bitlen (val32 ys))%Z;
    rewrite -?lock; simplWP; repeat prog.
  all: try wpenter.
  2: { move=> ->; rewrite ExpModelBounds.decide_bits //; right.
       change (ExpModel.bitlen (val32 ys + 16) <> ExpModel.bitlen (val32 ys)).
       rewrite -Vhi1; exact/Z.eqb_neq. }
  move/Z.eqb_eq: B1; rewrite Vlo1 => B1.
  move/Z.eqb_eq: B2; rewrite Vhi1 => B2.
  wpauto.
  wpenter.
  (* f = max(e, emin) - 53 - (hN - 160), e = hN - 160 + b - 1 *)
  set b := ExpModel.bitlen (val32 ys) in B1 B2 Rb *.
  have [F HF] : exists F, F = (Z.max (Int64.signed hN - 160 + b - 1) (-1022)
                               - 53 - (Int64.signed hN - 160))%Z by eexists.
  have RF : (- 10000 <= F <= 10000)%Z by rewrite HF; lia.
  rewrite (e_word hN b) repr_m1022 lt_small; try (apply: small64_le; lia).
  case C1: (-1022 <? Int64.signed hN - 160 + b - 1)%Z;
    rewrite -?lock; simplWP; repeat prog.
  all: wpauto.
  all: wpenter.
  all: rewrite /sem_binarith /sem_cast /shrink /=.
  all: try rewrite (e_word hN b).
  1: have EF : (Int64.signed hN - 160 + b - 1 - 53 - (Int64.signed hN - 160)
                = F)%Z by rewrite HF; move/Z.ltb_lt: C1; lia.
  2: have EF : (-1022 - 53 - (Int64.signed hN - 160) = F)%Z
       by rewrite HF; move/Z.ltb_ge: C1; lia.
  all: rewrite fs_word EF.
  (* f out of [64, 184]: hard *)
  all: rewrite lt_small; try (apply: small64_le; lia).
  all: case C2: (F <? 64)%Z; rewrite -?lock; simplWP; repeat prog.
  all: try (move=> ->;
            rewrite (decide_out (val32 ys) (Int64.signed hN) F B1 B2 HF) //;
            left; exact/Z.ltb_lt).
  all: wpauto.
  all: try wpenter.
  all: rewrite lt_small; try (apply: small64_le; lia).
  all: case C3: (184 <? F)%Z; rewrite -?lock; simplWP; repeat prog.
  all: try (move=> ->;
            rewrite (decide_out (val32 ys) (Int64.signed hN) F B1 B2 HF) //;
            right; exact/Z.ltb_lt).
  all: move/Z.ltb_ge: C2 => C2; move/Z.ltb_ge: C3 => C3.
  all: wpauto.
  (* lo = y mod 2^f, hi = 2^f - lo *)
  all: clear C1 EF.
  all: have HFu : Int64.unsigned (Int64.repr F) = F
         by apply: unsigned_small; lia.
  all: have HF192 : (Int64.unsigned (Int64.repr F) < ExpModel.num_bits)%Z
         by rewrite HFu; have -> : ExpModel.num_bits = 192%Z by []; lia.
  all: wpenter.
  all: move=> _ _ CALL.
  all: have [lo2 [E1 [Hlo2 [Llo2 Vlo2]]]] :=
         num_low_spec _ _ _ _ _ Hlo1 Hy Ly HF192 CALL.
  all: clear CALL; change (param 0 num_low81) with (VAR 1%positive "a") in E1.
  all: rewrite HFu in Vlo2.
  all: repeat prog.
  all: rewrite E1; clear E1.
  all: wpauto.
  all: wpenter.
  all: move=> _ _ CALL.
  all: have [hi2 [E1 [Hhi2 [Lhi2 Vhi2]]]] :=
         num_pow2_spec _ _ _ _ Hhi1 HF192 CALL.
  all: clear CALL; change (param 0 num_pow272) with (VAR 1%positive "a") in E1.
  all: rewrite HFu in Vhi2.
  all: repeat prog.
  all: rewrite E1; clear E1.
  all: wpauto.
  all: wpenter.
  all: have HL := low_lt (val32 ys) F ltac:(lia).
  all: move=> _ _ CALL.
  all: have [hi3 [E1 [Hhi3 [Lhi3 Vhi3]]]] :=
         num_sub_spec _ _ _ _ Hhi2 Hlo2 Lhi2 Llo2
         ltac:(rewrite Vlo2 Vhi2; lia) CALL.
  all: clear CALL; change (param 0 num_sub27) with (VAR 1%positive "a") in E1.
  all: rewrite Vhi2 Vlo2 in Vhi3.
  all: repeat prog.
  all: rewrite E1; clear E1.
  all: wpauto.
  all: wpenter.
  all: move=> _ _ CALL.
  all: move: (num_lt_spec _ _ _ _ Hlo2 Hhi3 Llo2 Lhi3 CALL) => {CALL} ->.
  all: rewrite Vlo2 Vhi3.
  all: repeat prog.
  all: wpauto.
  all: wpenter.
  (* d = min(lo, hi) *)
  all: case C4: (ExpModel.low (val32 ys) F <?
                 ExpModel.pow2 F - ExpModel.low (val32 ys) F)%Z;
       rewrite -?lock; simplWP; repeat prog.
  all: try wpenter.
  all: move=> _ _ CALL.
  all: rewrite Dw_lit in CALL.
  all: first
    [ have E1 := num_copy_spec _ _ _ _ HDl Hlo2 CALL;
      have Vdd : (val32 lo2 = if ExpModel.low (val32 ys) F <?
                   ExpModel.pow2 F - ExpModel.low (val32 ys) F
                   then ExpModel.low (val32 ys) F
                   else ExpModel.pow2 F - ExpModel.low (val32 ys) F)%Z
        by rewrite C4 Vlo2
    | have E1 := num_copy_spec _ _ _ _ HDl Hhi3 CALL;
      have Vdd : (val32 hi3 = if ExpModel.low (val32 ys) F <?
                   ExpModel.pow2 F - ExpModel.low (val32 ys) F
                   then ExpModel.low (val32 ys) F
                   else ExpModel.pow2 F - ExpModel.low (val32 ys) F)%Z
        by rewrite C4 Vhi3 ].
  all: clear CALL; change (param 0 num_copy12) with (VAR 1%positive "a") in E1.
  all: repeat prog.
  all: rewrite E1; clear E1.
  all: wpauto.
  all: first [ move: (Vdd : val32 lo2 = _) => _; clear Vlo2;
               generalize dependent lo2
             | clear Vhi3; generalize dependent hi3 ].
  all: move=> dd Hdd Ldd Vdd.
  all: repeat match goal with H : env |- _ => clear H end.
  all: repeat match goal with H : senv |- _ => clear H end.
  all: clear Rbl Rbh Vlo1 Vhi1 Hlo1 Llo1 Hhi1 Lhi1 HL.
  all: wpenter.
  all: move=> _ _ CALL.
  (* t = 2^(f-43) + D *)
  all: have U43 :
         Int64.unsigned (Int64.sub (Int64.repr F) (Int64.repr 43)) = (F - 43)%Z
         by rewrite sub_repr; apply: unsigned_small; lia.
  all: have H43 : (Int64.unsigned (Int64.sub (Int64.repr F) (Int64.repr 43)) <
                   ExpModel.num_bits)%Z
         by rewrite U43; have -> : ExpModel.num_bits = 192%Z by []; lia.
  all: have [t1 [E1 [Ht1 [Lt1 Vt1]]]] :=
         num_pow2_spec _ (Int64.sub (Int64.repr F) (Int64.repr 43)) _ _
           Ht H43 CALL.
  all: clear CALL; change (param 0 num_pow272) with (VAR 1%positive "a") in E1.
  all: rewrite U43 in Vt1.
  all: repeat prog.
  all: rewrite E1; clear E1.
  all: wpauto.
  all: wpenter.
  all: move=> _ _ CALL.
  all: eapply num_zero_spec in CALL; try (first [exact Hhi3 | exact Hdd]).
  all: change (param 0 num_zero6) with (VAR 1%positive "a") in CALL.
  all: repeat prog.
  all: rewrite CALL; clear CALL.
  all: wpauto.
  all: rewrite Dw_replace.
  all: wpenter.
  all: move=> _ _ CALL.
  all: rewrite Dw_lit in CALL.
  all: have [t2 [E1 [Ht2 [Lt2 Vt2]]]] := num_add_spec _ _ _ _ Ht1 HDl Lt1 LD
         ltac:(rewrite Vt1 VD; apply: pow2_add_D; lia) CALL.
  all: clear CALL; change (param 0 num_add18) with (VAR 1%positive "a") in E1.
  all: rewrite Vt1 VD in Vt2.
  all: repeat prog.
  all: rewrite E1; clear E1.
  all: wpauto.
  all: wpenter.
  all: move=> _ _ CALL.
  (* the test t < d *)
  all: move: (num_lt_spec _ _ _ _ Ht2 Hdd Lt2 Ldd CALL) => {CALL} ->.
  all: repeat prog.
  all: wpauto.
  all: try wpenter.
  all: case C5: (val32 t2 <? val32 dd)%Z; rewrite -?lock; simplWP; repeat prog.
  all: try wpauto.
  all: try wpenter.
  all: move=> ->.
  all: by rewrite (decide_end (val32 ys) (Int64.signed hN) F B1 B2 HF
                   ltac:(lia)) -Vdd -Vt2 C5.
Qed.
