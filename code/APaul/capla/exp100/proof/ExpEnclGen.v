(** * exp_encl_bits, with exp_core as a hypothesis

    exp_encl_bits calls exp_core (ExpCoreProof.v), used here through its
    spec, stated as a Section hypothesis.  ExpTopProof.v instantiates it. *)

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
Require Import Exp100Capla.GroupALemmas Exp100Capla.TopLemmasCapla.
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

Lemma WPcE : WPc = WP.
Proof. by []. Qed.

Opaque WPc.

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

(* split on the first test of the goal *)
Ltac wpcase B :=
  match goal with |- context [if ?b then _ else _] => case B: b end;
  rewrite -?lock; simplWP; repeat prog.

(* the head of a statement, for probes *)
Ltac shead a :=
  lazymatch a with
  | Sseq ?x _ => shead x
  | Scall _ ?f _ => idtac "call" f
  | Sletref _ (Scall _ ?f _) => idtac "letref-call" f
  | Sletref _ _ => idtac "letref"
  | Sifthenelse _ _ _ => idtac "if"
  | Sassign (?i, _) _ => idtac "assign" i
  | Sfree ?i => idtac "free" i
  | Salloc ?i _ => idtac "alloc" i
  | Sloop _ => idtac "loop"
  | Sblock _ => idtac "block"
  | Sreturn _ => idtac "return"
  | Sskip => idtac "skip"
  | _ => idtac "stmt"
  end.

(* the shape of the goal, for probes *)
Ltac summ := lazymatch goal with
  | |- WPc _ _ ?a _ _ _ => idtac "WPc"; shead a
  | |- WP _ _ ?a _ _ _ => idtac "WP"; shead a
  | |- (if ?b then _ else _) => idtac "IF"
  | |- let% _ := _ in _ => idtac "LET"
  | |- forall _, _ => idtac "FORALL"
  | |- ?a -> _ => idtac "ARROW"
  | |- exists _, _ => idtac "EXISTS"
  | |- _ = _ => idtac "EQ"
  | |- _ => idtac "OTHER"
  end.

(** ** Pure steps of exp_encl_bits (no WP) *)

(* rc == 0 as a boolean test. *)
Lemma rc_eq0 rc : Int64.eq rc (Int64.repr 0) = true -> Int64.unsigned rc = 0%Z.
Proof.
  have := Int64.eq_spec rc (Int64.repr 0) => + H; rewrite H => ->.
  exact: Int64.unsigned_zero.
Qed.

Lemma rc_neq0 rc : Int64.eq rc (Int64.repr 0) = false -> Int64.unsigned rc <> 0%Z.
Proof.
  have := Int64.eq_spec rc (Int64.repr 0) => + H; rewrite H => Hne Hu; apply: Hne.
  by rewrite -(Int64.repr_unsigned rc) Hu.
Qed.

(* Word i of M: limbs 2i and 2i+1 of y. *)
Definition packw (ys : list int64) (i : nat) : int64 :=
  Int64.or (List.nth (2 * i) ys Int64.zero)
    (Int64.shl' (List.nth (2 * i + 1) ys Int64.zero)
       (Int.modu (Int.repr 32) Int64.iwordsize')).

(* The value M[i] = y[2i] | (y[2i+1] << 32) computed by Capla. *)
Lemma pack_word a b :
  shrink u64 (sem_binarith Oor OInt64 (Vint64 a)
    (sem_binarith Oshl OInt64 (Vint64 b) (Vint (Int.repr 32)))) =
  Vint64 (Int64.or a (Int64.shl' b (Int.modu (Int.repr 32) Int64.iwordsize'))).
Proof. by []. Qed.

(* The index 2 i, for i < 3. *)
Lemma idx2 k : (Int64.unsigned k < 3)%Z ->
  Z.to_nat (Int64.unsigned (Int64.mul (Int64.repr 2) k)) =
  (2 * Z.to_nat (Int64.unsigned k))%nat.
Proof. move=> Hk; clia k. Qed.

(* The index 2 i + 1, for i < 3. *)
Lemma idx2S k : (Int64.unsigned k < 3)%Z ->
  Z.to_nat (Int64.unsigned (Int64.add (Int64.mul (Int64.repr 2) k) (Int64.repr 1))) =
  (2 * Z.to_nat (Int64.unsigned k) + 1)%nat.
Proof. move=> Hk; clia k. Qed.

(* The write of the packing loop, as a list of words. *)
Lemma pack_write (ys ms : list int64) k :
  length ys = 6%nat -> length ms = 3%nat -> (Int64.unsigned k < 3)%Z ->
  replace (Z.to_nat (Int64.unsigned k)) (map Vint64 ms)
    (shrink u64 (sem_binarith Oor OInt64
       (List.nth (Z.to_nat (Int64.unsigned (Int64.mul (Int64.repr 2) k)))
          (map Vint64 ys) Vundef)
       (sem_binarith Oshl OInt64
          (List.nth (Z.to_nat (Int64.unsigned
             (Int64.add (Int64.mul (Int64.repr 2) k) (Int64.repr 1))))
             (map Vint64 ys) Vundef)
          (Vint (Int.repr 32))))) =
  map Vint64 (replace (Z.to_nat (Int64.unsigned k)) ms
                (packw ys (Z.to_nat (Int64.unsigned k)))).
Proof.
  move=> Hy Hm Hk.
  rewrite idx2 // idx2S // !nth_map_V64 ?length_map; try lia.
  by rewrite pack_word replace_map.
Qed.

(* The invariant of the packing loop after one more step. *)
Lemma pack_inv (ys ms : list int64) n :
  length ys = 6%nat -> limbs ys -> length ms = 3%nat -> (n < 3)%coq_nat ->
  (forall j, (j < n)%coq_nat ->
     Int64.unsigned (List.nth j ms Int64.zero) =
     (Int64.unsigned (List.nth (2 * j) ys Int64.zero) +
      2 ^ 32 * Int64.unsigned (List.nth (2 * j + 1) ys Int64.zero))%Z) ->
  forall j, (j < S n)%coq_nat ->
     Int64.unsigned (List.nth j (replace n ms (packw ys n)) Int64.zero) =
     (Int64.unsigned (List.nth (2 * j) ys Int64.zero) +
      2 ^ 32 * Int64.unsigned (List.nth (2 * j + 1) ys Int64.zero))%Z.
Proof.
  move=> Hy Ly Hm Hn H j Hj.
  have [Hj'|->] : (j < n)%coq_nat \/ j = n by lia.
  - rewrite nth_replace_other; first lia; exact: H.
  - by rewrite nth_replace_same ?Hm // /packw or_shl32 //; exact: Ly.
Qed.

Section Encl.

(* The spec of exp_core (ExpCoreProof.v). *)
Hypothesis exp_core_spec : forall xb ys hs Xs qs q1s rs hhs ts Ta Ca L2a RMa e1 result,
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

(* The return code and, on success, M (3 words) and s as exp_encl_Z gives
   them. *)
Lemma exp_encl_bits_gen xb ms ss Ta Ca L2a RMa e1 result :
  tables_ok Ta Ca L2a RMa -> length ms = 3%nat -> length ss = 1%nat ->
  eval_funcall ge (Internal exp_encl_bits155)
    [Vint64 xb; Varr (map Vint64 ms); Varr (map Vint64 ss); Ta; Ca; L2a; RMa]
    e1 (Some result) ->
  exists rc, result = Vint64 rc /\
    (Int64.unsigned rc <> 0%Z ->
       ExpModel.exp_encl_Z (Int64.unsigned xb) = inl (Int64.unsigned rc)) /\
    (Int64.unsigned rc = 0%Z ->
       exists ms' s,
         e1!(param 1 exp_encl_bits155) = Some (Varr (map Vint64 ms')) /\
         length ms' = 3%nat /\
         e1!(param 2 exp_encl_bits155) = Some (Varr [Vint64 s]) /\
         ExpModel.exp_encl_Z (Int64.unsigned xb) =
           inr (valW (map Int64.unsigned ms'), Int64.signed s)).
Proof.
  move=> Htab Hm Hs.
  case: ss Hs => [|s0 [|? ?]] // _.
  intro_eval_funcall exp_encl_bits155 out se1 exec.
  match goal with H : Some result = outcome_result_value out |- _ =>
    have := H end.
  pattern out, e1, se1.
  apply: (WP_sound _ _ _ _ _ _ _ _ _ _ _ _ exec); first (by destruct out).
  change (fn_body FUNC) with BODY; rewrite /BODY.
  wpauto.
  (* the 8 allocs give zeros; exp_core through its spec *)
  wpenter.
  move=> _ _ CALL.
  have [rc [Erc [Hko Hok]]] := exp_core_spec xb (repeat Int64.zero 6) [Int64.zero]
    (repeat Int64.zero 6) (repeat Int64.zero 6) (repeat Int64.zero 6)
    (repeat Int64.zero 6) (repeat Int64.zero 6) (repeat Int64.zero 6)
    Ta Ca L2a RMa _ _ Htab (repeat_length _ _) erefl (repeat_length _ _)
    (repeat_length _ _) (repeat_length _ _) (repeat_length _ _)
    (repeat_length _ _) (repeat_length _ _) CALL.
  subst; repeat prog; clear CALL.
  wpauto.
  wpenter.
  wpcase B.
  all: wpauto.
  2: { (* rc <> 0: the frees, then return rc *)
       do 9 (try move=> ?; repeat prog; first [ wpone | wpenter | idtac ];
             repeat prog).
       exists rc; split => //; split.
       - by move=> Hrc; apply: encl_fail; apply: Hko.
       - by move=> Hrc; case: (rc_neq0 _ B). }
  (* rc = 0: y and hN from exp_core's spec *)
  have [ys' [hN [E1 [Hly [Ly [E2 [Hcore _]]]]]]] := Hok (rc_eq0 _ B).
  rewrite E1 E2.
  name_var "i" I.
  name_var "M" MM.
  (* after k steps, M[j] = y[2j] + 2^32 y[2j+1] for j < k *)
  pose Inv := fun (e: env) (se: senv) =>
    exists k ms',
      e!I = Some (Vint64 k) /\ (Int64.unsigned k <= 3)%Z /\
      e!MM = Some (Varr (map Vint64 ms')) /\ length ms' = 3%nat /\
      (forall j, (j < nat_of k)%coq_nat ->
         Int64.unsigned (List.nth j ms' Int64.zero) =
         (Int64.unsigned (List.nth (2 * j) ys' Int64.zero) +
          2 ^ 32 * Int64.unsigned (List.nth (2 * j + 1) ys' Int64.zero))%Z).
  exists Inv; split.
  - exists (Int64.repr 0), ms.
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & ms' & [= ->] & Hk3 & [= ->] & Hl & Hlo).
    tidy.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hk : (Int64.unsigned k < 3)%Z by move: END; clia k.
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) =
                 S (Z.to_nat (Int64.unsigned k)) by rewrite /nat_of; clia k.
      exists (Int64.add k (Int64.repr 1)),
        (replace (Z.to_nat (Int64.unsigned k)) ms'
           (packw ys' (Z.to_nat (Int64.unsigned k)))).
      rewrite pack_write // Hk1.
      repeat split => //.
      all: first [ clia k | by rewrite replace_length | idtac ].
      apply: pack_inv => //; clia k.
    + have Ek : nat_of k = 3%nat by move: END Hk3; rewrite /nat_of; clia k.
      repeat prog.
      (* s[0] = hs[0] - 160, the frees, then return rc *)
      do 12 (try move=> ?; repeat prog; first [ wpone | wpenter | idtac ];
             repeat prog).
      have [_ Hb2] := ExpModelBounds.core_bounds _ _ _ Hcore.
      exists rc; split => //; split.
      * by move=> Hrc; case: (Hrc (rc_eq0 _ B)).
      * move=> _; exists ms', (Int64.sub hN (Int64.repr 160)).
        repeat split => //.
        rewrite (encl_ok _ _ _ Hcore) signed_sub160 //.
        rewrite (pack_value ms' ys') // => i Hi.
        by apply: Hlo; rewrite Ek.
Qed.

End Encl.
