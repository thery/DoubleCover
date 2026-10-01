(** * T4: tstep, one step of the table *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Import Htr3.HtrBase.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Require Import Htr3.AddwProof.

(* A product of two words that does not overflow. *)
Lemma nat_of_mul a b n : (nat_of a * nat_of b <= nat_of n)%coq_nat ->
  nat_of (Int64.mul a b) = (nat_of a * nat_of b)%nat.
Proof.
  rewrite /nat_of Int64_mul_inj => H.
  have := Int64.unsigned_range a; have := Int64.unsigned_range b.
  have := Int64.unsigned_range n.
  change Int64.modulus with (2 ^ 64)%Z => Hn Hb Ha.
  have := Z2Nat.inj_mul _ _ (proj1 Ha) (proj1 Hb).
  have := Z.mul_nonneg_nonneg _ _ (proj1 Ha) (proj1 Hb).
  move=> H0 E; rewrite Z.mod_small; lia.
Qed.

(* The successor of a word below another word. *)
Lemma nat_of_add1 a b : (nat_of a < nat_of b)%coq_nat ->
  nat_of (Int64.add a (Int64.repr 1)) = S (nat_of a).
Proof. rewrite /nat_of; clia a, b. Qed.

(* Two arrays that agree on the words of B_i have the same B_i. *)
Lemma coef_ext a b (L i : nat) : length a = length b ->
  (forall p : nat, (i * L <= p)%nat /\ (p < i * L + L)%nat ->
     List.nth p a Int64.zero = List.nth p b Int64.zero) ->
  coef a L i = coef b L i.
Proof.
  move=> Hl Hp; rewrite /coef.
  apply: (nth_ext _ _ Int64.zero Int64.zero).
  - by rewrite length_firstn length_firstn length_skipn length_skipn Hl.
  - move=> j _; rewrite !nth_firstn.
    case: Nat.ltb_spec => // Hj.
    rewrite !nth_skipn_add; apply: Hp; split; lia.
Qed.

(* Two arrays that agree from word n on have the same tail. *)
Lemma skipn_ext a b (n : nat) : length a = length b ->
  (forall p : nat, (n <= p)%coq_nat ->
     List.nth p a Int64.zero = List.nth p b Int64.zero) ->
  skipn n a = skipn n b.
Proof.
  move=> Hl Hp.
  apply: (nth_ext _ _ Int64.zero Int64.zero).
  - by rewrite length_skipn length_skipn Hl.
  - move=> j _; rewrite !nth_skipn_add; apply: Hp; lia.
Qed.

(* A coefficient is below beta^l. *)
Lemma vcoef_bound xs (L i : nat) : (0 <= vcoef xs L i < base L)%Z.
Proof.
  have := val_bound (coef xs L i).
  have : (length (coef xs L i) <= L)%coq_nat.
  { by rewrite /coef length_firstn; lia. }
  move=> HL [H0 H1]; split => //.
  apply: (Z.lt_le_trans _ _ _ H1).
  rewrite /base; apply: Z.pow_le_mono_r; lia.
Qed.

(* tstepZ on the values of f at a .. a+n. *)
Lemma tstepZ_seq (f : nat -> Z) (a n : nat) :
  tstepZ (map f (seq a (S n))) =
    (map (fun i => f i + f (S i))%Z (seq a n) ++ [f (a + n)%nat])%list.
Proof.
  elim: n a => [|n IH] a; first by rewrite addn0.
  have -> : tstepZ (map f (seq a (S (S n)))) =
    (f a + f (S a))%Z :: tstepZ (map f (seq (S a) (S n))) by [].
  by rewrite IH addSnnS.
Qed.

(* One call of addw keeps the invariant of the loop: B_0 .. B_(t-1) are
   the new ones, the words from t*l on are the old ones. *)
Lemma tstep_inv_step xs xs' xs'' (L nt : nat) :
  length xs' = length xs -> length xs'' = length xs' ->
  (forall i, (i < nt)%coq_nat ->
     vcoef xs' L i = ((vcoef xs L i + vcoef xs L (S i)) mod base L)%Z) ->
  (forall p, (nt * L <= p)%coq_nat ->
     List.nth p xs' Int64.zero = List.nth p xs Int64.zero) ->
  val (firstn L (skipn (nt * L) xs'')) =
    ((val (firstn L (skipn (nt * L) xs')) +
      val (firstn L (skipn (S nt * L) xs'))) mod base L)%Z ->
  (forall p, (p < nt * L \/ nt * L + L <= p)%coq_nat ->
     List.nth p xs'' Int64.zero = List.nth p xs' Int64.zero) ->
  (forall i, (i < S nt)%coq_nat ->
     vcoef xs'' L i = ((vcoef xs L i + vcoef xs L (S i)) mod base L)%Z) /\
  (forall p, (S nt * L <= p)%coq_nat ->
     List.nth p xs'' Int64.zero = List.nth p xs Int64.zero).
Proof.
  move=> Hl Hl' Hdone Hout HV Hrest; split.
  - move=> i Hi.
    have [Hi'|->] : (i < nt)%coq_nat \/ i = nt by lia.
    + rewrite -Hdone // /vcoef (coef_ext xs'' xs') //.
      move=> p Hp; apply: Hrest; left; nia.
    + have E0 : coef xs' L nt = coef xs L nt.
      { by apply: coef_ext => // p Hp; apply: Hout; lia. }
      have E1 : coef xs' L (S nt) = coef xs L (S nt).
      { by apply: coef_ext => // p Hp; apply: Hout; nia. }
      rewrite /vcoef /coef HV -/(coef xs' L nt) -/(coef xs' L (S nt)).
      by rewrite E0 E1.
  - move=> p Hp; rewrite Hrest; [right; nia | apply: Hout; nia].
Qed.

(* At the end, B_0 .. B_(K-2) are the new ones and the words from (K-1)*l
   on are the old ones: this is tstepZ modulo beta^l. *)
Lemma tstep_final xs xs' (L K : nat) : (1 <= K)%coq_nat ->
  length xs' = length xs ->
  (forall i, (i < K - 1)%coq_nat ->
     vcoef xs' L i = ((vcoef xs L i + vcoef xs L (S i)) mod base L)%Z) ->
  (forall p, ((K - 1) * L <= p)%coq_nat ->
     List.nth p xs' Int64.zero = List.nth p xs Int64.zero) ->
  vcoefs xs' L K = map (fun z => z mod base L)%Z (tstepZ (vcoefs xs L K)) /\
  skipn (K * L)%nat xs' = skipn (K * L)%nat xs.
Proof.
  move=> HK Hl.
  have [n ->] : exists n : nat, K = S n by exists (K - 1)%nat; lia.
  rewrite subn1 succnK.
  move=> Hdone Hout.
  split; last first.
  { apply: skipn_ext => // p Hp; apply: Hout; nia. }
  rewrite /vcoefs tstepZ_seq seq_S map_app map_app /= add0n.
  congr (_ ++ [_])%list.
  - rewrite map_map; apply: map_ext_in => i /in_seq Hi.
    apply: Hdone; lia.
  - rewrite Z.mod_small; first by apply: vcoef_bound.
    rewrite /vcoef (coef_ext xs' xs) // => p Hp; apply: Hout; lia.
Qed.

(* The k coefficients become B_t + B_(t+1) modulo beta^l, the last one
   unchanged (tstepZ); the words after them are unchanged. *)
Theorem tstep_spec xs m k l e1 result :
  let K := nat_of k in let L := nat_of l in
  length xs = nat_of m -> (K * L <= nat_of m)%coq_nat -> (1 <= K)%coq_nat ->
  eval_funcall ge (Internal tstep34)
    [Varr (map Vint64 xs); Vint64 m; Vint64 k; Vint64 l] e1 (Some result) ->
  exists xs', e1!(param 0 tstep34) = Some (Varr (map Vint64 xs')) /\
    length xs' = length xs /\
    vcoefs xs' L K = map (fun z => z mod base L)%Z (tstepZ (vcoefs xs L K)) /\
    skipn (K * L) xs' = skipn (K * L) xs.
Proof.
  move=> K L Hlen HKL HK.
  intro_eval_funcall tstep34 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "t" T.
  name_var "B" A.
  repeat prog.
  (* After t calls: B_0 .. B_(t-1) are the new ones, the words from t*l on
     are the old ones. *)
  pose Inv := fun (e: env) (se: senv) =>
    exists t xs',
      e!T = Some (Vint64 t) /\
      (nat_of t <= K - 1)%coq_nat /\
      let nt := nat_of t in
      e!A = Some (Varr (map Vint64 xs')) /\
      length xs' = length xs /\
      (forall i, (i < nt)%coq_nat ->
         vcoef xs' L i = ((vcoef xs L i + vcoef xs L (S i)) mod base L)%Z) /\
      (forall p, (nt * L <= p)%coq_nat ->
         List.nth p xs' Int64.zero = List.nth p xs Int64.zero).
  exists Inv; split.
  - rewrite /Inv.
    exists (Int64.repr 0), xs.
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (t & xs' & [= ->] & Htk & [= ->] & Hl & Hdone & Hout) => /=.
    set nt := nat_of t.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      move=> _ _; rewrite /sem_binarith /sem_cast /=.
      have Htk' : (nt < K - 1)%coq_nat.
      { move: END HK; rewrite /nt /K /nat_of; lia. }
      have Ht1 : nat_of (Int64.add t (Int64.repr 1)) = S nt.
      { apply: (nat_of_add1 _ k); rewrite -/K; lia. }
      have Hia : nat_of (Int64.mul t l) = (nt * L)%nat.
      { apply: (nat_of_mul _ _ m); rewrite -/L -/nt.
        have : (nt * L <= K * L)%coq_nat by apply: Nat.mul_le_mono_r; lia.
        lia. }
      have Hib : nat_of (Int64.mul (Int64.add t (Int64.repr 1)) l) =
                 (S nt * L)%nat.
      { rewrite -Ht1; apply: (nat_of_mul _ _ m); rewrite Ht1 -/L.
        have : (S nt * L <= K * L)%coq_nat by apply: Nat.mul_le_mono_r; lia.
        lia. }
      have H1 : (S nt * L <= K * L)%coq_nat.
      { apply: Nat.mul_le_mono_r; lia. }
      have H2 : (S (S nt) * L <= K * L)%coq_nat.
      { apply: Nat.mul_le_mono_r; lia. }
      move=> CALL.
      have := addw_spec xs' m (Int64.mul t l)
        (Int64.mul (Int64.add t (Int64.repr 1)) l) l _ _.
      cbv zeta; rewrite Hia Hib -/L.
      move=> /(_ _ _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(left; lia) CALL).
      move=> [xs'' [E'' [Hl'' [HV Hrest]]]].
      repeat prog.
      change (param 0 addw12) with A in E''.
      rewrite E'' /=.
      have [Hd Ho] :=
        tstep_inv_step xs xs' xs'' L nt Hl Hl'' Hdone Hout HV Hrest.
      exists (Int64.add t (Int64.repr 1)), xs''.
      rewrite Ht1; repeat split => //; try lia.
    + have Ent : nt = (K - 1)%coq_nat.
      { move: END Htk HK; rewrite /nt /K /nat_of; lia. }
      repeat prog.
      have [Hv Hs] := tstep_final xs xs' L K HK Hl
        (fun i Hi => Hdone i ltac:(change (nat_of t) with nt; lia))
        (fun p Hp => Hout p ltac:(change (nat_of t) with nt; by rewrite Ent)).
      by exists xs'.
Qed.
