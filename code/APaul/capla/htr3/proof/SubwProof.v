(** * T2: subw, B_ia <- B_ia - B_ib mod beta^l *)

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

(* The borrow of one step of the loop is the true borrow. *)
Lemma borrow_step (a b c : int64) : (Int64.unsigned c <= 1)%Z ->
  let t := Int64.add b c in let d := Int64.sub a t in
  (Int64.unsigned d -
     2 ^ 64 * (if Int64.ltu t c || Int64.ltu a t then 1 else 0) =
   Int64.unsigned a - Int64.unsigned b - Int64.unsigned c)%Z.
Proof.
  move=> Hc t d; rewrite /d /t.
  case E1: (Int64.ltu _ c); case E2: (Int64.ltu _ _) => /=; lia.
Qed.

(* The invariant is kept by one step of the loop, on the words. *)
Lemma subw_step_val xs xs' ia ib nk (c c' d : int64) :
  (ia + nk < length xs)%coq_nat -> (ib + nk < length xs)%coq_nat ->
  length xs' = length xs ->
  (val (firstn nk (skipn ia xs')) - Int64.unsigned c * base nk =
   val (firstn nk (skipn ia xs)) - val (firstn nk (skipn ib xs)))%Z ->
  (Int64.unsigned d - 2 ^ 64 * Int64.unsigned c' =
   Int64.unsigned (List.nth (ia + nk) xs Int64.zero) -
   Int64.unsigned (List.nth (ib + nk) xs Int64.zero) - Int64.unsigned c)%Z ->
  (val (firstn (S nk) (skipn ia (replace (ia + nk) xs' d))) -
   Int64.unsigned c' * base (S nk) =
   val (firstn (S nk) (skipn ia xs)) - val (firstn (S nk) (skipn ib xs)))%Z.
Proof.
  move=> Ha Hb Hl HV Hs.
  rewrite skipn_replace_add.
  rewrite (val_firstn_S (replace _ _ _)) ?replace_length ?length_skipn;
    try lia.
  rewrite (val_firstn_S (skipn ia xs)) ?length_skipn; try lia.
  rewrite (val_firstn_S (skipn ib xs)) ?length_skipn; try lia.
  rewrite firstn_replace nth_replace_same ?length_skipn; try lia.
  rewrite !nth_skipn_add baseS.
  have := base_pos nk; nia.
Qed.

(* The coefficient at ia becomes (B_ia - B_ib) mod beta^l; every other word
   is unchanged.  The two coefficients do not overlap. *)
Theorem subw_spec xs m ia ib l e1 result :
  let IA := nat_of ia in let IB := nat_of ib in let L := nat_of l in
  length xs = nat_of m ->
  (IA + L <= nat_of m)%coq_nat -> (IB + L <= nat_of m)%coq_nat ->
  (IA + L <= IB \/ IB + L <= IA)%coq_nat ->
  eval_funcall ge (Internal subw19)
    [Varr (map Vint64 xs); Vint64 m; Vint64 ia; Vint64 ib; Vint64 l]
    e1 (Some result) ->
  exists xs', e1!(param 0 subw19) = Some (Varr (map Vint64 xs')) /\
    length xs' = length xs /\
    val (firstn L (skipn IA xs')) =
      ((val (firstn L (skipn IA xs)) - val (firstn L (skipn IB xs)))
         mod base L)%Z /\
    (forall p, (p < IA \/ IA + L <= p)%coq_nat ->
       List.nth p xs' Int64.zero = List.nth p xs Int64.zero).
Proof.
  move=> IA IB L Hlen HA HB Hdis.
  intro_eval_funcall subw19 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "i" i.
  name_var "B" A.
  name_var "cy" CY.
  name_var "t" T.
  repeat prog.
  (* After k steps: the first k words of B_ia, minus the borrow times
     beta^k, are B_ia - B_ib on k words; the words outside ia .. ia+k-1
     are unchanged. *)
  pose Inv := fun (e: env) (se: senv) =>
    exists k xs' c,
      e!i = Some (Vint64 k) /\
      ~~ Int64.ltu l k /\
      let nk := nat_of k in
      e!A = Some (Varr (map Vint64 xs')) /\
      e!CY = Some (Vint64 c) /\
      (Int64.unsigned c <= 1)%Z /\
      length xs' = length xs /\
      (forall p, (p < IA \/ IA + nk <= p)%coq_nat ->
         List.nth p xs' Int64.zero = List.nth p xs Int64.zero) /\
      (val (firstn nk (skipn IA xs')) - Int64.unsigned c * base nk =
       val (firstn nk (skipn IA xs)) - val (firstn nk (skipn IB xs)))%Z.
  exists Inv; split.
  - rewrite /Inv.
    exists (Int64.repr 0), xs, (Int64.repr 0).
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; try lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & xs' & c & [= ->] & Hkl & [= ->] & [= ->] & Hc & Hl & Hout & HV)
      => /=.
    set nk := nat_of k.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      (* The two reads and the write are at ib + k and ia + k. *)
      have Hk : (nk < L)%coq_nat by rewrite /nk /L /nat_of; clia k, l.
      have Hm := Int64.unsigned_range m.
      have Hib : Z.to_nat (Int64.unsigned (Int64.add ib k)) = (IB + nk)%nat.
      { rewrite /IB /nk /nat_of in HB Hk *.
        lia. }
      have Hia : Z.to_nat (Int64.unsigned (Int64.add ia k)) = (IA + nk)%nat.
      { rewrite /IA /nk /nat_of in HA Hk *.
        lia. }
      have Hbk : List.nth (IB + nk) xs' Int64.zero =
                 List.nth (IB + nk) xs Int64.zero by apply: Hout; lia.
      have Hak : List.nth (IA + nk) xs' Int64.zero =
                 List.nth (IA + nk) xs Int64.zero by apply: Hout; lia.
      rewrite Hib ?nth_map_V64 ?length_map ?Hbk /=; try lia.
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) = S nk.
      { rewrite /nk /nat_of; clia k, l. }
      have Hbs := borrow_step (List.nth (IA + nk) xs Int64.zero)
                    (List.nth (IB + nk) xs Int64.zero) c Hc.
      set d := Int64.sub (List.nth (IA + nk) xs Int64.zero)
                 (Int64.add (List.nth (IB + nk) xs Int64.zero) c).
      case C1: Int64.ltu; simplWP; repeat prog;
        rewrite Hia ?nth_map_V64 ?length_map ?Hak; try lia;
        rewrite /sem_binarith /sem_cast /sem_cmpu /= -/d.
      * exists (Int64.add k (Int64.repr 1)), (replace (IA + nk) xs' d),
          Int64.one.
        rewrite Hk1 replace_map; repeat split => //.
        -- clia l, k.
        -- by rewrite replace_length.
        -- move=> p Hp; rewrite nth_replace_other; try lia; apply: Hout; lia.
        -- apply: (subw_step_val xs xs' IA IB nk c) => //; lia.
      * exists (Int64.add k (Int64.repr 1)), (replace (IA + nk) xs' d).
        eexists.
        rewrite Hk1 replace_map; repeat split => //.
        -- clia l, k.
        -- case: Int64.ltu => /=; lia.
        -- by rewrite replace_length.
        -- move=> p Hp; rewrite nth_replace_other; try lia; apply: Hout; lia.
        -- apply: (subw_step_val xs xs' IA IB nk c) => //; try lia.
           by move: Hbs; cbv zeta; rewrite C1 orFb; case: Int64.ltu.
    (* The loop ends with k = l. *)
    + have Ek : k = l by clia k, l.
      subst k.
      exists xs'; repeat split => //.
      apply: (Z.mod_unique_pos _ _ (- Int64.unsigned c)); last first.
      { rewrite -/L in HV; lia. }
      have := val_bound (firstn L (skipn IA xs')).
      rewrite length_firstn length_skipn.
      have -> : Init.Nat.min L (length xs' - IA) = L by lia.
      lia.
Qed.
