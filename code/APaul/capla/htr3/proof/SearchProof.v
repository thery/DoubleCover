(** * T5: search, the whole search of one line *)

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

Require Import Htr3.DifftabProof Htr3.TstepProof.

(* ** Arithmetic on the table *)

(* Adding e to the top digit of a number written in base M. *)
Lemma add_top_digit (X B M u e : Z) : (0 <= X < B)%Z -> (0 < M)%Z ->
  (X + B * ((u + e) mod M) = (X + B * u + e * B) mod (B * M))%Z.
Proof.
  move=> HX HM.
  have Hd := Z.div_mod (u + e) M ltac:(lia).
  have Hr := Z.mod_pos_bound (u + e) M HM.
  apply: (Z.mod_unique_pos _ _ ((u + e) / M)); first nia.
  have -> : (X + B * u + e * B = X + B * (u + e))%Z by ring.
  rewrite {1}Hd; ring.
Qed.

(* Reducing modulo b before a step of the table changes nothing modulo b. *)
Lemma tstepZ_mod (b : Z) ds :
  map (fun z => z mod b)%Z (tstepZ (map (fun z => z mod b)%Z ds)) =
  map (fun z => z mod b)%Z (tstepZ ds).
Proof.
  elim: ds => [|a ds IH] //; case: ds IH => [|c r] IH.
    by rewrite /= Zmod_mod.
  have -> : tstepZ (map (fun z => z mod b)%Z (a :: c :: r)) =
    (a mod b + c mod b)%Z :: tstepZ (map (fun z => z mod b)%Z (c :: r))
    by [].
  have -> : tstepZ (a :: c :: r) = (a + c)%Z :: tstepZ (c :: r) by [].
  rewrite map_cons map_cons IH; congr (_ :: _).
  by rewrite -Zplus_mod.
Qed.

(* The first element of a list reduced modulo b. *)
Lemma nth0_mod (b : Z) T :
  List.nth 0 (map (fun z => z mod b)%Z T) 0%Z = (List.nth 0 T 0%Z mod b)%Z.
Proof. by case: T => [|x T] //=; rewrite Zmod_0_l. Qed.

(* beta^l, the two ways. *)
Lemma baseZ_base (L : nat) : baseZ (Z.of_nat L) = base L.
Proof. by []. Qed.

(* The weight of the top word of B_0. *)
Lemma top_weight (L : nat) : (1 <= L)%coq_nat ->
  (2 ^ (wbits * (Z.of_nat L - 1)))%Z = base (L - 1).
Proof. move=> HL; rewrite /base /wbits; f_equal; lia. Qed.

(* The top word of B_0 is the word l-1 of the array. *)
Lemma top_vcoef0 xs (L : nat) b : (1 <= L)%coq_nat ->
  (L <= length xs)%coq_nat -> b = vcoef xs L 0 ->
  top (Z.of_nat L) b = Int64.unsigned (List.nth (L - 1) xs Int64.zero).
Proof.
  move=> HL Hl ->.
  rewrite /top baseZ_base top_weight //.
  have [L' EL] : exists L', L = S L' by exists (L - 1)%nat; lia.
  have -> : (L - 1)%nat = L' by lia.
  have Hv : vcoef xs L 0 = val (firstn L xs) by [].
  rewrite Hv EL val_firstn_S; first by lia.
  have := val_bound (firstn L' xs); rewrite length_firstn.
  have -> : Nat.min L' (length xs) = L' by lia.
  have := Int64.unsigned_range (List.nth L' xs Int64.zero).
  change Int64.modulus with (2 ^ 64)%Z.
  have := base_pos L'; rewrite baseS => Hb Hu Hx.
  rewrite Z.mod_small; first nia.
  rewrite (Z.mul_comm (base L')) Z.div_add; first lia.
  rewrite Z.div_small //; lia.
Qed.

(* The window: err added to the word l-1 adds err * beta^(l-1) to B_0. *)
Lemma window_word xs (L : nat) (e : int64) : (1 <= L)%coq_nat ->
  (L <= length xs)%coq_nat ->
  vcoef (replace (L - 1) xs (Int64.add (List.nth (L - 1) xs Int64.zero) e))
    L 0 =
  ((vcoef xs L 0 + Int64.unsigned e * 2 ^ (wbits * (Z.of_nat L - 1)))
     mod base L)%Z.
Proof.
  move=> HL Hl; rewrite top_weight //.
  have [L' EL] : exists L', L = S L' by exists (L - 1)%nat; lia.
  have -> : (L - 1)%nat = L' by lia.
  rewrite /vcoef /coef /= EL.
  rewrite !val_firstn_S ?replace_length; try lia.
  rewrite firstn_replace nth_replace_same; first lia.
  rewrite Int64.add_unsigned Int64.unsigned_repr_eq baseS.
  change Int64.modulus with (2 ^ 64)%Z.
  have := val_bound (firstn L' xs); rewrite length_firstn.
  have -> : Nat.min L' (length xs) = L' by lia.
  move=> Hx; apply: add_top_digit => //; lia.
Qed.

(* ** The table held by the array *)

(* After difftab and the window, the array holds table 0 modulo beta^l. *)
Lemma window_vcoefs xs1 ds (L K : nat) (e : int64) :
  (1 <= L)%coq_nat -> (1 <= K)%coq_nat -> (K * L <= length xs1)%coq_nat ->
  vcoefs xs1 L K = map (fun j => fdiff ds j mod base L)%Z (seq 0 K) ->
  vcoefs (replace (L - 1) xs1 (Int64.add (List.nth (L - 1) xs1 Int64.zero) e))
    L K =
  map (fun z => z mod base L)%Z
    (window (Z.of_nat L) (Int64.unsigned e) (map (fdiff ds) (seq 0 K))).
Proof.
  move=> HL HK Hl.
  have HLl : (L <= length xs1)%coq_nat by nia.
  have [K' EK] : exists K', K = S K' by exists (K - 1)%nat; lia.
  rewrite /vcoefs EK.
  have -> : seq 0 (S K') = 0%nat :: seq 1 K' by [].
  rewrite !map_cons => [[H0 Ht]].
  congr (_ :: _).
  - by rewrite window_word // H0 Zplus_mod_idemp_l.
  - rewrite map_map -Ht; apply: map_ext_in => i /in_seq Hi.
    rewrite /vcoef (coef_ext _ xs1) // ?replace_length // => p Hp.
    rewrite nth_replace_other //; nia.
Qed.

(* One call of tstep: the array goes from table j to table (j+1). *)
Lemma table_step xs' xs'' (L K : nat) l e ds j :
  vcoefs xs' L K = map (fun z => z mod base L)%Z (table l e ds j) ->
  vcoefs xs'' L K = map (fun z => z mod base L)%Z (tstepZ (vcoefs xs' L K)) ->
  vcoefs xs'' L K = map (fun z => z mod base L)%Z (table l e ds (S j)).
Proof. by move=> H1 ->; rewrite H1 tstepZ_mod. Qed.

(* The test of the loop is cand: the word l-1 against 2 err. *)
Lemma cand_word xs' (L K : nat) e ds j :
  (1 <= L)%coq_nat -> (1 <= K)%coq_nat -> (L <= length xs')%coq_nat ->
  vcoefs xs' L K =
    map (fun z => z mod base L)%Z (table (Z.of_nat L) e ds j) ->
  cand (Z.of_nat L) e ds j =
    (Int64.unsigned (List.nth (L - 1) xs' Int64.zero) <=? 2 * e)%Z.
Proof.
  move=> HL HK Hl HV; rewrite /cand.
  set T := table _ _ _ _.
  have -> : top (Z.of_nat L) (List.nth 0 T 0%Z) =
            top (Z.of_nat L) (List.nth 0 (vcoefs xs' L K) 0%Z).
  { by rewrite HV nth0_mod /top baseZ_base Zmod_mod. }
  rewrite (top_vcoef0 xs' L) //.
  have [K' ->] : exists K', K = S K' by exists (K - 1)%nat; lia.
  by [].
Qed.

(* ** The candidates *)

(* One more j: j is added when it is a candidate. *)
Lemma cands_S l e ds j :
  cands l e ds (S j) =
  (cands l e ds j ++ (if cand l e ds j then [j] else []))%list.
Proof. by rewrite /cands seq_S filter_app /=; case: cand. Qed.

(* There are at most j candidates below j. *)
Lemma cands_length l e ds j : (length (cands l e ds j) <= j)%coq_nat.
Proof. by rewrite /cands; have := filter_length_le (cand l e ds) (seq 0 j);
  rewrite length_seq. Qed.

(* Reading a word of out as a natural number. *)
Lemma nth_map_nat (os : list int64) i :
  List.nth i (map nat_of os) 0%nat = nat_of (List.nth i os Int64.zero).
Proof. exact: (map_nth nat_of os Int64.zero i). Qed.

(* A candidate j is written at index count, while count < cap. *)
Lemma out_write (os : list int64) (cs : list nat) (cp : nat) (j : int64) :
  (length cs < cp)%coq_nat -> length os = cp ->
  (forall i, (i < Nat.min (length cs) cp)%coq_nat ->
     List.nth i (map nat_of os) 0%nat = List.nth i cs 0%nat) ->
  forall i, (i < Nat.min (length (cs ++ [nat_of j])) cp)%coq_nat ->
    List.nth i (map nat_of (replace (length cs) os j)) 0%nat =
    List.nth i (cs ++ [nat_of j]) 0%nat.
Proof.
  move=> Hc Hl Hi i; rewrite length_app /= => Hi'.
  rewrite nth_map_nat.
  have [Hlt|->] : (i < length cs)%coq_nat \/ i = length cs by lia.
  - rewrite app_nth1; first lia.
    rewrite -Hi; first lia.
    rewrite nth_map_nat nth_replace_other //; lia.
  - rewrite nth_middle nth_replace_same //; lia.
Qed.

(* Once count >= cap, out is left as it is. *)
Lemma out_full (os : list int64) (cs : list nat) (cp x : nat) :
  (cp <= length cs)%coq_nat ->
  (forall i, (i < Nat.min (length cs) cp)%coq_nat ->
     List.nth i (map nat_of os) 0%nat = List.nth i cs 0%nat) ->
  forall i, (i < Nat.min (length (cs ++ [x])) cp)%coq_nat ->
    List.nth i (map nat_of os) 0%nat = List.nth i (cs ++ [x]) 0%nat.
Proof.
  move=> Hc Hi i; rewrite length_app /= => Hi'.
  rewrite app_nth1; first lia.
  apply: Hi; lia.
Qed.

(* The out array, from its first entries. *)
Lemma firstn_out (os cs : list nat) (c : nat) : length os = c ->
  (forall i, (i < Nat.min (length cs) c)%coq_nat ->
     List.nth i os 0%nat = List.nth i cs 0%nat) ->
  firstn (Nat.min (length cs) c) os = firstn c cs.
Proof.
  move=> Hl Hi; apply: (nth_ext _ _ 0%nat 0%nat).
  - rewrite !length_firstn; lia.
  - move=> i; rewrite length_firstn => Hi'.
    rewrite !nth_firstn.
    have -> : Nat.ltb i (Nat.min (length cs) c) = true by apply/Nat.ltb_lt; lia.
    have -> : Nat.ltb i c = true by apply/Nat.ltb_lt; lia.
    apply: Hi; lia.
Qed.

(* The result is the number of candidates j = 0 .. n-1 (cands, in HtrDefs),
   and out holds the first cap of them, in increasing order. *)
Theorem search_spec xs m k l n err outs cap e1 result :
  let K := nat_of k in let L := nat_of l in let N := nat_of n in
  length xs = nat_of m -> (K * L <= nat_of m)%coq_nat ->
  (1 <= K)%coq_nat -> (1 <= L)%coq_nat ->
  (2 * Int64.unsigned err <= Int64.max_unsigned)%Z ->
  length outs = nat_of cap ->
  eval_funcall ge (Internal search46)
    [Varr (map Vint64 xs); Vint64 m; Vint64 k; Vint64 l; Vint64 n;
     Vint64 err; Varr (map Vint64 outs); Vint64 cap] e1 (Some result) ->
  let cs := cands (Z.of_nat L) (Int64.unsigned err) (vcoefs xs L K) N in
  exists c outs', result = Vint64 c /\
    e1!(param 6 search46) = Some (Varr (map Vint64 outs')) /\
    Int64.unsigned c = Z.of_nat (length cs) /\
    firstn (Nat.min (length cs) (nat_of cap)) (map nat_of outs') =
      firstn (nat_of cap) cs.
Proof.
  move=> K L N Hlen HKL HK HL Herr Hout.
  intro_eval_funcall search46 out se1 exec.
  (* The result is the returned value: keep it in the goal. *)
  match goal with H : Some result = outcome_result_value out |- _ =>
    have := H end.
  apply_WP_stmt exec out e1 se1.
  name_var "j" J.
  name_var "B" A.
  name_var "count" CNT.
  name_var "out" O.
  repeat prog.
  move=> _ _ CALL0.
  have [xs1 [E1 [Hl1 [HV1 _]]]] := difftab_spec xs m k l _ _ Hlen HKL CALL0.
  change (param 0 difftab29) with A in E1.
  repeat prog.
  rewrite E1; simplWP; repeat prog.
  have HLx : (L <= length xs1)%coq_nat by nia.
  have Hl1m : Z.to_nat (Int64.unsigned (Int64.sub l (Int64.repr 1))) =
              (L - 1)%nat.
  { rewrite /L /nat_of in HL *; clia l. }
  rewrite Hl1m nth_map_V64 ?length_map; first lia.
  rewrite /= replace_map.
  set xs2 := replace (L - 1) xs1 _.
  set ds := vcoefs xs L K.
  set Er := Int64.unsigned err.
  (* After j steps: B holds table j modulo beta^l, count is the number of
     candidates below j, and out holds the first cap of them. *)
  pose Inv := fun (e: env) (se: senv) =>
    exists j c xsj outsj,
      e!J = Some (Vint64 j) /\ (nat_of j <= N)%coq_nat /\
      e!CNT = Some (Vint64 c) /\
      e!A = Some (Varr (map Vint64 xsj)) /\ length xsj = length xs /\
      vcoefs xsj L K =
        map (fun z => z mod base L)%Z (table (Z.of_nat L) Er ds (nat_of j)) /\
      e!O = Some (Varr (map Vint64 outsj)) /\ length outsj = length outs /\
      Int64.unsigned c =
        Z.of_nat (length (cands (Z.of_nat L) Er ds (nat_of j))) /\
      (forall i,
         (i < Nat.min (length (cands (Z.of_nat L) Er ds (nat_of j)))
                (nat_of cap))%coq_nat ->
         List.nth i (map nat_of outsj) 0%nat =
         List.nth i (cands (Z.of_nat L) Er ds (nat_of j)) 0%nat).
  exists Inv; split.
  - rewrite /Inv.
    exists (Int64.repr 0), (Int64.repr 0), xs2, outs.
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; try lia.
    + by rewrite /xs2 replace_length.
    + rewrite /table /ds length_map length_seq.
      apply: window_vcoefs => //; lia.
    + move=> i; rewrite /cands /=; lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (j & c & xsj & outsj & [= ->] & Hjn & [= ->] & [= ->] & Hlj &
            HVj & [= ->] & Hloj & Hc & Hout') => /=.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have HLj : (L <= length xsj)%coq_nat by nia.
      rewrite Hl1m nth_map_V64 ?length_map; first lia.
      have Hcand := cand_word xsj L K Er ds (nat_of j) HL HK HLj HVj.
      rewrite /sem_cmpu /sem_binarith /sem_cast /=.
      have H2e : Int64.unsigned (Int64.mul (Int64.repr 2) err) = (2 * Er)%Z.
      { rewrite Int64_mul_inj.
        change (Int64.unsigned (Int64.repr 2)) with 2%Z.
        move: Herr; rewrite /Er.
        change Int64.max_unsigned with 18446744073709551615%Z.
        have := Int64.unsigned_range err.
        move=> ? ?; rewrite Z.mod_small; lia. }
      have Hj1 : nat_of (Int64.add j (Int64.repr 1)) = S (nat_of j).
      { apply: (nat_of_add1 _ n); move: END; rewrite /nat_of; lia. }
      have HjN : ((nat_of j) < N)%coq_nat.
      { move: END; rewrite /N /nat_of; lia. }
      case T: (Int64.ltu (Int64.mul (Int64.repr 2) err)
                 (List.nth (L - 1) xsj Int64.zero)); simplWP; repeat prog.
      * (* j is not a candidate: only the step of the table. *)
        move=> _ _ CALL.
        have Hlj' : length xsj = nat_of m by rewrite Hlj.
        have [xs'' [E'' [Hl'' [HV'' _]]]] :=
          tstep_spec xsj m k l _ _ Hlj' HKL HK CALL.
        change (param 0 tstep34) with A in E''.
        repeat prog.
        rewrite E'' /=.
        have Hc' : cand (Z.of_nat L) Er ds (nat_of j) = false.
        { rewrite Hcand; apply/Z.leb_gt; move: T H2e; lia. }
        exists (Int64.add j (Int64.repr 1)), c, xs'', outsj.
        rewrite Hj1 cands_S Hc' app_nil_r; repeat split => //.
        all: first [ lia | by rewrite Hl'' | exact: table_step HVj HV'' ].
      * have Hc' : cand (Z.of_nat L) Er ds (nat_of j) = true.
        { rewrite Hcand; apply/Z.leb_le; move: T H2e; lia. }
        have Hcn : (Int64.unsigned c < Int64.unsigned n)%Z.
        { have := cands_length (Z.of_nat L) Er ds (nat_of j).
          move: HjN Hc; rewrite /N /nat_of; lia. }
        have Hc1 : Int64.unsigned (Int64.add c (Int64.repr 1)) =
                   (Int64.unsigned c + 1)%Z.
        { move: Hcn; clia c, n. }
        case C: (Int64.ltu c cap); simplWP; repeat prog.
        -- (* count < cap: j is written in out. *)
           move=> _ _ CALL.
           have Hlj' : length xsj = nat_of m by rewrite Hlj.
           have [xs'' [E'' [Hl'' [HV'' _]]]] :=
             tstep_spec xsj m k l _ _ Hlj' HKL HK CALL.
           change (param 0 tstep34) with A in E''.
           repeat prog.
           rewrite E'' /=.
           set cs := cands (Z.of_nat L) Er ds (nat_of j).
           have Ec : Z.to_nat (Int64.unsigned c) = length cs.
           { by rewrite Hc Nat2Z.id. }
           have Hlt : (length cs < nat_of cap)%coq_nat.
           { have : (Int64.unsigned c < Int64.unsigned cap)%Z.
             { by move: C; rewrite /Int64.ltu; case: zlt. }
             rewrite /nat_of -Ec; lia. }
           exists (Int64.add j (Int64.repr 1)), (Int64.add c (Int64.repr 1)),
             xs'', (replace (length cs) outsj j).
           rewrite Ec replace_map Hj1 cands_S Hc' Hc1; repeat split => //.
           all: first [ lia | by rewrite Hl'' | exact: table_step HVj HV''
                      | by rewrite replace_length
                      | by rewrite length_app Hc /=; lia
                      | exact: out_write Hlt (etrans Hloj Hout) Hout' ].
        -- (* count >= cap: out is full. *)
           move=> _ _ CALL.
           have Hlj' : length xsj = nat_of m by rewrite Hlj.
           have [xs'' [E'' [Hl'' [HV'' _]]]] :=
             tstep_spec xsj m k l _ _ Hlj' HKL HK CALL.
           change (param 0 tstep34) with A in E''.
           repeat prog.
           rewrite E'' /=.
           set cs := cands (Z.of_nat L) Er ds (nat_of j).
           have Hge : (nat_of cap <= length cs)%coq_nat.
           { have : (Int64.unsigned cap <= Int64.unsigned c)%Z.
             { by move: C; rewrite /Int64.ltu; case: zlt => //; lia. }
             have Ec : Z.to_nat (Int64.unsigned c) = length cs.
             { by rewrite Hc Nat2Z.id. }
             rewrite /nat_of -Ec; lia. }
           exists (Int64.add j (Int64.repr 1)), (Int64.add c (Int64.repr 1)),
             xs'', outsj.
           rewrite Hj1 cands_S Hc' Hc1; repeat split => //.
           all: first [ lia | by rewrite Hl'' | exact: table_step HVj HV''
                      | by rewrite length_app Hc /=; lia
                      | exact: out_full Hge Hout' ].
    + repeat prog.
      have Ej : nat_of j = N.
      { move: END Hjn; rewrite /N /nat_of; lia. }
      rewrite Ej in Hc Hout'.
      exists c, outsj; repeat split => //.
      apply: firstn_out => //.
      by rewrite length_map Hloj Hout.
Qed.
