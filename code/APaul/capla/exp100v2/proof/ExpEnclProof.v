(** * exp_encl_bits: M and s as exp_encl_Z gives them

    exp_encl_bits calls exp_core: its statement [exp_core_spec] is a
    hypothesis of [exp_encl_bits_ok], proved in ExpCoreProof.v.  On
    success the loop packs the limbs of y two by two into the 3 words
    of M: after i rounds, M[j] = y[2j] + 2^32 y[2j+1] for j < i; then
    s[0] = hs[0] - 160. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** The packing loop *)

(* rc == 0 as a test on words. *)
Lemma rc_eq0 rc : Int64.eq rc (Int64.repr 0) = true -> Int64.unsigned rc = 0%Z.
Proof. by have := Int64.eq_spec rc (Int64.repr 0) => + H; rewrite H => ->. Qed.

Lemma rc_neq0 rc : Int64.eq rc (Int64.repr 0) = false -> Int64.unsigned rc <> 0%Z.
Proof.
have := Int64.eq_spec rc (Int64.repr 0) => + H; rewrite H => Hne Hu; apply: Hne.
by rewrite -(Int64.repr_unsigned rc) Hu.
Qed.

(* The k low words of M hold the limbs 0 .. 2k - 1 of y, two by two. *)
Definition packed (Mv : {ffun 'I_NM -> int64}) (yv : numA) (k : nat) : Prop :=
  forall j : 'I_NM, (j < k)%nat -> Int64.unsigned (Mv j) =
    (nth 0 (words yv) (2 * j) + 2 ^ limb_bits * nth 0 (words yv) (2 * j + 1))%Z.

(* Two limbs in one word: a | (b << 32) = a + 2^32 b. *)
Lemma or_shl32 a b : (Int64.unsigned a < 2 ^ 32)%Z -> (Int64.unsigned b < 2 ^ 32)%Z ->
  Int64.unsigned (Int64.or a (Int64.shl' b (Int.modu (Int.repr 32) Int64.iwordsize'))) =
  (Int64.unsigned a + 2 ^ 32 * Int64.unsigned b)%Z.
Proof.
move=> Ha Hb.
have Ra := Int64.unsigned_range a; have Rb := Int64.unsigned_range b.
have E32 : Int.unsigned (Int.modu (Int.repr 32) Int64.iwordsize') = 32%Z by [].
rewrite /Int64.or /Int64.shl' E32 Z.shiftl_mul_pow2 //.
rewrite (Int64.unsigned_repr (Int64.unsigned b * 2 ^ 32)); first
  by change Int64.max_unsigned with 18446744073709551615%Z; lia.
have -> : Z.lor (Int64.unsigned a) (Int64.unsigned b * 2 ^ 32) =
          (Int64.unsigned a + Int64.unsigned b * 2 ^ 32)%Z.
{ have Hl : Z.land (Int64.unsigned a) (Int64.unsigned b * 2 ^ 32) = 0%Z.
  { apply: Z.bits_inj' => k Hk.
    rewrite Z.land_spec Z.bits_0.
    case: (Z.lt_ge_cases k 32) => Hk32.
    - by rewrite Z.mul_pow2_bits_low // Bool.andb_false_r.
    - rewrite -(Z.mod_small (Int64.unsigned a) (2 ^ 32)); first lia.
      by rewrite Z.mod_pow2_bits_high //; lia. }
  by rewrite -Z.lxor_lor // -Z.add_nocarry_lxor. }
rewrite Int64.unsigned_repr; first
  by change Int64.max_unsigned with 18446744073709551615%Z; lia.
lia.
Qed.

(* One more round of the packing loop. *)
Lemma packed_step (Mv : {ffun 'I_NM -> int64}) (yv : numA) k (o0 o1 : 'I_NL) :
  limbsA yv -> (k < NM)%nat -> nat_of_ord o0 = muln 2 k ->
  nat_of_ord o1 = addn (muln 2 k) 1 -> packed Mv yv k ->
  packed (Mv ↑[k ← Int64.or (yv o0)
            (Int64.shl' (yv o1) (Int.modu (Int.repr 32) Int64.iwordsize'))])
    yv k.+1.
Proof.
move=> Hy Hk E0 E1 HM j Hj.
rewrite (setfP _ _ _ Hk); case: eqP => [Ej|Nj].
- have L0 := Hy o0; have L1 := Hy o1.
  move: L0 L1; rewrite /limb /limb_bits => L0 L1.
  rewrite or_shl32; [lia|lia|].
  rewrite Ej -E1 -E0.
  by rewrite 2!nth_words.
- apply: HM; move: Hj; rewrite ltnS leq_eqVlt => /orP [/eqP Ej|//].
  by case: Nj.
Qed.

(* After the 3 rounds, M holds y. *)
Lemma packed_all (Mv : {ffun 'I_NM -> int64}) (yv : numA) :
  packed Mv yv NM -> valW (words Mv) = valA yv.
Proof.
move=> HM.
have -> : words Mv = pack (words yv).
{ apply: (@eq_from_nth _ 0); first by rewrite size_words.
  move=> k; rewrite size_words => Hk.
  rewrite -[k]/(nat_of_ord (Ordinal Hk)) nth_words HM //.
  rewrite [RHS]nth_List_nth nth_pack; first by apply/ltP.
  rewrite -!nth_List_nth.
  by rewrite multE plusE. }
by rewrite valW_pack // length_words.
Qed.

(* hN - 160 does not wrap, for |hN| <= 2^12. *)
Lemma signed_sub160 hN :
  (- 2 ^ ExpModelBounds.hN_bits <= Int64.signed hN <= 2 ^ ExpModelBounds.hN_bits)%Z ->
  Int64.signed (Int64.sub hN (Int64.repr 160)) = (Int64.signed hN - 160)%Z.
Proof.
rewrite /ExpModelBounds.hN_bits => H.
rewrite Int64.sub_signed.
change (Int64.signed (Int64.repr 160)) with 160%Z.
rewrite Int64.signed_repr //.
change Int64.min_signed with (-9223372036854775808)%Z.
change Int64.max_signed with 9223372036854775807%Z; lia.
Qed.

(** ** The proof *)

(* enter_loop of CaplaProof, with the loop variables introduced under
   names chosen by the caller; enter_loop fails on this loop. *)
Ltac enter_loop_m I :=
  match goal with
  | _ := PENV ?pe, _ := NAMES ?names, _ := FUNC ?f |-
      interp (bind _ (exec_loop _ _ _ _ _ ?body)) ?e ?se = _ -> _ =>
    let sze := eval vm_compute in (fn_szenv' f) in
    let l := eval vm_compute in (assigned_vars pe body) in
    let ls := eval vm_compute in (initialized_vars body) in
    let l := constr:([seq option_get names!j j | j <- l]) in
    let l := eval simpl in l in
    let ls := constr:([seq option_get names!j j | j <- ls]) in
    let ls := eval simpl in ls in
    let Y := fresh in
    have Y : INV I e se;
    [|apply (ind_loop sze I l ls);
      [let h1 := fresh in let h2 := fresh in
       simpl; intros h1 h2; apply: h1 Y _;
       rewrite -h2 {h2}; f_equal; rewrite ?set_treeP /= ?set_treeP //;
       test l; test ls
      |exact Y
      |clear Y; move=> /= > ?]]
  end.

Theorem exp_encl_bits_ok : exp_core_spec -> exp_encl_bits_spec.
Proof.
move=> EC μ xb M s Ta Ca L2 RM r rl HT.
enter_func; csteps.
call EC => /(_ HT) [rc0 [y' [hs' [X' [q' [q1' [rr' [h' [t' [-> [-> [Hko Hok]]]]]]]]]]]].
csteps.
case EQ: Int64.eq => /=; last first.
{ (* rc <> 0: M and s are left as they are *)
  csteps; cret.
  do 3 eexists; split; first reflexivity; split; first reflexivity; split.
  - by move=> H; rewrite /ExpModel.exp_encl_Z (Hko H).
  - by move/(rc_neq0 _ EQ). }
csteps.
have [Hly Hcore] := Hok (rc_eq0 _ EQ).
inv I := { [:: i; M0] } (fun iv Mv => (iv:N <= 3)%nat /\ packed Mv y' iv:N).
enter_loop_m I.
{ prove_inv; exsp. }
move=> i1 M1 >; rewrite ?set_treeP.
unfold_inv => - [Hi Hq].
csteps.
case END: Int64.ltu => /=.
- csteps; evalf; csteps.
  cret; split=> // _; split.
  { solve_loop_conditions. }
  prove_inv; exsp.
  { move: END; clia. }
  have Hi3 : (i1:N < NM)%nat by exact: H1.
  have Ei : (Int64.add i1 (Int64.repr 1)):N = (i1:N).+1 by move: END; clia.
  rewrite Ei.
  apply: (packed_step _ _ _ _ _ Hly Hi3).
  { by move: END; clia. }
  { by move: END; clia. }
  exact: Hq.
- (* the loop is done: s[0] = hs[0] - 160 *)
  csteps.
  cret; split=> //= _.
  csteps; evalf; csteps; cret.
  do 3 eexists; split; first reflexivity; split; first reflexivity.
  split; first by move=> /(_ (rc_eq0 _ EQ)).
  move=> _.
  have Ei : i1:N = 3%nat by move: END Hi; clia.
  have HM : packed M1 y' NM by move: Hq; rewrite Ei.
  rewrite (packed_all M1 y' HM).
  rewrite (setfP _ _ _ H) /=.
  have [_ Hb] := ExpModelBounds.core_bounds _ _ _ Hcore.
  have E1 : forall o : 'I_1, hs' o = hs' ord0 by move=> o; rewrite (ord1 o).
  rewrite E1.
  have -> : (0 == (Int64.repr 0):N)%nat = true by [].
  rewrite (signed_sub160 _ Hb) /ExpModel.exp_encl_Z Hcore.
  done.
Qed.
