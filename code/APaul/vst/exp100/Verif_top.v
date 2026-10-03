(** * Task T6: maybe_hard_bits *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec E.TopLemmas.
Require Exp100.ExpConsts Exp100.ExpModel.

Lemma body_maybe_hard_bits :
  semax_body Vprog Gprog f_maybe_hard_bits maybe_hard_bits_spec.
Proof.
  start_function.
  forward_call (gv, Tsh, xb, v_y, v_hN).
  Intros vret; destruct vret as [[rc ys] hN]; cbn [fst snd] in *.
  rename H0 into Hok, H1 into Hko.
  destruct (Z.eqb_spec rc 0) as [->|Hrc].
  2: {
    pose proof (core_Z_rc _ _ (Hko Hrc)) as Hr.
    assert (Hm : M.maybe_hard_Z xb = 1).
    { unfold M.maybe_hard_Z; rewrite (Hko Hrc); reflexivity. }
    forward_if.
    - forward.
      cancel.
    - exfalso; apply Hrc.
      match goal with Hz : Int.repr rc = Int.zero |- _ =>
        apply repr_inj_signed; [rep_lia|rep_lia|exact Hz] end. }
  destruct (Hok eq_refl) as (Hcore & Hl & Hf); clear Hok Hko.
  destruct (core_bounds _ _ _ Hcore) as [Hyb HhN].
  destruct Dl_num as (HlD & HfD & HvD).
  pose proof (valZ_range _ Hl Hf) as Hyr.
  forward_if.
  { elim H0; reflexivity. }
  Intros.
  forward_call (Tsh, v_d).
  unfold num at 1.
  forward.
  replace_SEP 0 (num Tsh Dl v_d).
  { entailer!. }
  forward_call (Tsh, Tsh, v_lo, v_y, ys).
  forward_call (Tsh, Tsh, v_lo, v_d, ys, Dl).
  Intros lo1; rename H1 into Hllo, H2 into Hflo, H3 into Hvlo.
  forward_call (Tsh, Tsh, v_hi, v_y, ys).
  forward_call (Tsh, Tsh, v_hi, v_d, ys, Dl).
  { rewrite HvD; change num_bits with 192; zpow; lia. }
  Intros hi1; rename H1 into Hlhi, H2 into Hfhi, H3 into Hvhi.
  rewrite HvD in Hvlo, Hvhi.
  forward_call (Tsh, v_y, ys).
  forward_call (Tsh, v_lo, lo1).
  pose proof (bitlen_range _ (valZ_range _ Hl Hf)) as Rb.
  pose proof (bitlen_range _ (valZ_range _ Hllo Hflo)) as Rlo.
  pose proof (bitlen_range _ (valZ_range _ Hlhi Hfhi)) as Rhi.
  forward_if [temp _t'4 (Vint (Int.repr
    (if andb (M.bitlen (valZ lo1) =? M.bitlen (valZ ys))
             (M.bitlen (valZ hi1) =? M.bitlen (valZ ys)) then 0 else 1)))].
  { forward.
    rewrite (proj2 (Z.eqb_neq _ _) H1); entailer!. }
  { forward_call (Tsh, v_hi, hi1).
    forward.
    rewrite H1, Z.eqb_refl; entailer!.
    destruct (zeq _ _) as [E|E];
      [rewrite E, Z.eqb_refl|rewrite (proj2 (Z.eqb_neq _ _) E)];
      reflexivity. }
  forward_if.
  { forward.
    assert (Hm : M.maybe_hard_Z xb = 1).
    { match goal with Hz : Int.repr (if ?c then 0 else 1) <> _ |- _ =>
        destruct c eqn:Ec; [elim Hz; reflexivity|] end.
      rewrite andb_false_iff, !Z.eqb_neq, Hvlo, Hvhi in Ec.
      unfold M.maybe_hard_Z; rewrite Hcore; apply decide_bits; exact Ec. }
    rewrite Hm; entailer!.
    repeat sep_apply num_free; cancel. }
  match goal with Hz : Int.repr (if ?c then 0 else 1) = Int.zero |- _ =>
    destruct c eqn:Ec; [|exfalso; exact (Int.one_not_zero Hz)] end.
  rewrite andb_true_iff, !Z.eqb_eq, Hvlo, Hvhi in Ec; destruct Ec as [Eb1 Eb2].
  forward.
  forward.
  remember (M.bitlen (valZ ys)) as b eqn:Hb.
  assert (Ee : Int64.sub (Int64.add (Int64.sub (Int64.repr hN)
                 (Int64.repr (Int.signed (Int.repr 160))))
                 (Int64.repr (Int.signed (Int.repr b))))
                 (Int64.repr (Int.signed (Int.repr 1))) =
               Int64.repr (hN - 160 + b - 1)).
  { rewrite !Int.signed_repr by rep_lia.
    rewrite sub64_repr, add64_repr, sub64_repr; reflexivity. }
  rewrite Ee; clear Ee.
  zpow.
  forward_if [temp _t'6 (Vlong (Int64.repr (Z.max (hN - 160 + b - 1) (-1022))))].
  { forward.
    change (Int.signed (Int.neg (Int.repr 1022))) with (-1022) in *.
    rewrite Z.max_l by lia; entailer!. }
  { forward.
    change (Int.signed (Int.neg (Int.repr 1022))) with (-1022) in *.
    rewrite Z.max_r by lia; entailer!. }
  forward.
  forward.
  forward.
  remember (Z.max (hN - 160 + b - 1) (-1022) - 53 - (hN - 160)) as f eqn:Hfz.
  assert (Ef : Int64.sub (Int64.sub
                 (Int64.repr (Z.max (hN - 160 + b - 1) (-1022)))
                 (Int64.repr (Int.signed (Int.repr 53))))
                 (Int64.sub (Int64.repr hN)
                    (Int64.repr (Int.signed (Int.repr 160)))) =
               Int64.repr f).
  { rewrite !Int.signed_repr by rep_lia.
    rewrite !sub64_repr, Hfz; reflexivity. }
  rewrite Ef; clear Ef.
  assert (Rf : -2 ^ 13 <= f <= 2 ^ 13) by (zpow; lia).
  zpow.
  forward_if [temp _t'7 (Vint (Int.repr
                (if orb (f <? 64) (184 <? f) then 1 else 0)))].
  { forward.
    rewrite (proj2 (Z.ltb_lt _ _) H2); entailer!. }
  { forward.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia; cbn [orb].
    entailer!.
    change (32 * 6 - 8) with 184.
    unfold Int64.cmp, Int64.lt; rewrite !Int64.signed_repr by rep_lia.
    match goal with |- context [184 <? ?x] =>
      destruct (Z.ltb_spec 184 x), (zlt 184 x) end;
      try lia; reflexivity. }
  pose proof (decide_f (valZ ys) hN f ltac:(congruence) ltac:(congruence)
                ltac:(rewrite Hfz, Hb; reflexivity)) as Hd.
  forward_if.
  { forward.
    assert (Hm : M.maybe_hard_Z xb = 1).
    { unfold M.maybe_hard_Z; rewrite Hcore, Hd.
      match goal with Hz : Int.repr (if ?c then 1 else 0) <> _ |- _ =>
        destruct c; [reflexivity|elim Hz; reflexivity] end. }
    rewrite Hm; entailer!.
    repeat sep_apply num_free; cancel. }
  match goal with Hz : Int.repr (if ?c then 1 else 0) = Int.zero |- _ =>
    destruct c eqn:Ec; [exfalso; exact (Int.one_not_zero Hz)|] end.
  cbv iota zeta in Hd.
  rewrite orb_false_iff, Z.ltb_ge, Z.ltb_ge in Ec.
  (* missing: from num_low(lo, y, (int) f) to the end, see PICKUP-T6.md *)
  admit.
Admitted.
