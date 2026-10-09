(* AdjointFold.v — the adjoint simulation of folds updating an array in place
   (milestone M5).

   The body of such a fold binds scalars and ends with a single set of the
   state (abody): the forward sweep runs the steps, pushing the element each
   set overwrites on the tape when the state is recorded; the reverse sweep
   pops it back before replaying and transposing the step.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint Simplify Scoping
  AnfEquiv Correctness TangentCorrect TangentLoops TangentGood AdjointCorrect AdjointBranch.
From Corelib Require Import ssreflect ssrbool ssrfun.

Import ListNotations.
Open Scope list_scope.

Section Fold.
Variable cv : bool.

(* The tape of the forward sweep after one more step: the element its set
   overwrites, pushed last. *)
Lemma fold_pushes_snoc (b : val (dual R) -> val (dual R) -> anf (val (dual R)) bare) z tr st :
  fold_pushes b z (tr ++ [st]) =
  fold_pushes b z tr ++
  match set_index (b (VInt (z + Z.of_nat (length tr))) st), st with
  | Some zi, VArray l => [match nth_z zi (map dfst l) with Some x => x | None => 0%R end]
  | _, _ => []
  end.
Proof.
elim: tr z => [| st0 tr IH] z /=.
  by rewrite app_nil_r Z.add_0_r.
rewrite IH -app_assoc.
have -> : (z + 1 + Z.of_nat (length tr) = z + Z.pos (Pos.of_succ_nat (length tr)))%Z by lia.
by [].
Qed.

(* The forward sweep of a fold updating an array in place: each step runs the
   body, whose set overwrites one element of the array, pushed on the tape
   first when the state is recorded. *)
Lemma afwd_fold_inplace a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, abody (bP x y)) -> asim_fwd cv (AFold a loP hiP initP bP).
Proof.
move=> [q [-> Hqa]] Hab L k c s wP pp tail eA eW eT eD te n ve ty m rec HA HW HT HD Hc Htc Htail [j [Ej Hj]] Hst Hrec Hev.
have HA0 := HA; have HW0 := HW; have HD0 := HD.
destruct eA; try contradiction; destruct eW; try contradiction; destruct eT; try contradiction; destruct eD; try contradiction.
rewrite /= in HA HW HT HD.
repeat match goal with
       | H : _ /\ _ |- _ => destruct H
       | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gT _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       end; subst.
rename b into bA, b0 into bW, b1 into bT, b2 into bD.
match goal with H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ => rename H into HbA end.
match goal with H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ => rename H into HbW end.
match goal with H : forall (i1 : pv) (i2 : tvar W) (s1 : pv) (s2 : tvar W), _ |- _ => rename H into HbT end.
match goal with H : forall (i1 : pv) (i2 : val (dual R)) (s1 : pv) (s2 : val (dual R)), _ |- _ =>
  rename H into HbD end.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite /= in Htc.
destruct init as [ia | |]; try contradiction; move/in_gA: H13 => [HqL Eia]; subst ia.
destruct init0 as [iw | |]; try contradiction; move/in_gW: H9 => [_ Eiw]; subst iw.
destruct init1 as [it | |]; try contradiction; move/in_gT: H5 => [_ Eit]; subst it.
destruct init2 as [id | |]; try contradiction; move/in_gD: H1 => [_ Eid]; subst id.
case Eb: (ty_eqb (of_atom (amap pw loP)) Integer && ty_eqb (of_atom (amap pw hiP)) Integer) Htc => // Htc.
rewrite /= in Htc.
case Eqz: (vty (pw q)) Hqa Htc => [| | | z] // _ Htc.
rewrite /= in Htc.
(* the array is the one the place updates in place *)
have [Hown Etail] : owner wP pp = Some q /\ tail = true.
{ destruct pp as [| | | ix0 sx0]; destruct tail; rewrite /= in Htc; try discriminate.
  - destruct wP as [y |] eqn:Ew; rewrite /= in Htc; last by [].
    case E: (match amap pw y with AVar y0 => (vid (pw q) =? vid y0)%nat | _ => false end) Htc => // Htc.
    have [->] := unique_written_s _ _ _ _ _ _ _ _ _ Hs HqL erefl E.
    by rewrite /= Eqz.
  - case E: (vid (pw q) =? vid (pw sx0))%nat Htc => // Htc.
    have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hs.
    by rewrite (same_vid_s _ _ _ _ _ _ _ _ _ Hs HqL Hsx E). }
subst tail.
have Hin_pl : in_place_init (option_map (amap pw) wP) (wplace pp) true (AVar (pw q)) = true.
  by case: (in_place_init (option_map (amap pw) wP) (wplace pp) true (AVar (pw q))) Htc.
rewrite Hin_pl in Htc.
case Hocc: (occurs_anf (vid (pw q)) (S (S k)) (bW (anon k) (anon (S k)))) Htc => Htc.
  by case: (varg (pw q)) Htc => [[? ?] |].
case HtB: (typecheck (option_map (amap pw) wP) (ArrayBody (AVar (VInfo k Integer None)) (AVar (VInfo (S k) (Array z) None)))
            (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))) Htc => [tb [| mm]] // Htc.
case Etb: (ty_eqb tb (Array z)) Htc => // Htc.
case: (reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k)))) Htc => // Htc.
move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => <-.
rewrite /= Eqz in Hst; set n := DBound (j, j) in Hst Hrec *.
cbn [annotate_value_t rebuild_value fold_binders].
rewrite (fun w sv live0 recs lo hi init b nn rr z0 =>
  (eq_refl : fwd_value W w m (AFold (FoldAnn sv live0 recs) lo hi init b) (Array z0) nn rr =
   Fresh "i" (fun i => let '(ix, sx) := open_fold sv (Array z0) nn (DBound i) ((sweep_eqb m Forward && live0) || rr) in
     sbind (prim W w m (b ix sx)) (fun '(sb, _) =>
       Done ((if sweep_eqb m Forward && is_written w init && recs then [DTape (TapeOf nn)] else []) ++
             [DFor (DBound i) (spell lo) (spell hi) sb])%list)))).
cbn [open_pairs open_fold].
rewrite open_pairs_sbind.
lazymatch goal with |- context [@open_pairs ?A ?t (S c)] => destruct (@open_pairs A t (S c)) as [[sb vb] c2] eqn:Hob end.
have Hc2 : (S c <= c2)%nat.
  by lazymatch type of Hob with @open_pairs _ ?t _ = _ => have := open_pairs_mono t (S c); rewrite Hob end.
cbn [open_pairs]; split; first by lia.
have [Eidq [Hkq [Hstq [Htyq [Htvq [Htdq [Htidq [Hvaq [Hhtq Hzq]]]]]]]]] := static_in _ _ _ HL HqL.
rewrite /= in Hev.
case Hlo: (aeval_atom (duals reals) (amap pd loP)) Hev => [[| l | | |] |] // Hev.
case Hhi: (aeval_atom (duals reals) (amap pd hiP)) Hev => [[| h | | |] |] // Hev.
set vr := fold_varied k (AVar (pa q)) bA in Hob *.
set live := state_live cv k (AVar (pa q)) bA in Hob *.
set rs := sweep_eqb m Forward && live || rec in Hob *.
set recs := records cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) in Hrec *.
have Hrl : live = true -> recs = true.
  by rewrite /recs /live /state_live /= /fold_binders /= => ->.
(* at the top, the fold declares the tape of the written argument *)
have Hisw : not_in_loop pp -> is_written (option_map (amap pt) wP) (AVar (pt q)) = true.
{ move=> Hnl; have Htid := a_tid _ _ _ _ _ _ _ _ _ Hc q Hown Hnl.
  destruct pp as [| | | ix0 sx0]; rewrite /= in Hown Hnl; try discriminate; last done.
  destruct wP as [[y | |] |]; try discriminate.
  move: Hown; case: (vty (pw y)) => [| | | z0] //= [->].
  by case: (tid (pt q)) Htid => [t _ | /(_ erefl)] //=; rewrite Nat.eqb_refl. }
set dcl := sweep_eqb m Forward && is_written (option_map (amap pt) wP) (AVar (pt q)) && recs.
set s0 := if dcl then store_set s (keyv (TapeOf n)) (VTape []) else s.
have Hrun0 : run (if dcl then [DTape (TapeOf n)] else []) s = Some s0 by rewrite /s0; case: ifP.
(* the tape the steps push on: a fresh one at the top *)
have [t0 [Ht0 Ht0e]] : exists t0, (sweep_eqb m Forward && rs = true -> store_get s0 (keyv (TapeOf n)) = Some (VTape t0)) /\
                                  (m = Forward -> not_in_loop pp -> live = true -> t0 = []).
{ rewrite /s0; case Edcl: dcl.
    by exists []; split=> [_ | _ _ _] //; exact: store_get_set_same.
  have Hnot : m = Forward -> not_in_loop pp -> live = true -> False.
    by move=> Hm Hnl Hlv; move: Edcl; rewrite /dcl Hm (Hisw Hnl) (Hrl Hlv).
  case Ers: (sweep_eqb m Forward && rs); last by exists [].
  have [l0 Hl0] : exists l0, store_get s (keyv (TapeOf n)) = Some (VTape l0).
  { apply: Hrec; case Erc: rec; [by left | right].
    move: Ers; rewrite /rs Erc orb_false_r => Ers.
    destruct m; last by [].
    split=> //; split; first exact: Hrl.
    split; first by rewrite /= Eqz.
    by move=> Hnl; apply: (Hnot erefl Hnl). }
  by exists l0; split=> // Hm Hnl Hlv; case: (Hnot Hm Hnl Hlv). }
have Hvat : forall aP, In aP [loP; hiP; AVar q] -> forall p, aP = AVar p ->
              vatoms k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
{ move=> aP HaP p E; rewrite /vatoms; cbn [atoms_of_value]; rewrite atom_member_union.
  have Hin3 : In (amap pa aP) [amap pa loP; amap pa hiP; AVar (pa q)].
    by case: HaP => [<- | [<- | [<- | []]]] /=; auto.
  by rewrite (atom_member_atoms (pa p) _ _ Hin3) ?E. }
have Hvatq := Hvat (AVar q) (or_intror (or_intror (or_introl erefl))) q erefl.
have Hlivq : live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) q.
  by rewrite /live_value /= Nat.eqb_refl !orb_true_r.
(* the state is varied: the inout argument at the top, or the state of the enclosing loop *)
have Hvq : avaried (pa q) = true.
{ destruct pp as [| | | ix0 sx0]; rewrite /= in Hown; try discriminate.
  - destruct wP as [[y | |] |]; try discriminate.
    move: Hown; case: (vty (pw y)) => [| | | z0] //= [Eyq]; subst y.
    have Hqa' : is_array (vty (pw q)) by rewrite Eqz.
    exact: (proj2 (s_top _ _ _ _ _ _ _ Hs q erefl erefl Hqa') Hlivq).
  - case: Hown => Eyq; subst sx0.
    by have [_ [_ [_ [_ [-> _]]]]] := s_place _ _ _ _ _ _ _ Hs. }
have Hvr : vr = true by rewrite /vr /fold_varied /= Hvq.
have Hn0 : store_get s (keyv n) = Some (primal (pd q)).
  by rewrite Hst; exact: (a_owner _ _ _ _ _ _ _ _ _ Hc q Hown (or_intror Hvatq)).
have Hs0n : store_get s0 (keyv n) = Some (primal (pd q)).
  by rewrite /s0; case: ifP => _ //; rewrite store_get_set_other.
have Ts0 : tkeep c (Some n) s s0.
  rewrite /s0; case: ifP => _; last exact: tkeep_refl.
  by apply: tkeep_set_tape => //; right.
have Fs0 : fwd_frame c (Some n) None s s0.
{ move=> v _ Hcv Ht _ _; rewrite /s0; case: ifP => _ //.
  apply: store_get_set_other => K.
  have Ev : v = TapeOf n by apply: keyv_inj => //.
  by subst v; apply: Ht. }
have Hrs0 : rs = true -> exists tl, store_get s0 (keyv (TapeOf n)) = Some (VTape tl).
{ move=> Ers; case Efr: (sweep_eqb m Forward && rs); first by exists t0; exact: Ht0.
  have Erc : rec = true.
    by move: Efr; rewrite Ers andb_true_r => Efr; move: Ers; rewrite /rs Efr.
  have [tl Htl] := Hrec (or_introl Erc).
  rewrite /s0; case: ifP => _; [exists []; exact: store_get_set_same | by exists tl]. }
(* each step keeps the invariant; the loop runs the steps *)
set Inv := fun (zz : Z) (s' : store R) (st : val (dual R)) (tr : list (val (dual R))) =>
  fwd_frame c (Some n) None s s' /\ tkeep c (Some n) s s' /\ store_get s' (keyv n) = Some (primal st) /\
  has_type (Array z) st /\
  (sweep_eqb m Forward && rs = true -> store_get s' (keyv (TapeOf n)) = Some (VTape (rev (fold_pushes bD l tr) ++ t0))) /\
  (rs = true -> exists tl, store_get s' (keyv (TapeOf n)) = Some (VTape tl)) /\
  zz = (l + Z.of_nat (length tr))%Z.
have Hstep : forall zz s' st tr st', Inv zz s' st tr -> aeval (duals reals) (bD (VInt zz) st) = Some st' ->
               exists s'', run sb (store_set s' (KVar (out_dvar nat (DBound (c, c)))) (VInt zz)) = Some s'' /\
                           Inv (zz + 1)%Z s'' st' (tr ++ [st]).
{ move=> zz s' st tr st' [Fr [Tk [Ns [Ht [Tp [Tr Ez]]]]]] Hbd.
  set i := DBound (c, c).
  set s'' := store_set s' (keyv i) (VInt zz).
  change (store_set s' (KVar (out_dvar nat i)) (VInt zz)) with s''.
  have Ci : consistent i by [].
  have Cn : consistent n by [].
  have Ctn : consistent (TapeOf n) by [].
  have Kin : forall v, below c v -> consistent v -> keyv v <> keyv i.
    by move=> v Hb Hcv K; move: Hb; rewrite (keyv_inj _ _ Hcv Ci K) /=; lia.
  have Hbn : below c n by rewrite /n /=.
  have N'' : store_get s'' (keyv n) = Some (primal st).
    by rewrite /s'' store_get_set_other //; apply: not_eq_sym; apply: Kin.
  have T'' : store_get s'' (keyv (TapeOf n)) = store_get s' (keyv (TapeOf n)).
    by rewrite /s'' store_get_set_other // => K; move: (keyv_inj _ _ Ctn Ci K).
  (* the index and the state of the step *)
  set ix := PV (fresh k) (VInfo k Integer None) (open_index i) (VInt zz) c.
  set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None) (TVar n (Array z) None vr vr vr rs None) st j.
  have Hix : static_ok (S (S k)) ix by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    repeat split; rewrite /=; auto; try lia; try discriminate.
    by rewrite Hvr.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    constructor=> //; constructor=> //; apply: Forall_impl HL => p Hp; apply: (static_mono k) => //; lia.
  (* the variables the body reads are not the state before the loop *)
  have Hlive_b : forall p, In p L -> live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)) p ->
                   live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p /\ pn p <> pn q.
  { move=> p Hp Hl.
    have Ec := live_cont2 L k bP bW ix sx (VInfo k Integer None) (VInfo (S k) (Array z) None) (vid (pw p)) HbW HL erefl erefl erefl erefl.
    have Hl' : live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p.
      by move: Hl; rewrite /live_anf /live_value /= Ec => ->; rewrite !orb_true_r.
    split=> // E.
    case: (s_owner _ _ _ _ _ _ _ Hs q p Hown Hp E) => [Epq | //].
    by move: Hl; rewrite /live_anf Ec Epq Hocc. }
  have Hjq : pn q = j by move: Hst; rewrite /n /stored => -[].
  set liveb := live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)).
  have Hsb : sctx (sx :: ix :: L) (S (S k)) (S c) wP (PArray ix sx) liveb (Array z).
  { constructor=> //.
    - move=> p p' [<- | [<- | Hp]] [<- | [<- | Hp']] E //=; move: E => /=; try lia;
        try (case: (static_in _ _ _ HL Hp') => _ [Hk' _] /=; lia);
        try (case: (static_in _ _ _ HL Hp) => _ [Hk' _] /=; lia).
      exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hp').
    - move=> p [<- | [<- | Hp]] /=; try lia.
      by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
    - move=> a0 E; have [y [-> [Hy Hv]]] := s_written _ _ _ _ _ _ _ Hs _ E.
      by exists y; split=> //; split=> //; right; right.
    - by rewrite /= Hvr; repeat split; auto.
    - move=> o p [<-] [<- | [<- | Hp]] Ep; [by left | by move: Ep => /=; lia |].
      by right=> Hl; case: (Hlive_b p Hp Hl) => _ Hpn; apply: Hpn; rewrite Hjq.
    - move=> p o [<- | [<- | Hp]] Lp Ha Hg [<-] //.
      case: (Hlive_b p Hp Lp) => Hl' _.
      by rewrite /= -Hjq; exact: (s_arrays _ _ _ _ _ _ _ Hs p q Hp Hl' Ha Hg Hown). }
  have Hctx : actx (sx :: ix :: L) (S (S k)) (S c) s'' wP (PArray ix sx) liveb liveb (Array z).
  { constructor=> //.
    - move=> p [<- | [<- | Hp]] //=; exact: (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp).
    - move=> p [<- | [<- | Hp]] Hl; first exact: N''.
        by rewrite /s'' store_get_set_same.
      case: (Hlive_b p Hp Hl) => Hl' Hpn.
      have Hbp : below c (stored p) by rewrite /stored /=; exact: (s_num _ _ _ _ _ _ _ Hs _ Hp).
      have Hpn' : Some n <> Some (stored p).
        by move=> [E]; case: Hpn; move: E; rewrite Hjq /n /stored => ->.
      rewrite /s'' store_get_set_other; first by apply: not_eq_sym; apply: Kin.
      rewrite (Fr (stored p) Hbp erefl id Hpn') //.
      exact: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp (live_vatoms _ _ _ _ _ p HA0 HW0 HL Hp Hl')).
    - move=> p [<- | [<- | Hp]] Hr //=.
        by rewrite T''; apply: Tr.
      have [lt Hlt] := a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr.
      have [l' Hl'] := proj1 Tk _ _ Hlt.
      by exists l'; rewrite /s'' store_get_set_other // => K; move: (keyv_inj _ _ erefl Ci K).
    - by move=> o [<-] _; exact: N''. }
  (* the step runs the body *)
  have HtB' : typecheck (option_map (amap pw) wP) (wplace (PArray ix sx)) (S (S k)) (bW (pw ix) (pw sx)) = (Array z, Ok)
    by exact: HtB.
  have Hps := abody_psim cv _ (Hab ix sx) (sx :: ix :: L) (S (S k)) (S c) s'' wP (PArray ix sx) m Replay
                (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bT (pt ix) (pt sx)) (bD (pd ix) (pd sx)) (Array z) st'
                (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _) Hctx HtB' Hbd.
  move: Hps.
  lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
    have E : @open_pairs A t (S c) = ((sb, vb), c2) by exact: Hob end.
  rewrite E => -[_ [s3 [R3 [F3 [T3 [_ Ho3]]]]]].
  have [Tp3 [Ns3 Se3]] := Ho3 sx erefl.
  have Hsi : set_index (bD (pd ix) (pd sx)) <> None.
    by apply: (abody_set_index (sx :: ix :: L) _ _ st' (Hab ix sx) (HbD ix _ sx _) Hbd).
  have [Hht' _] := abody_act _ (Hab ix sx) (sx :: ix :: L) (S (S k)) wP (PArray ix sx)
                     (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bD (pd ix) (pd sx)) (Array z) st'
                     (HbA ix _ sx _) (HbW ix _ sx _) (HbD ix _ sx _) HL' HtB' Hbd.
  have Htape : forall r zi st0 tl, exists tl', tape_step r zi st0 (Some (VTape tl)) = Some (VTape tl').
    by move=> r zi st0 tl; rewrite /tape_step; case: r; case: zi => [zi|]; case: st0 => *; eexists.
  exists s3; split; first exact: R3.
  split.
  { move=> v Hb Hcv Htv Hex Hvo.
    have Hb' : below (S c) v by apply: (below_mono c) => //; lia.
    rewrite (F3 v Hb' Hcv Htv Hex Hvo) /s'' store_get_set_other; first by apply: not_eq_sym; apply: Kin.
    exact: Fr. }
  split.
  { apply: (tkeep_trans _ _ _ s') => //; apply: (tkeep_trans _ _ _ s''); first by apply: tkeep_set.
    by apply: (tkeep_mono _ (S c)) => //; lia. }
  split; first exact: Ns3.
  split; first exact: Hht'.
  (* the tape gets the element the set overwrites *)
  split.
  { move=> Efr; rewrite Tp3 T'' Tp // fold_pushes_snoc -Ez.
    case: (set_index (bD (VInt zz) st)) Hsi => [zi _ | []] //.
    destruct st; try contradiction.
    by rewrite /= Efr rev_app_distr. }
  split.
  { move=> Ers; have [tl Htl] := Tr Ers.
    by rewrite Tp3 T'' Htl; apply: Htape. }
  by rewrite length_app /= Ez; lia. }
have Hinit : Inv l s0 (pd q) [].
{ split; first exact: Fs0. split; first exact: Ts0. split; first exact: Hs0n.
  split; first by rewrite -Eqz. split; first by move=> E; rewrite (Ht0 E).
  split; first exact: Hrs0. by rewrite /= Z.add_0_r. }
have [sf [tr [Hex [Htr [Fs [Ts [Ns [_ [Tps _]]]]]]]]] :=
  fold_loop (fun v w => aeval (duals reals) (bD v w)) (run sb) (out_dvar nat (DBound (c, c))) Inv Hstep
            (count l h) l s0 (pd q) [] ve Hinit Hev.
(* the bounds, read before the loop *)
have Hatoms : forall aP, In aP [loP; hiP] -> forall p, aP = AVar p ->
                In p L /\ vatoms k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
{ move=> aP HaP p E; split; last by apply: (Hvat aP) => //; case: HaP => [<- | [<- | []]] /=; auto.
  by case: HaP => [Ea | [Ea | []]]; subst aP; auto. }
have Hops := fun aP H => operand_store _ _ _ _ _ _ _ _ _ aP Hc (Hatoms aP H).
have Hb0 : forall aP, In aP [loP; hiP] -> forall zb, aeval_atom (duals reals) (amap pd aP) = Some (VInt zb) ->
             xev s0 (spell (amap pt aP)) = Some (VInt zb).
{ move=> aP HaP zb Hz; have Hsz := aspell_ok k s aP _ (Hops aP HaP) Hz.
  rewrite /s0; case: ifP => _ //; rewrite xev_set_other //.
  by apply: (avoid_tape_spell k) => p E; case: (Hops aP HaP p E). }
have Hl0 : xev s0 (spell (amap pt loP)) = Some (VInt l) by apply: Hb0 => //=; auto.
have Hh0 : xev s0 (spell (amap pt hiP)) = Some (VInt h) by apply: Hb0 => //=; auto.
exists sf; split; first by rewrite run_app Hrun0 (run_for _ _ _ _ _ _ l h Hl0 Hh0) Hex.
split; first exact: Fs. split; first exact: Ts. split; first exact: Ns.
(* at the top, the tape holds the overwritten elements, last first *)
case=> Hm Hnl; rewrite /fold_tape Hlo Hhi.
change (aeval_atom (duals reals) (amap pd (AVar q))) with (Some (pd q)).
move=> tr'; rewrite Htr => -[<-].
split; first by rewrite /= Eqz.
move=> _ Hlv; split.
  have Efr : sweep_eqb m Forward && rs = true by rewrite /rs /live Hm Hlv.
  by rewrite (Tps Efr) (Ht0e Hm Hnl Hlv) app_nil_r.
by move=> ve'; rewrite Hev => -[<-].
Qed.

End Fold.
