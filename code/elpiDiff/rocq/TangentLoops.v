(* TangentLoops.v — theorem 1, continued: the loops of the tangent
   simulation, a map writing the output array, and the folds, on a real state
   or updating an array in place. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Tangent Simplify Scoping
  AnfEquiv Correctness TangentCorrect.

Import ListNotations.
Open Scope R_scope.

(* The context of the body of a map or of a scalar fold: no storage updated
   in place. *)
Lemma ctx_scalar (L : list pv) k c s wP (live : pv -> Prop) :
  Forall (static_ok k) L -> ids_unique L -> (forall p, In p L -> (pn p < c)%nat) ->
  (forall p, In p L -> live p -> store_ok s p) ->
  (forall a, wP = Some a -> exists y, a = AVar y /\ In y L /\ varg (pw y) <> None) ->
  ctx_ok L k c s wP PScalar live Real.
Proof.
  intros; constructor; auto; simpl; try (intros; discriminate); exact I.
Qed.

(* A write to a variable opened at or after c keeps the frame. *)
Lemma frame_set_fresh c ex s s' v w :
  frame c ex s s' -> ~ below c v -> consistent v -> frame c ex s (store_set s' (keyv v) w).
Proof.
  intros F Hb Hc u Hu Hcu Hex; rewrite store_get_set.
  destruct (key_eqb (keyv v) (keyv u)) eqn:E; [| apply F; auto].
  apply key_eqb_eq, keyv_inj in E; auto; subst; contradiction.
Qed.

Lemma count_nat lo hi : count lo hi = Z.to_nat (hi - lo).
Proof. reflexivity. Qed.

(* A map, at the end of a function that writes an array: the loop writes
   each element of the output, and of its tangent. *)
Lemma sim_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, sim_body (bP x)) -> sim_value (AMap loP hiP bP).
Proof.
  intros IHb.
  value_intro. simpl in Htc, Hev |- *.
  rename b into bA, b0 into bW, b1 into bT, b2 into bD.
  pose proof (c_static _ _ _ _ _ _ _ _ Hc) as HL.
  (* typing: at the top, at the end, from index 0, writing an array argument *)
  destruct pp as [| | | ix0 sx0]; simpl in Htc; try discriminate.
  destruct tail; [| discriminate].
  destruct loP as [? | ? | l0]; simpl in Htc; try discriminate.
  destruct hiP as [? | ? | h]; simpl in Htc; try discriminate.
  destruct (negb (l0 =? 0)%Z) eqn:El; [discriminate |].
  apply negb_false_iff, Z.eqb_eq in El; subst l0.
  assert (Hte : te = Array (h - 0)) by (clear - Htc; crush_match Htc).
  destruct (owner wP PTop) as [o |] eqn:Eo;
    [| destruct (c_ty _ _ _ _ _ _ _ _ Hc ltac:(rewrite <- (Htail eq_refl), Hte; exact I) Eo)].
  destruct wP as [[o' | |] |]; simpl in Eo; try discriminate.
  destruct (vty (pw o')) as [| | | ny] eqn:Ey; try discriminate; injection Eo as ->.
  simpl in Hst; injection Hst as Ej; subst j.
  assert (Hfacts : occurs_anf (vid (pw o)) (S k) (bW (anon k)) = false /\
                   typecheck (Some (AVar (pw o))) ScalarBody (S k) (bW (VInfo k Integer None)) = (Real, Ok)).
  { simpl in Htc; destruct (varg (pw o)) as [[nm [] ] |]; simpl in Htc; try discriminate;
      destruct (occurs_anf (vid (pw o)) (S k) (bW (anon k))); try discriminate;
      destruct (typecheck (Some (AVar (pw o))) ScalarBody (S k) (bW (VInfo k Integer None))) as [tb [| mm]];
      simpl in Htc; try discriminate; destruct (ty_eqb tb Real) eqn:Etb; try discriminate;
      apply ty_eqb_true in Etb; subst; auto. }
  destruct Hfacts as [Hnocc HtB].
  destruct (c_written _ _ _ _ _ _ _ _ Hc _ eq_refl) as [o'' [Eo'' [HoL _]]]; injection Eo'' as <-.
  destruct (c_top _ _ _ _ _ _ _ _ Hc o eq_refl eq_refl ltac:(rewrite Ey; exact I))
    as [Hty [_ [l1 [l2 [A1 [A2 [A3 A4]]]]]]].
  rewrite Ey in Hty, A2, A4; rewrite <- (Htail eq_refl), Hte in Hty; injection Hty as Ehn.
  (* the dual evaluation *)
  simpl in Hev; destruct (eval_map (fun v1 => aeval (duals reals) (bD v1)) 0 (count 0 h)) as [xs |] eqn:Hxs;
    [| discriminate]; injection Hev as <-.
  (* the body, opened *)
  rewrite open_pairs_sbind.
  destruct (open_pairs (tan W (Some (AVar (pt o)))
             (rebuild (tvar W) (bT (open_index (DBound (c, c)))) (annotate_body_t false Replay (S k) (bA (fresh k)))))
             (S c)) as [[sb [vb db]] c2] eqn:Hob.
  pose proof (open_pairs_mono (tan W (Some (AVar (pt o)))
             (rebuild (tvar W) (bT (open_index (DBound (c, c)))) (annotate_body_t false Replay (S k) (bA (fresh k)))))
             (S c)) as Hc2; rewrite Hob in Hc2; simpl in Hc2.
  match goal with |- context [open_pairs ?t (S c)] =>
    replace (open_pairs t (S c)) with ((sb, (vb, db)), c2) by (rewrite <- Hob; reflexivity) end.
  cbn [open_pairs spell amap].
  set (vr := varied_anf (S k) (bA (fresh k))).
  set (n := DBound (pn o, pn o)) in *.
  set (i := DBound (c, c)) in *.
  set (bodyst := (sb ++ [DAssign (DAt (DVar n) (DVar i)) vb;
                         DAssign (DAt (DVar (DotOf n)) (DVar i)) (if vr then db else DReal "0")])%list).
  match goal with |- context [run ?t s] =>
    replace (run t s) with (run [DFor i (DInt 0) (DInt h) bodyst] s)
      by (unfold tan_map, bodyst; destruct vr; reflexivity) end.
  assert (Hlen1 : length l1 = count 0 h) by (rewrite A2, count_nat; congruence).
  assert (Hlen2 : length l2 = count 0 h) by (rewrite A4, count_nat; congruence).
  assert (Hown : owner (Some (AVar o)) PTop = Some o) by (simpl; rewrite Ey; reflexivity).
  (* the variables the body reads are not the output array *)
  assert (Hlive_b : forall p, In p L -> live_anf (S k) (bW (VInfo k Integer None)) p ->
                    live_value k (AMap (ANat 0) (ANat h) bW) p /\ pn p <> pn o).
  { intros p Hp Hl.
    assert (Hl' : live_value k (AMap (ANat 0) (ANat h) bW) p).
    { unfold live_anf, live_value in *; simpl.
      rewrite <- (live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ H7 HL eq_refl eq_refl); exact Hl. }
    split; [exact Hl' |]; intros E.
    destruct (c_owner _ _ _ _ _ _ _ _ Hc o p Hown Hp E) as [-> | Hn]; [| contradiction].
    unfold live_anf in Hl.
    rewrite (live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ H7 HL eq_refl eq_refl) in Hl.
    congruence. }
  set (Inv := fun (z : Z) (s' : store R) (acc : list (dual R)) =>
         z = Z.of_nat (length acc) /\ frame c (Some n) s s' /\
         store_get s' (keyv n) = Some (VArray (map dfst acc ++ skipn (length acc) l1))%list /\
         store_get s' (keyv (DotOf n)) = Some (VArray (map dsnd acc ++ skipn (length acc) l2))%list /\
         (vr = false -> Forall (fun d => dsnd d = 0) acc)).
  assert (Hloop : exists sf, exec_up R (run bodyst) (out_dvar nat i) 0 (count 0 h) s = Some sf /\
                             Inv (0 + Z.of_nat (count 0 h))%Z sf ([] ++ xs)%list).
  { apply (map_loop_bounded (fun v => aeval (duals reals) (bD v)) (run bodyst) (out_dvar nat i) Inv
             (Z.of_nat (count 0 h))); [| lia | | exact Hxs].
    - intros z s' acc d Hz [Ez [Hfr' [Hn' [Hd' Hzero]]]] Hbd.
      set (s'' := store_set s' (KVar (out_dvar nat i)) (VInt z)).
      set (ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c))) (VInt z) c).
      assert (Hix : static_ok (S k) ix) by (repeat split; simpl; auto; try lia; discriminate).
      assert (Hpo : (pn o < c)%nat) by exact (c_num _ _ _ _ _ _ _ _ Hc o HoL).
      assert (Hctx : ctx_ok (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar
                       (live_anf (S k) (bW (VInfo k Integer None))) Real).
      { apply ctx_scalar.
        - constructor; [exact Hix |]; apply Forall_impl with (P := static_ok k); auto.
          intros p Hp; apply (static_mono k); auto.
        - intros p q [<- | Hp] [<- | Hq] E; auto;
            try (destruct (static_in _ _ _ HL Hq) as [_ [Hq' _]]; simpl in E; lia);
            try (destruct (static_in _ _ _ HL Hp) as [_ [Hp' _]]; simpl in E; lia).
          exact (c_unique _ _ _ _ _ _ _ _ Hc _ _ Hp Hq E).
        - intros p [<- | Hp]; simpl; [lia |]; pose proof (c_num _ _ _ _ _ _ _ _ Hc _ Hp); lia.
        - intros p [<- | Hp] Hl.
          + split; [unfold s''; rewrite store_get_set_same; reflexivity | discriminate].
          + destruct (Hlive_b p Hp Hl) as [Hl' Hpn].
            pose proof (c_num _ _ _ _ _ _ _ _ Hc _ Hp) as Hpc.
            destruct (c_store _ _ _ _ _ _ _ _ Hc _ Hp Hl') as [S1 S2].
            assert (F1 : store_get s' (keyv (stored p)) = store_get s (keyv (stored p)))
              by (apply Hfr'; unfold stored; simpl; auto; intros m E; injection E as <-;
                  unfold n; split; intros E; inversion E; auto).
            assert (F2 : store_get s' (keyv (DotOf (stored p))) = store_get s (keyv (DotOf (stored p))))
              by (apply Hfr'; unfold stored; simpl; auto; intros m E; injection E as <-;
                  unfold n; split; intros E; inversion E; auto).
            unfold s''; split.
            * rewrite store_get_set_other; [rewrite F1; exact S1 | unfold keyv, stored; simpl; intros E; inversion E; lia].
            * intros Hd; rewrite store_get_set_other; [rewrite F2; exact (S2 Hd) | unfold keyv; simpl; discriminate].
        - intros a0 E; injection E as <-; exists o; split; [reflexivity | split; [right; exact HoL |]].
          destruct (c_written _ _ _ _ _ _ _ _ Hc _ eq_refl) as [? [E [_ Hg]]]; injection E as <-; exact Hg. }
      specialize (IHb ix (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar Replay (bA (fresh k))
                    (bW (VInfo k Integer None)) (bT (open_index (DBound (c, c)))) (bD (VInt z)) Real (VReal d)
                    (H10 ix _) (H7 ix _) (H4 ix _) (H1 ix _) Hctx I HtB Hbd).
      match type of IHb with context [open_pairs ?t (S c)] =>
        replace (open_pairs t (S c)) with ((sb, (vb, db)), c2) in IHb by (rewrite <- Hob; reflexivity) end.
      destruct IHb as [_ [_ [Hzb [_ [Hrvd [s3 [Hrun3 [Hfr3 [Hvb Hdb]]]]]]]]].
      apply dot_vars_res in Hrvd.
      (* the stored array and the index, after the body *)
      assert (Kin : keyv i <> keyv n) by (unfold keyv, i, n; simpl; intros E; inversion E; lia).
      assert (S3n : store_get s3 (keyv n) = store_get s' (keyv n)).
      { rewrite (Hfr3 n); [unfold s''; apply store_get_set_other; exact Kin | unfold n; simpl; lia
                          | reflexivity | discriminate]. }
      assert (S3d : store_get s3 (keyv (DotOf n)) = store_get s' (keyv (DotOf n))).
      { rewrite (Hfr3 (DotOf n)); [unfold s''; apply store_get_set_other; unfold keyv; simpl; discriminate
                                  | unfold n; simpl; lia | reflexivity | discriminate]. }
      assert (S3i : xev s3 (DVar i) = Some (VInt z)).
      { change (xev s3 (DVar i)) with (store_get s3 (keyv i)).
        rewrite (Hfr3 i); [unfold s''; apply store_get_set_same | unfold i; simpl; lia | reflexivity | discriminate]. }
      assert (Hacc : (length acc < length l1)%nat /\ (length acc < length l2)%nat) by lia.
      set (a1 := VArray (map dfst (acc ++ [d]) ++ skipn (length (acc ++ [d])) l1)%list).
      set (a2 := VArray (map dsnd (acc ++ [d]) ++ skipn (length (acc ++ [d])) l2)%list).
      set (s4 := store_set s3 (keyv n) a1).
      assert (Hrun4 : run [DAssign (DAt (DVar n) (DVar i)) vb] s3 = Some s4).
      { apply (run_assign_at s3 n _ _ (map dfst acc ++ skipn (length acc) l1)%list z (dfst d)); [rewrite S3n; exact Hn' | exact S3i | exact Hvb |].
        rewrite Ez; apply replace_step; lia. }
      (* the tangent written: the tangent of the body, or 0 when it is not varied *)
      assert (Hav : avoid (keyv n) db).
      { intros x Hx E; destruct (Hrvd x Hx) as [[p [[<- | Hp] [Lp [-> | ->]]]] | [Hb Hcx]];
          first [ (unfold keyv, n, stored in E; simpl in E; inversion E; lia)
                | (destruct Lp as [Lp | Lp];
                   [ destruct (Hlive_b p Hp Lp) as [_ Hpn]; unfold keyv, n, stored in E; simpl in E;
                     inversion E; auto
                   | discriminate ])
                | (apply keyv_inj in E; [subst; simpl in Hb; lia | exact Hcx | reflexivity]) ]. }
      assert (Hdv : xev s4 (if vr then db else DReal "0") = Some (VReal (dsnd d))).
      { destruct vr eqn:Hvr.
        - unfold s4; rewrite xev_set_other; [exact Hdb | exact Hav].
        - rewrite (Hzb Hvr), xev_DReal, lit_0; reflexivity. }
      assert (Hrun5 : run [DAssign (DAt (DVar (DotOf n)) (DVar i)) (if vr then db else DReal "0")] s4 =
                      Some (store_set s4 (keyv (DotOf n)) a2)).
      { apply (run_assign_at s4 (DotOf n) _ _ (map dsnd acc ++ skipn (length acc) l2)%list z (dsnd d)).
        - unfold s4; rewrite store_get_set_other; [rewrite S3d; exact Hd' | apply keyv_dot_neq].
        - unfold s4; rewrite xev_set_other; [exact S3i | intros x [<- | []]; exact Kin].
        - exact Hdv.
        - rewrite Ez; apply replace_step; lia. }
      exists (store_set s4 (keyv (DotOf n)) a2); split.
      + unfold bodyst; rewrite run_app, Hrun3; exact (run_two _ _ _ _ _ Hrun4 Hrun5).
      + split; [rewrite length_app; simpl; lia |].
        split.
        * apply frame_set; [| reflexivity | right; reflexivity].
          apply frame_set; [| reflexivity | left; reflexivity].
          apply (frame_chain c (S c) _ s s'' s3); [| exact Hfr3 | lia].
          apply frame_set_fresh; [exact Hfr' | unfold i; simpl; lia | reflexivity].
        * split; [unfold s4; rewrite store_get_set_other, store_get_set_same; [reflexivity | apply not_eq_sym, keyv_dot_neq] |].
          split; [rewrite store_get_set_same; reflexivity |].
          intros Hvr; apply Forall_app; split; [exact (Hzero Hvr) | constructor; [exact (Hzb Hvr) | constructor]].
    - split; [reflexivity | split; [apply frame_refl | split; [exact A1 | split; [exact A3 |]]]].
      intros _; constructor. }
  destruct Hloop as [sf [Hex [_ [Hfr [Hn' [Hd' Hzero]]]]]].
  simpl app in Hn', Hd', Hzero.
  pose proof (eval_map_length _ _ _ _ Hxs) as Hlx.
  rewrite Hlx, <- Hlen1, skipn_all, app_nil_r in Hn'.
  rewrite Hlx, <- Hlen2, skipn_all, app_nil_r in Hd'.
  split; [lia |].
  split; [rewrite Hte; simpl; rewrite Hlx; reflexivity |].
  split; [exact Hzero |].
  split; [intros _; rewrite Hte; exact I |].
  exists sf; split; [rewrite (run_for _ _ _ _ _ _ 0 h) by reflexivity; rewrite Hex; reflexivity |].
  split; [exact Hfr | split; [exact Hn' | intros _; exact Hd']].
Qed.

(* The body of a fold, opened as the simulation opens it and as well_formed's
   occurs opens it, has the same occurrences. *)
Lemma live_cont2 L k (bP : pv -> pv -> anf pv bare) (bW : vinfo -> vinfo -> anf vinfo bare) x y w1 w2 id :
  (forall i1 i2 s1 s2, anf_eq ((s1, s2) :: (i1, i2) :: gW L) (bP i1 s1) (bW i2 s2)) ->
  Forall (static_ok k) L -> aid (pa x) = k -> aid (pa y) = S k -> vid w1 = k -> vid w2 = S k ->
  occurs_anf id (S (S k)) (bW w1 w2) = occurs_anf id (S (S k)) (bW (anon k) (anon (S k))).
Proof.
  intros HbW HL Hx Hy Hw1 Hw2.
  apply (proj1 occurs_transfer (bP x y) ((y, w2) :: (x, w1) :: gW L) ((y, anon (S k)) :: (x, anon k) :: gW L));
    auto.
  pose proof (aids_below L k HL) as Ha.
  assert (Hxn : ~ In x L) by (intros I; specialize (Ha _ I); lia).
  assert (Hyn : ~ In y L) by (intros I; specialize (Ha _ I); lia).
  assert (Hxy : x <> y) by (intros ->; lia).
  split.
  - intros p u1 u2 [E1 | [E1 | I1]] [E2 | [E2 | I2]];
      repeat match goal with
      | E : (_, _) = (_, _) |- _ => inversion E; subst; clear E
      | I : In (_, _) (gW L) |- _ => apply in_gW in I; destruct I as [? ?]; subst
      end; simpl; auto; try contradiction; try lia.
  - intros p u [[E | [E | I]] | [E | [E | I]]];
      try (inversion E; subst; lia); apply in_gW in I as [I _]; specialize (Ha _ I); lia.
Qed.

(* A fold: a loop updating the state, a real in a fresh variable, or the
   array updated in place. *)
Lemma sim_fold a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (forall x y, sim_body (bP x y)) -> sim_value (AFold a loP hiP initP bP).
Proof.
  intros IHb.
  value_intro. simpl in Htc, Hev |- *.
  rename b into bA, b0 into bW, b1 into bT, b2 into bD.
  match goal with H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ => rename H into HbA end.
  match goal with H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ => rename H into HbW end.
  match goal with H : forall (i1 : pv) (i2 : tvar W) (s1 : pv) (s2 : tvar W), _ |- _ => rename H into HbT end.
  match goal with H : forall (i1 : pv) (i2 : val (dual R)) (s1 : pv) (s2 : val (dual R)), _ |- _ =>
    rename H into HbD end.
  pose proof (c_static _ _ _ _ _ _ _ _ Hc) as HL.
  (* the bounds, the initial state *)
  destruct (ty_eqb (of_atom (amap pw loP)) Integer && ty_eqb (of_atom (amap pw hiP)) Integer) eqn:Eb;
    [| discriminate].
  assert (Hlv : forall p, loP = AVar p \/ hiP = AVar p \/ initP = AVar p ->
            In p L /\ live_value k (AFold Bare (amap pw loP) (amap pw hiP) (amap pw initP) bW) p).
  { intros p [E | [E | E]]; subst; split; auto; unfold live_value; simpl;
      rewrite Nat.eqb_refl, ?orb_true_r; reflexivity. }
  assert (Hops : forall aP, (aP = loP \/ aP = hiP \/ aP = initP) ->
            forall p, aP = AVar p -> static_ok k p /\ store_ok s p).
  { intros aP HaP p E; destruct (Hlv p ltac:(destruct HaP as [-> | [-> | ->]]; auto)) as [Hp Lp].
    split; [exact (static_in _ _ _ HL Hp) | exact (c_store _ _ _ _ _ _ _ _ Hc _ Hp Lp)]. }
  destruct (aeval_atom (duals reals) (amap pd loP)) as [[| l | | |] |] eqn:Hlo; try discriminate.
  destruct (aeval_atom (duals reals) (amap pd hiP)) as [[| h | | |] |] eqn:Hhi; try discriminate.
  destruct (aeval_atom (duals reals) (amap pd initP)) as [s0 |] eqn:Hin; [| discriminate].
  assert (Hslo := spell_ok k s loP _ (Hops loP ltac:(auto)) Hlo).
  assert (Hshi := spell_ok k s hiP _ (Hops hiP ltac:(auto)) Hhi).
  assert (Hsin := spell_ok k s initP _ (Hops initP ltac:(auto)) Hin).
  set (svr := fold_varied k (amap pa initP) bA) in *.
  destruct (ty_eqb (of_atom (amap pw initP)) Real) eqn:Er.
  - (* a real state, at the top *)
    apply ty_eqb_true in Er.
    destruct pp as [| | | ix0 sx0]; simpl in Htc; try discriminate.
    destruct (typecheck (option_map (amap pw) wP) ScalarBody (S (S k))
                (bW (VInfo k Integer None) (VInfo (S k) Real None))) as [tb [| mm]] eqn:HtB;
      simpl in Htc; try discriminate.
    destruct (ty_eqb tb Real) eqn:Etb; simpl in Htc; try discriminate.
    apply ty_eqb_true in Etb; subst tb; injection Htc as <-.
    assert (Hfresh : forall p, In p L -> pn p <> j).
    { intros p Hp E.
      assert (Hs : storage wP tail (AFold a loP hiP initP bP) = None)
        by (destruct initP as [q | |]; simpl in Er |- *; try rewrite Er; reflexivity).
      rewrite Hs in Hst; destruct (Hst p Hp) as [H' _]; apply H'; unfold stored; rewrite E; reflexivity. }
    cbn [open_pairs].
    rewrite open_pairs_sbind.
    match goal with |- context [open_pairs ?t (S c)] =>
      destruct (open_pairs t (S c)) as [[sb [vb db]] c2] eqn:Hob;
      pose proof (open_pairs_mono t (S c)) as Hc2; rewrite Hob in Hc2; simpl in Hc2 end.
    cbv beta iota.
    set (n := DBound (j, j)) in *.
    set (i := DBound (c, c)) in *.
    set (bodyst := (sb ++ (if svr then [DAssign (DVar n) vb; DAssign (DVar (DotOf n)) db]
                           else [DAssign (DVar n) vb]))%list).
    set (pre := if svr then [DDefine DMutable n (spell (amap pt initP));
                             DDefine DMutable (DotOf n) (dot (amap pt initP))]
                else [DDefine DMutable n (spell (amap pt initP))]).
    cbn [open_pairs].
    change (varied (amap pa initP) || varied_anf (S (S k)) (bA (fresh k) (fresh (S k)))) with svr.
    match goal with |- context [run ?t s] =>
      replace (run t s) with (run (pre ++ [DFor i (spell (amap pt loP)) (spell (amap pt hiP)) bodyst])%list s)
        by (unfold tan_fold, pre, bodyst; destruct svr; reflexivity) end.
    (* the initial state *)
    assert (Hint : has_type Real s0)
      by (rewrite <- Er; exact (atom_type k initP s0 (fun p E => proj1 (Hops initP ltac:(auto) p E)) Hin)).
    destruct s0 as [d0 | | | |]; try contradiction.
    assert (Hnot : forall aP, (aP = loP \/ aP = hiP \/ aP = initP) ->
                   forall p, aP = AVar p -> static_ok k p /\ pn p <> j).
    { intros aP HaP p E; split; [exact (proj1 (Hops aP HaP p E)) |].
      apply Hfresh; apply (Hlv p); destruct HaP as [-> | [-> | ->]]; auto. }
    destruct (avoid_spell k loP j (Hnot loP ltac:(auto))) as [L1 [_ [L3 _]]].
    destruct (avoid_spell k hiP j (Hnot hiP ltac:(auto))) as [H1' [_ [H3' _]]].
    destruct (avoid_spell k initP j (Hnot initP ltac:(auto))) as [I1 [I2 [I3 I4]]].
    assert (Hdin := dot_ok k s initP _ (Hops initP ltac:(auto)) Hin).
    set (s1 := if svr then store_set (store_set s (keyv n) (VReal (dfst d0))) (keyv (DotOf n)) (VReal (dsnd d0))
               else store_set s (keyv n) (VReal (dfst d0))).
    assert (Hrun1 : run pre s = Some s1).
    { unfold pre, s1; destruct svr.
      - apply run_define2; [exact Hsin | rewrite xev_set_other; [exact Hdin | exact I2]].
      - apply run_define; exact Hsin. }
    assert (Hlo1 : xev s1 (spell (amap pt loP)) = Some (VInt l))
      by (unfold s1; destruct svr; rewrite ?xev_set_other; auto).
    assert (Hhi1 : xev s1 (spell (amap pt hiP)) = Some (VInt h))
      by (unfold s1; destruct svr; rewrite ?xev_set_other; auto).
    (* the loop *)
    set (Inv := fun (z : Z) (s' : store R) (st : val (dual R)) =>
           frame c (Some n) s s' /\ store_get s' (keyv n) = Some (primal st) /\
           (svr = true -> store_get s' (keyv (DotOf n)) = Some (tangent st)) /\
           has_type Real st /\ (svr = false -> zero st)).
    assert (Hlive_b : forall p, In p L -> live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None)) p ->
                      live_value k (AFold Bare (amap pw loP) (amap pw hiP) (amap pw initP) bW) p).
    { intros p Hp Hl; unfold live_anf, live_value in *; simpl.
      rewrite <- (live_cont2 L k bP bW (pfresh k) (pfresh (S k)) (VInfo k Integer None) (VInfo (S k) Real None)
                   _ HbW HL eq_refl eq_refl eq_refl eq_refl); rewrite Hl, !orb_true_r; reflexivity. }
    assert (Hloop : exists sf, exec_up R (run bodyst) (out_dvar nat i) l (count l h) s1 = Some sf /\
                               Inv (l + Z.of_nat (count l h))%Z sf ve).
    { apply (fold_loop_sim (fun v w => aeval (duals reals) (bD v w)) (run bodyst) (out_dvar nat i) Inv)
        with (st := VReal d0); [| | exact Hev].
      - intros z s' st st' [Hfr' [Hn' [Hd' [Hht' Hz']]]] Hbd.
        destruct st as [dst | | | |]; try contradiction.
        set (s'' := store_set s' (KVar (out_dvar nat i)) (VInt z)).
        set (ix := PV (AV k false) (VInfo k Integer None) (TVar i Integer None false false false false None)
                      (VInt z) c).
        set (sx := PV (AV (S k) svr) (VInfo (S k) Real None) (TVar n Real None svr svr svr false None)
                      (VReal dst) j).
        assert (Kin : keyv i <> keyv n) by (unfold keyv, i, n; simpl; intros E; inversion E; lia).
        assert (Kid : keyv i <> keyv (DotOf n)) by (unfold keyv, i, n; simpl; discriminate).
        assert (Hctx : ctx_ok (sx :: ix :: L) (S (S k)) (S c) s'' wP PScalar
                         (live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None))) Real).
        { apply ctx_scalar.
          - constructor; [| constructor]; [repeat split; simpl; auto; try lia; discriminate
                                         | repeat split; simpl; auto; try lia; discriminate |].
            apply Forall_impl with (P := static_ok k); auto; intros p Hp; apply (static_mono k); auto.
          - intros p q Hp Hq E; destruct Hp as [<- | [<- | Hp]], Hq as [<- | [<- | Hq]]; simpl in E;
              try reflexivity; try lia;
              try (destruct (static_in _ _ _ HL Hq) as [_ [Hq' _]]; lia);
              try (destruct (static_in _ _ _ HL Hp) as [_ [Hp' _]]; lia).
            exact (c_unique _ _ _ _ _ _ _ _ Hc _ _ Hp Hq E).
          - intros p [<- | [<- | Hp]]; simpl; try lia; pose proof (c_num _ _ _ _ _ _ _ _ Hc _ Hp); lia.
          - intros p [<- | [<- | Hp]] Hl.
            + split; unfold s''; simpl.
              * rewrite store_get_set_other; [exact Hn' | intro E; apply Kin; exact E].
              * intros Hs; rewrite store_get_set_other; [exact (Hd' Hs) | intro E; apply Kid; exact E].
            + split; [unfold s''; rewrite store_get_set_same; reflexivity | discriminate].
            + pose proof (Hfresh p Hp) as Hpn; pose proof (c_num _ _ _ _ _ _ _ _ Hc _ Hp) as Hpc.
              destruct (c_store _ _ _ _ _ _ _ _ Hc _ Hp (Hlive_b p Hp Hl)) as [S1 S2].
              assert (F1 : store_get s' (keyv (stored p)) = store_get s (keyv (stored p)))
                by (apply Hfr'; unfold stored; simpl; auto; intros m E; injection E as <-;
                    unfold n; split; intros E; inversion E; auto).
              assert (F2 : store_get s' (keyv (DotOf (stored p))) = store_get s (keyv (DotOf (stored p))))
                by (apply Hfr'; unfold stored; simpl; auto; intros m E; injection E as <-;
                    unfold n; split; intros E; inversion E; auto).
              unfold s''; split.
              * rewrite store_get_set_other; [rewrite F1; exact S1 | unfold keyv, stored; simpl; intros E; inversion E; lia].
              * intros Hd; rewrite store_get_set_other; [rewrite F2; exact (S2 Hd) | unfold keyv; simpl; discriminate].
          - intros a0 E; destruct (c_written _ _ _ _ _ _ _ _ Hc _ E) as [y [-> [Hy Hg]]].
            exists y; split; [reflexivity | split; [right; right; exact Hy | exact Hg]]. }
        specialize (IHb ix sx (sx :: ix :: L) (S (S k)) (S c) s'' wP PScalar Replay (bA (pa ix) (pa sx))
                      (bW (VInfo k Integer None) (VInfo (S k) Real None)) (bT (pt ix) (pt sx)) (bD (VInt z) (VReal dst))
                      Real st' (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _) Hctx I HtB Hbd).
        match type of IHb with context [open_pairs ?t (S c)] =>
          replace (open_pairs t (S c)) with ((sb, (vb, db)), c2) in IHb by (rewrite <- Hob; reflexivity) end.
        destruct IHb as [_ [Hht2 [Hzb [_ [Hrvd [s3 [Hrun3 [Hfr3 [Hvb Hdb]]]]]]]]].
        destruct st' as [dst' | | | |]; try contradiction.
        assert (S3n : store_get s3 (keyv n) = store_get s' (keyv n)).
        { rewrite (Hfr3 n); [unfold s''; apply store_get_set_other; exact Kin | unfold n; simpl; lia
                            | reflexivity | discriminate]. }
        assert (Hav : avoid (keyv n) db).
        { intros x Hx E; destruct (Hrvd x Hx) as [[p [_ [_ ->]]] | [Hb Hcx]].
          - unfold keyv, n in E; simpl in E; discriminate.
          - apply keyv_inj in E; [subst; simpl in Hb; lia | exact Hcx | reflexivity]. }
        set (s4 := store_set s3 (keyv n) (VReal (dfst dst'))).
        assert (Hfr4 : frame c (Some n) s s4).
        { unfold s4; apply frame_set; [| reflexivity | left; reflexivity].
          apply (frame_chain c (S c) _ s s'' s3); [| exact Hfr3 | lia].
          apply frame_set_fresh; [exact Hfr' | unfold i; simpl; lia | reflexivity]. }
        assert (Hzst : svr = false -> zero (VReal dst')).
        { intros Hs; apply Hzb; unfold ix, sx; simpl; rewrite Hs.
          unfold svr, fold_varied in Hs; apply orb_false_iff in Hs as [_ Hs]; exact Hs. }
        destruct svr eqn:Hsvr.
        + exists (store_set s4 (keyv (DotOf n)) (VReal (dsnd dst'))); split.
          * unfold bodyst; rewrite run_app, Hrun3.
            rewrite run_assign_var with (v := VReal (dfst dst')) by exact Hvb.
            rewrite run_assign_var with (v := VReal (dsnd dst')); [reflexivity |].
            unfold s4; rewrite xev_set_other; [exact Hdb | exact Hav].
          * split; [apply frame_set; [exact Hfr4 | reflexivity | right; reflexivity] |].
            split; [rewrite store_get_set_other; [unfold s4; rewrite store_get_set_same; reflexivity
                                                 | apply not_eq_sym, keyv_dot_neq] |].
            split; [intros _; rewrite store_get_set_same; reflexivity |].
            split; [exact I | discriminate].
        + exists s4; split.
          * unfold bodyst; rewrite run_app, Hrun3.
            rewrite run_assign_var with (v := VReal (dfst dst')) by exact Hvb; reflexivity.
          * split; [exact Hfr4 |].
            split; [unfold s4; rewrite store_get_set_same; reflexivity |].
            split; [discriminate | split; [exact I | exact Hzst]].
      - unfold Inv, s1; split; [| split; [| split; [| split]]].
        + destruct svr; [apply frame_set; [apply frame_set; [apply frame_refl | reflexivity | auto]
                                          | reflexivity | auto]
                        | apply frame_set; [apply frame_refl | reflexivity | auto]].
        + destruct svr; [rewrite store_get_set_other, store_get_set_same; [reflexivity | apply not_eq_sym, keyv_dot_neq]
                        | rewrite store_get_set_same; reflexivity].
        + intros Hs; rewrite Hs; rewrite store_get_set_same; reflexivity.
        + exact I.
        + intros Hs; unfold svr, fold_varied in Hs; apply orb_false_iff in Hs as [Hs _].
          exact (atom_zero k initP _ (fun p E => proj1 (Hops initP ltac:(auto) p E)) Hs Hin). }
    destruct Hloop as [sf [Hex [Hfrf [Hnf [Hdf [Hhtf Hzf]]]]]].
    split; [lia | split; [exact Hhtf | split; [exact Hzf | split; [intros _; exact I |]]]].
    exists sf; split.
    + rewrite run_app, Hrun1, (run_for _ _ _ _ _ _ l h Hlo1 Hhi1), Hex; reflexivity.
    + split; [exact Hfrf | split; [exact Hnf |]].
      intros [Hs | Hs]; [exact (Hdf Hs) |].
      exfalso; apply Hs; destruct initP as [q | |]; simpl in Er |- *; try rewrite Er; reflexivity.
  - (* an array updated in place *)
    admit.
Admitted.
