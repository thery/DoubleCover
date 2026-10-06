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
