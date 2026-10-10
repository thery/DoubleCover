(* AdjointNestLoop.v — the reverse sweep of nested in-place folds: an outer
   in-place fold whose body ends with an inner in-place fold on its state
   (fbody).

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint
  Simplify Scoping AnfEquiv Correctness TangentCorrect TangentLoops TangentGood
  AdjointCorrect AdjointBranch AdjointFold AdjointFoldy AdjointNestSide
  AdjointNest AdjointNestRev.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Section NestLoop.
Variable cv : bool.

(* The init of the tail fold of a body is the variable a0. *)
Fixpoint tail_init (a0 : avar) (k : nat) (b : anf avar bare) : Prop :=
  match b with
  | ALet _ e c =>
      match e with
      | AFold _ _ _ init _ => init = AVar a0
      | _ => tail_init a0 (S k) (c (let_binder k e))
      end
  | ARet _ => True
  end.

(* The inner fold of a step of the outer loop is on its state sx, by its
   typing. *)
Lemma fbody_tail_init (bP : anf pv bare) : fbody bP ->
  forall L k wP ix sx bA bW te,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW ->
  (forall p, In p L -> (vid (pw p) < k)%nat) -> (vid (pw sx) < k)%nat ->
  (forall p, In p L -> vid (pw p) = vid (pw sx) -> p = sx) ->
  typecheck (option_map (amap pw) wP) (ArrayBody (AVar (pw ix)) (AVar (pw sx)))
    k bW = (te, Ok) ->
  tail_init (pa sx) k bA.
Proof.
elim: bP => [a e c IH | x] //= Hfb L k wP ix sx bA bW te HA HW Hk Hsk Hu.
case: bA HA => [aA eA cA | ?] //= [HeA HcA].
case: bW HW => [aW eW cW | ?] //= [HeW HcW] Htc.
case Hte: (typecheck_value _ _ _ _ eW) Htc => [te0 []] // Htc.
set x := PV (let_binder k eA) (VInfo k te0 None) dummy_tvar (VInt 0) 0.
have Hrec : (forall y, fbody (c y)) ->
    tail_init (pa sx) (S k) (cA (let_binder k eA)).
  move=> Hb.
  apply: (IH x (Hb x) (x :: L) (S k) wP ix sx _ _ te (HcA x _) (HcW x _))
    => //.
  - by move=> p [<- | Hp] //=; have := Hk p Hp; lia.
  - by lia.
  move=> p [<- | Hp] /= E; first by lia.
  exact: Hu.
clearbody x.
case: e Hfb HeA HeW Hte
  => // [f0 a0 | f0 a0 b0 | a0 i0 | fa lo hi [s | ? | ?] bi] //=
  Hfb HeA HeW Hte.
- by case: eA HeA Hrec => //= ? ? _ Hrec; exact: Hrec.
- by case: eA HeA Hrec => //= ? ? ? _ Hrec; exact: Hrec.
- by case: eA HeA Hrec => //= ? ? _ Hrec; exact: Hrec.
case: eA HeA Hrec => // fa' lo' hi' [sA | ? | ?] biA [_ [_ [HsA _]]] _ //.
case: eW HeW Hte => // fw lw hw [sW | ? | ?] biW [_ [_ [HsW _]]] Hte //.
move/in_gA: HsA => [HsL EsA]; move/in_gW: HsW => [_ EsW]; subst sA sW.
rewrite /= in Hte.
have Evid : (vid (pw s) =? vid (pw sx))%nat = true.
  move: Hte; case: (_ && _) => //; case: (ty_eqb _ Real) => //.
  case: (vty (pw s)) => // n; case: (WellFormed.is_tail cW k) => //.
  by case: (vid (pw s) =? vid (pw sx))%nat.
have Ess : s = sx by apply: Hu => //; exact/Nat.eqb_eq.
by rewrite Ess.
Qed.

(* The tail tape of a step of the outer loop: the tape of the storage holds,
   on top, what the inner fold of the step pushed, and the storage its
   value, when that fold is live. *)
Lemma tail_tape_fbody (bP : anf pv bare) : fbody bP ->
  forall L k bA bD s n sx lv R v0,
  anf_eq (gA L) bP bA -> anf_eq (gD L) bP bD -> In sx L ->
  (forall p, In p L -> pa p = pa sx -> p = sx) ->
  (forall p, In p L -> (aid (pa p) < k)%nat) ->
  is_array (vty (pw sx)) -> tail_init (pa sx) k bA ->
  tail_fold_live cv k bA = Some lv ->
  aeval (duals reals) bD = Some v0 ->
  (lv = true -> store_get s (keyv n) = Some (primal v0)) ->
  (lv = true -> store_get s (keyv (TapeOf n)) =
     Some (VTape (rev (body_pushes bD (pd sx)) ++ R))) ->
  tail_tape cv k L bP bA bD s n.
Proof.
elim: bP => [a e c IH | x] //= Hfb L k [aA eA cA | ?] [aD eD cD | ?] s n sx
  lv R v0 // [HeA HcA] [HeD HcD] HsL Hu Hk Hsa Hti Htl Hev Hn Ht.
rewrite /= in Hev.
have [ve Ev] : exists ve, aeval_value (duals reals) eD = Some ve.
  by move: Hev; case: (aeval_value _ eD) => [ve |] // _; exists ve.
rewrite Ev /= in Hev.
set xv := PV (AV 0 false) (anon 0) dummy_tvar ve 0.
(* a scalar let: the tape is the one of the rest of the step *)
have Hop : (forall y, fbody (c y)) ->
    tail_init (pa sx) (S k) (cA (let_binder k eA)) ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) = Some lv ->
    tail_tape cv k L (ALet a e c) (ALet aA eA cA) (ALet aD eD cD) s n.
  move=> Hb Hti' Htl'.
  have Hnr : forall r, cD ve <> ARet r.
    by move=> r Er; move: (HcD xv ve) (Hb xv); rewrite Er; case: (c xv).
  split.
    by move=> Hpt; exfalso; have := Hb sx; rewrite Hpt.
  move=> y Ey Eyv.
  have Ev' : ve = pd y by move: Ev; rewrite Eyv => -[].
  apply: (IH y (Hb y) (y :: L) (S k) _ _ s n sx lv R v0) => //.
  - by rewrite /= Ey; exact: HcA.
  - exact: HcD.
  - by right.
  - move=> p [<- | Hp] E; last exact: Hu.
    by have := Hk sx HsL; rewrite -E Ey /=; lia.
  - by move=> p [<- | Hp]; [rewrite Ey /=; lia | have := Hk p Hp; lia].
  - by rewrite -Ev'.
  by move=> El; rewrite (Ht El) (body_pushes_let _ _ _ _ _ Ev Hnr) Ev'.
case: e Hfb HeA HeD Hop
  => // [f0 a0 | f0 a0 b0 | a0 i0 | fa lo hi [s0 | ? | ?] bi] //=
  Hfb HeA HeD Hop.
- by case: eA HeA Hti Htl Hop => // ? ? _ Hti Htl Hop; exact: (Hop Hfb Hti Htl).
- by case: eA HeA Hti Htl Hop => // ? ? ? _ Hti Htl Hop;
    exact: (Hop Hfb Hti Htl).
- by case: eA HeA Hti Htl Hop => // ? ? _ Hti Htl Hop; exact: (Hop Hfb Hti Htl).
(* the inner fold, on the state sx *)
case: Hfb => [_ [_ Hret]]; clear Hop.
have [r EcA] : exists r, cA (let_binder k eA) = ARet r.
  have := HcA xv (let_binder k eA); rewrite Hret.
  by case: (cA _) => // r _; exists r.
have EcD : cD ve = ARet (AVar ve).
  have := HcD (PV (let_binder k eA) (anon 0) dummy_tvar ve 0) ve.
  rewrite Hret; case: (cD ve) => // -[d | ? | ?] //= [[<-] // | /in_gD [_ ->]].
  by [].
rewrite EcD /= in Hev; case: Hev => Ev0; subst v0.
case: eA HeA Hti Htl EcA => // fa' loA hiA iA biA [_ [_ [HiA _]]] Hti Htl EcA.
rewrite /= in Hti; subst iA.
move/in_gA: HiA => [Hs0L Es0]; have Es0x := Hu _ Hs0L (esym Es0); subst s0.
case: eD HeD Ev EcD Ht => // fd loD hiD iD biD [HloD [HhiD [HiD _]]] Ev EcD Ht.
case: iD HiD Ev Ht => // dd /in_gD [_ Edd] Ev Ht; subst dd.
(* its liveness is the one of the outer loop *)
have Efl : fold_live cv k (AVar (pa sx)) biA = lv.
  move: Htl; rewrite /= EcA /fold_live /fold_binders /=.
  by case: (tail_fold_live _ _ _) => [l0 |] [].
split; last by move=> y _ _; rewrite Hret.
move=> _ eW HeW.
case: eW HeW => // fw loW hiW [w | ? | ?] biW [_ [_ [HiW _]]] //.
move/in_gW: HiW => [_ Ew]; subst w.
rewrite /fold_tape.
move: Ev; rewrite /=.
case Hlo: (aeval_atom _ loD) => [[| l | | |] |] //.
case Hhi: (aeval_atom _ hiD) => [[| h | | |] |] // Ev.
move=> tr Htr; split.
  by move: Hsa; rewrite /=; case: (vty (pw sx)).
move=> _; rewrite Efl => El.
split.
  exists R; rewrite (Ht El) /= Hlo Hhi Ev EcD Htr fold_pushes_fix.
  by [].
by move=> ve'; rewrite Ev => -[<-]; exact: Hn.
Qed.

(* The reverse sweep of the outer fold of a nest: its state is not
   recorded, each step gives the state back through its inner fold. *)
Lemma arev_fold_nest a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, fbody (bP x y)) -> asim_rev cv (AFold a loP hiP initP bP).
Proof.
move=> [q [-> Hqa]] Hab L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT
  HD Hs Hbar Htc Htail [j [Ej Hj]] Hst Hev Hvr.
case: eA HA Hvr => // ann loA hiA iA bA [HloA [HhiA [HiA HbA]]] Hvr.
case: eW HW Htc Hs => // ann0 loW hiW iW bW [HloW [HhiW [HiW HbW]]] Htc Hs.
case: eT HT => // ann1 loT hiT iT bT [HloT [HhiT [HiT HbT]]].
case: eD HD Hev => // ann2 loD hiD iD bD [HloD [HhiD [HiD HbD]]] Hev.
move/atom_graph: HloA => [ElA HloL]; move/atom_graph: HhiA => [EhA HhiL].
move/atom_graph: HloW => [ElW _]; move/atom_graph: HhiW => [EhW _].
move/atom_graph: HloT => [ElT _]; move/atom_graph: HhiT => [EhT _].
move/atom_graph: HloD => [ElD _]; move/atom_graph: HhiD => [EhD _].
subst loA hiA loW hiW loT hiT loD hiD.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite /= in Htc.
case: iA HiA Hvr => // ia /in_gA [HqL Eia] Hvr; subst ia.
case: iW HiW Htc Hs => // iw /in_gW [_ Eiw] Htc Hs; subst iw.
case: iT HiT => // it /in_gT [_ Eit]; subst it.
case: iD HiD Hev => // id /in_gD [_ Eid] Hev; subst id.
case Eb: (ty_eqb (of_atom (amap pw loP)) Integer &&
  ty_eqb (of_atom (amap pw hiP)) Integer) Htc => // Htc.
rewrite /= in Htc.
case Eqz: (vty (pw q)) Hqa Htc => [| | | z] // _ Htc.
rewrite /= in Htc.
(* the array is the one the place updates in place *)
have [Hown Etail] : owner wP pp = Some q /\ tail = true.
  case: pp Hs Htc => [| | | ix0 sx0] Hs Htc; case Et: tail Htc => //= Htc.
  - case Ew: wP Hs Htc => [y |] //= Hs Htc.
    case E: (match amap pw y with
      | AVar y0 => (vid (pw q) =? vid y0)%nat | _ => false end) Htc => // Htc.
    have [->] := unique_written_s _ _ _ _ _ _ _ _ _ Hs HqL erefl E.
    by rewrite /= Eqz.
  case E: (vid (pw q) =? vid (pw sx0))%nat Htc => // Htc.
  have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hs.
  by rewrite (same_vid_s _ _ _ _ _ _ _ _ _ Hs HqL Hsx E).
subst tail.
have Hin_pl : in_place_init (option_map (amap pw) wP) (wplace pp) true
    (AVar (pw q)) = true.
  by case: (in_place_init _ _ _ _) Htc.
rewrite Hin_pl in Htc.
case Hocc: (occurs_anf (vid (pw q)) (S (S k)) (bW (anon k) (anon (S k)))) Htc
  => Htc.
  by case: (varg (pw q)) Htc => [[? ?] |].
case HtB: (typecheck (option_map (amap pw) wP)
    (ArrayBody (AVar (VInfo k Integer None))
       (AVar (VInfo (S k) (Array z) None)))
    (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))) Htc
  => [tb [| mm]] // Htc.
case Etb: (ty_eqb tb (Array z)) Htc => // Htc.
case Hrai: (reads_around_inner_loop (S k) (S (S k))
  (bW (anon k) (anon (S k)))) Htc => // Htc.
move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => <-.
subst n; rewrite /= Eqz in Hst; set n := DBound (j, j) in Hst Hev Hvr *.
cbn [annotate_value_t rebuild_value fold_binders].
rewrite (fun w sv live0 recs lo hi init b nn z0 =>
  (eq_refl : rev_value W w vo (AFold (FoldAnn sv live0 recs) lo hi init b)
     (Array z0) nn =
   Fresh "i" (fun i =>
     let '(ix, sx) := open_fold sv (Array z0) nn (DBound i) false in
     sbind (adj W w vo Replay (b ix sx) (DReal "0")) (fun sw =>
       Done (rev_loop W (DBound i) (spell lo) (spell hi)
               (if live0 then [DPop (TapeOf nn)
                  (DAt (DVar nn) (tail_index W (b ix sx)))] else [])
               [] sw))))).
cbn [open_pairs open_fold].
rewrite open_pairs_sbind.
lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
  case Hob: (@open_pairs A t (S c)) => [[fb rb] c2] end.
have Hc2 : (S c <= c2)%nat.
  by lazymatch type of Hob with @open_pairs _ ?t _ = _ =>
    have := open_pairs_mono t (S c); rewrite Hob end.
cbn [open_pairs]; split; first by lia.
move=> s2 O Hrd Hr Hns Htp Hft Hrec.
(* the fold updates in place the written argument q, at the top, or the state
   q of an enclosing in-place loop, ending its body *)
have Hpl : pp = PTop \/ exists ix0 sx0, pp = PArray ix0 sx0.
  case Epp: pp Hown => [| | | ix0 sx0] //= _; first by left.
  by right; exists ix0, sx0.
have {}Hft := Hft Hpl.
have Hlivq :
    live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) q.
  by rewrite /live_value /= Nat.eqb_refl !orb_true_r.
have Hqa' : is_array (vty (pw q)) by rewrite Eqz.
have Hvq : avaried (pa q) = true.
  case: Hpl => [Epp | [ix0 [sx0 Epp]]]; move: Hown Hs; rewrite Epp.
    case Ew: wP => [[y | |] |] //= + Hs.
    case: (vty (pw y)) => // [z0] [Eyq]; subst y.
    exact: (proj2 (s_top _ _ _ _ _ _ _ Hs q erefl erefl Hqa') Hlivq).
  move=> /= [<-] Hs.
  by have [_ [_ [_ [_ [-> _]]]]] := s_place _ _ _ _ _ _ _ Hs.
have HqO : In (tangent (pd q), n) O.
  by rewrite Hst; exact: (r_owner _ _ _ _ _ _ _ Hr q Hown).
have HnO : In n (map snd O) by apply/in_map_iff; exists (tangent (pd q), n).
have Eput : oput O n (tangent ve) = oset O n (tangent ve).
  by rewrite /oput; case: in_dec.
rewrite Eput.
have {}Hrec : not_in_loop pp ->
    records cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) =
      false ->
    store_get s2 (keyv n) = Some (primal (pd q)).
  by move=> Hnl Er; apply: (Hrec Hnl _ q Hown Hvq Er); rewrite /= Eqz.
(* the states of the fold *)
rewrite /= in Hev.
case Hlo: (aeval_atom (duals reals) (amap pd loP)) Hev
  => [[| l | | |] |] // Hev.
case Hhi: (aeval_atom (duals reals) (amap pd hiP)) Hev
  => [[| h | | |] |] // Hev.
have [tr Htr] := fold_trace_exists _ _ _ _ _ Hev.
set dflt := VReal (Dual 0 0).
have [Hlen [Hst0 Hstep]] := fold_trace_step _ _ _ _ _ _ dflt Hev Htr.
set N := count l h.
set st := fun jn => nth jn (tr ++ [ve]) dflt.
(* the outer state is not recorded; the tape holds the pushes of the inner
   folds, when they are live *)
have Hsd := fbody_state_dead cv L k bP bA bW (AVar (pa q)) z wP Hab HbA HbW HL
  (s_unique _ _ _ _ _ _ _ Hs) HtB Hrai.
rewrite Hsd.
set live := fold_live cv k (AVar (pa q)) bA.
have Hrecs : records cv k
    (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) = live.
  exact: (records_fold_nest cv L k ann _ _ bP bA bW _ z wP Hab HbA HbW HL
    (s_unique _ _ _ _ _ _ _ Hs) HtB Hrai).
have [rest [Htape0 Hn_live]] : exists rest,
    (live = true -> store_get s2 (keyv (TapeOf n)) =
       Some (VTape (rev (fold_pushes bD l tr) ++ rest))) /\
    (live = true -> store_get s2 (keyv n) = Some (primal ve)).
  move: Hft; rewrite /fold_tape Hlo Hhi.
  change (aeval_atom (duals reals) (amap pd (AVar q))) with (Some (pd q)).
  move=> /(_ tr Htr) [_ Ha].
  have Har : is_array (of_atom (AVar (pw q))) by rewrite /= Eqz.
  case El: live; last by exists [].
  have [[rest Ht] Hv] := Ha Har El.
  by exists rest; split=> _; [exact: Ht | exact: Hv ve Hev].
have Hn_dead : not_in_loop pp -> live = false ->
    store_get s2 (keyv n) = Some (primal (pd q)).
  by move=> Hnl Hl; apply: Hrec Hnl _; rewrite Hrecs.
(* the states of the fold are arrays of the type of the state *)
set vr := fold_varied k (AVar (pa q)) bA.
have Hvr' : vr = true by rewrite /vr /fold_varied /= Hvq.
have [Eidq [Hkq [Hstq [Htyq [Htvq [Htdq [Htidq [Hvaq [Hhtq Hzq]]]]]]]]] :=
  static_in _ _ _ HL HqL.
have Hstates : forall jn, (jn <= N)%nat -> has_type (Array z) (st jn).
  elim=> [| jn IH] Hjn; first by rewrite /st Hst0 -Eqz.
  have Hjn' : (jn <= N)%nat by lia.
  have Hlt : (jn < count l h)%nat by rewrite -/N; lia.
  have Hs1 := Hstep jn Hlt.
  have Ej : st jn = nth jn tr dflt by rewrite /st app_nth1 // Hlen.
  set ix := PV (fresh k) (VInfo k Integer None)
    (open_index (DBound (0%nat, 0%nat))) (VInt (l + Z.of_nat jn)) 0.
  set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None)
    (TVar (DBound (0%nat, 0%nat)) (Array z) None vr vr vr false None)
              (nth jn tr dflt) 0.
  have Hix : static_ok (S (S k)) ix.
    by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    repeat split; rewrite /=; auto; try lia; try discriminate;
      last by rewrite Hvr'.
    by rewrite -Ej; apply: IH.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    constructor=> //; constructor=> //; apply: Forall_impl HL => p Hp.
    by apply: (static_mono k) => //; lia.
  have HtB' : typecheck (option_map (amap pw) wP) (wplace (PArray ix sx))
      (S (S k)) (bW (pw ix) (pw sx)) = (Array z, Ok)
    by exact: HtB.
  have [Hht _] := fbody_act _ (Hab ix sx) (sx :: ix :: L) (S (S k)) wP
    (PArray ix sx) (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx))
    (bD (pd ix) (pd sx)) (Array z) (st (S jn))
    (HbA ix _ sx _) (HbW ix _ sx _) (HbD ix _ sx _) HL' HtB' Hs1.
  exact: Hht.
(* the loop: P jn s, the store before the step jn of the reverse loop *)
set i := DBound (c, c).
pose body := (fb ++ rb)%list.
set P := fun (jn : nat) (s : store R) =>
  (forall v, below c v -> consistent v -> is_primal v -> v <> n ->
     store_get s (keyv v) = store_get s2 (keyv v)) /\
  tkeep c (Some n) s2 s /\
  rev_frame_x c (inplace wP pp) n (oset O n (tangent ve)) s2 s /\
  (live = true -> store_get s (keyv (TapeOf n)) =
     Some (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest))) /\
  store_get s (keyv n) =
    (if live then Some (primal (st jn)) else store_get s2 (keyv n)) /\
  (forall t m, In (t, m) (oset O n (tangent (st jn))) -> shaped t (barv s m)) /\
  pairing (oset O n (tangent (st jn))) s = pairing (oset O n (tangent ve)) s2.
(* the step of the outer loop does not read its state *)
have Htl_body : tail_fold_live cv (S (S k)) (bA (AV k false) (AV (S k) vr)) =
    Some live.
  set ox := PV (AV k false) (VInfo k Integer None) dummy_tvar (VInt 0) 0.
  set oy := PV (AV (S k) vr) (VInfo (S k) (Array z) None) dummy_tvar
    (VInt 0) 0.
  rewrite (fbody_tail_live cv _ (Hab ox oy) (oy :: ox :: L) _ _
    (HbA ox (pa ox) oy (pa oy))).
  by rewrite /live (fold_live_nest cv L k bP _ bA Hab HbA).
have [Hts_body _] := tail_state_nest cv L k bP bA bW (AVar (pa q)) z wP Hab
  HbA HbW HL Hvr' HtB.
have Hstep' : forall jn s, (jn < N)%nat -> P (S jn) s ->
    exists s', run body (store_set s (KVar (out_dvar nat i))
      (VInt (l + Z.of_nat jn))) = Some s' /\ P jn s'.
  move=> jn s Hjn [K0 [T0 [F0 [Tp0 [N0 [Sh0 Pr0]]]]]].
  set zz := (l + Z.of_nat jn)%Z.
  set s'' := store_set s (keyv i) (VInt zz).
  change (store_set s (KVar (out_dvar nat i)) (VInt zz)) with s''.
  have Ej : st jn = nth jn tr dflt by rewrite /st app_nth1 // Hlen.
  have Hs1 := Hstep jn Hjn.
  have Ht0 : has_type (Array z) (nth jn tr dflt).
    by rewrite -Ej; apply: Hstates; lia.
  have Ht1 : has_type (Array z) (st (S jn)) by apply: Hstates; lia.
  (* the index and the state of the step *)
  set ix := PV (fresh k) (VInfo k Integer None) (open_index i) (VInt zz) c.
  set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None)
    (TVar n (Array z) None vr vr vr false None) (nth jn tr dflt) j.
  have Hix : static_ok (S (S k)) ix.
    by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    by repeat split; rewrite /=; auto; try lia; try discriminate;
      last by rewrite Hvr'.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    constructor=> //; constructor=> //; apply: Forall_impl HL => p Hp.
    by apply: (static_mono k) => //; lia.
  have Hk' : forall p, In p (sx :: ix :: L) -> (vid (pw p) < S (S k))%nat.
    move=> p [<- | [<- | Hp]] /=; try lia.
    by have [_ [Hkp _]] := static_in _ _ _ HL Hp; lia.
  have Hu' : ids_unique (sx :: ix :: L).
    move=> p p' [<- | [<- | Hp]] [<- | [<- | Hp']] E //=; move: E => /=;
      try lia;
      try (case: (static_in _ _ _ HL Hp') => _ [Hk1 _] /=; lia);
      try (case: (static_in _ _ _ HL Hp) => _ [Hk1 _] /=; lia).
    exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hp').
  have HtB' : typecheck (option_map (amap pw) wP) (wplace (PArray ix sx))
      (S (S k)) (bW (pw ix) (pw sx)) = (Array z, Ok) by exact: HtB.
  have Hjt : (jn < length tr)%nat by rewrite Hlen.
  have Hfl : length (firstn jn tr) = jn by apply: firstn_length_le; lia.
  have Epush : fold_pushes bD l (firstn (S jn) tr) =
      fold_pushes bD l (firstn jn tr) ++
        body_pushes (bD (VInt zz) (nth jn tr dflt)) (nth jn tr dflt).
    by rewrite (firstn_S_nth dflt _ _ Hjt) fold_pushes_snoc Hfl -/zz.
  have Kti : keyv (TapeOf n) <> keyv i by rewrite /keyv.
  have Ktn : keyv (TapeOf n) <> keyv n by rewrite /keyv.
  have Kin : keyv i <> keyv n by rewrite /keyv /=; case=> E; lia.
  (* the replay of the body keeps the keys, its transpose writes adjoints *)
  have Hrep : forall s0 s1, run fb s0 = Some s1 -> forall v, below (S c) v ->
      consistent v -> store_get s1 (keyv v) = store_get s0 (keyv v).
    move: (adj_replay_fbody cv _ (Hab ix sx) (sx :: ix :: L) (S (S k))
             (option_map (amap pt) wP) vo (bA (pa ix) (pa sx))
             (bT (pt ix) (pt sx)) (DReal "0") (S c) (HbA ix _ sx _)
             (HbT ix _ sx _)).
    lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
      have E : @open_pairs A t (S c) = ((fb, rb), c2) by exact: Hob end.
    by rewrite E.
  (* the context of the body *)
  have Hlive_b : forall p, In p L ->
      live_anf (S (S k)) (bW (pw ix) (pw sx)) p ->
      live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p
      /\ pn p <> pn q.
    move=> p Hp Hl.
    have Ec := live_cont2 L k bP bW ix sx (pw ix) (pw sx) (vid (pw p)) HbW HL
      erefl erefl erefl erefl.
    have Hl' : live_value k
        (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p.
      by move: Hl; rewrite /live_anf /live_value /= Ec => ->;
        rewrite !orb_true_r.
    split=> // E.
    case: (s_owner _ _ _ _ _ _ _ Hs q p Hown Hp E) => [Epq | //].
    by move: Hl; rewrite /live_anf Ec Epq Hocc.
  have Hjq : pn q = j by move: Hst; rewrite /n /stored => -[].
  set liveb := live_anf (S (S k)) (bW (pw ix) (pw sx)).
  have Hsb : sctx (sx :: ix :: L) (S (S k)) (S c) wP (PArray ix sx) liveb
      (Array z).
    constructor=> //.
    - move=> p [<- | [<- | Hp]] /=; try lia.
      by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
    - move=> a0 E; have [y [-> [Hy Hv]]] := s_written _ _ _ _ _ _ _ Hs _ E.
      by exists y; split=> //; split=> //; right; right.
    - by rewrite /= Hvr'; repeat split; auto.
    - move=> o p [<-] [<- | [<- | Hp]] Ep; [by left | by move: Ep => /=; lia |].
      by right=> Hl; case: (Hlive_b p Hp Hl) => _ Hpn; apply: Hpn; rewrite Hjq.
    - move=> p o [<- | [<- | Hp]] Lp Ha Hgp [<-] //.
      case: (Hlive_b p Hp Lp) => Hl' _.
      by rewrite /= -Hjq; exact: (s_arrays _ _ _ _ _ _ _ Hs p q Hp Hl' Ha Hgp
        Hown).
  (* the store at the start of the step *)
  have Ci : consistent i by [].
  have Cn : consistent n by [].
  have Ctn : consistent (TapeOf n) by [].
  have Kni : keyv n <> keyv i by apply: not_eq_sym.
  have Kvi : forall v, below c v -> consistent v -> keyv v <> keyv i.
    by move=> v Hb Cv K; move: Hb; rewrite (keyv_inj _ _ Cv Ci K) /=; lia.
  have Hsp_v : forall v, below c v -> consistent v ->
      store_get s'' (keyv v) = store_get s (keyv v).
    move=> v Hb Cv.
    have Kiv : keyv i <> keyv v by apply: not_eq_sym; apply: Kvi.
    by rewrite /s'' store_get_set_other.
  have Bn0 : below c n by rewrite /=; lia.
  have Btn0 : below c (TapeOf n) by rewrite /=; lia.
  have Hsp_n : store_get s'' (keyv n) =
      (if live then Some (primal (st (S jn))) else store_get s2 (keyv n)).
    by rewrite (Hsp_v _ Bn0 Cn) N0.
  have Hsp_t : live = true -> store_get s'' (keyv (TapeOf n)) =
      Some (VTape (rev (fold_pushes bD l (firstn (S jn) tr)) ++ rest)).
    by move=> El; rewrite (Hsp_v _ Btn0 Ctn) (Tp0 El).
  have Hsp_i : store_get s'' (keyv i) = Some (VInt zz).
    by rewrite /s'' store_get_set_same.
  have Tsp : tkeep c (Some n) s s'' by apply: tkeep_set.
  (* the variables the replay reads hold their values; not the state *)
  set tbb := tbr cv Replay (S (S k)) (bA (pa ix) (pa sx)).
  have Htb_sx : ~ tbb sx.
    have Hsl : tbb sx -> state_live cv k (AVar (pa q)) bA = true by [].
    by move=> Ht; move: (Hsl Ht); rewrite Hsd.
  have Hst_p : forall p, In p L -> stored p = DBound (pn p, pn p) by [].
  have Hstore_L : forall p, In p L -> tbb p ->
      store_get s'' (keyv (stored p)) = Some (primal (pd p)).
    move=> p Hp Htb.
    have Hl := tbr_occurs cv (sx :: ix :: L) (S (S k)) _ _ _ Replay p
      (HbA ix _ sx _) (HbW ix _ sx _) HL' (or_intror (or_intror Hp))
      (or_introl Htb).
    case: (Hlive_b p Hp Hl) => Hlv Hpn.
    have [Eid [Hkp _]] := static_in _ _ _ HL Hp.
    have Hvr2 : vreads cv k
        (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
      move: Htb; rewrite /tbb /tbr /vreads; cbn [value_needs fold_binders].
      case: (needs cv Replay (S (S k)) _) => [u0 l0] /= Hm.
      rewrite atom_member_union !atom_member_remove ?Hm ?orb_true_r //;
        by cbn [same_term aid]; rewrite Eid; apply Nat.eqb_neq; lia.
    have Hsn : stored p <> n.
      by rewrite Hst_p // /n => -[E _]; apply: Hpn; rewrite Hjq.
    have Hbp : below c (stored p).
      by rewrite Hst_p //; exact: (s_num _ _ _ _ _ _ _ Hs _ Hp).
    have Cp : consistent (stored p) by rewrite Hst_p.
    have Pp : is_primal (stored p) by rewrite Hst_p.
    rewrite (Hsp_v _ Hbp Cp) (K0 _ Hbp Cp Pp Hsn).
    apply: (Hrd p Hp Hvr2 Hlv); right.
    rewrite /inplace Hown => -[Eqp]; exfalso; apply: Hsn.
    by rewrite Hst /stored Eqp.
  have Hctx : actx (sx :: ix :: L) (S (S k)) (S c) s'' wP (PArray ix sx) liveb
      tbb (Array z).
    constructor=> //.
    - by move=> p [<- | [<- | Hp]] //=; exact: Hbar.
    - move=> p [<- | [<- | Hp]] Htb.
      + by case: Htb_sx.
      + by rewrite Hsp_i.
      + exact: Hstore_L.
    - move=> p [<- | [<- | Hp]] Hrc //.
      have [lt Hlt] := Htp p Hp Hrc.
      have [l' Hl'] := proj1 T0 _ _ Hlt.
      exact: (proj1 Tsp _ _ Hl').
    - by move=> o [<-] [// | Htb]; case: Htb_sx.
  (* the replay, then the transpose of the body *)
  have Hra : real_or_array (Array z) by [].
  have NF : forall A : Prop, Replay = Forward -> A by [].
  have Hpp : Replay = Replay -> PArray ix sx <> PTop by [].
  move: (fbody_asim cv _ (Hab ix sx) (sx :: ix :: L) (S (S k)) (S c) s'' wP
           (PArray ix sx) Replay _ _ _ _ (Array z) (st (S jn)) (DReal "0") vo
           (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _) Hctx
           Hra HtB' Hs1 (NF _) (NF _) (NF _) Hpp (NF _)).
  lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
    have E : @open_pairs A t (S c) = ((fb, rb), c2) by exact: Hob end.
  rewrite E => -[_ [Hht [s1 [R1 [F1 [T1 [_ Hrv]]]]]]].
  have Ein : inplace wP (PArray ix sx) = Some n by [].
  have Hs1v : forall v, below (S c) v -> consistent v ->
      store_get s1 (keyv v) = store_get s'' (keyv v).
    by move=> v; apply: Hrep.
  have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
  have On : forall t t', In (t, n) (oset O n t') -> t = t'.
    move=> t t' /in_map_iff [[a0 b0] [Eab _]]; move: Eab => /=.
    case: ifP => [_ [-> _] // | Hne [_ Ebn]].
    by move: Hne; rewrite Ebn /= Nat.eqb_refl.
  (* the owners of the transpose: the state holds the tangent of st jn *)
  set O' := oset O n (tangent (st jn)).
  have HmO : forall t m, In (t, m) O' -> exists t0, In (t0, m) O.
    move=> t m Hin.
    have : In m (map snd O).
      rewrite -(oset_snd O n (tangent (st jn))); apply/in_map_iff.
      by exists (t, m).
    by move=> /in_map_iff [[t0 m0] [/= -> Ho1]]; exists t0.
  have HbO : forall t m, In (t, m) O' -> exists j', m = DBound (j', j') /\
      (j' < c)%nat.
    by move=> t m /HmO [t0 Ho1]; exact: (r_below _ _ _ _ _ _ _ Hr t0 m Ho1).
  have Hsp_bar : forall v, is_bar v ->
      store_get s'' (keyv v) = store_get s (keyv v).
    move=> v Bv.
    have K1 : forall x, ~ is_bar x -> keyv x <> keyv v.
      by move=> y0 Hy0; apply: not_eq_sym; apply: keyv_bar_other.
    have Ki1 := K1 i id.
    by rewrite /s'' store_get_set_other.
  have Hbar1 : forall t m, In (t, m) O' -> barv s1 m = barv s m.
    move=> t m Hin; have [j' [Em Hj']] := HbO t m Hin.
    have Bb : below (S c) (BarOf m) by rewrite Em /=; lia.
    have Cb : consistent (BarOf m) by rewrite Em.
    by rewrite /barv (Hs1v _ Bb Cb) Hsp_bar.
  have Htj : has_type (Array z) (st jn) by apply: Hstates; lia.
  have Hshape1 : forall t m, In (t, m) O' -> shaped t (barv s1 m).
    move=> t m Hin; rewrite (Hbar1 _ _ Hin).
    have [j' [Em _]] := HbO t m Hin.
    have Cm : consistent m by rewrite Em.
    case: (dvar_eq_dec_c m n) => [Emn | Hne].
      move: Hin; rewrite Emn => Hin; rewrite (On _ _ Hin).
      have Hin' := oset_in _ _ (tangent (st (S jn))) Hok Cn HnO.
      exact: (shaped_array_same z (st (S jn)) (st jn) _ Ht1 Htj
        (Sh0 _ _ Hin')).
    case: (oset_mem _ _ _ _ _ Hin) => [Ho1 | [Ee _]].
      by apply: Sh0; apply: oset_other.
    by case: Hne; move/(dvar_eq_consistent n m Cn Cm): Ee.
  set use := useful cv Replay (S (S k)) (bA (pa ix) (pa sx)).
  have Huse_L : forall p, In p L -> use p ->
      vflows cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p
      /\ stored p <> n.
    move=> p Hp Hu.
    have Hl := tbr_occurs cv (sx :: ix :: L) (S (S k)) _ _ _ Replay p
      (HbA ix _ sx _) (HbW ix _ sx _) HL' (or_intror (or_intror Hp))
      (or_intror Hu).
    case: (Hlive_b p Hp Hl) => _ Hpn.
    have [Eid [Hkp _]] := static_in _ _ _ HL Hp.
    split; last by rewrite Hst_p // /n => -[E0 _]; apply: Hpn; rewrite Hjq.
    move: Hu; rewrite /use /useful /vflows; cbn [value_needs fold_binders].
    case: (needs cv Replay (S (S k)) _) => [u0 l0] /= Hm.
    rewrite atom_member_union !atom_member_remove ?Hm ?orb_true_r //;
      by cbn [same_term aid]; rewrite Eid; apply Nat.eqb_neq; lia.
  have Hr1 : rctx (sx :: ix :: L) (S c) wP (PArray ix sx) O' use s1.
    constructor.
    - by rewrite /O' oset_snd; exact: (r_nodup _ _ _ _ _ _ _ Hr).
    - exact: Hshape1.
    - move=> t m Hin; have [j' [-> Hj']] := HbO t m Hin.
      by exists j'; split=> //; lia.
    - move=> p [<- | [<- | Hp]] Hu Hva.
      + by rewrite /O' Ej; apply: oset_in.
      + by move: Hva.
      + have [Hvf Hsn] := Huse_L p Hp Hu.
        by apply: oset_other => //; exact: (r_useful _ _ _ _ _ _ _ Hr p Hp
          Hvf Hva).
    - move=> p t [<- | [<- | Hp]] Hu Hin.
      + by rewrite (On _ _ Hin) Ej.
      + by have [j' [[Ec _] Hj']] := HbO _ _ Hin; lia.
      + have [Hvf Hsn] := Huse_L p Hp Hu.
        case: (oset_mem _ _ _ _ _ Hin) => [Ho1 | [Ee _]].
          exact: (r_value _ _ _ _ _ _ _ Hr p t Hp Hvf Ho1).
        have Cp : consistent (stored p) by rewrite Hst_p.
        by case: Hsn; move/(dvar_eq_consistent n _ Cn Cp): Ee.
    - by move=> o [<-]; rewrite /O' Ej; apply: oset_in.
    - by move=> p ny r [<- | [<- | Hp]] //; exact: (r_args _ _ _ _ _ _ _ Hr p
        ny r Hp).
    - exact: (r_written _ _ _ _ _ _ _ Hr).
  have Hseed : seed_ok (S c) (Array z) (DReal "0") s1 by split=> // x0 [].
  have Htp1 : tapes_ok (sx :: ix :: L) s1.
    move=> p [<- | [<- | Hp]] Hrc //.
    have [lt Hlt] := Htp p Hp Hrc.
    have [l' Hl'] := proj1 T0 _ _ Hlt.
    have [l'' Hl''] := proj1 Tsp _ _ Hl'.
    exact: (proj1 T1 _ _ Hl'').
  have Bn : below (S c) n by rewrite /=; lia.
  have Btn : below (S c) (TapeOf n) by rewrite /=; lia.
  have Hs1_n : store_get s1 (keyv n) =
      (if live then Some (primal (st (S jn))) else store_get s2 (keyv n)).
    by rewrite (Hs1v _ Bn Cn) Hsp_n.
  have Hs1_t : live = true -> store_get s1 (keyv (TapeOf n)) =
      Some (VTape (rev (body_pushes (bD (VInt zz) (nth jn tr dflt))
        (nth jn tr dflt)) ++ (rev (fold_pushes bD l (firstn jn tr)) ++ rest))).
    move=> El; rewrite (Hs1v _ Btn Ctn) (Hsp_t El) Epush rev_app_distr.
    by rewrite app_assoc.
  (* the tail tape of the step: the pushes of its inner fold *)
  have Htt1 : forall ix0 sx0 n0, PArray ix sx = PArray ix0 sx0 ->
      Some n = Some n0 -> tail_tape cv (S (S k)) (sx :: ix :: L) (bP ix sx)
        (bA (pa ix) (pa sx)) (bD (pd ix) (pd sx)) s1 n0.
    move=> ix0 sx0 n0 _ [<-].
    have Husx : forall p, In p (sx :: ix :: L) -> vid (pw p) = vid (pw sx) ->
        p = sx.
      move=> p [<- | [<- | Hp]] //= Evd; first by lia.
      by have [_ [Hkp _]] := static_in _ _ _ HL Hp; lia.
    have Hti := fbody_tail_init _ (Hab ix sx) (sx :: ix :: L) (S (S k)) wP ix sx
      _ _ _ (HbA ix _ sx _) (HbW ix _ sx _) Hk' (Hk' sx (or_introl erefl))
      Husx HtB'.
    apply: (tail_tape_fbody _ (Hab ix sx) (sx :: ix :: L) (S (S k)) _ _ s1 n
      sx live _ (st (S jn)) (HbA ix (pa ix) sx (pa sx))
      (HbD ix (pd ix) sx (pd sx))) => //.
    - by left.
    - move=> p [<- | [<- | Hp]] // Epa; first by case: Epa => Epa; lia.
      have [Eid [Hkp _]] := static_in _ _ _ HL Hp.
      by move: Epa => /(f_equal aid) /=; lia.
    - move=> p [<- | [<- | Hp]] /=; try lia.
      by have [Eid [Hkp _]] := static_in _ _ _ HL Hp; lia.
    - by move=> El; rewrite Hs1_n El.
    exact: Hs1_t.
  have [s3 [R3 [_ [_ [T3 [RF3 [Sh3 [Pr3 TB3]]]]]]]] :=
    Hrv s1 O' (agree_prim_refl _ _ _) Hr1 Hseed Htp1 Htt1.
  (* the reverse sweep of the step gives the state back, popping its pushes *)
  have TB := TB3 (fun H => H) I sx erefl.
  rewrite Hts_body -/live in TB.
  have Hpb : forall v, is_primal v -> ~ is_bar v /\ ~ is_tape v.
    by case=> * //; split.
  (* the invariant one step down *)
  exists s3; split.
    by rewrite /body run_app R1 R3.
  split.
    move=> v Hb Cv Pv Hvn; have [Bv Tv] := Hpb v Pv.
    have Hb' : below (S c) v by apply: (below_mono c) => //; lia.
    rewrite (RF3 v Hb' Cv Tv); last first.
    - by rewrite Hs1v // Hsp_v // K0.
    - by move=> m Em; move: Pv; rewrite Em.
    by rewrite Ein => -[Env]; apply: Hvn; rewrite Env.
  split.
    apply: (tkeep_trans _ _ _ s) => //; apply: (tkeep_trans _ _ _ s'') => //.
    apply: (tkeep_trans _ _ _ s1); first by apply: (tkeep_mono _ (S c)) => //;
      lia.
    by apply: (tkeep_mono _ (S c)) => //; lia.
  split.
    move=> v Hvn Hb Cv Tv Hex Hbo; rewrite -(F0 v Hvn Hb Cv Tv Hex Hbo).
    have Hb' : below (S c) v by apply: (below_mono c) => //; lia.
    rewrite (RF3 v Hb' Cv Tv); last first.
    - by rewrite Hs1v // Hsp_v.
    - by move=> m Em; rewrite /O' oset_snd; move: (Hbo m Em); rewrite oset_snd.
    by rewrite Ein => -[Ev]; apply: Hvn.
  case El: live TB => TB.
    split.
      move=> _; case: TB => _ Tp; apply: Tp.
      exact: (Hs1_t El).
    split; first by case: TB => -> _; rewrite Ej.
    split; first exact: Sh3.
    have Hbar2 : forall t m, In (t, m) (oset O n (tangent (st (S jn)))) ->
        barv s1 m = barv s m.
      move=> t m Hin.
      have : In m (map snd O').
        rewrite /O' !oset_snd -(oset_snd O n (tangent (st (S jn)))).
        by apply/in_map_iff; exists (t, m).
      by move=> /in_map_iff [[t0 m0] [/= -> Ho1]]; exact: (Hbar1 _ _ Ho1).
    by rewrite Pr3 Ein /= oset_oset (pairing_ext_own _ _ _ Hbar2).
  split; first by [].
  split; first by rewrite TB Hs1_n El.
  split; first exact: Sh3.
  have Hbar2 : forall t m, In (t, m) (oset O n (tangent (st (S jn)))) ->
      barv s1 m = barv s m.
    move=> t m Hin.
    have : In m (map snd O').
      rewrite /O' !oset_snd -(oset_snd O n (tangent (st (S jn)))).
      by apply/in_map_iff; exists (t, m).
    by move=> /in_map_iff [[t0 m0] [/= -> Ho1]]; exact: (Hbar1 _ _ Ho1).
  by rewrite Pr3 Ein /= oset_oset (pairing_ext_own _ _ _ Hbar2).
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
have Hnd := r_nodup _ _ _ _ _ _ _ Hr.
have Cn : consistent n by [].
have HstN : st N = ve by rewrite /st app_nth2 Hlen // Nat.sub_diag.
have Hst0' : st 0%nat = pd q by exact: Hst0.
have Htq : has_type (Array z) (pd q) by rewrite -Hst0'; apply: Hstates; lia.
have Htve : has_type (Array z) ve by rewrite -HstN; apply: Hstates.
have Hcons : forall t m t', In (t, m) (oset O n t') -> consistent m.
  move=> t m t' Hin.
  have : In m (map snd (oset O n t')) by apply/in_map_iff; exists (t, m).
  rewrite oset_snd => /in_map_iff [[t0 m0] [/= <- Hi]].
  exact: (Hok t0 m0 Hi).
(* before the loop: the final state *)
have HP : P N s2.
  split; first by [].
  split; first exact: tkeep_refl.
  split; first by move=> *.
  split; first by move=> El; rewrite firstn_all2 ?Hlen //; exact: Htape0.
  split; first by case El: live => //; rewrite HstN; exact: Hn_live.
  split; last by rewrite HstN.
  move=> t m; rewrite HstN => Hin; have Hm := Hcons _ _ _ Hin.
  case: (oset_mem _ _ _ _ _ Hin) => [Hi | [Em ->]].
    exact: (r_shape _ _ _ _ _ _ _ Hr t m Hi).
  move/(dvar_eq_consistent n m Cn Hm): Em => <-.
  exact: (shaped_array_same z (pd q) ve _ Htq Htve
    (r_shape _ _ _ _ _ _ _ Hr _ _ HqO)).
(* the bounds of the loop, read in the store *)
have Hlh : forall aP, (aP = loP \/ aP = hiP) -> forall p, aP = AVar p ->
    static_ok k p /\ store_get s2 (keyv (stored p)) = Some (primal (pd p)).
  move=> aP HaP p E.
  have Hp : In p L by case: HaP E => -> E; [exact: HloL p E | exact: HhiL p E].
  split; first exact: (static_in _ _ _ HL Hp).
  have Hlp : live_value k
      (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p.
    rewrite /live_value /=.
    by case: HaP E => -> ->; rewrite /= Nat.eqb_refl /= ?orb_true_r.
  have Hvp : vreads cv k
      (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
    rewrite /vreads; cbn [value_needs fold_binders].
    case: (needs cv Replay (S (S k)) _) => [u0 l0] /=.
    rewrite !atom_member_union.
    by case: HaP E => -> ->; rewrite /= Nat.eqb_refl /= ?orb_true_r.
  apply: (Hrd p Hp Hvp Hlp).
  case: Hpl => [Epp | _]; first by left; rewrite Epp.
  right; rewrite /inplace Hown => -[Epq].
  have Hpi : vty (pw p) = Integer.
    move/andb_true_iff: Eb => [E1 E2].
    by case: HaP E => -> E; rewrite E /= in E1 E2;
      [move/ty_eqb_true: E1 | move/ty_eqb_true: E2].
  case: (s_owner _ _ _ _ _ _ _ Hs q p Hown Hp (esym Epq)) => [Epq' | Hnl].
    by exfalso; subst p; rewrite Eqz in Hpi.
  by exfalso; exact: Hnl Hlp.
have Hslo := aspell_ok k s2 loP _ (Hlh loP (or_introl erefl)) Hlo.
have Hshi := aspell_ok k s2 hiP _ (Hlh hiP (or_intror erefl)) Hhi.
(* after the loop: the initial state *)
have [sf [Hex Pf]] := exec_down_loop_from (run body) (out_dvar nat i) l N P
  Hstep' N s2 (le_n N) HP.
have Hdown : exec_down R (run body) (out_dvar nat i) (h - 1) (count l h) s2 =
    Some sf.
  case: (Nat.eq_dec N 0) => [E0 | Hn0].
    by move: Hex; rewrite -/N E0.
  have -> : (h - 1 = l + Z.of_nat N - 1)%Z.
    by rewrite /N count_nat in Hn0 |- *; lia.
  exact: Hex.
case: Pf => [K [Tk [F [Tpf [Nn [Sh Pr]]]]]].
have Eo : oset O n (tangent (pd q)) = O by apply: oset_same.
rewrite Hst0' Eo in Sh Pr.
exists sf; split.
  by rewrite (run_forback _ _ _ _ _ _ l h Hslo Hshi) Hdown.
split; first exact: K.
split; first by move=> _ _ o; rewrite Hown => -[<-]; rewrite Hvq.
split.
  move=> Hnl _ o; rewrite Hown => -[<-] _; rewrite Nn.
  case El: live; first by rewrite Hst0'.
  exact: Hn_dead Hnl El.
do 4!(split=> //).
(* in a loop body, the state before the fold is back in the storage *)
move=> Hnl _ o; rewrite Hown => -[<-]; rewrite /fold_back Hlo Hhi -/live.
split=> El; last by rewrite Nn El.
exists tr; split; first exact: Htr.
split; first by rewrite Nn El Hst0'.
move=> l0 E; rewrite (Tpf El) /=.
by move: (Htape0 El); rewrite E => -[/app_inv_head ->].
Qed.


End NestLoop.
