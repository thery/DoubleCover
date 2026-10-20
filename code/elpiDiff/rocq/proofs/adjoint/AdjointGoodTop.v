(* AdjointGoodTop.v — the opened adjoint function keeps the scoping
   discipline (good): its parameters are consistent, and its statements,
   from the parameters in scope and writable, are good (agood_adj at the top:
   the forward sweep, the prologue of the seed, the reverse sweep and the
   returned value). Then simplify_correct_tapes gives the run of the
   simplified adjoint function.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import DualsDerive AdjointNesty.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform
  Adjoint Simplify Scoping SimplifyCorrect AnfEquiv Correctness
  TangentCorrect TangentGood TangentTop AdjointCorrect AdjointSpec
  AdjointGood AdjointGoodFwd AdjointGoodRev AdjointTop.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

(* The parameters of the primal arguments: their storage. *)
Lemma params_adjoint_primal cv Ls :
  params (map (adjoint_primal W cv) (map arg_entry Ls)) = map stored Ls.
Proof.
elim: Ls => [| p Ls IH] //=; rewrite -IH; congr (_ :: _).
rewrite /arg_entry /stored.
by case: (varg (pw p)) => [[nm r] |] //=; case: (vty (pw p)); case: r;
  case: (cv).
Qed.

(* The parameters of the adjoints: the adjoints of the arguments with a
   derivative. *)
Lemma params_adjoint_bars Ls :
  params (concat (map (adjoint_bar W) (map arg_entry Ls))) =
  map (fun p => BarOf (stored p)) (filter (fun p => has_dot (dname p)) Ls).
Proof.
elim: Ls => [| p Ls IH] //=.
rewrite params_app IH /dname /arg_entry /stored.
by case: (varg (pw p)) => [[nm r] |] //=; case: (vty (pw p)); case: r.
Qed.

(* The parameters of the adjoint function. *)
Lemma params_adjoint_inv cv Ls extra y :
  In y (params (map (adjoint_primal W cv) (map arg_entry Ls) ++
                concat (map (adjoint_bar W) (map arg_entry Ls)) ++ extra)) ->
  (exists p, In p Ls /\ (y = stored p \/ y = BarOf (stored p))) \/
  In y (params extra).
Proof.
rewrite !params_app params_adjoint_primal params_adjoint_bars.
move=> /(in_app_or _ _ _) [/(in_map_iff _ _ _) [p [<- Hp]] |
  /(in_app_or _ _ _) [H | H]].
- by left; exists p; split=> //; left.
- move: H => /(in_map_iff _ _ _) [p [<- /filter_In [Hp _]]].
  by left; exists p; split=> //; right.
by right.
Qed.

Lemma params_adjoint_primal_in cv Ls extra p :
  In p Ls ->
  In (stored p) (params (map (adjoint_primal W cv) (map arg_entry Ls) ++
                 concat (map (adjoint_bar W) (map arg_entry Ls)) ++ extra)).
Proof.
move=> Hp; rewrite params_app params_adjoint_primal.
by apply: in_or_app; left; apply: in_map.
Qed.

Lemma params_adjoint_bar_in cv Ls extra p :
  In p Ls -> has_dot (dname p) = true ->
  In (BarOf (stored p))
    (params (map (adjoint_primal W cv) (map arg_entry Ls) ++
             concat (map (adjoint_bar W) (map arg_entry Ls)) ++ extra)).
Proof.
move=> Hp Hd; rewrite !params_app params_adjoint_bars.
apply: in_or_app; right; apply: in_or_app; left.
by apply: (in_map (fun p => BarOf (stored p))); apply/filter_In.
Qed.

(* The body of the adjoint function: the forward sweep, the prologue of
   the seed, the reverse sweep and the end (the returned value). *)
Lemma finish_good (sc : list (dvar W)) (fw pro rv tl : list (dstmt W)) F
  c0 c' (se : dexpr W) (Bars Tape RV : list (dvar W) -> Prop) :
  Forall (fun x => below c0 x /\ consistent x) sc ->
  good_k sc sc c' fw (fun sc1 wr1 => fwd_post F c0 c' sc sc1 /\ RV sc1 /\
    forall sc2 wr2, rscope F c0 c' sc1 wr1 sc2 wr2 -> Bars wr2 ->
      Tape wr2 -> expr_ok sc2 se ->
      good_k sc2 wr2 c' rv (fun _ _ => True)) ->
  (forall wr, incl sc wr -> Bars wr) -> (forall wr, Tape wr) ->
  (forall sc1 wr1, incl sc sc1 -> incl sc wr1 -> incl wr1 sc1 ->
     Forall (fun x => below c' x /\ consistent x) sc1 ->
     (forall x, In x sc1 -> In x sc \/ is_barv x = false) ->
     good_k sc1 wr1 c' pro (fun sc2 _ =>
       (forall x, In x sc2 -> In x sc1 \/ dnum x = None) /\
       expr_ok sc2 se)) ->
  (forall sc1 sc3 wr3, RV sc1 -> incl sc1 sc3 -> good sc3 wr3 tl) ->
  good sc sc (fw ++ pro ++ rv ++ tl).
Proof.
move=> Hb Hfw HB HT Hpro Htl.
have G : good_k sc sc c' (fw ++ pro ++ rv)
    (fun sc3 _ => exists sc1, RV sc1 /\ incl sc1 sc3).
  apply: (good_k_app _ _ c' c' _ _ _ _ Hfw).
  move=> sc1 wr1 I1 I2 Hb1 Hw1 [Hpost [HRV Hrev]].
  have Hbv : forall x, In x sc1 -> In x sc \/ is_barv x = false.
    move=> x /Hpost [H | [[j0 [_ [_ [_ H]]]] | [-> | [j0 [_ ->]]]]];
      by [left | right].
  apply: (good_k_app _ _ c' c' _ _ _ _ (Hpro sc1 wr1 I1 I2 Hw1 Hb1 Hbv)).
  move=> sc2 wr2 J1 J2 Hb2 Hw2 [Hn2 Hse].
  have Hrs : rscope F c0 c' sc1 wr1 sc2 wr2.
    split=> //; split=> //; split=> //; split=> //.
    move=> x /Hn2 [H | H]; first exact: fwd_post_new Hb Hpost x H.
    by move=> [j0 [_ [Hd _]]]; rewrite H in Hd.
  have Hwr2 : incl sc wr2 by move=> y Hy; apply/J2/I2.
  apply: (good_k_weaken _ _ _ _ _ _ _ (Hrev sc2 wr2 Hrs (HB _ Hwr2) (HT _)
    Hse)) => // sc3 wr3 K1 _ _ _ _.
  by exists sc1; split=> // y Hy; apply/K1/J1.
rewrite app_assoc app_assoc -(app_assoc fw).
apply: G => sc3 wr3 _ _ _ _ [sc1 [HR I]].
exact: Htl HR I.
Qed.

Theorem adjoint_good (cv : bool) (f : function) (x : list (val R))
  (dx : list R) (v : val (dual R)) r ps ss k :
  parametric f -> well_formed (normalize f) = Ok ->
  Forall2 fits (decls f) x ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) =
    Some v ->
  open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 =
    (DBody r ps ss, k) ->
  Forall consistent (params ps) /\ good (params ps) (params ps) ss.
Proof.
move=> Hpar Hwf Hfit Hev Hob0.
have Ecva := annotate_cv_decls cv f Hpar.
set cva := annotate_cv cv (normalize f) in Ecva *.
set xs := seed_args (decls f) x dx in Hev *.
have Hnp := normalize_parametric f Hpar.
set dP := afdef (normalize f) pv.
have HD := Hnp pv (val (dual R)); rewrite -/dP in HD.
rewrite /aeval_function in Hev.
have [L [res [bP Ho]]] := open_P_some dP [] 0 xs _ v HD Hev.
have [new [EL [Hlen Hargs]]] := open_P_args dP 0 xs [] L res bP Ho.
rewrite app_nil_r in EL; subst new.
have [bA [HbA Htr]] :=
  annotate_open_cv cva dP [] 0 xs L res bP _ (Hnp pv avar) Ho.
have [resW [bW [HrW [HbW Hwfd]]]] :=
  wf_open dP [] 0 xs L res bP _ (decls f) (Hnp pv vinfo) Ho.
have Hds := decls_open dP (map (fun p => (p, tt)) []) [] 0 xs L res bP _
  (Hnp pv unit) Ho.
have {}Hds : decls f = map (fun p => fst (arg_entry p)) (rev L) by exact: Hds.
rewrite Nat.add_0_l in Htr Hwfd.
set n := length xs in Hlen Htr Hwfd.
set tr := annotate_definition_t cva 0 (afdef (normalize f) avar) in Htr.
have [resT [bT [HrT [HbT Hopen]]]] :=
  tangent_open dP [] 0 xs L res bP (afdef (normalize f) (tvar W)) tr
    (adjoint_body W cv) (Hnp pv (tvar W)) Ho.
rewrite Nat.add_0_l -/n in Hopen.
rewrite /well_formed -/(decls f) in Hwf.
case Hnrv: (non_real_varied (decls f)) Hwf => [? |] // Hwf.
rewrite Hwfd in Hwf.
move: Hob0.
change (open_pairs
          (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0)
  with (open_pairs (open_arguments W (rebuild_definition (tvar W)
          (afdef (normalize f) (tvar W)) tr) 0
          (map arg_entry []) (adjoint_body W cv)) 0).
rewrite Hopen /adjoint_body Htr.
have [Hargs' [HnL [Hstat [Huniq [Hnum [Hpn_inj Hxs]]]]]] :=
  open_args_facts _ _ _ _ n Hfit Hnrv Hds Hlen erefl Hargs.
rewrite -map_rev.
have Hparg : forall p, In p L -> exists nm0 t0 r0 i0 x0,
    p = arg_pv nm0 t0 r0 i0 x0.
  move=> p Hp; have [i0 [nm0 [t0 [r0 [x0 [-> _]]]]]] := Hargs' p Hp.
  by exists nm0, t0, r0, i0, x0.
have Hbar : forall p, In p L -> tbar (pt p) = avaried (pa p).
  by move=> p /Hparg [? [? [? [? [? ->]]]]].
have Hdot : forall p, In p L -> tbar (pt p) = true ->
    has_dot (dname p) = true.
  move=> p /Hargs' [i [nm [t [r0 [x0 [-> [_ [Hd _]]]]]]]] /= Ht.
  have := non_real_varied_none _ nm t r0 Hnrv (nth_error_In _ _ Hd) Ht.
  by rewrite /dname /arg_entry /=; clear Hd; case: t; case: r0 Ht.
have HrL : forall p, In p (rev L) <-> In p L.
  by move=> p; split=> /in_rev_iff.
have Hsc_ok : forall extra, (forall y, In y (params extra) ->
      below n y /\ consistent y) ->
    forall y, In y (params (map (adjoint_primal W cv) (map arg_entry (rev L))
      ++ concat (map (adjoint_bar W) (map arg_entry (rev L))) ++ extra)) ->
    below n y /\ consistent y.
  move=> extra He y /params_adjoint_inv [[p [Hp [-> | ->]]] | /He //];
    by rewrite /stored /=; have := Hnum p (proj1 (HrL p) Hp); split=> //; lia.
have Hmf : Forward = Forward -> PTop = PTop by [].
have Hmr : Forward = Replay -> PTop <> PTop by [].
have [[EW [Hnw HtcB]] | [w [nm [role [EW [Hg [Hwr [H1w [Hraw [HtcB
    [Hdep Hinout]]]]]]]]]]] := wf_result_facts _ _ _ _ Hwf.
  (* the function returns a real *)
  subst resW; destruct res as [tR | yP]; simpl in HrW;
    [subst tR | contradiction].
  destruct resT as [tT | yT]; simpl in HrT; [subst tT | contradiction].
  have Hwio : writes_inout (decls f) = false.
    case E: (writes_inout (decls f)) => //.
    move/existsb_exists: E => [[nm0 t0 r0] [Hd0 E]].
    case: r0 Hd0 E => // Hd0 _.
    have : existsb written_decl (decls f) = true.
      by apply/existsb_exists; exists (Decl nm0 t0 Inout).
    by rewrite Hnw.
  have Ecv' : cva = cv by rewrite Ecva Hwio andb_true_r.
  clearbody cva; clear Ecva; subst cva.
  cbn [adjoint_seed inout_result negb]; rewrite andb_true_r open_pairs_sbind.
  set vo := (if cv then Some (AReturns Real) else None)
    : option (aresult (tvar W)).
  set se := DVar (BarOf (@ResultVar W)).
  case Hob: (open_pairs (adj W None vo Forward
    (rebuild (tvar W) bT (annotate_body_t cv Forward n bA)) se) n)
    => [[fw rv] c'].
  cbn [open_pairs adjoint_finish].
  set PS := map (adjoint_primal W cv) (map arg_entry (rev L)) ++
    concat (map (adjoint_bar W) (map arg_entry (rev L))) ++
    [DParam ByValue Real (BarOf ResultVar)].
  have Hs : sctx L n n None PTop (live_anf n bW) Real.
    by constructor; auto; try (intros; discriminate); try exact I; case.
  have Hcv : Forward = Forward -> vo <> None -> cv = true.
    by rewrite /vo; case: (cv).
  have := proj1 (agood_adj cv) bP L n n None PTop Forward vo bA bW bT Real se
    HbA HbW HbT Hs I Hbar Hcv HtcB Hmf Hmr.
  rewrite Hob => -[Hc [F HF]].
  have Hbn : Forall (fun y => below n y /\ consistent y) (params PS).
    apply/Forall_forall; apply: Hsc_ok => y [<- | []].
    by split=> //; apply/below_dnum.
  have Hres : In (BarOf ResultVar) (params PS).
    by rewrite !params_app; apply/in_or_app; right; apply/in_or_app; right;
      left.
  have Hfs : fscope L n None PTop (tbr cv Forward n bA) (params PS)
      (params PS).
    split=> //; split; first exact: incl_refl.
    split=> // p Hp _.
    by apply: params_adjoint_primal_in; apply/HrL.
  have Htp : tape_fwd None PTop Forward (records_in cv n bA) (params PS)
      (params PS) by move=> o E.
  have Hvo : vo_scope Forward vo (params PS) (params PS).
    move=> _; split; last by rewrite /vo; case: (cv).
    move=> t _ /params_adjoint_inv [[p [_ [E | E]]] | [E | []]] //.
  have Hgood : forall tl, (forall sc1 sc3 wr3,
      (Forward = Forward -> forall t, vo = Some (AReturns t) ->
         In ResultVar sc1) -> incl sc1 sc3 -> good sc3 wr3 tl) ->
      good (params PS) (params PS) (fw ++ [] ++ rv ++ tl).
    move=> tl Htl.
    apply: (finish_good _ fw [] rv tl F n c' se
      (bars_ok L (useful cv Forward n bA) None PTop)
      (tape_rev None PTop (records_in cv n bA)) _ Hbn
      (HF _ _ Hfs Htp Hvo)) => //.
    - move=> wr I; split=> [p Hp _ Ht | o E] //.
      by apply/I/params_adjoint_bar_in; [apply/HrL | apply: Hdot].
    move=> sc1 wr1 I1 _ Hw1 Hb1 _; apply: good_k_nil => //.
    by split; [move=> y Hy; left | apply: I1].
  rewrite -/PS; case Ecv: (cv) => -[_ <- <- _].
    split; first by apply: (Forall_impl _ _ Hbn) => y [].
    apply: Hgood => sc1 sc3 wr3 HR I.
    apply: GoodReturn; last exact: GoodNil.
    by apply/I/(HR erefl Real); rewrite /vo Ecv.
  split; first by apply: (Forall_impl _ _ Hbn) => y [].
  rewrite -[rv]app_nil_r; apply: Hgood => *; exact: GoodNil.
(* the function writes an argument *)
subst resW; destruct res as [tR | yP]; simpl in HrW; [contradiction |].
destruct yP as [y | | ]; simpl in HrW; try contradiction.
move/in_gW: HrW => [HyL Ew]; subst w.
destruct resT as [tT | yT]; simpl in HrT; [contradiction |].
destruct yT as [yt | | ]; simpl in HrT; try contradiction.
move/in_gT: HrT => [_ Eyt]; subst yt.
have [j [nm' [t [r0 [x0 [Ey [Hxj [Hdj Hj]]]]]]]] := Hargs' y HyL.
have Hvy : vty (pw y) = t by rewrite Ey.
rewrite Ey /= in Hg; case: Hg => Enm Erole; subst nm role.
have Hdecl_y : dname y = Decl nm' t r0 by rewrite Ey.
rewrite Hvy in Hraw HtcB.
have Hdy : has_dot (dname y) = true.
  by rewrite Hdecl_y; move: Hraw Hwr; case: (t); case: (r0).
have HyR : In y (rev L) by apply/HrL.
have Hnd : NoDup (rev L) by apply: (NoDup_map_inv pn).
have Hdn : map dname (rev L) = decls f by rewrite Hds.
have Hu : forall p, In p (rev L) -> written_decl (dname p) = true -> p = y.
  move=> p Hp Wp; apply: (written_unique (rev L) p y Hnd) => //.
    by rewrite Hdn.
  by rewrite Hdecl_y.
have Hwio : writes_inout (decls f) =
    match r0 with Inout => true | _ => false end.
  have Hno : writes_inout (decls f) = true -> r0 = Inout.
    move/existsb_exists => [[nm0 t0 r1] [Hd0 E]].
    case: r1 Hd0 E => // Hd0 _.
    rewrite -Hdn in Hd0; move: Hd0 => /(in_map_iff _ _ _) [p [Ep Hp]].
    have Wp : written_decl (dname p) = true by rewrite Ep.
    by move: Ep; rewrite (Hu p Hp Wp) Hdecl_y => -[_ _ ->].
  case E: (writes_inout (decls f)); first by rewrite (Hno E).
  case Er: (r0) => //.
  rewrite -E; apply/existsb_exists; exists (Decl nm' t Inout); split=> //.
  by rewrite -Er; exact: nth_error_In Hdj.
have Hir : inout_result W (AWrites (AVar (pt y))) =
    match r0 with Inout => true | _ => false end.
  by rewrite Ey; case: (r0).
rewrite Hir.
move Hcvw : (cv && ~~ match r0 with Inout => true | _ => false end) => cvw.
have Ecvw : cva = cvw by rewrite Ecva Hwio.
clearbody cva; clear Ecva; subst cva.
set vo := (if cvw then Some (AWrites (AVar (pt y))) else None)
  : option (aresult (tvar W)).
case Eseed: (adjoint_seed W (AWrites (AVar (pt y)))) => [[extra pro] se].
have Hextra : extra = [].
  move: Eseed; rewrite /adjoint_seed Ey /=.
  by case: (t) => [| | | z]; case: (r0); case=> <-.
subst extra; rewrite open_pairs_sbind.
case Hob: (open_pairs (adj W (Some (AVar (pt y))) vo Forward
  (rebuild (tvar W) bT (annotate_body_t cvw Forward n bA)) se) n)
  => [[fw rv] c'].
cbn [open_pairs adjoint_finish].
set PS := map (adjoint_primal W cv) (map arg_entry (rev L)) ++
  concat (map (adjoint_bar W) (map arg_entry (rev L))) ++ [].
(* the written argument at the top *)
have Hown_cases : owner (Some (AVar y)) PTop =
    match t with Array _ => Some y | _ => None end.
  by rewrite /= Hvy.
have Hs : sctx L n n (Some (AVar y)) PTop (live_anf n bW) t.
  constructor.
  + exact: Hstat.
  + exact: Huniq.
  + exact: Hnum.
  + by move=> a0 [<-]; exists y; split=> //; split=> //; rewrite Ey.
  + exact: I.
  + move=> o p Hw0 Hp E; rewrite Hown_cases in Hw0.
    case: (t) Hw0 => // z [Eo]; subst o.
    by left; exact: Hpn_inj p y Hp HyL E.
  + move=> p o Hp Lp Ha Hg' Hw0; rewrite Hown_cases in Hw0.
    case: (t) Hw0 => // z [Eo]; subst o.
    case: Hg' => [Hg' | Hg'].
      by have [? [? [? [? [? [Ep _]]]]]] := Hargs' p Hp; subst p.
    by case: Hg' => ->.
  + by move=> Ha; rewrite Hown_cases; case: (t) Ha.
  + move=> y' _ [<-] Ha; split; first by rewrite Hvy.
    move=> Ly; destruct r0; rewrite /= in Hwr; try discriminate.
    * by move: Ly; rewrite /live_anf Hdep.
    by rewrite Ey.
have Hcv : Forward = Forward -> vo <> None -> cvw = true.
  by rewrite /vo; case: (cvw).
have := proj1 (agood_adj cvw) bP L n n (Some (AVar y)) PTop Forward vo bA bW
  bT t se HbA HbW HbT Hs Hraw Hbar Hcv HtcB Hmf Hmr.
rewrite Hob => -[Hc [F HF]].
have Hbn : Forall (fun y => below n y /\ consistent y) (params PS).
  by apply/Forall_forall; apply: Hsc_ok => y0 [].
have Hyp : In (stored y) (params PS).
  exact: params_adjoint_primal_in.
have Hyb : In (BarOf (stored y)) (params PS).
  exact: params_adjoint_bar_in.
have Hnotape : forall z, ~ In (TapeOf z) (params PS).
  by move=> z /params_adjoint_inv [[p [_ [E | E]]] | []].
have Hnores : ~ In (BarOf ResultVar) (params PS).
  by move=> /params_adjoint_inv [[p [_ [E | E]]] | []].
have Hfs : fscope L n (Some (AVar y)) PTop (tbr cvw Forward n bA)
    (params PS) (params PS).
  split=> //; split; first exact: incl_refl.
  split; first by move=> p Hp _; apply: params_adjoint_primal_in; apply/HrL.
  by move=> o; rewrite Hown_cases; case: (t) => // z [<-].
(* its tape is declared by the in-place fold *)
have Htp : tape_fwd (Some (AVar y)) PTop Forward (records_in cvw n bA)
    (params PS) (params PS).
  move=> o; rewrite Hown_cases; case: (t) => // z [<-].
  split=> [_ | Hl]; last by case: (Hl I).
  by split; [exact: Hnotape | rewrite Ey].
have Hvo : vo_scope Forward vo (params PS) (params PS).
  move=> _; split; first by rewrite /vo; case: (cvw).
  move=> y'; rewrite /vo; case: (cvw) => // -[<-].
  have -> : stored_of W (AVar (pt y)) = stored y by rewrite Ey.
  exact: Hyp.
(* the prologue of the seed *)
have Hpro : forall sc1 wr1, incl (params PS) sc1 -> incl (params PS) wr1 ->
    incl wr1 sc1 -> Forall (fun x => below c' x /\ consistent x) sc1 ->
    (forall x, In x sc1 -> In x (params PS) \/ is_barv x = false) ->
    good_k sc1 wr1 c' pro (fun sc2 _ =>
      (forall x, In x sc2 -> In x sc1 \/ dnum x = None) /\ expr_ok sc2 se).
  move=> sc1 wr1 I1 I2 Hw1 Hb1 Hbv.
  have Hys : stored_of W (AVar (pt y)) = stored y by rewrite Ey.
  move: Eseed; rewrite /adjoint_seed Hys.
  have -> : tof (AVar (pt y)) = t by rewrite Ey.
  have -> : role_of W (AVar (pt y)) = Some r0 by rewrite Ey.
  case: (t) Hraw => [| | | z] // _; case: (r0) => -[<- <-].
  all: try (apply: good_k_nil => //; split; [by move=> z0 Hz; left |
    first [by [] | by apply: I1]]).
  (* an inout real: its adjoint moves to the seed *)
  move=> rest Hrest /=.
  have Hn1 : ~ In (BarOf ResultVar) sc1.
    by move=> /Hbv [H | //]; apply: Hnores.
  apply: GoodConstant => //; first by apply/I1.
  apply: GoodAssign; [by apply/I2 | by [] |].
  apply: Hrest; [by move=> z0 Hz; right | by [] | | | ].
  - by constructor=> //; split=> //; apply/below_dnum.
  - by move=> z0 Hz; right; apply: Hw1.
  split; last by left.
  by move=> z0 [<- | Hz]; [right | left].
have Hfin : good (params PS) (params PS) (fw ++ pro ++ rv).
  rewrite -[rv]app_nil_r.
  apply: (finish_good _ fw pro rv [] F n c' se
    (bars_ok L (useful cvw Forward n bA) (Some (AVar y)) PTop)
    (tape_rev (Some (AVar y)) PTop (records_in cvw n bA)) _ Hbn
    (HF _ _ Hfs Htp Hvo)) => //.
  - move=> wr I; split=> [p Hp _ Ht | o].
      by apply/I/params_adjoint_bar_in; [apply/HrL | apply: Hdot].
    by rewrite Hown_cases; case: (t) => // z [<-]; split; apply: I.
  - by move=> wr o _ Hl; case: (Hl I).
  by move=> *; exact: GoodNil.
have Hcon : Forall consistent (params PS).
  by apply: (Forall_impl _ _ Hbn) => y0 [].
by case: (cv) => -[_ <- <- _].
Qed.

(* Milestone M6: the simplified adjoint function computes the gradient, for
   the bodies of adjoint_nesty_duals: the opened adjoint function keeps the
   scoping discipline (adjoint_good), so simplify preserves its run
   (simplify_correct_tapes). *)
Corollary adjoint_nesty_simplified (cv : bool) (f : function)
  (x : list (val R)) (xb yb dx : list R) (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok ->
  Forall2 fits (decls f) x ->
  length xb = in_dim x ->
  length yb = length (reals_of_val (TangentCorrect.primal v)) ->
  length dx = in_dim x ->
  (forall L res bP, open_P (afdef (normalize f) pv) 0
     (seed_args (decls f) x dx) [] = Some (L, res, bP) -> nesty true bP) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) =
    Some v ->
  exists out g,
    exec_dfunction reals
      (simplify (Adjoint.adjoint cv (annotate cv (normalize f))))
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb =
      dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false ->
       value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
move=> Hp Hw Hf Hxb Hyb Hdx Hs Hev.
have [r [ps [ss [k [out [g [Ho [Hex Hrest]]]]]]]] :=
  adjoint_nesty_duals cv f x xb yb dx v Hp Hw Hf Hxb Hyb Hdx Hs Hev.
have [Hc Hgd] := adjoint_good cv f x dx v r ps ss k Hp Hw Hf Hev Ho.
exists out, g; split; last exact: Hrest.
exact: (simplify_correct_tapes _ _ r ps ss k out Ho Hc Hgd Hex).
Qed.
