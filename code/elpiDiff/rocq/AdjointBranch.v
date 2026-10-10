(* AdjointBranch.v — the adjoint simulation of branches (milestone M2).

   The forward sweep computes a branch with prim: the statements of the branch
   taken, then its value into the storage of the let (psim_body). The reverse
   sweep replays the branch taken (adj Replay) and transposes it, from the
   adjoint of the let: the simulation of the body of the branch (asim_body),
   run in the store of the reverse sweep. Branch bodies bind operations, reads
   of arrays and branches (well_formed: no update, map or fold in a branch). *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint
  Simplify Scoping AnfEquiv Correctness TangentCorrect TangentLoops TangentGood
  AdjointCorrect.

From ElpiDiff Require Import Dot.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

(* ---------------------------------------------------------------------------
   The atoms of a body (the analyses, binders opened with fresh) are the
   variables that occur in it (well_formed, binders opened with anon). *)

Lemma atom_member_id x l : atom_member (AVar x) l = atom_member (AVar (AV (aid
  x) false)) l.
Proof. by []. Qed.

Lemma atom_member_remove_full x y l :
  atom_member y (atom_remove x l) = negb (same_term x y) && atom_member y l.
Proof.
rewrite /atom_member /atom_remove; elim: l => [|z l IH] /=.
  by case: (same_term x y).
case Exz: (same_term x z) => /=; rewrite IH.
  case Exy: (same_term x y) => //=; case Eyz: (same_term y z) => //=.
  move: Exz Exy Eyz; clear.
  case: x => // x; case: y => // y; case: z => // z /=.
  by move=> /Nat.eqb_eq ? /Nat.eqb_neq ? /Nat.eqb_eq ?; lia.
case Exy: (same_term x y); case Eyz: (same_term y z) => //=.
move: Exz Exy Eyz; clear; case: x => // x; case: y => // y; case: z => // z /=.
by move=> /Nat.eqb_neq ? /Nat.eqb_eq ? /Nat.eqb_eq ?; lia.
Qed.

Lemma same_fresh j i : j <> i -> same_term (AVar (fresh j)) (AVar (AV i false))
  = false.
Proof. by move=> H; apply/Nat.eqb_neq. Qed.

(* Outside the body of an in-place loop, there is no tail tape to give. *)
Lemma no_tail_tape_branch cv k L b bA bD s :
  forall ix sx n0, PBranch = PArray ix sx -> None = Some n0 ->
  tail_tape cv k L b bA bD s n0.
Proof. by []. Qed.

Lemma no_tail_tape_scalar cv k L b bA bD s :
  forall ix sx n0, PScalar = PArray ix sx -> None = Some n0 ->
  tail_tape cv k L b bA bD s n0.
Proof. by []. Qed.

Definition dummy_tvar : tvar W := TVar ResultVar Real None false false false
  false None.

(* A variable opened by both analyses at k. *)
Definition opened (k : nat) : pv := PV (fresh k) (anon k) dummy_tvar (VInt 0%Z)
  0.

Lemma atoms_atom G (aP : atom pv) aA aW i :
  atom_eq (gA G) aP aA -> atom_eq (gW G) aP aW -> (forall q, In q G -> aid (pa
    q) = vid (pw q)) ->
  atom_member (AVar (AV i false)) (atoms_of_atom aA) = occurs_atom i aW.
Proof.
move=> /atom_graph [-> HA] /atom_graph [-> _] Hid.
case: aP HA => [q | |] HA //=.
by rewrite (Hid q (HA q erefl)) Nat.eqb_sym orb_false_r.
Qed.

Lemma atoms_occurs :
  (forall bP : anf pv bare, forall G bA bW k i,
     anf_eq (gA G) bP bA -> anf_eq (gW G) bP bW -> (forall q, In q G -> aid (pa
       q) = vid (pw q)) -> (i < k)%nat ->
     atom_member (AVar (AV i false)) (atoms_of_anf k bA) = occurs_anf i k bW) /\
  (forall eP : value pv bare, forall G eA eW k i,
     value_eq (gA G) eP eA -> value_eq (gW G) eP eW -> (forall q, In q G -> aid
       (pa q) = vid (pw q)) -> (i < k)%nat ->
     atom_member (AVar (AV i false)) (atoms_of_value k eA) = occurs_value i k
       eW).
Proof.
apply anf_value_ind.
- move=> a e IHe b IHb G bA bW k i.
  case: bA => [aA eA cA |]; case: bW => [aW eW cW |] //=.
  move=> [HeA HcA] [HeW HcW] Hid Hi.
  rewrite atom_member_union atom_member_remove_full.
  rewrite (IHe G eA eW k i HeA HeW Hid Hi).
  have Hki : k <> i by lia.
  rewrite (same_fresh _ _ Hki) /=; congr (_ || _).
  have Hid' : forall q, In q (opened k :: G) -> aid (pa q) = vid (pw q).
    by move=> q [<- | Hq] //; exact: Hid.
  have HiS : (i < S k)%nat by lia.
  exact: (IHb (opened k) (opened k :: G) _ _ _ _ (HcA _ _) (HcW _ _) Hid' HiS).
- move=> x G [? ? ? | aA] [? ? ? | aW] //= k i HA HW Hid _.
  exact: atoms_atom G x aA aW i HA HW Hid.
- move=> f x G [] // f1 a1 [] // f2 a2 k i [_ HA] [_ HW] Hid _.
  exact: atoms_atom G x _ _ i HA HW Hid.
- move=> f x y G [] // f1 a1 b1 [] // f2 a2 b2 k i.
  move=> [_ [HA1 HA2]] [_ [HW1 HW2]] Hid _.
  rewrite /= !atom_member_union /= (atoms_atom G x _ _ i HA1 HW1 Hid).
  by rewrite (atoms_atom G y _ _ i HA2 HW2 Hid).
- move=> x j G [] // a1 j1 [] // a2 j2 k i [HA1 HA2] [HW1 HW2] Hid _.
  rewrite /= !atom_member_union /= (atoms_atom G x _ _ i HA1 HW1 Hid).
  by rewrite (atoms_atom G j _ _ i HA2 HW2 Hid).
- move=> x j y G [] // a1 j1 y1 [] // a2 j2 y2 k i.
  move=> [HA1 [HA2 HA3]] [HW1 [HW2 HW3]] Hid _.
  rewrite /= !atom_member_union /= (atoms_atom G x _ _ i HA1 HW1 Hid).
  rewrite (atoms_atom G j _ _ i HA2 HW2 Hid).
  by rewrite (atoms_atom G y _ _ i HA3 HW3 Hid) ?orb_false_r ?orb_assoc.
- move=> c t IHt e IHe G [] // c1 t1 e1 [] // c2 t2 e2 k i.
  move=> [HA1 [HA2 HA3]] [HW1 [HW2 HW3]] Hid Hi.
  rewrite /= !atom_member_union (atoms_atom G c _ _ i HA1 HW1 Hid).
  by rewrite (IHt G _ _ k i HA2 HW2 Hid Hi) (IHe G _ _ k i HA3 HW3 Hid Hi).
- move=> lo hi b IHb G [] // l1 h1 b1 [] // l2 h2 b2 k i.
  move=> [HA1 [HA2 HA3]] [HW1 [HW2 HW3]] Hid Hi.
  rewrite /= !atom_member_union /= (atoms_atom G lo _ _ i HA1 HW1 Hid).
  rewrite (atoms_atom G hi _ _ i HA2 HW2 Hid).
  have Hki : k <> i by lia.
  rewrite atom_member_remove_full (same_fresh _ _ Hki) /=.
  congr (_ || _).
  have Hid' : forall q, In q (opened k :: G) -> aid (pa q) = vid (pw q).
    by move=> q [<- | Hq] //; exact: Hid.
  have HiS : (i < S k)%nat by lia.
  exact: (IHb (opened k) (opened k :: G) _ _ _ _ (HA3 _ _) (HW3 _ _) Hid' HiS).
move=> a lo hi init b IHb G [] // a1 l1 h1 i1 b1 [] // a2 l2 h2 i2 b2 k i.
move=> [HA1 [HA2 [HA3 HA4]]] [HW1 [HW2 [HW3 HW4]]] Hid Hi.
rewrite /= !atom_member_union /= (atoms_atom G lo _ _ i HA1 HW1 Hid).
rewrite (atoms_atom G hi _ _ i HA2 HW2 Hid).
rewrite (atoms_atom G init _ _ i HA3 HW3 Hid).
have Hki : k <> i by lia.
have HSki : S k <> i by lia.
rewrite !atom_member_remove_full (same_fresh _ _ Hki) (same_fresh _ _ HSki) /=.
congr (_ || _); first by rewrite orb_assoc.
have Hid' : forall q, In q (opened (S k) :: opened k :: G) ->
    aid (pa q) = vid (pw q).
  by move=> q [<- | [<- | Hq]] //; exact: Hid.
have HiS : (i < S (S k))%nat by lia.
exact: (IHb (opened k) (opened (S k)) (opened (S k) :: opened k :: G)
  _ _ _ _ (HA4 _ _ _ _) (HW4 _ _ _ _) Hid' HiS).
Qed.

(* The atoms the partial derivatives read are operands. *)
Lemma read_by1 f (a : atom avar) y :
  atom_member y (read_by a (partial1 f a)) = true -> atom_member y
    (atoms_of_atom a) = true.
Proof.
rewrite /read_by; case Ep: (partial1 f a) => [p |] //.
case: (varied a) => //.
move: Ep; case: f => [| | | | | | [|z|z] |] //=.
all: move=> [<-] /=; rewrite ?atom_member_union /= ?orb_false_r //.
Qed.

Lemma needs_op2 f (a b : atom avar) y :
  atom_member y (fst (match partial2 f a b with
                      | Some (pa, pb) => (atom_union (read_by a (Some pa))
                        (read_by b (Some pb)), atoms_of_atoms [a; b])
                      | None => ([], atoms_of_atoms [a; b]) end))
  || atom_member y (snd (match partial2 f a b with
                      | Some (pa, pb) => (atom_union (read_by a (Some pa))
                        (read_by b (Some pb)), atoms_of_atoms [a; b])
                      | None => ([], atoms_of_atoms [a; b]) end)) = true ->
  atom_member y (atoms_of_atom a) || atom_member y (atoms_of_atom b) = true.
Proof.
have Hs : atom_member y (atoms_of_atoms [a; b]) =
    atom_member y (atoms_of_atom a) || atom_member y (atoms_of_atom b).
  by rewrite /= !atom_member_union /= ?orb_false_r.
case: f; cbn [partial2 fst snd]; rewrite Hs.
9: move=> _.
all: case/orP; last by [].
all: rewrite /read_by; case: (varied a); case: (varied b) => /=.
all: rewrite ?atom_member_union /= ?atom_member_union /= ?orb_false_r.
all: move=> H; apply/orP; repeat case/orP: H => H; by [|tauto].
Qed.

Lemma pairing_ext_own O s s' : (forall t m, In (t, m) O -> barv s m = barv s' m)
  -> pairing O s = pairing O s'.
Proof.
elim: O => [|[t m] O IH] H //=.
have -> : pairing O s = pairing O s'.
  by apply: IH => t' m' Hi; apply: (H t'); right.
by rewrite (H t m (or_introl erefl)).
Qed.


(* The value of a body has the type it is checked at, and a zero tangent when
   the body is not varied. *)
Definition act_body (bP : anf pv bare) : Prop :=
  forall L k wP pp bA bW bD ty v,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gD L) bP bD -> Forall
    (static_ok k) L ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  aeval (duals reals) bD = Some v ->
  has_type ty v /\ (varied_anf k bA = false -> zero v).

Lemma act_ret (aP : atom pv) : act_body (ARet aP).
Proof.
move=> L k wP pp [? ? ? | aA] [? ? ? | aW] [? ? ? | aD] //= ty v.
move=> /atom_graph [-> Hin] /atom_graph [-> _] /atom_graph [-> _] HL Htc Hev.
have H1 : forall p, aP = AVar p -> static_ok k p.
  by move=> p E; apply: (static_in _ _ _ HL); auto.
have Ety : ty = of_atom (amap pw aP).
  move: Htc; case: aP {Hin H1 Hev} => [p | s | z] /=; [| by case | by case].
  case: (varg (pw p)) => [[? ?] |] /=; last by case.
  by case: (_ && _) => -[].
subst ty; split; first exact: atom_type k aP v H1 Hev.
by move=> Hv; exact: atom_zero k aP v H1 Hv Hev.
Qed.

(* The let, its continuation active for the variables of the type of the
   value only. *)
Lemma act_let_typed a (eP : value pv bare) (cP : pv -> anf pv bare) :
  act_value eP ->
  (forall x, Some (vty (pw x)) = ptype eP -> act_body (cP x)) ->
  act_body (ALet a eP cP).
Proof.
move=> IHa IHb L k wP pp [aA eA cA | ?] [aW eW cW | ?] [aD eD cD | ?] //= ty v.
move=> [HeA HcA] [HeW HcW] [HeD HcD] HL Htc Hev.
case Hte: (typecheck_value (option_map (amap pw) wP) (wplace pp)
  (WellFormed.is_tail cW k) k eW) Htc => [te []] //= Htc.
case Hve: (aeval_value (duals reals) eD) Hev => [ve |] //= Hev.
have [Ht [Hz Hra]] := IHa L k wP pp _ eA eW eD te ve HeA HeW HeD HL Hte Hve.
set vr := varied_value k eA.
set x := PV (let_binder k eA) (VInfo k te None)
  (open_let te (DBound (0%nat, 0%nat) : dvar W) vr false) ve 0.
have Hxs : static_ok (S k) x.
  by repeat split; simpl; auto; try lia; discriminate.
have HL' : Forall (static_ok (S k)) (x :: L).
  apply: Forall_cons Hxs _; apply: Forall_impl HL => p Hp.
  by apply: static_mono Hp _; lia.
have Hxt : Some (vty (pw x)) = ptype eP.
  by rewrite (ptype_ok _ _ _ _ _ _ _ _ HeW Hte).
exact: IHb x Hxt (x :: L) (S k) wP pp (cA (pa x)) (cW (pw x)) (cD (pd x)) ty v
  (HcA x (pa x)) (HcW x (pw x)) (HcD x (pd x)) HL' Htc Hev.
Qed.

Lemma act_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  act_value eP -> (forall x, act_body (cP x)) -> act_body (ALet a eP cP).
Proof. by move=> Ha Hb; apply: act_let_typed => // x _. Qed.

Lemma act_ite (cP : atom pv) (tP eP : anf pv bare) :
  act_body tP -> act_body eP -> act_value (AIte cP tP eP).
Proof.
move=> IHt IHe L k wP pp tail [] // cA tA eA0 [] // cW tW eW0 [] // cD tD eD0.
move=> te ve HA HW HD HL Htc Hev; rewrite /= in HA HW HD.
move: HA HW HD Htc Hev => [/atom_graph [-> HcA] [HtA HeA]].
move=> [/atom_graph [-> HcW] [HtW HeW]] [/atom_graph [-> HcD] [HtD HeD]].
move=> Htc Hev; rewrite /= in Htc Hev *.
set X := (if ty_eqb _ _ then _ else _) in Htc.
have {}Htc : X = (te, Ok) by case: (wplace pp) Htc.
rewrite /X {X} in Htc.
case: (ty_eqb (of_atom (amap pw cP)) Boolean) Htc => //.
case HtW': (typecheck (option_map (amap pw) wP) InBranch k tW) => [t3 [] ] /=;
  last by case: (typecheck _ _ k eW0).
case HeW': (typecheck (option_map (amap pw) wP) InBranch k eW0) => [t4 [] ] //=.
case E3: (ty_eqb t3 Real); case E4: (ty_eqb t4 Real) => //= -[<-].
move/ty_eqb_true: E3 HtW' => -> HtW'; move/ty_eqb_true: E4 HeW' => -> HeW'.
case: (aeval_atom (duals reals) (amap pd cP)) Hev => [[| | [] | |] |] // Hev.
  have [Ht Hz] := IHt L k wP PBranch _ _ _ Real ve HtA HtW HtD HL HtW' Hev.
  by split=> //; split=> [/orb_false_iff [Hvt _] | _]; [exact: Hz | by []].
have [Ht Hz] := IHe L k wP PBranch _ _ _ Real ve HeA HeW HeD HL HeW' Hev.
by split=> //; split=> [/orb_false_iff [_ Hve] | _]; [exact: Hz | by []].
Qed.

(* The typing of a map: at the top, at the end, from index 0, with a body
   computing reals in a scalar place. *)
Lemma map_typing wW pp tail k (lo hi : atom vinfo) (bW : vinfo -> anf vinfo
  bare) te :
  typecheck_value wW (wplace pp) tail k (AMap lo hi bW) = (te, Ok) ->
  pp = PTop /\ tail = true /\ lo = ANat 0 /\
  exists h, hi = ANat h /\ te = Array (h - 0) /\
    typecheck wW ScalarBody (S k) (bW (VInfo k Integer None)) = (Real, Ok) /\
    forall y, wW = Some (AVar y) ->
      (forall nm r, varg y = Some (nm, r) -> r <> Inout) /\ occurs_anf (vid y)
        (S k) (bW (anon k)) = false.
Proof.
case: pp => [| | | ix sx] //= Htc.
case: tail Htc => [| Htc]; last by case: lo Htc; case: hi.
case: lo => [? | ? | l0] //; case: hi => [? | ? | h] //=.
case El: (negb (l0 =? 0)%Z) => //.
move/negbFE/Z.eqb_eq: El => ->.
do 3!split=> //; exists h; split=> //.
case: wW Htc => [[y | s | z] |] Htc;
  first case Ev: (varg y) Htc => [[nm []] |] //= Htc.
all: try (case Eo: (occurs_anf (vid y) (S k) (bW (anon k))) Htc => // Htc).
all: case Etb: (typecheck _ ScalarBody (S k) _) Htc => [tb [| mm]] //=.
all: case Er: (ty_eqb tb Real) => // -[<-].
all: move/ty_eqb_true: Er Etb => -> Etb.
all: do 2!split=> //; move=> y' // [<-].
all: by split=> // nm' r'; rewrite Ev => // -[_ Er]; subst r'.
Qed.

Lemma act_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, act_body (bP x)) -> act_value (AMap loP hiP bP).
Proof.
move=> IHb L k wP pp tail [] // loA hiA bA [] // loW hiW bW [] // loD hiD bD.
move=> te ve HA HW HD HL Htc Hev; rewrite /= in HA HW HD.
move: HA HW HD Htc Hev => [/atom_graph [-> _] [/atom_graph [-> _] HbA]].
move=> [/atom_graph [-> _] [/atom_graph [-> _] HbW]].
move=> [/atom_graph [-> _] [/atom_graph [-> _] HbD]] Htc Hev.
move/map_typing: Htc => [_ [_ [Elo [h [Ehi [Ete [HtB _]]]]]]]; subst te.
case: loP Elo Hev => [? | ? | l0] //= [El0]; subst l0.
case: hiP Ehi => [? | ? | h'] //= [Eh]; subst h'.
case Hxs: (eval_map (fun v1 => aeval (duals reals) (bD v1)) 0 (count 0 h))
  => [xs |] //= [<-].
split; first by rewrite /= (eval_map_length _ _ _ _ Hxs) count_nat.
split=> // Hv /=.
apply: (eval_map_Forall (fun d => dsnd d = 0) _ _ _ _ _ Hxs) => z x Hbd.
set ix := PV (fresh k) (VInfo k Integer None)
  (open_index (DBound (0%nat, 0%nat))) (VInt z) 0.
have Hix : static_ok (S k) ix.
  by repeat split; simpl; auto; try lia; discriminate.
have HL' : Forall (static_ok (S k)) (ix :: L).
  apply: Forall_cons Hix _; apply: Forall_impl HL => p Hp.
  by apply: static_mono Hp _; lia.
have [_ Hz] := IHb ix (ix :: L) (S k) wP PScalar (bA (fresh k))
  (bW (VInfo k Integer None)) (bD (VInt z)) Real (VReal x)
  (HbA ix (pa ix)) (HbW ix (pw ix)) (HbD ix (pd ix)) HL' HtB Hbd.
exact: Hz Hv.
Qed.

Lemma owner_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  act_value (AMap loP hiP bP) -> act_owner (AMap loP hiP bP).
Proof.
move=> Ha L k c wP pp live ty tail eA eW eD ve o HA HW HD Hs Hlv Es Ho Hev.
move=> Hvr Hargs Hwr te Htc Htail.
have HL := s_static _ _ _ _ _ _ _ Hs.
have [Hht [Hz _]] := Ha L k wP pp tail eA eW eD te ve HA HW HD HL Htc Hev.
move/(_ Hvr): Hz => Hz.
case: eW HW Htc {Hlv} => [] // loW hiW bW HW.
move/map_typing=> [Epp [Etl [_ [h [_ [Ete [_ Hy]]]]]]]; subst pp tail te.
case: wP Hs Es Ho Hwr Hy => [[o' | |] |] // Hs Es Ho Hwr Hy.
rewrite /= in Ho.
case Ey: (vty (pw o')) Ho => [| | | ny] // [Eo]; subst o'.
have [Hni _] := Hy (pw o) erefl.
have [o'' [[<-] [HoL _]]] := s_written _ _ _ _ _ _ _ Hs _ erefl.
have [nm [r [Hvg Hw]]] := Hwr o erefl.
have Hav : avaried (pa o) = false.
  rewrite (Hargs o nm r HoL Hvg); move: (Hni nm r Hvg).
  by move: Hw; case: (r).
have [_ [_ [_ [_ [_ [_ [_ [_ [Hhto Hzo]]]]]]]]] := static_in _ _ _ HL HoL.
move/(_ Hav): Hzo => Hzo.
have Harr : is_array (vty (pw o)) by rewrite Ey.
have [Ety _] := s_top _ _ _ _ _ _ _ Hs o erefl erefl Harr.
rewrite Ey -(Htail erefl) in Ety; case: Ety => Ehn.
rewrite Ey in Hhto; case: (pd o) Hhto Hzo => [| | | lo |] //.
case: ve Hht Hz {Hev} => [| | | xs |] //= Hht Hz Hhto Hzo.
congr VArray; apply: zeros_eq; [exact/Forall_map | exact/Forall_map |].
by rewrite !length_map Hht Hhto Ehn.
Qed.

Lemma owner_ite (cP : atom pv) (tP eP : anf pv bare) : act_owner (AIte cP tP
  eP).
Proof. by []. Qed.

Lemma inplace_ite (cv : bool) (cP : atom pv) (tP eP : anf pv bare) :
  inplace_only cv (AIte cP tP eP).
Proof. by move=> L k wP pp tail eA eW te _ _ _ _ _ []. Qed.


(* Loops. *)
Lemma run_forback i lo hi b ss s l h :
  xev s lo = Some (VInt l) -> xev s hi = Some (VInt h) ->
  run (DForBack i lo hi b :: ss) s =
  match exec_down R (run b) (out_dvar nat i) (h - 1) (count l h) s with Some s1
    => run ss s1 | None => None end.
Proof. by rewrite /run /xev => /= -> ->. Qed.

(* A loop down from n - 1 to 0, by an invariant indexed by the next index. *)
Lemma exec_down_loop (body : store R -> option (store R)) (i : dvar nat) (N :
  nat) (P : nat -> store R -> Prop) :
  (forall j s, (j < N)%nat -> P (S j) s -> exists s', body (store_set s (KVar i)
    (VInt (Z.of_nat j))) = Some s' /\ P j s') ->
  forall n s, (n <= N)%nat -> P n s -> exists s', exec_down R body i (Z.of_nat n
    - 1) n s = Some s' /\ P 0%nat s'.
Proof.
move=> Hstep; elim=> [| n IH] s Hn Hp; cbn [exec_down]; first by exists s.
have -> : (Z.of_nat (S n) - 1)%Z = Z.of_nat n by lia.
have Hn' : (n < N)%nat by lia.
have [s1 [-> Hp1]] := Hstep n s Hn' Hp.
by apply: IH Hp1; lia.
Qed.

Lemma run_push s t x v l :
  store_get s (keyv x) = Some (VReal v) -> store_get s (keyv (TapeOf t)) = Some
    (VTape l) ->
  run [DPush (TapeOf t) (DVar x)] s = Some (store_set s (keyv (TapeOf t)) (VTape
    (v :: l))).
Proof. by rewrite /run /keyv /= => -> ->. Qed.

Lemma run_incr_bar s x n a b :
  barv s x = Some (VReal a) -> barv s n = Some (VReal b) ->
  run [DIncrement (DVar (BarOf x)) (DVar (BarOf n))] s = Some (store_set s (keyv
    (BarOf x)) (VReal (a + b))).
Proof. by rewrite /run /barv /keyv /= => -> ->. Qed.

(* The steps of a fold, from its trace. *)
Lemma fold_trace_step (ev : val (dual R) -> val (dual R) -> option (val (dual
  R))) z n st ve tr d :
  eval_fold ev z n st = Some ve -> fold_trace ev z n st = Some tr ->
  length tr = n /\ nth 0 (tr ++ [ve]) d = st /\
  forall jn, (jn < n)%nat -> ev (VInt (z + Z.of_nat jn)) (nth jn tr d) = Some
    (nth (S jn) (tr ++ [ve]) d).
Proof.
elim: n z st tr => [| n IH] z st tr; cbn [eval_fold fold_trace].
  by move=> [<-] [<-]; split=> //; split=> // jn Hj; lia.
case E: (ev (VInt z) st) => [st1 |] //= He.
case E1: (fold_trace ev (z + 1) n st1) => [tr1 |] // [<-].
have [Hl [H0 Hs]] := IH (z + 1)%Z st1 tr1 He E1.
split; first by rewrite /= Hl.
split=> // -[| jn] Hj /=.
  by rewrite Z.add_0_r E H0.
have -> : (z + Z.of_nat (S jn) = z + 1 + Z.of_nat jn)%Z by lia.
by apply: Hs; lia.
Qed.

Lemma fold_trace_exists (ev : val (dual R) -> val (dual R) -> option (val (dual
  R))) z n st ve :
  eval_fold ev z n st = Some ve -> exists tr, fold_trace ev z n st = Some tr.
Proof.
elim: n z st => [| n IH] z st; cbn [eval_fold fold_trace]; first by eauto.
case: (ev (VInt z) st) => [st1 |] //= He.
by have [tr ->] := IH (z + 1)%Z st1 He; eauto.
Qed.

(* A loop down from lo + n - 1 to lo, by an invariant indexed by the number of
  steps left. *)
Lemma exec_down_loop_from (body : store R -> option (store R)) (i : dvar nat)
  (lo : Z) (N : nat) (P : nat -> store R -> Prop) :
  (forall j s, (j < N)%nat -> P (S j) s -> exists s', body (store_set s (KVar i)
    (VInt (lo + Z.of_nat j))) = Some s' /\ P j s') ->
  forall n s, (n <= N)%nat -> P n s -> exists s', exec_down R body i (lo +
    Z.of_nat n - 1) n s = Some s' /\ P 0%nat s'.
Proof.
move=> Hstep; elim=> [| n IH] s Hn Hp; cbn [exec_down]; first by exists s.
have -> : (lo + Z.of_nat (S n) - 1)%Z = (lo + Z.of_nat n)%Z by lia.
have Hn' : (n < N)%nat by lia.
have [s1 [-> Hp1]] := Hstep n s Hn' Hp.
by apply: IH Hp1; lia.
Qed.

(* A loop up from z computing a fold, by an invariant on the state of the fold
   and the states before each step done. *)
Lemma fold_loop (ev : val (dual R) -> val (dual R) -> option (val (dual R)))
  (body : store R -> option (store R)) (i : dvar nat)
  (Inv : Z -> store R -> val (dual R) -> list (val (dual R)) -> Prop) :
  (forall z s st tr st', Inv z s st tr -> ev (VInt z) st = Some st' ->
     exists s', body (store_set s (KVar i) (VInt z)) = Some s' /\ Inv (z + 1)%Z
       s' st' (tr ++ [st])%list) ->
  forall n z s st tr ve, Inv z s st tr -> eval_fold ev z n st = Some ve ->
  exists s' tr', exec_up R body i z n s = Some s' /\ fold_trace ev z n st = Some
    tr' /\
                 Inv (z + Z.of_nat n)%Z s' ve (tr ++ tr')%list.
Proof.
move=> Hstep.
elim=> [| n IH] z s st tr ve Hinv; cbn [eval_fold exec_up fold_trace].
  by move=> [<-]; exists s, []; rewrite Z.add_0_r app_nil_r.
case E: (ev (VInt z) st) => [st1 |] //= Hev.
have [s1 [-> Hi1]] := Hstep z s st tr st1 Hinv E.
have [s' [tr' [He [-> Hi']]]] :=
  IH (z + 1)%Z s1 st1 (tr ++ [st])%list ve Hi1 Hev.
exists s', (st :: tr'); split=> //; split=> //.
have -> : (z + Z.of_nat (S n) = z + 1 + Z.of_nat n)%Z by lia.
by rewrite -app_assoc in Hi'.
Qed.

Lemma eval_map_nth (ev : val (dual R) -> option (val (dual R))) i n xs j d0 :
  eval_map ev i n = Some xs -> (j < n)%nat -> ev (VInt (i + Z.of_nat j)) = Some
    (VReal (nth j xs d0)).
Proof.
elim: n i xs j => [| n IH] i xs j H Hj; first lia.
move: H; cbn [eval_map].
case E: (ev (VInt i)) => [[x | | | |] |] //=.
case E1: (eval_map ev (i + 1)%Z n) => [xs1 |] // [<-].
case: j Hj => [| j] Hj /=; first by rewrite Z.add_0_r.
have -> : (i + Z.of_nat (S j) = i + 1 + Z.of_nat j)%Z by lia.
by apply: IH; [exact: E1 | lia].
Qed.

Lemma skipn_nth_cons {A : Type} (l : list A) j d :
  (j < length l)%nat -> skipn j l = nth j l d :: skipn (S j) l.
Proof.
by elim: j l => [| j IH] [| a l] /= H; try lia; auto; apply: IH; lia.
Qed.

Lemma dotl_zero_l l m : Forall (fun x => x = 0) l -> dotl l m = 0.
Proof.
move=> H; elim: H m => [| x l' Hx Hl IH] [| b m] //.
by rewrite dotl_cons IH Hx; ring.
Qed.

Lemma inner_tangent_zero v b : zero v -> inner (TangentCorrect.tangent v) b = 0.
Proof.
case: v => [d | | | l |] /= Hz; try by case: b => [[] |].
  by case: b => [[y | | | |] |] //=; rewrite Hz; ring.
case: b => [[| | | m |] |] //=.
by apply: dotl_zero_l; rewrite Forall_map.
Qed.

Lemma xev_at s a ix l z :
  store_get s (keyv a) = Some (VArray l) -> store_get s (keyv ix) = Some (VInt
    z) ->
  xev s (DAt (DVar a) (DVar ix)) = option_map VReal (nth_z z l).
Proof. by rewrite /xev /keyv /= => -> ->; case: (nth_z z l). Qed.

Lemma nth_z_of_nat {A : Type} (l : list A) j d : (j < length l)%nat -> nth_z
  (Z.of_nat j) l = Some (nth j l d).
Proof.
move=> H; rewrite /nth_z.
have -> : (Z.of_nat j <? 0)%Z = false by apply/Z.ltb_ge; lia.
by rewrite Nat2Z.id; apply: nth_error_nth'.
Qed.

(* Owners, without one of them. *)
Definition odel (O : owners) (n : dvar W) : owners :=
  filter (fun tm => if dvar_eq_dec_c (snd tm) n then false else true) O.

Lemma odel_in O n t m : In (t, m) (odel O n) <-> In (t, m) O /\ m <> n.
Proof.
by rewrite /odel filter_In /=; case: (dvar_eq_dec_c m n) => [E | NE] /=;
  intuition congruence.
Qed.

Lemma odel_snd O n m : In m (map snd (odel O n)) -> In m (map snd O) /\ m <> n.
Proof.
move=> /(in_map_iff _ _ _) [[t m'] [/= E Hi]]; subst m'.
move/odel_in: Hi => [Hi Hn]; split=> //.
by apply/(in_map_iff _ _ _); exists (t, m).
Qed.

Lemma odel_nodup O n : NoDup (map snd O) -> NoDup (map snd (odel O n)).
Proof.
elim: O => [| [t m] O IH] /=; first by constructor.
move=> /NoDup_cons_iff [Hm Hd]; rewrite /odel /=.
case: (dvar_eq_dec_c m n) => [E | Hne] /=; first exact: IH.
constructor; last exact: IH.
by move=> Hi; apply: Hm; case: (odel_snd O n m Hi).
Qed.

Lemma odel_notin O n : ~ In n (map snd O) -> odel O n = O.
Proof.
elim: O => [| [t m] O IH] H //; rewrite /odel /=.
case: (dvar_eq_dec_c m n) => [E | Hne] /=.
  by subst; exfalso; apply: H; left.
by congr (_ :: _); apply: IH => I; apply: H; right.
Qed.

Lemma pairing_odel O n t s :
  NoDup (map snd O) -> In (t, n) O -> pairing O s = pairing (odel O n) s + inner
    t (barv s n).
Proof.
elim: O => [| [t0 n0] O IH] //=.
move=> /NoDup_cons_iff [Hn Hd'] Hi; rewrite /odel /=.
case: (dvar_eq_dec_c n0 n) => [E | Hne] /=.
  subst n0; case: Hi => [[<-] | Hi]; last first.
    by exfalso; apply: Hn; apply/(in_map_iff _ _ _); exists (t, n).
  by rewrite -/(odel O n) odel_notin //=; ring.
case: Hi => [[_ E] | Hi]; first by congruence.
by rewrite /= -/(odel O n) (IH Hd' Hi); ring.
Qed.

Section Branch.
Variable cv : bool.

(* What the adjoint code of a body needs occurs in it. *)
Lemma needs_occurs :
  (forall bP : anf pv bare, forall G bA bW m k i,
     anf_eq (gA G) bP bA -> anf_eq (gW G) bP bW -> (forall q, In q G -> aid (pa
       q) = vid (pw q)) -> (i < k)%nat ->
     atom_member (AVar (AV i false)) (fst (needs cv m k bA)) || atom_member
       (AVar (AV i false)) (snd (needs cv m k bA)) = true ->
     occurs_anf i k bW = true) /\
  (forall eP : value pv bare, forall G eA eW k i,
     value_eq (gA G) eP eA -> value_eq (gW G) eP eW -> (forall q, In q G -> aid
       (pa q) = vid (pw q)) -> (i < k)%nat ->
     atom_member (AVar (AV i false)) (fst (value_needs cv k eA)) || atom_member
       (AVar (AV i false)) (snd (value_needs cv k eA)) = true ->
     occurs_value i k eW = true).
Proof.
apply anf_value_ind.
- move=> a e IHe b IHb G bA bW m k i.
  case: bA => [aA eA cA | ?]; case: bW => [aW eW cW | ?] //=.
  move=> [HeA HcA] [HeW HcW] Hid Hi Hn.
  set x1 := PV (let_binder k eA) (anon k) dummy_tvar (VInt 0%Z) 0.
  have Hid' : forall q, In q (x1 :: G) -> aid (pa q) = vid (pw q).
    by move=> q [<- | Hq] //; exact: Hid.
  have HiS : (i < S k)%nat by lia.
  have IHc := IHb x1 (x1 :: G) (cA (let_binder k eA)) (cW (anon k)) m (S k) i
    (HcA x1 _) (HcW x1 _) Hid' HiS.
  have Hval := IHe G eA eW k i HeA HeW Hid Hi.
  have Hat := (proj2 atoms_occurs) e G eA eW k i HeA HeW Hid Hi.
  case Eb: (needs cv m (S k) (cA (let_binder k eA))) Hn IHc
    => [ub lb] Hn /= IHc.
  case: (varied_value k eA && _) Hn => Hn;
    [case Ev: (value_needs cv k eA) Hval Hn => [rd fl] /= Hval Hn |];
    case: (atom_member (AVar (let_binder k eA)) lb || _) Hn => /= Hn;
    rewrite ?atom_member_union ?atom_member_remove_full /= in Hn;
    apply/orP; repeat case/orP: Hn => Hn; repeat case/andP: Hn => _ Hn;
    first [ by right; apply: IHc; rewrite Hn ?orb_true_r
          | by left; apply: Hval; rewrite Hn ?orb_true_r
          | by left; rewrite -Hat
          | by [] ].
- move=> x G [? ? ? | aA] [? ? ? | aW] //= m k i HA HW Hid _.
  rewrite -(atoms_atom G x aA aW i HA HW Hid).
  by case: (sweep_eqb m Forward && cv) => /=; rewrite ?orb_diag ?orb_false_r.
- move=> f x G [] // f1 a1 [] // f2 a2 k i [<- HA] [_ HW] Hid _ Hn.
  rewrite /= -(atoms_atom G x _ _ i HA HW Hid).
  cbn [value_needs fst snd] in Hn; case/orP: Hn => [Hn | //].
  exact: read_by1 Hn.
- move=> f x y G [] // f1 a1 b1 [] // f2 a2 b2 k i [<- [HA1 HA2]] [_ [HW1 HW2]].
  move=> Hid _ Hn; rewrite /= -(atoms_atom G x _ _ i HA1 HW1 Hid).
  rewrite -(atoms_atom G y _ _ i HA2 HW2 Hid).
  cbn [value_needs] in Hn; case: (comparison f) Hn => // Hn.
  exact: needs_op2 Hn.
- move=> x j G [] // a1 j1 [] // a2 j2 k i [HA1 HA2] [HW1 HW2] Hid _ Hn.
  rewrite /= -(atoms_atom G x _ _ i HA1 HW1 Hid).
  rewrite -(atoms_atom G j _ _ i HA2 HW2 Hid).
  by cbn [value_needs fst snd] in Hn; case/orP: Hn => ->; rewrite ?orb_true_r.
- move=> x j y G [] // a1 j1 y1 [] // a2 j2 y2 k i.
  move=> [HA1 [HA2 HA3]] [HW1 [HW2 HW3]] Hid _ Hn.
  rewrite /= -(atoms_atom G x _ _ i HA1 HW1 Hid).
  rewrite -(atoms_atom G j _ _ i HA2 HW2 Hid).
  rewrite -(atoms_atom G y _ _ i HA3 HW3 Hid).
  cbn [value_needs fst snd] in Hn.
  rewrite /= ?atom_member_union /= ?orb_false_r in Hn.
  by repeat case/orP: Hn => Hn; rewrite Hn ?orb_true_r.
- move=> c t IHt e IHe G [] // cA0 tA0 eA0 [] // cW0 tW0 eW0 k i.
  move=> HA HW Hid Hi Hn; rewrite /= in HA HW.
  case: HA HW => [HA1 [HA2 HA3]] [HW1 [HW2 HW3]].
  rewrite /= -(atoms_atom G c _ _ i HA1 HW1 Hid).
  have Ht := IHt G _ _ Replay k i HA2 HW2 Hid Hi.
  have He := IHe G _ _ Replay k i HA3 HW3 Hid Hi.
  cbn [value_needs] in Hn.
  case: (needs cv Replay k tA0) Hn Ht => [ut lt] Hn /= Ht.
  case: (needs cv Replay k eA0) Hn He => [ue le] Hn /= He.
  rewrite !atom_member_union in Hn; repeat case/orP: Hn => Hn;
    first [ by rewrite Hn
          | by rewrite Ht ?orb_true_r // Hn ?orb_true_r
          | by rewrite He ?orb_true_r // Hn ?orb_true_r ].
- move=> lo hi b IHb G [] // lA hA bA0 [] // lW hW bW0 k i HA HW Hid Hi Hn.
  rewrite /= in HA HW; case: HA HW => [HA1 [HA2 HA3]] [HW1 [HW2 HW3]].
  rewrite /= -(atoms_atom G lo _ _ i HA1 HW1 Hid).
  rewrite -(atoms_atom G hi _ _ i HA2 HW2 Hid).
  have Hid' : forall q, In q (opened k :: G) -> aid (pa q) = vid (pw q).
    by move=> q [<- | Hq] //; exact: Hid.
  have HiS : (i < S k)%nat by lia.
  have Hb := IHb (opened k) (opened k :: G) _ _ Replay (S k) i
    (HA3 _ _) (HW3 _ _) Hid' HiS.
  cbn [pa pw opened] in Hb; cbn [value_needs] in Hn.
  case: (needs cv Replay (S k) (bA0 (fresh k))) Hn Hb => [u l] Hn /= Hb.
  have Hki : k <> i by lia.
  rewrite /= ?atom_member_union ?atom_member_remove_full ?orb_false_r in Hn.
  rewrite (same_fresh _ _ Hki) /= in Hn.
  repeat case/orP: Hn => Hn;
    first [ by rewrite Hn ?orb_true_r
          | by rewrite Hb ?orb_true_r // Hn ?orb_true_r ].
move=> a lo hi init b IHb G [] // aA0 lA hA init0 b0 [] // aW0 lW hW initW bW0.
move=> k i HA HW Hid Hi Hn; rewrite /= in HA HW.
case: HA HW => [HA1 [HA2 [HA3 HA4]]] [HW1 [HW2 [HW3 HW4]]].
rewrite /= -(atoms_atom G lo _ _ i HA1 HW1 Hid).
rewrite -(atoms_atom G hi _ _ i HA2 HW2 Hid).
rewrite -(atoms_atom G init _ _ i HA3 HW3 Hid).
set sv := PV (snd (fold_binders k init0 b0)) (anon (S k)) dummy_tvar
  (VInt 0%Z) 0.
have Hid' : forall q, In q (sv :: opened k :: G) -> aid (pa q) = vid (pw q).
  by move=> q [<- | [<- | Hq]] //; exact: Hid.
have HiS : (i < S (S k))%nat by lia.
have Hb := IHb (opened k) sv (sv :: opened k :: G) _ _ Replay (S (S k)) i
  (HA4 _ _ _ _) (HW4 _ _ _ _) Hid' HiS.
cbn [value_needs] in Hn; rewrite /fold_binders in Hn.
rewrite /sv /fold_binders in Hb; cbn [fst snd pa pw opened] in Hb.
rewrite /fresh in Hb.
case: (needs cv Replay (S (S k))
        (b0 (AV k false) (AV (S k) (fold_varied k init0 b0)))) Hn Hb
  => [u l] Hn /= Hb.
rewrite /= ?atom_member_union ?atom_member_remove_full ?orb_false_r in Hn.
have Hki : k <> i by lia.
have E2 : same_term (AVar (AV (S k) (fold_varied k init0 b0)))
    (AVar (AV i false)) = false by apply/Nat.eqb_neq => /=; lia.
rewrite (same_fresh _ _ Hki) E2 /= in Hn.
repeat case/orP: Hn => Hn;
  first [ by rewrite Hn ?orb_true_r
        | by rewrite Hb ?orb_true_r // Hn ?orb_true_r ].
Qed.

(* The atoms of a value are variables that occur in it. *)
Lemma vatoms_live L k (eP : value pv bare) eA eW p :
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> Forall (static_ok k) L -> In
    p L ->
  vatoms k eA p -> live_value k eW p.
Proof.
move=> HA HW HL Hp; rewrite /vatoms /live_value atom_member_id.
have [Eid [Hk _]] := static_in _ _ _ HL Hp.
have Hid : forall q, In q L -> aid (pa q) = vid (pw q).
  by move=> q Hq; case: (static_in _ _ _ HL Hq).
by rewrite ((proj2 atoms_occurs) eP L eA eW k (aid (pa p)) HA HW Hid) ?Eid.
Qed.

Lemma live_vatoms L k (eP : value pv bare) eA eW p :
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> Forall (static_ok k) L -> In
    p L ->
  live_value k eW p -> vatoms k eA p.
Proof.
move=> HA HW HL Hp; rewrite /vatoms /live_value atom_member_id.
have [Eid [Hk _]] := static_in _ _ _ HL Hp.
have Hid : forall q, In q L -> aid (pa q) = vid (pw q).
  by move=> q Hq; case: (static_in _ _ _ HL Hq).
by rewrite ((proj2 atoms_occurs) eP L eA eW k (aid (pa p)) HA HW Hid) ?Eid.
Qed.

Lemma live_atoms L k (bP : anf pv bare) bA bW p :
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> Forall (static_ok k) L -> In p L
    ->
  live_anf k bW p -> atom_member (AVar (pa p)) (atoms_of_anf k bA) = true.
Proof.
move=> HA HW HL Hp; rewrite /live_anf atom_member_id.
have [Eid [Hk _]] := static_in _ _ _ HL Hp.
have Hid : forall q, In q L -> aid (pa q) = vid (pw q).
  by move=> q Hq; case: (static_in _ _ _ HL Hq).
by rewrite ((proj1 atoms_occurs) bP L bA bW k (aid (pa p)) HA HW Hid) ?Eid.
Qed.

(* The tape of the storage updated in place after a body: when it records, the
   element its last set overwrites is pushed. *)
Definition tape_step (r : bool) (zi : option Z) (st : val (dual R)) (t : option
  (val R)) : option (val R) :=
  if r then
    match zi, st, t with
    | Some z, VArray l, Some (VTape l0) =>
        Some (VTape (match nth_z z (map dfst l) with Some x => x | None => 0 end
          :: l0))
    | _, _, _ => t
    end
  else t.

(* Two versions of an array that differ at most at the index of a set. *)
Definition same_except (zi : option Z) (l0 l1 : list R) : Prop :=
  length l1 = length l0 /\ forall z, zi <> Some z -> nth_z z l1 = nth_z z l0.

Lemma replace_nth_other {A : Type} n n' (x : A) l l1 :
  replace_nth n x l = Some l1 -> n' <> n -> nth_error l1 n' = nth_error l n'.
Proof.
elim: n n' l l1 => [| n IH] n' [| y l] l1 //=.
  by move=> [<-]; case: n' => [| n'] //.
case E: (replace_nth n x l) => [l2 |] // [<-].
case: n' => [| n'] //= Hne.
by apply: (IH n' l l2 E); lia.
Qed.

Lemma replace_same_except z (y : R) l0 l1 : replace_nth_z z y l0 = Some l1 ->
  same_except (Some z) l0 l1.
Proof.
rewrite /replace_nth_z /same_except /nth_z; case Ez: (z <? 0)%Z => // H.
split; first exact: (replace_nth_length _ _ _ _ H).
move=> z' Hne; case Ez': (z' <? 0)%Z => //.
apply: (replace_nth_other _ _ _ _ _ H).
move: Ez Ez' => /Z.ltb_ge Ez /Z.ltb_ge Ez' E; apply: Hne; congr Some; lia.
Qed.

(* The bodies of in-place loops on the state st: operations and reads, then
   a set of the state or an in-place fold, that ends it, or the state itself,
   unchanged. *)
Fixpoint ibody (st : pv) (b : anf pv bare) : Prop :=
  match b with
  | ALet _ e b' =>
      match e with
      | AOp1 _ _ | AOp2 _ _ _ | AGet _ _ => forall x, ibody st (b' x)
      | ASet _ _ _ => forall x, b' x = ARet (AVar x)
      | AFold _ _ _ (AVar s) _ =>
          s = st /\ forall x, b' x = ARet (AVar x)
      | _ => False
      end
  | ARet (AVar y) => y = st
  | ARet _ => False
  end.

(* Whether the innermost fold of a body is live. *)
Definition tail_live (k : nat) (b : anf avar bare) : bool :=
  match tail_fold_live cv k b with Some l => l | None => false end.

Lemma tail_live_let k a eA cA :
  tail_live (S k) (cA (let_binder k eA)) = true ->
  tail_live k (ALet a eA cA) = true.
Proof.
rewrite /tail_live /=.
by case: eA => // ? ? ? ? ?; case: (cA _).
Qed.

Lemma owner_branch_none wP o : owner wP PBranch = Some o -> False.
Proof. by []. Qed.

Lemma owner_scalar_none wP o : owner wP PScalar = Some o -> False.
Proof. by []. Qed.

(* The forward sweep of a branch body: prim computes every let, then the
   value of the body, from the variables that occur in it. In the body of an
   in-place loop, the storage of the state gets the value of the body, and its
   tape the elements the step pushes, when the state is recorded or the
   innermost fold live. *)
Definition psim_body (bP : anf pv bare) : Prop :=
  forall L k c s wP pp m m' bA bW bT bD ty v,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq
    (gD L) bP bD ->
  actx L k c s wP pp (live_anf k bW) (live_anf k bW) ty ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  aeval (duals reals) bD = Some v ->
  (forall o, owner wP pp = Some o -> sweep_eqb m Forward && tail_live k bA =
    true ->
     exists l, store_get s (keyv (TapeOf (stored o))) = Some (VTape l)) ->
  let '((sb, x), c') :=
    open_pairs (prim W (option_map (amap pt) wP) m (rebuild _ bT
      (annotate_body_t cv m' k bA))) c in
  (c <= c')%nat /\
  exists s1, run sb s = Some s1 /\ fwd_frame c (inplace wP pp) None s s1 /\
    tkeep c (inplace wP pp) s s1 /\
    xev s1 x = Some (primal v) /\
    (forall o, owner wP pp = Some o -> ibody o bP ->
       store_get s1 (keyv (stored o)) = Some (primal v) /\
       (sweep_eqb m Forward && (trecorded (pt o) || tail_live k bA) = true ->
        tid (pt o) = None ->
        forall l0, store_get s (keyv (TapeOf (stored o))) = Some (VTape l0) ->
        store_get s1 (keyv (TapeOf (stored o))) =
          Some (VTape (rev (body_pushes bD (pd o)) ++ l0)))).

Lemma prim_let w m a e b :
  prim W w m (ALet a e b) =
  let '(vr, _, _) := let_ann a in
  with_storage w e b (fun n rec =>
    sbind (fwd_value W w m e (Transform.type_of e) n rec) (fun se =>
    sbind (prim W w m (b (open_let (Transform.type_of e) n vr rec))) (fun '(sb,
      x) => Done (app se sb, x)))).
Proof. by []. Qed.

Lemma psim_ret (aP : atom pv) : psim_body (ARet aP).
Proof.
move=> L k c s wP pp m m'
  [? ? ? | aA] [? ? ? | aW] [? ? ? | aT] [? ? ? | aD] //=.
move=> ty v /atom_graph [_ H] /atom_graph [-> _] /atom_graph [-> _].
move=> /atom_graph [-> _] Hc Htc Hev _.
split=> //; exists s; split=> //.
split; first by [].
split; first exact: tkeep_refl.
split; last first.
  move=> o _ Hib.
  case Ea: aP H Hev Hib => [y | ? | ?] // H Hev Eyo; subst y.
  case: Hev => <-; split; last by move=> _ _ l0 ->.
  apply: (a_store _ _ _ _ _ _ _ _ _ Hc o (H o erefl)).
  by rewrite Ea /live_anf /= Nat.eqb_refl.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
apply: (aspell_ok k s aP) Hev => p Ep; subst aP.
split; first exact: (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (H p erefl)).
apply: (a_store _ _ _ _ _ _ _ _ _ Hc p (H p erefl)).
by rewrite /live_anf /= Nat.eqb_refl.
Qed.

(* The let, its continuation simulated for the variables of the type of the
   value only. *)
Lemma psim_let_typed a (eP : value pv bare) (cP : pv -> anf pv bare) :
  asim_fwd cv eP -> act_value eP ->
  (forall wP tail, storage wP tail eP = None) ->
  (forall a0 i0 y0, eP <> ASet a0 i0 y0) ->
  (forall x, Some (vty (pw x)) = ptype eP -> psim_body (cP x)) ->
  psim_body (ALet a eP cP).
Proof.
move=> IHf IHa Hsn Hns IHb L k c s wP pp m m'.
move=> [aA eA cA | ?] [aW eW cW | ?] [aT eT cT | ?] [aD eD cD | ?] ty v;
  move=> HA HW HT HD Hc Htc Hev Htp0; rewrite /= in HA HW HT HD; try by [].
case: HA HW HT HD => [HeA HcA] [HeW HcW] [HeT HcT] [HeD HcD].
rewrite /= in Htc Hev.
case Hte: (typecheck_value (option_map (amap pw) wP) (wplace pp)
  (WellFormed.is_tail cW k) k eW) Htc => [te []] // Htc.
case Hve: (aeval_value (duals reals) eD) Hev => [ve |] // Hev.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have HL := s_static _ _ _ _ _ _ _ Hs.
cbn [annotate_body_t].
case Hneeds: (needs cv m' (S k) (cA (let_binder k eA))) => [u l].
set vr := varied_value k eA; set vt := annotate_value_t cv k eA.
set rest := annotate_body_t cv m' (S k) (cA (let_binder k eA)).
cbn [rebuild]; rewrite prim_let; cbv [let_ann].
rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW HeT HL Hte).
set Kf := (X in with_storage _ _ _ X).
have Hwr : forall a0, wP = Some a0 -> exists y, a0 = AVar y /\ In y L.
  by move=> a0 /(s_written _ _ _ _ _ _ _ Hs) [y [-> [Hy _]]]; exists y.
have [n [rec [c0 [Hopen Hn]]]] := open_with_storage' L k wP eP eT vt
  (fun v0 => rebuild _ (cT v0) rest) Kf c HeT HL Hwr.
rewrite Hopen; rewrite /= in Htc.
have Hst : forall p, In p L -> (vid (pw p) < k)%nat /\ tid (pt p) <> Some 0%nat.
  by move=> p Hp; have [_ [H1 [_ [_ [_ [_ [H2 _]]]]]]] := static_in _ _ _ HL Hp.
rewrite -(is_tail_transfer L k cP cW cT rest HcW HcT Hst) in Hn.
set tail := WellFormed.is_tail cW k in Hte Hn.
have Htail_ty : tail = true -> te = ty.
  move=> Ht.
  have [_ E] :=
    tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL erefl Ht.
  by rewrite E /= in Htc; case: Htc.
have Es := Hsn wP tail; rewrite Es in Hn; case: Hn => En [Ec0 Erec].
subst n c0 rec.
rewrite /Kf open_pairs_sbind.
case Hfe: (open_pairs (fwd_value _ _ _ _ _ _ _) (S c)) => [se c1].
rewrite open_pairs_sbind.
case Hob: (open_pairs (prim _ _ _ _) c1) => [[sb xb] c2].
cbn [open_pairs].
have Hc01 : (S c <= c1)%nat.
  by rewrite -[c1]/(snd (se, c1)) -Hfe; exact: open_pairs_mono.
have Haid := aids_below L k HL.
have Hlv_e : forall p, live_value k eW p -> live_anf k (ALet aW eW cW) p.
  by move=> p; rewrite /live_value /live_anf /= => ->.
have [Hht [Hz Hra]] := IHa L k wP pp tail eA eW eD te ve HeA HeW HeD HL Hte Hve.
have Hnotin : forall p, In p L -> stored p <> DBound (c, c).
  move=> p Hp; rewrite /stored => -[E].
  by have := s_num _ _ _ _ _ _ _ Hs p Hp; lia.
set x := PV (let_binder k eA) (VInfo k te None)
  (open_let te (DBound (c, c)) vr false) ve c.
have Hx : aid (pa x) = k by [].
have HxL : ~ In x L := fresh_notin L k x Haid Hx.
(* the forward sweep of the value *)
have Hc1 : actx L k (S c) s wP pp (live_value k eW) (vatoms k eA) ty.
  apply: (actx_weaken _ _ _ _ _ _ _ _ _ _ _ _ Hc Hlv_e); last by lia.
  by move=> p Hp Hv; apply: Hlv_e; exact: vatoms_live HeA HeW HL Hp Hv.
have Hj1 : exists j, DBound (c, c) = DBound (j, j) /\ (j < S c)%nat.
  by exists c; split; [by [] | lia].
have Hst1 : match storage wP tail eP return Prop with
    | Some m0 => DBound (c, c) = m0
    | None => forall p, In p L -> stored p <> DBound (c, c) end.
  by rewrite Es.
have Hr1 : false = true \/ (m = Forward /\ records cv k eA = true /\
    storage wP tail eP <> None /\ ~ not_in_loop pp) ->
    exists l0, store_get s (keyv (TapeOf (DBound (c, c)))) = Some (VTape l0).
  by move=> [// | [_ [_ [Hs' _]]]]; case: (Hs' Es).
have IH := IHf L k (S c) s wP pp tail eA eW eT eD te (DBound (c, c)) ve ty m
  false HeA HeW HeT HeD Hc1 Hte Htail_ty Hj1 Hst1 Hr1 Hve.
cbv zeta in IH; rewrite -/vt Hfe in IH.
case: IH => _ [se1 [R1 [F1 [T1 [S1 _]]]]].
(* the rest of the body, with x in scope *)
have Hlive_c : forall p, In p L -> live_anf (S k) (cW (VInfo k te None)) p ->
    live_anf k (ALet aW eW cW) p.
  move=> p Hp; rewrite /live_anf.
  rewrite (live_cont L k cP cW x (VInfo k te None) _ HcW HL Hx erefl) /= => ->.
  by rewrite orb_true_r.
have Hold : forall p, In p L ->
    store_get se1 (keyv (stored p)) = store_get s (keyv (stored p)).
  move=> p Hp; have Hn := s_num _ _ _ _ _ _ _ Hs p Hp.
  apply: F1; [by rewrite /stored /=; lia | by [] | by rewrite /=; tauto | |].
    by move=> E; apply: (Hnotin p Hp); congruence.
  by [].
have Hxs : static_ok (S k) x.
  by repeat split; simpl; auto; try lia; discriminate.
have Hs' : sctx (x :: L) (S k) (S c) wP pp
    (live_anf (S k) (cW (VInfo k te None))) ty.
  constructor.
  - apply: Forall_cons Hxs _; apply: Forall_impl HL => p Hp.
    by apply: static_mono Hp _; lia.
  - move=> p q [<- | Hp] [<- | Hq] E //.
    + have := Haid _ Hq; have [E' _] := static_in _ _ _ HL Hq.
      by rewrite /= in E; lia.
    + have := Haid _ Hp; have [E' _] := static_in _ _ _ HL Hp.
      by rewrite /= in E; lia.
    exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
  - move=> p [<- | Hp] /=; first lia.
    by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
  - move=> a0 /(s_written _ _ _ _ _ _ _ Hs) [y [-> [Hy Hv]]].
    by exists y; split=> //; split; [right | ].
  - move: (s_place _ _ _ _ _ _ _ Hs); case: (pp) => //= ix sx [A [B C]].
    by split; [right | split; [right |]].
  - move=> o p Ho [<- | Hp] Ep.
      have := s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho).
      by rewrite /= in Ep; lia.
    case: (s_owner _ _ _ _ _ _ _ Hs o p Ho Hp Ep) => [H | H]; first by left.
    by right=> Hl; apply/H/Hlive_c.
  - move=> p o [<- | Hp] Lp Ha Hg Ho.
      have [_ [o' [Ho' Es']]] := inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW
        Hte Htail_ty (or_intror Ha).
      by rewrite Es in Es'.
    exact: (s_arrays _ _ _ _ _ _ _ Hs p o Hp (Hlive_c _ Hp Lp) Ha Hg Ho).
  - exact: (s_ty _ _ _ _ _ _ _ Hs).
  move=> y Hpp Hw Ha.
  have [T1' T2'] := s_top _ _ _ _ _ _ _ Hs y Hpp Hw Ha.
  have [y' [[<-] [Hy _]]] := s_written _ _ _ _ _ _ _ Hs _ Hw.
  by split=> // Ly; apply/T2'/Hlive_c.
have Hc' : actx (x :: L) (S k) c1 se1 wP pp
    (live_anf (S k) (cW (VInfo k te None)))
    (live_anf (S k) (cW (VInfo k te None))) ty.
  constructor.
  - exact: (sctx_weaken _ _ _ _ _ _ _ _ _ Hs' (fun p H => H) Hc01).
  - by move=> p [<- | Hp] //; exact: (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp).
  - move=> p [<- | Hp] Hl; first exact: S1.
    rewrite Hold //; apply: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp).
    exact: Hlive_c.
  - move=> p [<- | Hp] Hr //.
    have [lt Hlt] := a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr.
    exact: (proj1 T1 _ _ Hlt).
  - move=> o Ho Hor; have HoL := owner_in_s _ _ _ _ _ _ _ _ Hs Ho.
    rewrite Hold //; apply: (a_owner _ _ _ _ _ _ _ _ _ Hc o Ho).
    by case: Hor => [Hl | Ht]; [left | right; exact: Hlive_c].
  exact: (a_tid _ _ _ _ _ _ _ _ _ Hc).
have Htp1 : forall o, owner wP pp = Some o ->
    sweep_eqb m Forward && tail_live (S k) (cA (pa x)) = true ->
    exists l, store_get se1 (keyv (TapeOf (stored o))) = Some (VTape l).
  move=> o Ho /andP [Hm Ht].
  have [lt Hlt] := Htp0 o Ho (introT andP (conj Hm (tail_live_let _ _ _ _ Ht))).
  exact: (proj1 T1 _ _ Hlt).
have Hxt : Some (vty (pw x)) = ptype eP.
  by rewrite (ptype_ok _ _ _ _ _ _ _ _ HeW Hte).
have IH := IHb x Hxt (x :: L) (S k) c1 se1 wP pp m m' (cA (pa x)) (cW (pw x))
  (cT (pt x)) (cD (pd x)) ty v (HcA x _) (HcW x _) (HcT x _) (HcD x _)
  Hc' Htc Hev Htp1.
rewrite /x in IH; cbn [pt pa pd pw] in IH; rewrite -/rest Hob in IH.
case: IH => Hc12 [s1 [Rb [Fb [Tb Vb]]]].
have Hcc1 : (c <= c1)%nat by lia.
split; first lia.
exists s1; split; first by rewrite run_app R1.
split.
  move=> v0 Hb0 Hc0 Ht0 Hex _.
  rewrite (Fb v0 (below_mono c c1 v0 Hb0 Hcc1) Hc0 Ht0 Hex) //.
  have HcS : (c <= S c)%nat by lia.
  apply: F1; [exact: below_mono Hb0 HcS | by [] | by [] | | by []].
  by case=> E; subst v0; rewrite /= in Hb0; lia.
split.
  apply: tkeep_trans (tkeep_mono _ _ _ _ _ Tb Hcc1).
  apply: (tkeep_fresh c (S c) _ (inplace wP pp) _ _ T1 _
    (Nat.le_succ_diag_r c)).
  by rewrite /=; lia.
case: Vb => Vx Vt; split; first exact: Vx.
move=> o Ho Hib.
have HoL := owner_in_s _ _ _ _ _ _ _ _ Hs Ho.
have [Hibc [Ebp Etl]] : ibody o (cP x) /\
    body_pushes (ALet aD eD cD) (pd o) = body_pushes (cD ve) (pd o) /\
    tail_live k (ALet aA eA cA) = tail_live (S k) (cA (let_binder k eA)).
  move: Hib HeA HeD Hve Hns Hsn; case Ee: eP =>
    [f0 a0 | f0 a0 b0 | a0 i0 | a0 i0 y0 | ? ? ? | ? ? ? | ? ? ? i0 ?] //=
    Hib HeA HeD Hve Hns Hsn.
  - split; first exact: Hib.
    case Ea: eA HeA => // [? ?] _; case Ed: eD HeD Hve => // [? ?] _ Ev.
    by move: Ev; rewrite /= => ->.
  - split; first exact: Hib.
    case Ea: eA HeA => // [? ? ?] _.
    case Ed: eD HeD Hve => // [? ? ?] _ Ev.
    by move: Ev; rewrite /= => ->.
  - split; first exact: Hib.
    case Ea: eA HeA => // [? ?] _; case Ed: eD HeD Hve => // [? ?] _ Ev.
    by move: Ev; rewrite /= => ->.
  - by case: (Hns _ _ _ erefl).
  case Ei: i0 Hib Hsn => [q | ? | ?] // [Eq _] Hsn; subst q.
  have Hqa := owner_array _ _ _ _ _ _ _ _ Hs Ho.
  by move: (Hsn wP tail); rewrite /=; case: (vty (pw o)) Hqa.
have [Vt1 Vt2] := Vt o Ho Hibc.
split; first exact: Vt1.
move=> Hcnd Htid l0 E0; rewrite Ebp; apply: Vt2 => //; first by rewrite -Etl.
rewrite -E0.
have Hno := s_num _ _ _ _ _ _ _ Hs o HoL.
apply: (proj2 T1); [by rewrite /stored /=; lia | by [] |].
by move=> E; have := Hnotin o HoL; congruence.
Qed.

Lemma psim_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  asim_fwd cv eP -> act_value eP -> (forall wP tail, storage wP tail eP = None)
    ->
  (forall a0 i0 y0, eP <> ASet a0 i0 y0) -> (forall x, psim_body (cP x)) ->
  psim_body (ALet a eP cP).
Proof. by move=> *; apply: psim_let_typed => // x _. Qed.


(* The set that ends the body of an in-place loop: it updates the state in
   place, pushing the element it overwrites when the state is recorded. *)
Lemma psim_set_let a (aP iP vP : atom pv) (cP : pv -> anf pv bare) : psim_body
  (ALet a (ASet aP iP vP) cP).
Proof.
move=> L k c s wP pp m m'.
move=> [aA eA cA | ?] [aW eW cW | ?] [aT eT cT | ?] [aD eD cD | ?] ty v;
  move=> HA HW HT HD Hc Htc Hev _; rewrite /= in HA HW HT HD; try by [].
case: HA HW HT HD => [HeA HcA] [HeW HcW] [HeT HcT] [HeD HcD].
case: eA HeA => // a1 i1 y1 HeA; rewrite /= in HeA.
case: HeA => /atom_graph [Ea1 HaL]
  [/atom_graph [Ei1 HiL] /atom_graph [Ey1 HvL]].
case: eW HeW Htc Hc => // a2 i2 y2 HeW Htc Hc; rewrite /= in HeW.
case: HeW => /atom_graph [Ea2 _] [/atom_graph [Ei2 _] /atom_graph [Ey2 _]].
case: eT HeT => // a3 i3 y3 HeT; rewrite /= in HeT.
case: HeT => /atom_graph [Ea3 _] [/atom_graph [Ei3 _] /atom_graph [Ey3 _]].
case: eD HeD Hev => // a4 i4 y4 HeD Hev; rewrite /= in HeD.
case: HeD => /atom_graph [Ea4 _] [/atom_graph [Ei4 _] /atom_graph [Ey4 _]].
subst a1 i1 y1 a2 i2 y2 a3 i3 y3 a4 i4 y4.
rewrite /= in Htc Hev.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have HL := s_static _ _ _ _ _ _ _ Hs.
case: pp Hc Hs Htc => [| | | ix sx] // Hc Hs Htc.
case: aP HaL Hc Hs Htc Hev => [q | ? | ?] // HaL Hc Hs Htc Hev.
rewrite /= in Htc.
case Eq: (vty (pw q)) Htc => [| | | nq] // Htc.
set cnd := (X in if X then Some nq else None) in Htc.
case Ecd: cnd Htc => // Htc; rewrite /cnd in Ecd; clear cnd.
move/andP: Ecd => [/andP [/andP [Etl /Nat.eqb_eq Esx] Ev] Eidx].
have HqL : In q L by exact: HaL.
have Hsx : In sx L by exact: (proj1 (proj2 (s_place _ _ _ _ _ _ _ Hs))).
have Eqs : q = sx by exact: (s_unique _ _ _ _ _ _ _ Hs _ _ HqL Hsx Esx).
subst q; clear HqL Esx.
have Haid := aids_below L k HL.
cbn [amap aeval_atom] in Hev.
case Epd: (pd sx) Hev => [| | | l |] // Hev.
case Hi: (aeval_atom (duals reals) (amap pd iP)) Hev => [[| z | | |] |] // Hev.
case Hv: (aeval_atom (duals reals) (amap pd vP)) Hev
  => [[[y dy] | | | |] |] // Hev.
case Er: (replace_nth_z z (Dual y dy) l) Hev => [l1 |] // Hev.
rewrite /= in Hev.
set vr := varied_value k (ASet (amap pa (AVar sx)) (amap pa iP) (amap pa vP)).
set rec := trecorded (pt sx).
set x := PV (let_binder k (ASet (amap pa (AVar sx)) (amap pa iP) (amap pa vP)))
  (VInfo k (Array nq) None) (open_let (Array nq) (stored sx) vr rec)
  (VArray l1) (pn sx).
have Hx : aid (pa x) = k by [].
have HxL := fresh_notin L k x Haid Hx.
have [Hcx EW] := tail_cont L k cP cW x (VInfo k (Array nq) None) HcW HL Hx Etl.
have ED : cD (pd x) = ARet (AVar (pd x)).
  have := HcD x (pd x); rewrite Hcx.
  case: (cD (pd x)) => [? ? ? | [t' | |]] //=.
  by case=> [[->] | /in_gD [I _]].
rewrite /= in ED; rewrite ED /= in Hev; case: Hev => <-.
rewrite EW /= in Htc; case: Htc => Ety; subst ty.
have ET : cT (pt x) = ARet (AVar (pt x)).
  have := HcT x (pt x); rewrite Hcx.
  case: (cT (pt x)) => [? ? ? | [t' | |]] //=.
  by case=> [[->] | /in_gT [I _]].
have EA : cA (pa x) = ARet (AVar (pa x)).
  have := HcA x (pa x); rewrite Hcx.
  case: (cA (pa x)) => [? ? ? | [t' | |]] //=.
  by case=> [[->] | /in_gA [I _]].
have [_ [_ [Hstq [Htyq _]]]] := static_in _ _ _ HL Hsx.
cbn [annotate_body_t].
case Hneeds: (needs cv m' (S k) _) => [u0 l0].
cbn [rebuild]; rewrite prim_let; cbv [let_ann].
cbn [amap rebuild_value with_storage Transform.type_of tof].
rewrite Htyq Eq Hstq.
change (open_let (Array nq) (stored sx)
  (varied_value k (ASet (AVar (pa sx)) (amap pa iP) (amap pa vP)))
  (trecorded (pt sx))) with (pt x).
change (let_binder k (ASet (AVar (pa sx)) (amap pa iP) (amap pa vP)))
  with (pa x).
rewrite ET EA.
cbn [annotate_body_t rebuild prim fwd_value sbind open_pairs spell].
have Hlive : forall p, In p L ->
    (AVar sx = AVar p \/ iP = AVar p \/ vP = AVar p) ->
    live_anf k (ALet aW (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) cW)
      p.
  move=> p Hp; rewrite /live_anf /= => -[[<-] | [-> | ->]] /=;
    by rewrite Nat.eqb_refl /= ?orb_true_r.
have Hops : forall aP0, (aP0 = iP \/ aP0 = vP) -> forall p, aP0 = AVar p ->
    static_ok k p /\ store_get s (keyv (stored p)) = Some (primal (pd p)).
  move=> aP0 HaP p E.
  have Hp : In p L by case: HaP E => -> E; [exact: HiL | exact: HvL].
  split; first exact: (static_in _ _ _ HL Hp).
  apply: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp); apply: Hlive => //.
  by case: HaP E => -> E; auto.
have Hsi := aspell_ok k s iP _ (Hops iP (or_introl erefl)) Hi.
have Hsv := aspell_ok k s vP _ (Hops vP (or_intror erefl)) Hv.
have Hsti : forall p, iP = AVar p -> static_ok k p.
  by move=> p E; case: (Hops iP (or_introl erefl) p E).
have Hstv : forall p, vP = AVar p -> static_ok k p.
  by move=> p E; case: (Hops vP (or_intror erefl) p E).
have Hq : store_get s (keyv (stored sx)) = Some (VArray (map dfst l)).
  have Hlq := Hlive sx Hsx (or_introl erefl).
  by rewrite (a_owner _ _ _ _ _ _ _ _ _ Hc sx erefl (or_intror Hlq)) Epd.
have Esi :
    set_index (ALet aD (ASet (AVar (pd sx)) (amap pd iP) (amap pd vP)) cD)
    = Some z.
  have Hval : aeval_value (duals reals)
      (ASet (AVar (pd sx)) (amap pd iP) (amap pd vP)
       : value (val (dual R)) bare)
      = Some (VArray l1).
    by rewrite /= Epd Hi Hv /= Er.
  by rewrite /set_index Hval ED -/set_index Hi.
have Hm := replace_nth_z_map dfst z (Dual y dy) l; rewrite Er /= in Hm.
have Hassign : forall s0,
    store_get s0 (keyv (stored sx)) = Some (VArray (map dfst l)) ->
    xev s0 (spell (amap pt iP)) = Some (VInt z) ->
    xev s0 (spell (amap pt vP)) = Some (VReal y) ->
    run [DAssign (DAt (DVar (stored sx)) (spell (amap pt iP)))
      (spell (amap pt vP))] s0 =
    Some (store_set s0 (keyv (stored sx)) (VArray (map dfst l1))).
  move=> s0 G1 G2 G3.
  exact: (run_assign_at s0 (stored sx) _ _ (map dfst l) z y (map dfst l1)
    G1 G2 G3 Hm).
have Hcn : consistent (stored sx) by [].
change (tstored (pt x)) with (stored sx).
case Erec: (sweep_eqb m Forward && trecorded (pt sx));
  cbn [sbind open_pairs]; (split; first lia).
  (* recorded: the element overwritten is pushed first *)
  have Erec0 := Erec; move/andP: Erec => [_ Erec'].
  have [lt Hlt] := a_tape _ _ _ _ _ _ _ _ _ Hc sx Hsx Erec'.
  have [old Hold] := replace_nth_z_nth _ _ _ _ Er.
  set s0 := store_set s (keyv (TapeOf (stored sx))) (VTape (dfst old :: lt)).
  have Hn0 : store_get s0 (keyv (stored sx)) = Some (VArray (map dfst l)).
    by rewrite /s0 store_get_set_other.
  exists (store_set s0 (keyv (stored sx)) (VArray (map dfst l1))); split.
    rewrite app_nil_r -[[_; _]]/([_] ++ [_]) run_app.
    have -> : run [DPush (TapeOf (stored sx))
        (DAt (DVar (stored sx)) (spell (amap pt iP)))] s = Some s0.
      move: Hq Hsi Hlt; rewrite /keyv /xev => Hq' Hsi' Hlt'.
      by rewrite /run /= Hq' /= Hsi' /= nth_z_map Hold /= Hlt'.
    apply: Hassign => //.
      by rewrite /s0 xev_set_other //; exact: (avoid_tape_spell k).
    by rewrite /s0 xev_set_other //; exact: (avoid_tape_spell k).
  split.
    move=> v0 Hb Hcv Ht Hex _.
    rewrite store_get_set_other.
      by move=> /(keyv_inj _ _ Hcn Hcv) E; subst v0; apply: Hex.
    rewrite /s0 store_get_set_other //.
    have Hct : consistent (TapeOf (stored sx)) by [].
    by move=> /(keyv_inj _ _ Hct Hcv) E; subst v0; apply: Ht.
  split.
    apply: (tkeep_trans _ _ _ s0).
      by apply: tkeep_set_tape => //; right.
    by apply: tkeep_set => //=; tauto.
  split; first exact: store_get_set_same.
  move=> o [<-] _.
  split; first exact: store_get_set_same.
  move=> _ _ t0; rewrite Hlt => -[<-].
  rewrite store_get_set_other // /s0 store_get_set_same.
  have Ebp : body_pushes
      (ALet aD (ASet (AVar (pd sx)) (amap pd iP) (amap pd vP)) cD) (pd sx) =
      [dfst old].
    have Hval : aeval_value (duals reals)
        (ASet (AVar (pd sx)) (amap pd iP) (amap pd vP)
         : value (val (dual R)) bare) = Some (VArray l1).
      by rewrite /= Epd Hi Hv /= Er.
    rewrite /body_pushes Hval ED -/body_pushes Hi Epd.
    by rewrite nth_z_map Hold.
  by rewrite Ebp.
exists (store_set s (keyv (stored sx)) (VArray (map dfst l1))); split.
  by rewrite app_nil_r; apply: Hassign.
split.
  move=> v0 Hb Hcv Ht Hex _; apply: store_get_set_other.
  by move=> /(keyv_inj _ _ Hcn Hcv) E; subst v0; apply: Hex.
split; first by apply: tkeep_set => //=; tauto.
split; first exact: store_get_set_same.
move=> o [<-] _.
split; first exact: store_get_set_same.
move=> Hcnd; exfalso; move: Hcnd.
have Etv : tail_live k
    (ALet aA (ASet (AVar (pa sx)) (amap pa iP) (amap pa vP)) cA) = false.
  by rewrite /tail_live /=; change (cA _) with (cA (pa x)); rewrite EA.
by rewrite Etv orb_false_r Erec.
Qed.

(* The body of an in-place loop: operations and reads, then a set of the
   state that ends it. *)
Fixpoint abody (b : anf pv bare) : Prop :=
  match b with
  | ALet _ e b' =>
      match e with
      | AOp1 _ _ | AOp2 _ _ _ | AGet _ _ => forall x, abody (b' x)
      | ASet _ _ _ => forall x, b' x = ARet (AVar x)
      | _ => False
      end
  | ARet _ => False
  end.

Lemma abody_straight b : abody b -> straight b.
Proof.
elim: b => [a e b' IH | x] //=.
case: e => // [? ? | ? ? ? | ? ? | ? ? ?] Hb; split=> // x.
- exact/IH/Hb.
- exact/IH/Hb.
- exact/IH/Hb.
by rewrite (Hb x).
Qed.

(* A branch body sits in place PBranch, where nothing is updated in place. *)
Lemma sctx_branch L k c wP pp (live live' : pv -> Prop) ty :
  sctx L k c wP pp live ty -> (forall p, live' p -> live p) -> sctx L k c wP
    PBranch live' Real.
Proof.
by case=> *; constructor; auto; rewrite /=; try (move=> *; discriminate).
Qed.

(* The forward sweep of a branch: the result is a real variable, assigned by
   the branch taken after its statements. *)
Lemma afwd_ite (cP : atom pv) (tP eP : anf pv bare) :
  psim_body tP -> psim_body eP -> asim_fwd cv (AIte cP tP eP).
Proof.
move=> IHt IHe.
fwd_intro.
rewrite /= in Htc Hev Hst *.
rename t into tA, e into eA, t0 into tW, e0 into eW, t1 into tT, e1 into eT,
  t2 into tD, e2 into eD.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have HL := s_static _ _ _ _ _ _ _ Hs.
(* typing *)
set X := (if ty_eqb _ _ then _ else _) in Htc.
have {}Htc : X = (te, Ok) by case: (wplace pp) Htc.
rewrite /X {X} in Htc.
case Ecb: (ty_eqb (of_atom (amap pw cP)) Boolean) Htc => //.
case HtW: (typecheck (option_map (amap pw) wP) InBranch k tW) => [t3 [] ] /=;
  last by case: (typecheck _ _ k eW).
case HeW: (typecheck (option_map (amap pw) wP) InBranch k eW) => [t4 [] ] //=.
case E3: (ty_eqb t3 Real); case E4: (ty_eqb t4 Real) => //= -[Ete].
subst te.
move/ty_eqb_true: E3 HtW => -> HtW; move/ty_eqb_true: E4 HeW => -> HeW.
(* the condition *)
case Hcd: (aeval_atom (duals reals) (amap pd cP)) Hev => [[| | b | |] |] // Hev.
have Hcs : forall p, cP = AVar p ->
    static_ok k p /\ store_get s (keyv (stored p)) = Some (primal (pd p)).
  move=> p Ep; split; first exact: (static_in _ _ _ HL (H p Ep)).
  apply: (a_store _ _ _ _ _ _ _ _ _ Hc p (H p Ep)); subst cP.
  by rewrite /vatoms /= !atom_member_union /= Nat.eqb_refl.
have Hsc := aspell_ok k s cP _ Hcs Hcd; rewrite /= in Hsc.
(* the two bodies, opened *)
rewrite open_pairs_sbind.
case Hot: (open_pairs (prim _ _ _ (rebuild _ tT _)) c) => [[st vt] c1].
rewrite open_pairs_sbind.
case Hoe: (open_pairs (prim _ _ _ (rebuild _ eT _)) c1) => [[se' ve'] c2].
have M1 : (c <= c1)%nat.
  by rewrite -[c1]/(snd (st, vt, c1)) -Hot; exact: open_pairs_mono.
have M2 : (c1 <= c2)%nat.
  by rewrite -[c2]/(snd (se', ve', c2)) -Hoe; exact: open_pairs_mono.
cbn [open_pairs].
set n := DBound (j, j) in Hst Hrec *.
set s0 := store_set s (keyv n) (VReal 0%R).
have Hcn0 : consistent n by [].
have Hnp : forall p, In p L -> keyv n <> keyv (stored p).
  move=> p Hp K; have Hcp : consistent (stored p) by [].
  exact: (Hst p Hp (esym (keyv_inj _ _ Hcn0 Hcp K))).
have Hcn : forall p, cP = AVar p -> static_ok k p /\ pn p <> j.
  move=> p E; split; first exact: (proj1 (Hcs p E)).
  by move=> Ej'; apply: (Hst p (H p E)); rewrite /stored /n Ej'.
have [C1 _] := avoid_spell k cP j Hcn.
have Hsc0 : xev s0 (spell (amap pt cP)) = Some (VBool b).
  by rewrite /s0 xev_set_other.
(* the branch taken *)
have Hctx : forall bW,
    (forall p, live_anf k bW p -> live_value k (AIte (amap pw cP) tW eW) p) ->
    (forall p, In p L -> live_anf k bW p ->
       vatoms k (AIte (amap pa cP) tA eA) p) ->
    forall c', (c <= c')%nat ->
    actx L k c' s0 wP PBranch (live_anf k bW) (live_anf k bW) Real.
  move=> bW Hl Ha c' Hcc; constructor.
  - exact: (sctx_weaken _ _ _ _ _ _ _ _ _ (sctx_branch _ _ _ _ _ _ _ _ Hs Hl)
      (fun p H0 => H0) Hcc).
  - exact: (a_bar _ _ _ _ _ _ _ _ _ Hc).
  - move=> p Hp Hl'; rewrite /s0 store_get_set_other; first exact: Hnp.
    exact: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp (Ha p Hp Hl')).
  - move=> p Hp Hr; have [lt Hlt] := a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr.
    by exists lt; rewrite /s0 store_get_set_other.
  - by [].
  by [].
have Hbody : exists (sb : list (dstmt W)) (vb : dexpr W) (s1 : store R)
    (vv : val (dual R)),
    run sb s0 = Some s1 /\ fwd_frame c None None s0 s1 /\
    tkeep c None s0 s1 /\ xev s1 vb = Some (primal vv) /\ ve = vv /\
    (if b then st else se') = sb /\ (if b then vt else ve') = vb.
  case: b Hev {Hsc Hsc0 Hcd} => Hev.
    have Hl : forall p, live_anf k tW p ->
        live_value k (AIte (amap pw cP) tW eW) p.
      by move=> p; rewrite /live_anf /live_value /= => ->; rewrite ?orb_true_r.
    have Ha : forall p, In p L -> live_anf k tW p ->
        vatoms k (AIte (amap pa cP) tA eA) p.
      move=> p Hp Hl'; rewrite /vatoms /= !atom_member_union.
      by rewrite (live_atoms L k tP tA tW p H9 H6 HL Hp Hl') orb_true_r.
    have := IHt L k c s0 wP PBranch m Replay tA tW tT tD Real ve H9 H6 H3 H0
      (Hctx tW Hl Ha c (le_n c)) HtW Hev
      (fun o Ho _ => False_ind _ (owner_branch_none _ _ Ho)).
    rewrite Hot => -[_ [s1 [Hrun [Hfr [Htk [Hv _]]]]]].
    by case: Htk => Hk1 Hk2; exists st, vt, s1, ve; repeat split; auto.
  have Hl : forall p, live_anf k eW p ->
      live_value k (AIte (amap pw cP) tW eW) p.
    by move=> p; rewrite /live_anf /live_value /= => ->; rewrite ?orb_true_r.
  have Ha : forall p, In p L -> live_anf k eW p ->
      vatoms k (AIte (amap pa cP) tA eA) p.
    move=> p Hp Hl'; rewrite /vatoms /= !atom_member_union.
    by rewrite (live_atoms L k eP eA eW p H10 H7 HL Hp Hl') !orb_true_r.
  have := IHe L k c1 s0 wP PBranch m Replay eA eW eT eD Real ve H10 H7 H4 H1
    (Hctx eW Hl Ha c1 M1) HeW Hev
    (fun o Ho _ => False_ind _ (owner_branch_none _ _ Ho)).
  rewrite Hoe => -[_ [s1 [Hrun [Hfr [Htk [Hv _]]]]]].
  case: (tkeep_mono _ _ _ _ _ Htk M1) => Hk1 Hk2.
  exists se', ve', s1, ve; repeat split; auto.
  by move=> v0 Hb0; apply: Hfr; exact: (below_mono c c1 v0 Hb0 M1).
case: Hbody => sb [vb [s1 [vv [Hrun [Hfr [Htk [Hv [Eve [Esb Evb]]]]]]]]].
subst vv; split; first lia.
exists (store_set s1 (keyv n) (primal ve)).
split.
  rewrite run_realvar -/s0 (run_branch _ _ _ _ _ _ Hsc0).
  move: Esb Evb; case: (b) => /= -> ->.
    by rewrite run_app Hrun /= (run_assign_var _ _ _ _ _ Hv).
  by rewrite run_app Hrun /= (run_assign_var _ _ _ _ _ Hv).
split.
  move=> v0 Hb0 Hc0 Ht0 Hne _.
  rewrite store_get_set_other.
    by move=> /(keyv_inj _ _ Hcn0 Hc0) E; subst v0; apply: Hne.
  rewrite (Hfr v0 Hb0 Hc0 Ht0) //.
  rewrite /s0 store_get_set_other // => /(keyv_inj _ _ Hcn0 Hc0) E.
  by subst v0; apply: Hne.
split; last by split; [apply: store_get_set_same |].
apply: (tkeep_trans _ _ _ s1).
  apply: (tkeep_trans _ _ _ s0); last exact: tkeep_none Htk.
  by apply: tkeep_set => //=; tauto.
by apply: tkeep_set => //=; tauto.
Qed.

Lemma rev_value_ite w vo (c : atom (tvar W)) t e te n :
  rev_value W w vo (AIte c t e) te n =
  sbind (adj W w vo Replay t (DVar (BarOf n))) (fun '(ft, rt) =>
  sbind (adj W w vo Replay e (DVar (BarOf n))) (fun '(fe, re) =>
    Done [DBranch (spell c) (app ft rt) (app fe re)])).
Proof. by []. Qed.

Lemma tbr_occurs L k (bP : anf pv bare) bA bW m p :
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> Forall (static_ok k) L -> In p L
    ->
  (tbr cv m k bA p \/ useful cv m k bA p) -> live_anf k bW p.
Proof.
move=> HA HW HL Hp Ht; rewrite /live_anf.
have [Eid [Hk _]] := static_in _ _ _ HL Hp; rewrite -Eid.
apply: ((proj1 needs_occurs) bP L bA bW m k (aid (pa p)) HA HW).
- by move=> q Hq; case: (static_in _ _ _ HL Hq).
- lia.
by case: Ht; rewrite /tbr /useful atom_member_id => ->; rewrite ?orb_true_r.
Qed.

(* The reverse sweep of a branch: the branch taken is replayed, then
   transposed from the adjoint of the variable of the let. *)
Lemma arev_ite (cP : atom pv) (tP eP : anf pv bare) :
  asim_body cv tP -> asim_body cv eP -> asim_rev cv (AIte cP tP eP).
Proof.
move=> IHt IHe.
rev_intro.
rewrite /= in Htc Hev Hst; cbn [rebuild_value annotate_value_t].
rewrite rev_value_ite.
rename t into tA, e into eA, t0 into tW, e0 into eW, t1 into tT, e1 into eT,
  t2 into tD, e2 into eD.
have HL := s_static _ _ _ _ _ _ _ Hs.
(* typing *)
have Hnl : not_in_loop pp by move: Htc; case: (pp).
set X := (if ty_eqb _ _ then _ else _) in Htc.
have {}Htc : X = (te, Ok) by case: (wplace pp) Htc.
rewrite /X {X} in Htc.
case Ecb: (ty_eqb (of_atom (amap pw cP)) Boolean) Htc => //.
case HtW: (typecheck (option_map (amap pw) wP) InBranch k tW) => [t3 [] ] /=;
  last by case: (typecheck _ _ k eW).
case HeW: (typecheck (option_map (amap pw) wP) InBranch k eW) => [t4 [] ] //=.
case E3: (ty_eqb t3 Real); case E4: (ty_eqb t4 Real) => //= -[Ete].
subst te.
move/ty_eqb_true: E3 HtW => -> HtW; move/ty_eqb_true: E4 HeW => -> HeW.
case Hcd: (aeval_atom (duals reals) (amap pd cP)) Hev => [[| | b | |] |] // Hev.
(* the two bodies, opened *)
rewrite open_pairs_sbind.
case Hot: (open_pairs _ c) => [[ft rt] c1].
have M1 : (c <= c1)%nat.
  by rewrite -[c1]/(snd (ft, rt, c1)) -Hot; exact: open_pairs_mono.
cbv iota beta; rewrite open_pairs_sbind.
case Hoe: (open_pairs _ c1) => [[fe re] c2].
have M2 : (c1 <= c2)%nat.
  by rewrite -[c2]/(snd (fe, re, c2)) -Hoe; exact: open_pairs_mono.
cbn [open_pairs]; split; first lia.
move=> s2 O Hrd Hr Hns Htp _ _.
set n := DBound (j, j) in Hst Hns Hot Hoe *.
case: (Hns erefl) => Hn_notin Hsh.
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
(* the reads of the reverse sweep of the branch *)
have Hreads : forall p, In p L ->
    atom_member (AVar (pa p)) (atom_union (atom_union
      (atoms_of_atom (amap pa cP)) (snd (needs cv Replay k tA)))
      (snd (needs cv Replay k eA))) = true ->
    vreads cv k (AIte (amap pa cP) tA eA) p.
  move=> p _; rewrite /vreads; cbn [value_needs].
  by case: (needs cv Replay k tA) => ? ?; case: (needs cv Replay k eA).
have Hflows : forall p, In p L ->
    atom_member (AVar (pa p)) (atom_union (fst (needs cv Replay k tA))
      (fst (needs cv Replay k eA))) = true ->
    vflows cv k (AIte (amap pa cP) tA eA) p.
  move=> p _; rewrite /vflows; cbn [value_needs].
  by case: (needs cv Replay k tA) => ? ?; case: (needs cv Replay k eA).
(* the condition *)
have Hcs : forall p, cP = AVar p ->
    static_ok k p /\ store_get s2 (keyv (stored p)) = Some (primal (pd p)).
  move=> p Ep; split; first exact: (static_in _ _ _ HL (H8 p Ep)).
  apply: (Hrd p (H8 p Ep)); [| | by left].
    apply: (Hreads p (H8 p Ep)); subst cP.
    by rewrite !atom_member_union /= Nat.eqb_refl.
  by subst cP; rewrite /live_value /= Nat.eqb_refl.
have Hsc := aspell_ok k s2 cP _ Hcs Hcd; rewrite /= in Hsc.
(* the branch taken *)
have Gen : forall (bP : anf pv bare) bA bW bT bD cb fb rb cb',
    asim_body cv bP -> anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW ->
    anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD ->
    typecheck (option_map (amap pw) wP) InBranch k bW = (Real, Ok) ->
    aeval (duals reals) bD = Some ve -> (c <= cb)%nat ->
    open_pairs (adj W (option_map (amap pt) wP) vo Replay
      (rebuild (tvar W) bT (annotate_body_t cv Replay k bA))
      (DVar (BarOf n))) cb = ((fb, rb), cb') ->
    (forall p, live_anf k bW p -> live_value k (AIte (amap pw cP) tW eW) p) ->
    (forall p, In p L -> tbr cv Replay k bA p ->
       vreads cv k (AIte (amap pa cP) tA eA) p) ->
    (forall p, In p L -> useful cv Replay k bA p ->
       vflows cv k (AIte (amap pa cP) tA eA) p) ->
    exists s3, run (fb ++ rb) s2 = Some s3 /\
      (forall v, below c v -> consistent v -> is_primal v -> v <> n ->
         store_get s3 (keyv v) = store_get s2 (keyv v)) /\
      (not_in_loop pp -> storage wP tail (AIte cP tP eP) <> None ->
         forall o, owner wP pp = Some o -> avaried (pa o) = false ->
         store_get s3 (keyv n) = store_get s2 (keyv n)) /\
      tkeep c (Some n) s2 s3 /\
      rev_frame_x c (inplace wP pp) n
        (oput O n (TangentCorrect.tangent ve)) s2 s3 /\
      (forall t m, In (t, m) O -> shaped t (barv s3 m)) /\
      pairing O s3 = pairing (oput O n (TangentCorrect.tangent ve)) s2.
  move=> bP bA bW bT bD cb fb rb cb' IH HbA HbW HbT HbD Htcb Hevb Hcb Hob.
  move=> Hlive Htbr Huse.
  have Hctx : actx L k cb s2 wP PBranch (live_anf k bW) (tbr cv Replay k bA)
      Real.
    constructor.
    - exact: (sctx_weaken _ _ _ _ _ _ _ _ _
        (sctx_branch _ _ _ _ _ _ _ _ Hs Hlive) (fun p Hm => Hm) Hcb).
    - exact: Hbar.
    - move=> p Hp Ht; apply: (Hrd p Hp (Htbr p Hp Ht)); last by left.
      apply: Hlive.
      exact: (tbr_occurs L k bP bA bW Replay p HbA HbW HL Hp (or_introl Ht)).
    - exact: Htp.
    - by [].
    by [].
  have Hnf : forall P : Prop, Replay = Forward -> P by [].
  have Hpb : Replay = Replay -> PBranch <> PTop by [].
  have := IH L k cb s2 wP PBranch Replay bA bW bT bD Real ve (DVar (BarOf n))
    vo HbA HbW HbT HbD Hctx I Htcb Hevb (Hnf _) (Hnf _) (Hnf _) Hpb (Hnf _).
  rewrite Hob => -[_ [Hht [s1 [R1 [F1 [T1 [_ Hrev]]]]]]].
  destruct ve as [d | | | |]; try (rewrite /= in Hht; contradiction).
  rewrite /= in Hsh; case Ebn: (barv s2 n) Hsh => [[bn | | | |] |] // _.
  have Hown : forall t m, In (t, m) O -> barv s1 m = barv s2 m.
    move=> t m Hi; have [jm [-> Hjm]] := r_below _ _ _ _ _ _ _ Hr t m Hi.
    rewrite /barv; apply: F1; [rewrite /=; lia | by [] | rewrite /=; tauto |
      by [] | by []].
  have Hbn1 : barv s1 n = Some (VReal bn).
    rewrite -Ebn /barv; apply: F1; [rewrite /=; lia | by [] |
      rewrite /=; tauto | by [] | by []].
  have Hr1 : rctx L cb wP PBranch O (useful cv Replay k bA) s1.
    constructor.
    - exact: (r_nodup _ _ _ _ _ _ _ Hr).
    - move=> t m Hi; rewrite (Hown t m Hi).
      exact: (r_shape _ _ _ _ _ _ _ Hr t m Hi).
    - move=> t m Hi; have [jm [E Hjm]] := r_below _ _ _ _ _ _ _ Hr t m Hi.
      by exists jm; split=> //; lia.
    - move=> p Hp Hu Hv.
      exact: (r_useful _ _ _ _ _ _ _ Hr p Hp (Huse p Hp Hu) Hv).
    - move=> p t Hp Hu Hi.
      exact: (r_value _ _ _ _ _ _ _ Hr p t Hp (Huse p Hp Hu) Hi).
    - by [].
    - exact: (r_args _ _ _ _ _ _ _ Hr).
    exact: (r_written _ _ _ _ _ _ _ Hr).
  have Hseed : seed_ok cb Real (DVar (BarOf n)) s1.
    split; last by move=> _; exists bn.
    by move=> y [<- | []]; split=> //=; lia.
  have Htp1 : tapes_ok L s1.
    move=> p Hp Hrp; have [lt Hlt] := Htp p Hp Hrp.
    exact: (proj1 T1 _ _ Hlt).
  have [s3 [R3 [_ [_ [T3 [F3 [S3 [P3 _]]]]]]]] :=
    Hrev s1 O (agree_prim_refl _ _ _) Hr1 Hseed Htp1
      (no_tail_tape_branch _ _ _ _ _ _ _).
  exists s3; split; first by rewrite run_app R1.
  have Hprim : forall v, below c v -> consistent v -> is_primal v ->
      store_get s3 (keyv v) = store_get s2 (keyv v).
    move=> v Hb0 Hc0 Hp0; have Hb1 := below_mono c cb v Hb0 Hcb.
    have Ht0 : ~ is_tape v by move: Hp0; case: (v) => /=; tauto.
    have Hnb : forall m0, v = BarOf m0 -> ~ In m0 (map snd O).
      by move=> m0 E; move: Hp0; rewrite E.
    have Hne : inplace wP PBranch <> Some v by [].
    rewrite (F3 v Hb1 Hc0 Ht0 Hne Hnb).
    by apply: F1; [exact: Hb1 | exact: Hc0 | exact: Ht0 | by [] | by []].
  split; first by move=> v Hb0 Hc0 Hp0 _; exact: Hprim.
  split; first by move=> _ Hsn; case: (Hsn erefl).
  split.
    exact: (tkeep_none _ _ _ _
      (tkeep_mono _ _ _ _ _ (tkeep_trans _ _ _ _ _ T1 T3) Hcb)).
  split.
    apply: rev_frame_x_of => v Hb0 Hc0 Ht0 _ Hb'.
    have Hb1 := below_mono c cb v Hb0 Hcb.
    have Hne : inplace wP PBranch <> Some v by [].
    have Hnb : forall m0, v = BarOf m0 -> ~ In m0 (map snd O).
      move=> m0 E Hm; apply: (Hb' m0 E).
      by rewrite (oput_notin O n _ Hn_notin); right.
    rewrite (F3 v Hb1 Hc0 Ht0 Hne Hnb).
    by apply: F1; [exact: Hb1 | exact: Hc0 | exact: Ht0 | by [] | by []].
  split; first exact: S3.
  rewrite P3 (oput_notin O n _ Hn_notin) /result_pairing /seed_value.
  rewrite -[xev s1 _]/(barv s1 n) Hbn1 (pairing_ext_own O s1 s2 Hown).
  have -> : pairing ((TangentCorrect.tangent (VReal d), n) :: O) s2 =
      inner (TangentCorrect.tangent (VReal d)) (barv s2 n) + pairing O s2.
    by [].
  by rewrite Ebn /=; ring.
case: b Hev Hsc Hcd => Hev Hsc Hcd.
  have Hl : forall p, live_anf k tW p ->
      live_value k (AIte (amap pw cP) tW eW) p.
    by move=> p; rewrite /live_anf /live_value /= => ->; rewrite ?orb_true_r.
  have Htb : forall p, In p L -> tbr cv Replay k tA p ->
      vreads cv k (AIte (amap pa cP) tA eA) p.
    move=> p Hp; rewrite /tbr => Ht; apply: Hreads => //.
    by rewrite !atom_member_union Ht orb_true_r.
  have Hu : forall p, In p L -> useful cv Replay k tA p ->
      vflows cv k (AIte (amap pa cP) tA eA) p.
    move=> p Hp; rewrite /useful => Ht; apply: Hflows => //.
    by rewrite atom_member_union Ht.
  have [s3 [R3 [K3 [Kn3 Hs3]]]] := Gen tP tA tW tT tD c ft rt c1 IHt H9 H6 H3
    H0 HtW Hev (le_n c) Hot Hl Htb Hu.
  exists s3; split; first by rewrite (run_branch _ _ _ _ _ true Hsc) R3.
  split; first exact: K3.
  split; first exact: Kn3.
  split; first by move=> _ /(_ erefl).
  by have [T3 [F3 [S3 P3]]] := Hs3; do 4!(split=> //).
have Hl : forall p, live_anf k eW p ->
    live_value k (AIte (amap pw cP) tW eW) p.
  by move=> p; rewrite /live_anf /live_value /= => ->; rewrite ?orb_true_r.
have Htb : forall p, In p L -> tbr cv Replay k eA p ->
    vreads cv k (AIte (amap pa cP) tA eA) p.
  move=> p Hp; rewrite /tbr => Ht; apply: Hreads => //.
  by rewrite !atom_member_union Ht !orb_true_r.
have Hu : forall p, In p L -> useful cv Replay k eA p ->
    vflows cv k (AIte (amap pa cP) tA eA) p.
  move=> p Hp; rewrite /useful => Ht; apply: Hflows => //.
  by rewrite atom_member_union Ht orb_true_r.
have [s3 [R3 [K3 [Kn3 Hs3]]]] := Gen eP eA eW eT eD c1 fe re c2 IHe H10 H7 H4
  H1 HeW Hev M1 Hoe Hl Htb Hu.
exists s3; split; first by rewrite (run_branch _ _ _ _ _ false Hsc) R3.
split; first exact: K3.
split; first exact: Kn3.
split; first by move=> _ /(_ erefl).
by have [T3 [F3 [S3 P3]]] := Hs3; do 4!(split=> //).
Qed.



(* The forward sweep of a map: a loop over the indices, computing each element
   by the primal computation of the body, into the written array. *)
Lemma afwd_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, psim_body (bP x)) -> asim_fwd cv (AMap loP hiP bP).
Proof.
move=> IHb L k c s wP pp tail eA eW eT eD te n ve ty m rec HA HW HT HD Hc Htc
  Htail [j [Ej Hj]] Hst Hrec Hev.
have HA0 := HA; have HW0 := HW.
destruct eA, eW, eT, eD; simpl in HA, HW, HT, HD; try contradiction;
graph_split.
rewrite /= in Htc Hev Hst *.
rename b into bA, b0 into bW, b1 into bT, b2 into bD.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have HL := s_static _ _ _ _ _ _ _ Hs.
destruct pp as [| | | ix0 sx0]; rewrite /= in Htc; try discriminate.
destruct tail; [| discriminate].
destruct loP as [? | ? | l0]; rewrite /= in Htc; try discriminate.
destruct hiP as [? | ? | h]; rewrite /= in Htc; try discriminate.
case El: (negb (l0 =? 0)%Z) Htc => // Htc.
move/negbFE/Z.eqb_eq: El => El; subst l0.
have Hte : te = Array (h - 0) by clear -Htc; crush_match Htc.
have Harr : is_array ty by rewrite -(Htail erefl) Hte.
case Eo: (owner wP PTop) => [o |]; last first.
  by case: (s_ty _ _ _ _ _ _ _ Hs Harr Eo).
destruct wP as [[o' | |] |]; rewrite /= in Eo; try discriminate.
case Ey: (vty (pw o')) Eo => [| | | ny] // [Eo]; subst o'.
rewrite /= in Hst; case: Hst => Ej _; subst j.
have [Hnocc HtB] : occurs_anf (vid (pw o)) (S k) (bW (anon k)) = false /\
    typecheck (Some (AVar (pw o))) ScalarBody (S k) (bW (VInfo k Integer None))
    = (Real, Ok).
  move: Htc => /=; case: (varg (pw o)) => [[nm []] |] //=;
    case: (occurs_anf _ _ _) => //;
    case: (typecheck _ ScalarBody _ _) => [tb [| mm]] //=;
    by case Etb: (ty_eqb tb Real) => //; move/ty_eqb_true: Etb => ->.
clear Htc.
have [o'' [[<-] [HoL _]]] := s_written _ _ _ _ _ _ _ Hs _ erefl.
have Ehn : ny = (h - 0)%Z.
  have Hao : is_array (vty (pw o)) by rewrite Ey.
  have [Hty _] := s_top _ _ _ _ _ _ _ Hs o erefl erefl Hao.
  by rewrite Ey -(Htail erefl) Hte in Hty; case: Hty.
(* the written array, at the start *)
have Hown : owner (Some (AVar o)) PTop = Some o by rewrite /= Ey.
have A1 := a_owner _ _ _ _ _ _ _ _ _ Hc o Hown (or_introl I).
have [_ [_ [_ [_ [_ [_ [_ [_ [Hht _]]]]]]]]] := static_in _ _ _ HL HoL.
rewrite Ey in Hht; case Epd: (pd o) Hht A1 => [| | | lo |] // Hht A1.
rewrite /= in Hht A1; set l1 := map dfst lo in A1.
(* the dual evaluation *)
rewrite /= in Hev.
case Hxs: (eval_map (fun v1 => aeval (duals reals) (bD v1)) 0 (count 0 h)) Hev
  => [xs |] // [<-].
(* the body, opened *)
rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[sb vb] c2].
have Hc2 : (S c <= c2)%nat.
  by rewrite -[c2]/(snd (sb, vb, c2)) -Hob; exact: open_pairs_mono.
cbn [open_pairs spell amap]; split; first lia.
set n := DBound (pn o, pn o) in Hrec *.
set i := DBound (c, c) in Hob *.
set bodyst := (sb ++ [DAssign (DAt (DVar n) (DVar i)) vb])%list.
have Hlen1 : length l1 = count 0 h.
  by rewrite /l1 length_map Hht count_nat; lia.
(* the variables the body reads are not the output array *)
have Hlive_b : forall p, In p L ->
    live_anf (S k) (bW (VInfo k Integer None)) p ->
    live_value k (AMap (ANat 0) (ANat h) bW) p /\ pn p <> pn o.
  move=> p Hp Hl.
  have Hlc := live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ H7 HL
    erefl erefl.
  have Hl' : live_value k (AMap (ANat 0) (ANat h) bW) p.
    by move: Hl; rewrite /live_anf /live_value /= Hlc.
  split=> // E.
  case: (s_owner _ _ _ _ _ _ _ Hs o p Hown Hp E) => [Ep | /(_ Hl') []].
  subst p; move: Hl; rewrite /live_anf Hlc; congruence.
set Inv := fun (z : Z) (s' : store R) (acc : list (dual R)) =>
  z = Z.of_nat (length acc) /\ fwd_frame c (Some n) None s s' /\
  tkeep c (Some n) s s' /\
  store_get s' (keyv n) = Some (VArray (map dfst acc ++ skipn (length acc) l1)).
have Hloop : exists sf,
    exec_up R (run bodyst) (out_dvar nat i) 0 (count 0 h) s = Some sf /\
    Inv (0 + Z.of_nat (count 0 h))%Z sf ([] ++ xs)%list.
  apply: (map_loop_bounded (fun v => aeval (duals reals) (bD v)) (run bodyst)
    (out_dvar nat i) Inv (Z.of_nat (count 0 h))); [| lia | | exact: Hxs].
    move=> z s' acc d Hz [Ez [Hfr' [Htk' Hn']]] Hbd.
    set s'' := store_set s' (keyv i) (VInt z).
    change (store_set s' (KVar (out_dvar nat i)) (VInt z)) with s''.
    set ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c)))
      (VInt z) c.
    have Hix : static_ok (S k) ix.
      by repeat split; simpl; auto; try lia; discriminate.
    have Hci : consistent i by [].
    have Kin : forall v, below c v -> consistent v -> keyv v <> keyv i.
      move=> v Hb Hcv K; have E := keyv_inj _ _ Hcv Hci K; subst v.
      by rewrite /i /= in Hb; lia.
    have Hctx : actx (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar
        (live_anf (S k) (bW (VInfo k Integer None)))
        (live_anf (S k) (bW (VInfo k Integer None))) Real.
      constructor.
      - apply: sctx_scalar.
        + apply: Forall_cons Hix _; apply: Forall_impl HL => p Hp.
          by apply: static_mono Hp _; lia.
        + move=> p q [<- | Hp] [<- | Hq] E //.
          * have [_ [Hq' _]] := static_in _ _ _ HL Hq.
            by rewrite /= in E; lia.
          * have [_ [Hp' _]] := static_in _ _ _ HL Hp.
            by rewrite /= in E; lia.
          exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
        + move=> p [<- | Hp] /=; first lia.
          by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
        move=> a0 [<-]; exists o; split=> //; split; first by right.
        by have [? [[<-] [_ Hg]]] := s_written _ _ _ _ _ _ _ Hs _ erefl.
      - by move=> p [<- | Hp] //; exact: (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp).
      - move=> p [<- | Hp] Hl; first by rewrite /s'' store_get_set_same.
        have [Hl' Hpn] := Hlive_b p Hp Hl.
        have Hpc := s_num _ _ _ _ _ _ _ Hs _ Hp.
        have Hbp : below c (stored p) by [].
        rewrite /s'' store_get_set_other; first by apply/not_eq_sym/Kin.
        have Htp' : ~ is_tape (stored p) by rewrite /=; tauto.
        have Hne : Some n <> Some (stored p).
          by move=> [E]; rewrite /n /stored in E; congruence.
        rewrite (Hfr' (stored p) Hbp erefl Htp' Hne) //.
        exact: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp
          (live_vatoms _ _ _ _ _ p HA0 HW0 HL Hp Hl')).
      - move=> p [<- | Hp] Hr //.
        have [lt Hlt] := a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr.
        have [l' Hl'] := proj1 Htk' _ _ Hlt.
        by exists l'; rewrite /s'' store_get_set_other.
      - by [].
      by [].
    have := IHb ix (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar m Replay
      (bA (fresh k)) (bW (VInfo k Integer None))
      (bT (open_index (DBound (c, c)))) (bD (VInt z)) Real (VReal d)
      (H10 ix _) (H7 ix _) (H4 ix _) (H1 ix _) Hctx HtB Hbd
      (fun o Ho _ => False_ind _ (owner_scalar_none _ _ Ho)).
    rewrite Hob => -[_ [s3 [R3 [F3 [T3 [X3 _]]]]]].
    have Hbn : below (S c) n by rewrite /n /=; lia.
    have Hcn : consistent n by [].
    have Htn : ~ is_tape n by rewrite /=; tauto.
    have S3n : store_get s3 (keyv n) = store_get s' (keyv n).
      rewrite (F3 n Hbn Hcn Htn) // /s'' store_get_set_other //.
      by apply/not_eq_sym/Kin.
    have S3i : xev s3 (DVar i) = Some (VInt z).
      have Hbi : below (S c) i by rewrite /i /=; lia.
      have Hti : ~ is_tape i by rewrite /=; tauto.
      rewrite -[xev s3 _]/(store_get s3 (keyv i)) (F3 i Hbi Hci Hti) //.
      exact: store_get_set_same.
    have Hacc : (length acc < length l1)%nat by lia.
    set a1 := VArray (map dfst (acc ++ [d]) ++ skipn (length (acc ++ [d])) l1).
    set s4 := store_set s3 (keyv n) a1.
    have Hrun4 : run [DAssign (DAt (DVar n) (DVar i)) vb] s3 = Some s4.
      apply: (run_assign_at s3 n _ _ (map dfst acc ++ skipn (length acc) l1) z
        (dfst d)); [by rewrite S3n | exact: S3i | exact: X3 |].
      by rewrite Ez; apply: replace_step.
    exists s4; split; first by rewrite /bodyst run_app R3.
    split; first by rewrite length_app /=; lia.
    split.
      move=> v Hb Hcv Ht Hex Hvo.
      rewrite /s4 store_get_set_other.
        by move=> /(keyv_inj _ _ Hcn Hcv) E; subst v; apply: Hex.
      have HcS : (c <= S c)%nat by lia.
      rewrite (F3 v (below_mono c (S c) v Hb HcS) Hcv Ht) //.
      rewrite /s'' store_get_set_other; first by apply/not_eq_sym/Kin.
      exact: (Hfr' v Hb Hcv Ht Hex Hvo).
    split.
      apply: (tkeep_trans _ _ _ s'); first exact: Htk'.
      apply: (tkeep_trans _ _ _ s'').
        by rewrite /s''; apply: tkeep_set => //=; tauto.
      apply: (tkeep_trans _ _ _ s3).
        exact: (tkeep_none _ _ _ _
          (tkeep_mono _ _ _ _ _ T3 (Nat.le_succ_diag_r c))).
      by rewrite /s4; apply: tkeep_set => //=; tauto.
    by rewrite /s4 store_get_set_same.
  split=> //; split; first by [].
  by split; [exact: tkeep_refl | exact: A1].
case: Hloop => sf [Hex [_ [Hfr [Htk Hn']]]].
rewrite [_ ++ xs]/= (eval_map_length _ _ _ _ Hxs) -Hlen1 skipn_all app_nil_r
  in Hn'.
exists sf; split; last by [].
by rewrite (run_for _ _ _ _ _ _ 0 h) // Hex.
Qed.


(* The reverse sweep of a map: a loop down the indices, replaying the body and
   transposing it from the adjoint of its element. *)
Lemma arev_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, asim_body cv (bP x)) -> asim_rev cv (AMap loP hiP bP).
Proof.
move=> IHb L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT HD Hs Hbar Htc
  Htail [j [Ej Hj]] Hst Hev Hvr.
have HA0 := HA; have HW0 := HW.
destruct eA, eW, eT, eD; simpl in HA, HW, HT, HD; try contradiction;
graph_split.
rewrite /= in Htc Hst *.
rename b into bA, b0 into bW, b1 into bT, b2 into bD.
have HL := s_static _ _ _ _ _ _ _ Hs.
destruct pp as [| | | ix0 sx0]; rewrite /= in Htc; try discriminate.
destruct tail; [| discriminate].
destruct loP as [? | ? | l0]; rewrite /= in Htc; try discriminate.
destruct hiP as [? | ? | h]; rewrite /= in Htc; try discriminate.
case El: (negb (l0 =? 0)%Z) Htc => // Htc.
move/negbFE/Z.eqb_eq: El => El; subst l0.
have Hte : te = Array (h - 0) by clear -Htc; crush_match Htc.
have Harr : is_array ty by rewrite -(Htail erefl) Hte.
case Eo: (owner wP PTop) => [o |]; last first.
  by case: (s_ty _ _ _ _ _ _ _ Hs Harr Eo).
destruct wP as [[o' | |] |]; rewrite /= in Eo; try discriminate.
case Ey: (vty (pw o')) Eo => [| | | ny] // [Eo]; subst o'.
rewrite /= in Hst; case: Hst => Ej _; subst j.
have [[nm [ro [Hro Hnio]]] [Hnocc HtB]] :
    (exists nm r, varg (pw o) = Some (nm, r) /\ r <> Inout) /\
    occurs_anf (vid (pw o)) (S k) (bW (anon k)) = false /\
    typecheck (Some (AVar (pw o))) ScalarBody (S k) (bW (VInfo k Integer None))
    = (Real, Ok).
  have [o'' [[<-] [_ Hg]]] := s_written _ _ _ _ _ _ _ Hs _ erefl.
  move: Htc Hg => /=; case: (varg (pw o)) => [[nm r] |] //=.
  case: r => //=; case: (occurs_anf _ _ _) => //;
    case: (typecheck _ ScalarBody _ _) => [tb [| mm]] //=;
    case Etb: (ty_eqb tb Real) => // _ _; move/ty_eqb_true: Etb => ->;
    by split=> //; exists nm; eexists.
clear Htc.
have [o'' [[<-] [HoL _]]] := s_written _ _ _ _ _ _ _ Hs _ erefl.
rewrite /= in Hev.
case Hxs: (eval_map (fun v1 => aeval (duals reals) (bD v1)) 0 (count 0 h)) Hev
  => [xs |] // [<-].
(* the written array: dependent, with a zero tangent, and its adjoint *)
have Ehn : ny = (h - 0)%Z.
  have Hao : is_array (vty (pw o)) by rewrite Ey.
  have [Hty _] := s_top _ _ _ _ _ _ _ Hs o erefl erefl Hao.
  by rewrite Ey -(Htail erefl) Hte in Hty; case: Hty.
have [_ [_ [_ [_ [_ [_ [_ [_ [Hht Hzo]]]]]]]]] := static_in _ _ _ HL HoL.
rewrite Ey in Hht; case Epd: (pd o) Hht Hzo => [| | | lo |] // Hht Hzo.
rewrite /= in Hht.
have Hlx := eval_map_length _ _ _ _ Hxs.
(* the body, opened *)
rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[fb rb] c2].
have Hc2 : (S c <= c2)%nat.
  by rewrite -[c2]/(snd (fb, rb, c2)) -Hob; exact: open_pairs_mono.
cbn [open_pairs spell amap rev_loop]; split; first lia.
move=> s2 O Hrd Hr _ Htp _ _.
set n := DBound (pn o, pn o).
set i := DBound (c, c) in Hob *.
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
have Hnd := r_nodup _ _ _ _ _ _ _ Hr.
have Hown : owner (Some (AVar o)) PTop = Some o by rewrite /= Ey.
have HoO := r_owner _ _ _ _ _ _ _ Hr o Hown; rewrite Epd in HoO.
have Hav : avaried (pa o) = false.
  have [ny' [r' [Hr' Hw']]] := r_written _ _ _ _ _ _ _ Hr o erefl.
  move: Hr'; rewrite Hro => -[_ Er']; subst r'.
  rewrite (r_args _ _ _ _ _ _ _ Hr o nm ro HoL Hro).
  by move: Hw' Hnio; case: (ro).
have Hzl := Hzo Hav; rewrite /= in Hzl.
have Hsh := r_shape _ _ _ _ _ _ _ Hr _ _ HoO; rewrite /= -/n in Hsh.
case Eyb: (barv s2 n) Hsh => [[| | | yb |] |] // Hsh.
rewrite length_map in Hsh.
have Hcount : length xs = count 0 h by exact: Hlx.
have Hlyb : length yb = count 0 h by rewrite -Hsh Hht Ehn count_nat; lia.
set O' := odel O n.
have Hnd' : NoDup (map snd O') by exact: (odel_nodup O n Hnd).
have HnO' : ~ In n (map snd O').
  by move=> Hi; exact: (proj2 (odel_snd O n n Hi)).
(* the variables of the body *)
have Hlive_b : forall p, In p L ->
    live_anf (S k) (bW (VInfo k Integer None)) p ->
    live_value k (AMap (ANat 0) (ANat h) bW) p /\ pn p <> pn o.
  move=> p Hp Hl.
  have Hlc := live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ H7 HL
    erefl erefl.
  have Hl' : live_value k (AMap (ANat 0) (ANat h) bW) p.
    by move: Hl; rewrite /live_anf /live_value /= Hlc.
  split=> // E.
  case: (s_owner _ _ _ _ _ _ _ Hs o p Hown Hp E) => [Ep | /(_ Hl') []].
  subst p; move: Hl; rewrite /live_anf Hlc; congruence.
set body := ([] ++ fb ++ [] ++ rb)%list.
set N := count 0 h.
set P := fun (jn : nat) (s' : store R) =>
  (forall v, below c v -> consistent v -> is_primal v ->
     store_get s' (keyv v) = store_get s2 (keyv v)) /\
  tkeep c (Some n) s2 s' /\ rev_frame c (Some n) O' s2 s' /\
  barv s' n = Some (VArray yb) /\
  (forall t m, In (t, m) O' -> shaped t (barv s' m)) /\
  pairing O' s' = pairing O' s2 + dotl (skipn jn (map dsnd xs)) (skipn jn yb).
have Hloop : exists sf,
    exec_down R (run body) (out_dvar nat i) (Z.of_nat N - 1) N s2 = Some sf /\
    P 0%nat sf.
  apply: (exec_down_loop (run body) (out_dvar nat i) N P); [| lia |].
    move=> jn s Hjn [K0 [T0 [F0 [B0 [S0 P0]]]]].
    have Hreads : forall p, In p L -> tbr cv Replay (S k) (bA (fresh k)) p ->
        vreads cv k (AMap (ANat 0) (ANat h) bA) p.
      move=> p Hp; have [Eid [Hk _]] := static_in _ _ _ HL Hp.
      rewrite /tbr /vreads; cbn [value_needs].
      case: (needs cv Replay (S k) (bA (fresh k))) => u l /= Ht.
      have Hkp : (k =? aid (pa p))%nat = false by apply/Nat.eqb_neq; lia.
      rewrite atom_member_union atom_member_remove_full Ht /same_term /fresh /=.
      by rewrite Hkp /= ?orb_true_r.
    have Hflows : forall p, In p L ->
        useful cv Replay (S k) (bA (fresh k)) p ->
        vflows cv k (AMap (ANat 0) (ANat h) bA) p.
      move=> p Hp; have [Eid [Hk _]] := static_in _ _ _ HL Hp.
      rewrite /useful /vflows; cbn [value_needs].
      case: (needs cv Replay (S k) (bA (fresh k))) => u l /= Ht.
      have Hkp : (k =? aid (pa p))%nat = false by apply/Nat.eqb_neq; lia.
      by rewrite atom_member_remove_full Ht /same_term /fresh /= Hkp.
    set z := Z.of_nat jn.
    set s'' := store_set s (keyv i) (VInt z).
    change (store_set s (KVar (out_dvar nat i)) (VInt z)) with s''.
    set ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c)))
      (VInt z) c.
    have Hix : static_ok (S k) ix.
      by repeat split; simpl; auto; try lia; discriminate.
    have HL' : Forall (static_ok (S k)) (ix :: L).
      apply: Forall_cons Hix _; apply: Forall_impl HL => p Hp.
      by apply: static_mono Hp _; lia.
    have Hci : consistent i by [].
    have Kin : forall v, below c v -> consistent v -> keyv v <> keyv i.
      move=> v Hb Hcv K; have E := keyv_inj _ _ Hcv Hci K; subst v.
      by rewrite /i /= in Hb; lia.
    set d0 := Dual 0 0.
    have Hbd : aeval (duals reals) (bD (VInt z)) = Some (VReal (nth jn xs d0)).
      have E := eval_map_nth _ 0 _ _ jn d0 Hxs Hjn.
      by rewrite Z.add_0_l in E.
    have Hctx : actx (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar
        (live_anf (S k) (bW (VInfo k Integer None)))
        (tbr cv Replay (S k) (bA (fresh k))) Real.
      constructor.
      - apply: sctx_scalar; first exact: HL'.
        + move=> p q [<- | Hp] [<- | Hq] E //.
          * have [_ [Hq' _]] := static_in _ _ _ HL Hq.
            by rewrite /= in E; lia.
          * have [_ [Hp' _]] := static_in _ _ _ HL Hp.
            by rewrite /= in E; lia.
          exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
        + move=> p [<- | Hp] /=; first lia.
          by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
        move=> a0 [<-]; exists o; split=> //; split; first by right.
        by have [? [[<-] [_ Hg]]] := s_written _ _ _ _ _ _ _ Hs _ erefl.
      - by move=> p [<- | Hp] //; exact: Hbar.
      - move=> p [<- | Hp] Ht; first by rewrite /s'' store_get_set_same.
        have Hlb : live_anf (S k) (bW (VInfo k Integer None)) p.
          exact: (tbr_occurs (ix :: L) (S k) (bP ix) (bA (fresh k))
            (bW (VInfo k Integer None)) Replay p (H10 ix (pa ix))
            (H7 ix (pw ix)) HL' (or_intror Hp) (or_introl Ht)).
        have [Hl' Hpn] := Hlive_b p Hp Hlb.
        have Hpc := s_num _ _ _ _ _ _ _ Hs _ Hp.
        have Hbp : below c (stored p) by [].
        rewrite /s'' store_get_set_other; first by apply/not_eq_sym/Kin.
        rewrite (K0 (stored p) Hbp erefl I).
        exact: (Hrd p Hp (Hreads p Hp Ht) Hl' (or_introl I)).
      - move=> p [<- | Hp] Hrc //.
        have [lt Hlt] := Htp p Hp Hrc; have [l' Hl'] := proj1 T0 _ _ Hlt.
        by exists l'; rewrite /s'' store_get_set_other.
      - by [].
      by [].
    have Hnf : forall P : Prop, Replay = Forward -> P by [].
    have Hpb : Replay = Replay -> PScalar <> PTop by [].
    have := IHb ix (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar Replay
      (bA (fresh k)) (bW (VInfo k Integer None))
      (bT (open_index (DBound (c, c)))) (bD (VInt z)) Real
      (VReal (nth jn xs d0)) (DAt (DVar (BarOf n)) (DVar i)) vo
      (H10 ix _) (H7 ix _) (H4 ix _) (H1 ix _) Hctx I HtB Hbd
      (Hnf _) (Hnf _) (Hnf _) Hpb (Hnf _).
    rewrite Hob => -[_ [_ [s1 [R1 [F1 [T1 [_ Hrev]]]]]]].
    cbn [inplace owner option_map sweep_eqb] in F1, Hrev.
    have Hnb : forall v, ~ is_tape v -> below (S c) v -> consistent v ->
        store_get s1 (keyv v) = store_get s'' (keyv v).
      by move=> v Ht Hb Hcv; rewrite (F1 v Hb Hcv Ht).
    have Hns : forall v, below c v -> consistent v ->
        store_get s'' (keyv v) = store_get s (keyv v).
      by move=> v Hb Hcv; rewrite /s'' store_get_set_other //;
        apply/not_eq_sym/Kin.
    have Hcbn : consistent (BarOf n) by [].
    have Htbn : ~ is_tape (BarOf n) by rewrite /=; tauto.
    have Hbn0 : below c (BarOf n) by [].
    have Hbn1 : below (S c) (BarOf n) by rewrite /n /=; lia.
    have B1 : barv s1 n = Some (VArray yb).
      by rewrite /barv (Hnb _ Htbn Hbn1 Hcbn) (Hns _ Hbn0 Hcbn).
    have I1 : store_get s1 (keyv i) = Some (VInt z).
      have Hti : ~ is_tape i by rewrite /=; tauto.
      have Hbi : below (S c) i by rewrite /i /=; lia.
      by rewrite (Hnb _ Hti Hbi Hci) /s'' store_get_set_same.
    have Hjy : (jn < length yb)%nat by lia.
    have Hyj : xev s1 (DAt (DVar (BarOf n)) (DVar i)) =
        Some (VReal (nth jn yb 0)).
      rewrite (xev_at s1 (BarOf n) i yb z B1 I1) /z.
      by rewrite (nth_z_of_nat yb jn 0 Hjy).
    have Hown_b : forall t m, In (t, m) O' -> barv s1 m = barv s m.
      move=> t m /odel_in [Hi _].
      have [jm [-> Hjm]] := r_below _ _ _ _ _ _ _ Hr t m Hi.
      have Hc1 : consistent (BarOf (DBound (jm, jm))) by [].
      have Ht1 : ~ is_tape (BarOf (DBound (jm, jm))) by rewrite /=; tauto.
      have Hb0 : below c (BarOf (DBound (jm, jm))) by [].
      have Hb1 : below (S c) (BarOf (DBound (jm, jm))) by rewrite /=; lia.
      by rewrite /barv (Hnb _ Ht1 Hb1 Hc1) (Hns _ Hb0 Hc1).
    have Ts1 : tkeep c (Some n) s2 s1.
      apply: (tkeep_trans _ _ _ s); first exact: T0.
      apply: (tkeep_trans _ _ _ s'').
        by rewrite /s''; apply: tkeep_set => //=; tauto.
      exact: (tkeep_none _ _ _ _
        (tkeep_mono _ _ _ _ _ T1 (Nat.le_succ_diag_r c))).
    have Hr1 : rctx (ix :: L) (S c) (Some (AVar o)) PScalar O'
        (useful cv Replay (S k) (bA (fresh k))) s1.
      constructor.
      - exact: Hnd'.
      - by move=> t m Hi; rewrite (Hown_b t m Hi); exact: S0.
      - move=> t m /odel_in [Hi _].
        have [jm [E Hjm]] := r_below _ _ _ _ _ _ _ Hr t m Hi.
        by exists jm; split=> //; lia.
      - move=> p [<- | Hp] Hu Hv //.
        apply/odel_in; split.
          exact: (r_useful _ _ _ _ _ _ _ Hr p Hp (Hflows p Hp Hu) Hv).
        have Hlb : live_anf (S k) (bW (VInfo k Integer None)) p.
          exact: (tbr_occurs (ix :: L) (S k) (bP ix) (bA (fresh k))
            (bW (VInfo k Integer None)) Replay p (H10 ix (pa ix))
            (H7 ix (pw ix)) HL' (or_intror Hp) (or_intror Hu)).
        have [_ Hpn] := Hlive_b p Hp Hlb.
        by move=> E; rewrite /stored /n in E; congruence.
      - move=> p t [<- | Hp] Hu Hin.
          move/odel_in: Hin => [Hin _].
          have [jm [E Hjm]] := r_below _ _ _ _ _ _ _ Hr _ _ Hin.
          by rewrite /stored /= in E; case: E => E1 _; lia.
        exact: (r_value _ _ _ _ _ _ _ Hr p t Hp (Hflows p Hp Hu)
          (proj1 (proj1 (odel_in O n t (stored p)) Hin))).
      - by [].
      - move=> p ny0 r0 [<- | Hp] Hv //.
        exact: (r_args _ _ _ _ _ _ _ Hr p ny0 r0 Hp Hv).
      exact: (r_written _ _ _ _ _ _ _ Hr).
    have Hseed : seed_ok (S c) Real (DAt (DVar (BarOf n)) (DVar i)) s1.
      split; last by move=> _; exists (nth jn yb 0).
      by move=> y /= [<- | [<- | []]]; split=> //; rewrite /n /i /=; lia.
    have Htp1 : tapes_ok (ix :: L) s1.
      move=> p [<- | Hp] Hrc //; have [lt Hlt] := Htp p Hp Hrc.
      exact: (proj1 Ts1 _ _ Hlt).
    have [s3 [R3 [_ [_ [T3 [F3 [S3 [P3 _]]]]]]]] :=
      Hrev s1 O' (agree_prim_refl _ _ _) Hr1 Hseed Htp1
        (no_tail_tape_scalar _ _ _ _ _ _ _).
    exists s3; split; first by rewrite /body /= run_app R1.
    have Hp3 : forall v, below c v -> consistent v -> ~ is_tape v ->
        (forall m, v = BarOf m -> ~ In m (map snd O')) ->
        store_get s3 (keyv v) = store_get s (keyv v).
      move=> v Hb Hcv Ht Hbo; have HcS : (c <= S c)%nat by lia.
      have Hb1 := below_mono c (S c) v Hb HcS.
      have Hne : None <> Some v by [].
      rewrite (F3 v Hb1 Hcv Ht Hne Hbo) (Hnb v Ht Hb1 Hcv).
      exact: Hns.
    split.
      move=> v Hb Hcv Hpv.
      have Ht : ~ is_tape v by move: Hpv; case: (v) => /=; tauto.
      have Hbo : forall m, v = BarOf m -> ~ In m (map snd O').
        by move=> m0 E; move: Hpv; rewrite E.
      by rewrite (Hp3 v Hb Hcv Ht Hbo); exact: K0.
    split.
      exact: (tkeep_trans _ _ _ _ _ Ts1 (tkeep_none _ _ _ _
        (tkeep_mono _ _ _ _ _ T3 (Nat.le_succ_diag_r c)))).
    split.
      move=> v Hb Hcv Ht Hex Hbo.
      by rewrite (Hp3 v Hb Hcv Ht Hbo); exact: F0.
    split.
      have Hbo : forall m0, BarOf n = BarOf m0 -> ~ In m0 (map snd O').
        by move=> m0 [<-].
      by rewrite /barv (Hp3 _ Hbn0 Hcbn Htbn Hbo).
    split; first exact: S3.
    rewrite P3 /result_pairing /seed_value Hyj.
    rewrite (pairing_ext_own O' s1 s Hown_b) P0.
    have Hjx : (jn < length (map dsnd xs))%nat by rewrite length_map; lia.
    rewrite (skipn_nth_cons _ _ (dsnd d0) Hjx) (skipn_nth_cons yb jn 0 Hjy).
    by rewrite dotl_cons map_nth; ring.
  split=> //; split; first exact: tkeep_refl.
  split; first by [].
  split; first exact: Eyb.
  split.
    by move=> t m /odel_in [Hi _]; exact: (r_shape _ _ _ _ _ _ _ Hr t m Hi).
  have E1 : skipn N (map dsnd xs) = [].
    by apply: skipn_all2; rewrite length_map; lia.
  have E2 : skipn N yb = [] by apply: skipn_all2; lia.
  by rewrite E1 E2 /dotl /=; ring.
case: Hloop => sf [Hex [K [T [F [B [Sh Pf]]]]]].
exists sf; split.
  rewrite (run_forback _ _ _ _ _ _ 0 h) //.
  have Hdown : exec_down R (run body) (out_dvar nat i) (h - 1) N s2 = Some sf.
    case: (Nat.eq_dec N 0) => [E0 | Hn0]; first by rewrite E0 in Hex *.
    have := count_nat 0 h; rewrite -/N => HN.
    have -> : (h - 1)%Z = (Z.of_nat N - 1)%Z by lia.
    exact: Hex.
  by rewrite Hdown.
have Eput : oput O n (tangent (VArray xs)) = oset O n (tangent (VArray xs)).
  rewrite /oput; case: (in_dec dvar_eq_dec_c n (map snd O)) => [_ | Hni] //.
  have Hin : In n (map snd O).
    by apply/(in_map_iff _ _ _); exists (tangent (VArray lo), stored o).
  by case: (Hni Hin).
rewrite Eput.
split; first by move=> v Hb0 Hc0 Hp0 _; exact: K.
split.
  move=> _ _ o0 _ _; have Hbn : below c n by [].
  exact: (K n Hbn erefl I).
split; first by move=> _ _ o0 [<-]; rewrite Hav.
split; first exact: T.
split.
  apply: rev_frame_x_of; rewrite /inplace Hown.
  change (Some (stored o)) with (Some n).
  apply: (rev_frame_mono c c _ _ _ _ _ F (le_n c)) => m Hm; left.
  by rewrite oset_snd; exact: (proj1 (odel_snd O n m Hm)).
split.
  move=> t m Hi; case: (dvar_eq_dec_c m n) => [Em | Hne].
    subst m; rewrite B.
    by have := r_shape _ _ _ _ _ _ _ Hr t n Hi; rewrite Eyb.
  exact: (Sh t m (proj2 (odel_in O n t m) (conj Hi Hne))).
split; last by move=> *; rewrite /fold_back.
rewrite (pairing_odel O n _ sf Hnd HoO) (pairing_oset O s2 _ n _ Hok Hnd HoO).
rewrite (pairing_odel O n _ s2 Hnd HoO) -/O' Pf B Eyb.
by rewrite !(inner_tangent_zero (VArray lo) _ Hzl) /=; ring.
Qed.

(* The forward sweep of a scalar fold: the state starts from the initial value,
   and each step pushes it on the tape when it is recorded, then computes the
   next state by the primal computation of the body. *)
Lemma afwd_fold a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (forall p, initP = AVar p -> ~ is_array (vty (pw p))) ->
  (forall x y, psim_body (bP x y)) -> (forall x y, act_body (bP x y)) ->
  asim_fwd cv (AFold a loP hiP initP bP).
Proof.
move=> Hna IHb IHa L k c s wP pp tail eA eW eT eD te n ve ty m rec HA HW HT HD
  Hc Htc Htail [j [Ej Hj]] Hst Hrec Hev.
have HA0 := HA; have HW0 := HW; have HD0 := HD.
destruct eA, eW, eT, eD; simpl in HA, HW, HT, HD; try contradiction;
graph_split.
rename b into bA, b0 into bW, b1 into bT, b2 into bD.
match goal with
  H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ =>
  rename H into HbA end.
match goal with
  H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ =>
  rename H into HbW end.
match goal with
  H : forall (i1 : pv) (i2 : tvar W) (s1 : pv) (s2 : tvar W), _ |- _ =>
  rename H into HbT end.
match goal with
  H : forall (i1 : pv) (i2 : val (dual R)) (s1 : pv) (s2 : val (dual R)),
      _ |- _ =>
  rename H into HbD end.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite /= in Htc.
case Eb: (ty_eqb (of_atom (amap pw loP)) Integer &&
  ty_eqb (of_atom (amap pw hiP)) Integer) Htc => // Htc.
case Er: (ty_eqb (of_atom (amap pw initP)) Real) Htc => Htc; last first.
  exfalso; move: Htc; case Eo: (of_atom (amap pw initP)) Er => [| | | nA] //.
  move=> _; move: Eo; case: (initP) Hna => [q | ? | ?] Hna //= Eo.
  have Har : is_array (vty (pw q)) by rewrite Eo.
  by move=> _; exact: (Hna q erefl Har).
move/ty_eqb_true: Er => Er.
destruct pp as [| | | ix0 sx0]; rewrite /= in Htc; try discriminate.
case HtB: (typecheck (option_map (amap pw) wP) ScalarBody (S (S k))
  (bW (VInfo k Integer None) (VInfo (S k) Real None))) Htc
  => [tb [| mm]] // Htc.
rewrite /= in Htc; case Etb: (ty_eqb tb Real) Htc => // -[Ete]; subst te.
move/ty_eqb_true: Etb HtB => -> HtB.
cbn [annotate_value_t rebuild_value fold_binders].
rewrite (fun w sv live0 recs lo hi init b nn rr =>
  (eq_refl : fwd_value W w m (AFold (FoldAnn sv live0 recs) lo hi init b) Real
    nn rr =
   Fresh "i" (fun i => let '(ix, sx) := open_fold sv Real nn (DBound i) false in
     sbind (prim W w m (b ix sx)) (fun r => Done (fwd_fold W (DBound i)
       (spell lo) (spell hi) (spell init) (sweep_eqb m Forward && live0) nn
       r))))).
cbn [open_pairs open_fold].
rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[sb vb] c2].
have Hc2 : (S c <= c2)%nat.
  by rewrite -[c2]/(snd (sb, vb, c2)) -Hob; exact: open_pairs_mono.
cbn [open_pairs]; split; first lia.
set n := DBound (j, j) in Hst Hrec *.
set i := DBound (c, c) in Hob *.
have Hsto : storage wP tail (AFold a loP hiP initP bP) = None.
  move: Hna; case: (initP) => [q | ? | ?] //= Hna.
  case Eq: (vty (pw q)) => [| | | nq] //.
  have Har : is_array (vty (pw q)) by rewrite Eq.
  by case: (Hna q erefl Har).
rewrite Hsto in Hst.
have Hatoms : forall aP, (aP = loP \/ aP = hiP \/ aP = initP) -> forall p,
    aP = AVar p -> In p L /\
    vatoms k (AFold ann (amap pa loP) (amap pa hiP) (amap pa initP) bA) p.
  move=> aP HaP p E; split.
    by case: HaP => [Ea | [Ea | Ea]]; subst aP; auto.
  rewrite /vatoms /= !atom_member_union.
  case: HaP => [Ea | [Ea | Ea]];
    by rewrite -Ea E /= Nat.eqb_refl /= ?orb_true_r.
have Hops := fun aP H => operand_store _ _ _ _ _ _ _ _ _ aP Hc (Hatoms aP H).
have Hl3 : loP = loP \/ loP = hiP \/ loP = initP by left.
have Hh3 : hiP = loP \/ hiP = hiP \/ hiP = initP by right; left.
have Hi3 : initP = loP \/ initP = hiP \/ initP = initP by right; right.
rewrite /= in Hev.
case Hlo: (aeval_atom (duals reals) (amap pd loP)) Hev
  => [[| l | | |] |] // Hev.
case Hhi: (aeval_atom (duals reals) (amap pd hiP)) Hev
  => [[| h | | |] |] // Hev.
case Hin: (aeval_atom (duals reals) (amap pd initP)) Hev => [s0 |] // Hev.
have Hslo := aspell_ok k s loP _ (Hops loP Hl3) Hlo.
have Hshi := aspell_ok k s hiP _ (Hops hiP Hh3) Hhi.
have Hsin := aspell_ok k s initP _ (Hops initP Hi3) Hin.
have Hint : has_type Real s0.
  rewrite -Er.
  exact: (atom_type k initP s0 (fun p E => proj1 (Hops initP Hi3 p E)) Hin).
destruct s0 as [d0 | | | |]; try contradiction.
set live := sweep_eqb m Forward && state_live cv k (amap pa initP) bA.
set bst := ((if live then [DPush (TapeOf n) (DVar n)] else []) ++ sb ++
  [DAssign (DVar n) vb])%list.
set pre := DDefine DMutable n (spell (amap pt initP)) ::
  (if live then [DTape (TapeOf n)] else []).
have Hnot : forall aP, (aP = loP \/ aP = hiP \/ aP = initP) -> forall p,
    aP = AVar p -> static_ok k p /\ pn p <> j.
  move=> aP HaP p E; split; first exact: (proj1 (Hops aP HaP p E)).
  move=> Ep; have := Hst p (proj1 (Hatoms aP HaP p E)).
  by rewrite /stored /n Ep.
have Hsta : forall aP, (aP = loP \/ aP = hiP \/ aP = initP) -> forall p,
    aP = AVar p -> static_ok k p.
  by move=> aP HaP p E; exact: (proj1 (Hops aP HaP p E)).
have [L1 _] := avoid_spell k loP j (Hnot loP Hl3).
have [H1' _] := avoid_spell k hiP j (Hnot hiP Hh3).
have [I1 _] := avoid_spell k initP j (Hnot initP Hi3).
set s1 := if live then store_set (store_set s (keyv n) (VReal (dfst d0)))
    (keyv (TapeOf n)) (VTape [])
  else store_set s (keyv n) (VReal (dfst d0)).
have Hrun1 : run pre s = Some s1.
  rewrite /pre /s1; case: (live); last exact: run_define Hsin.
  by rewrite -[_ :: [_]]/([_] ++ [_]) run_app (run_define _ _ _ _ _ Hsin).
have Hb1 : forall aP, (aP = loP \/ aP = hiP) -> forall z,
    xev s (spell (amap pt aP)) = Some (VInt z) ->
    xev s1 (spell (amap pt aP)) = Some (VInt z).
  move=> aP HaP z Hz.
  have HaP' : aP = loP \/ aP = hiP \/ aP = initP by case: HaP; auto.
  have [Hav _] := avoid_spell k aP j (Hnot aP HaP').
  have Hat : avoid (keyv (TapeOf n)) (spell (amap pt aP)).
    by apply: (avoid_tape_spell k); exact: Hsta aP HaP'.
  by rewrite /s1; case: (live); rewrite !xev_set_other.
rewrite (_ : run _ s = run (pre ++ [DFor i (spell (amap pt loP))
    (spell (amap pt hiP)) bst])%list s).
  by rewrite /fwd_fold /pre /bst; case: (live).
rewrite run_app Hrun1 (run_for _ _ _ _ _ _ l h
  (Hb1 _ (or_introl erefl) _ Hslo) (Hb1 _ (or_intror erefl) _ Hshi)).
set vr := fold_varied k (amap pa initP) bA.
set Inv := fun (z : Z) (s' : store R) (st : val (dual R))
    (tr : list (val (dual R))) =>
  fwd_frame c (Some n) None s s' /\ tkeep c (Some n) s s' /\
  store_get s' (keyv n) = Some (primal st) /\
  has_type Real st /\ (vr = false -> zero st) /\
  (live = true ->
   store_get s' (keyv (TapeOf n)) = Some (VTape (rev (map real_of tr)))).
have Hstep : forall z s' st tr st', Inv z s' st tr ->
    aeval (duals reals) (bD (VInt z) st) = Some st' ->
    exists s'', run bst (store_set s' (KVar (out_dvar nat i)) (VInt z)) =
      Some s'' /\ Inv (z + 1)%Z s'' st' (tr ++ [st])%list.
  move=> z s' st tr st' [Fr [Tk [Ns [Ht [Hz Tp]]]]] Hbd.
  case: st Ht Ns Hz Hbd => [ds | | | |] // _ Ns Hz Hbd.
  set s'' := store_set s' (keyv i) (VInt z).
  change (store_set s' (KVar (out_dvar nat i)) (VInt z)) with s''.
  have Hci : consistent i by [].
  have Kin : forall v, below c v -> consistent v -> keyv v <> keyv i.
    move=> v Hb Hcv K; have E := keyv_inj _ _ Hcv Hci K; subst v.
    by rewrite /i /= in Hb; lia.
  have Hbn : below c n by [].
  have Hcn : consistent n by [].
  have Hctn : consistent (TapeOf n) by [].
  have N'' : store_get s'' (keyv n) = Some (VReal (dfst ds)).
    rewrite /s'' store_get_set_other; first by apply/not_eq_sym/Kin.
    exact: Ns.
  set sp := if live then store_set s'' (keyv (TapeOf n))
      (VTape (dfst ds :: rev (map real_of tr)))
    else s''.
  have Rp : run (if live then [DPush (TapeOf n) (DVar n)] else []) s'' =
      Some sp.
    rewrite /sp; case El: (live) => //.
    apply: run_push; first exact: N''.
    by rewrite /s'' store_get_set_other //; exact: (Tp El).
  have Np : store_get sp (keyv n) = Some (VReal (dfst ds)).
    by rewrite /sp; case: (live) => //; rewrite store_get_set_other.
  have Hsp : forall v, below c v -> consistent v -> ~ is_tape v ->
      store_get sp (keyv v) = store_get s' (keyv v).
    move=> v Hb Hcv Htv; rewrite /sp; case: (live).
      rewrite store_get_set_other.
        by move=> /(keyv_inj _ _ Hctn Hcv) E; subst v; exact: Htv I.
      by rewrite /s'' store_get_set_other //; apply/not_eq_sym/Kin.
    by rewrite /s'' store_get_set_other //; apply/not_eq_sym/Kin.
  have Tsp : tkeep c (Some n) s' sp.
    apply: (tkeep_trans _ _ _ s'').
      by rewrite /s''; apply: tkeep_set => //=; tauto.
    rewrite /sp; case: (live); last exact: tkeep_refl.
    by apply: tkeep_set_tape => //; right.
  set ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c)))
    (VInt z) c.
  set sx := PV (AV (S k) vr) (VInfo (S k) Real None)
    (TVar n Real None vr vr vr false None) (VReal ds) j.
  have Hix : static_ok (S (S k)) ix.
    by repeat split; simpl; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    by repeat split; simpl; auto; try lia; discriminate.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    apply: Forall_cons Hsx _; apply: Forall_cons Hix _.
    apply: Forall_impl HL => p Hp; by apply: static_mono Hp _; lia.
  have Hlive_b : forall p, In p L ->
      live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None))
        p ->
      live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (amap pw initP) bW)
        p.
    move=> p Hp; rewrite /live_anf /live_value /=.
    rewrite -(live_cont2 L k bP bW ix sx (VInfo k Integer None)
      (VInfo (S k) Real None) _ HbW HL erefl erefl erefl erefl) => ->.
    by rewrite !orb_true_r.
  have Hctx : actx (sx :: ix :: L) (S (S k)) (S c) sp wP PScalar
      (live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None)))
      (live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None)))
      Real.
    constructor.
    - apply: sctx_scalar; first exact: HL'.
      + move=> p q [<- | [<- | Hp]] [<- | [<- | Hq]] E //; rewrite /= in E;
          try lia;
          try (have [_ [Hq' _]] := static_in _ _ _ HL Hq; rewrite /= in E; lia);
          try (have [_ [Hp' _]] := static_in _ _ _ HL Hp; rewrite /= in E; lia).
        exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
      + move=> p [<- | [<- | Hp]] /=; [lia | lia |].
        by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
      move=> a0 /(s_written _ _ _ _ _ _ _ Hs) [y [-> [Hy Hv]]].
      by exists y; split=> //; split; [right; right |].
    - move=> p [<- | [<- | Hp]] //.
      exact: (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp).
    - move=> p [<- | [<- | Hp]] Hl.
      + exact: Np.
      + rewrite /sp; case: (live).
          by rewrite store_get_set_other // /s'' store_get_set_same.
        by rewrite /s'' store_get_set_same.
      have Hpc := s_num _ _ _ _ _ _ _ Hs _ Hp.
      have Hbp : below c (stored p) by [].
      have Htp' : ~ is_tape (stored p) by rewrite /=; tauto.
      rewrite (Hsp (stored p) Hbp erefl Htp').
      have Hne : Some n <> Some (stored p).
        by move=> E; have := Hst p Hp; congruence.
      rewrite (Fr (stored p) Hbp erefl Htp' Hne) //.
      exact: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp
        (live_vatoms _ _ _ _ _ p HA0 HW0 HL Hp (Hlive_b p Hp Hl))).
    - move=> p [<- | [<- | Hp]] Hrc //.
      have [lt Hlt] := a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hrc.
      exact: (proj1 (tkeep_trans _ _ _ _ _ Tk Tsp) _ _ Hlt).
    - by [].
    by [].
  have := IHb ix sx (sx :: ix :: L) (S (S k)) (S c) sp wP PScalar m Replay
    (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bT (pt ix) (pt sx))
    (bD (pd ix) (pd sx)) Real st' (HbA ix _ sx _) (HbW ix _ sx _)
    (HbT ix _ sx _) (HbD ix _ sx _) Hctx HtB Hbd
    (fun o Ho _ => False_ind _ (owner_scalar_none _ _ Ho)).
  rewrite Hob => -[_ [s3 [R3 [F3 [T3 [X3 _]]]]]].
  have [Hht' Hz'] := IHa ix sx (sx :: ix :: L) (S (S k)) wP PScalar
    (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bD (pd ix) (pd sx)) Real st'
    (HbA ix _ sx _) (HbW ix _ sx _) (HbD ix _ sx _) HL' HtB Hbd.
  case: st' Hht' Hz' X3 {Hbd} => [ds' | | | |] // _ Hz' X3.
  set s4 := store_set s3 (keyv n) (VReal (dfst ds')).
  exists s4; split.
    rewrite /bst run_app Rp run_app R3.
    by rewrite (run_assign_var _ _ _ (VReal (dfst ds')) _ X3).
  split.
    move=> v Hb Hcv Htv Hex Hvo.
    rewrite /s4 store_get_set_other.
      by move=> /(keyv_inj _ _ Hcn Hcv) E; subst v; apply: Hex.
    have HcS := Nat.le_succ_diag_r c.
    rewrite (F3 v (below_mono c (S c) v Hb HcS) Hcv Htv) //.
    by rewrite (Hsp v Hb Hcv Htv); exact: (Fr v Hb Hcv Htv Hex Hvo).
  split.
    apply: (tkeep_trans _ _ _ s'); first exact: Tk.
    apply: (tkeep_trans _ _ _ sp); first exact: Tsp.
    apply: (tkeep_trans _ _ _ s3).
      exact: (tkeep_none _ _ _ _
        (tkeep_mono _ _ _ _ _ T3 (Nat.le_succ_diag_r c))).
    by rewrite /s4; apply: tkeep_set => //=; tauto.
  split; first by rewrite /s4 store_get_set_same.
  split=> //; split.
    move=> Hv; apply: Hz'.
    move: (Hv); rewrite /vr /fold_varied => /orb_false_iff [_ Hb'].
    by rewrite /sx /= Hv.
  move=> El; rewrite /s4 store_get_set_other //.
  have Hbn' := below_mono c (S c) n Hbn (Nat.le_succ_diag_r c).
  rewrite (proj2 T3 n Hbn' erefl) //.
  by rewrite /sp El store_get_set_same map_app rev_app_distr.
have Hcn0 : consistent n by [].
have Hctn : consistent (TapeOf n) by [].
have Hinit : Inv l s1 (VReal d0) [].
  split.
    move=> v Hb Hcv Ht Hex _.
    have Hvn : keyv n <> keyv v.
      move=> K; have E := keyv_inj _ _ Hcn0 Hcv K; subst v.
      exact: (Hex erefl).
    rewrite /s1; case: (live); last by rewrite store_get_set_other.
    rewrite store_get_set_other; last by rewrite store_get_set_other.
    by move=> K; have E := keyv_inj _ _ Hctn Hcv K; subst v; exact: Ht I.
  split.
    rewrite /s1; case: (live); last by apply: tkeep_set => //=; tauto.
    apply: (tkeep_trans _ _ _ (store_set s (keyv n) (VReal (dfst d0)))).
      by apply: tkeep_set => //=; tauto.
    by apply: tkeep_set_tape => //; right.
  split.
    rewrite /s1; case: (live); last exact: store_get_set_same.
    by rewrite store_get_set_other // store_get_set_same.
  split; first exact: Hint.
  split.
    move=> Hv; move: (Hv); rewrite /vr /fold_varied => /orb_false_iff [Hvi _].
    exact: (atom_zero k initP _ (Hsta initP Hi3) Hvi Hin).
  by move=> El; rewrite /s1 El store_get_set_same.
have [sf [tr [Hex [Htr [Fs [Ts [Ns [_ [_ Tps]]]]]]]]] :=
  fold_loop (fun v w => aeval (duals reals) (bD v w)) (run bst)
    (out_dvar nat i) Inv Hstep (count l h) l s1 (VReal d0) [] ve Hinit Hev.
exists sf; split; first by rewrite Hex.
split; first exact: Fs.
split; first exact: Ts.
split; first exact: Ns.
split; last by move=> _ Hnl; case: Hnl.
case=> Hm _; rewrite /fold_tape Hlo Hhi Hin => tr' Htr'.
rewrite Htr in Htr'; case: Htr' => <-.
split; first by move=> _ Hlv; apply: Tps; rewrite /live Hm Hlv.
by rewrite Er.
Qed.

(* The reverse sweep of a scalar fold: a loop down the steps, popping the
   state before the step when it is recorded, replaying the body and
   transposing it from the adjoint of the state after the step; the adjoint
   of the state before the first step goes to the initial value. *)
Lemma arev_fold a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (forall p, initP = AVar p -> ~ is_array (vty (pw p))) ->
  (forall x y, asim_body cv (bP x y)) -> (forall x y, act_body (bP x y)) ->
  asim_rev cv (AFold a loP hiP initP bP).
Proof.
move=> Hna IHb IHa L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT HD Hs
  Hbar Htc Htail [j [Ej Hj]] Hst Hev Hvr.
have HA0 := HA; have HW0 := HW; have HD0 := HD.
destruct eA, eW, eT, eD; simpl in HA, HW, HT, HD; try contradiction;
graph_split.
rename b into bA, b0 into bW, b1 into bT, b2 into bD.
match goal with
  H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ =>
  rename H into HbA end.
match goal with
  H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ =>
  rename H into HbW end.
match goal with
  H : forall (i1 : pv) (i2 : tvar W) (s1 : pv) (s2 : tvar W), _ |- _ =>
  rename H into HbT end.
match goal with
  H : forall (i1 : pv) (i2 : val (dual R)) (s1 : pv) (s2 : val (dual R)),
      _ |- _ =>
  rename H into HbD end.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite /= in Htc.
case Eb: (ty_eqb (of_atom (amap pw loP)) Integer &&
  ty_eqb (of_atom (amap pw hiP)) Integer) Htc => // Htc.
case Er: (ty_eqb (of_atom (amap pw initP)) Real) Htc => Htc; last first.
  exfalso; move: Htc; case Eo: (of_atom (amap pw initP)) Er => [| | | nA] //.
  move=> _; move: Eo; case: (initP) Hna => [q | ? | ?] Hna //= Eo.
  have Har : is_array (vty (pw q)) by rewrite Eo.
  by move=> _; exact: (Hna q erefl Har).
move/ty_eqb_true: Er => Er.
destruct pp as [| | | ix0 sx0]; rewrite /= in Htc; try discriminate.
case HtB: (typecheck (option_map (amap pw) wP) ScalarBody (S (S k))
  (bW (VInfo k Integer None) (VInfo (S k) Real None))) Htc
  => [tb [| mm]] // Htc.
rewrite /= in Htc; case Etb: (ty_eqb tb Real) Htc => // -[Ete]; subst te.
move/ty_eqb_true: Etb HtB => -> HtB.
cbn [annotate_value_t rebuild_value fold_binders].
rewrite (fun w sv live0 recs lo hi init b nn =>
  (eq_refl : rev_value W w vo (AFold (FoldAnn sv live0 recs) lo hi init b) Real
    nn =
   Fresh "i" (fun i => Fresh "r" (fun r =>
     let '(ix, sx) := open_fold sv Real nn (DBound i) false in
     sbind (adj W w vo Replay (b ix sx) (DVar (BarOf (DBound r)))) (fun sw =>
       Done (rev_loop W (DBound i) (spell lo) (spell hi)
         (if live0 then [DPop (TapeOf nn) (DVar nn)] else [])
         [DDefine (DConstant Real) (BarOf (DBound r)) (DVar (BarOf nn));
          DAssign (DVar (BarOf nn)) (DReal "0")] sw ++
         match bar init with
         | Some bi => [DIncrement bi (DVar (BarOf nn))]
         | None => [] end)%list))))).
cbn [open_pairs open_fold].
rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S (S c))) => [[fb rb] c2].
have Hc2 : (S (S c) <= c2)%nat.
  by rewrite -[c2]/(snd (fb, rb, c2)) -Hob; exact: open_pairs_mono.
cbn [open_pairs]; split; first lia.
move=> s2 O Hrd Hr Hns Htp Hft _.
set n := DBound (j, j) in Hst Hft Hns Hrd Htp Hr *.
set i := DBound (c, c) in Hob *.
set r := DBound (S c, S c) in Hob *.
have Hsto : storage wP tail (AFold a loP hiP initP bP) = None.
  move: Hna; case: (initP) => [q | ? | ?] //= Hna.
  case Eq: (vty (pw q)) => [| | | nq] //.
  have Har : is_array (vty (pw q)) by rewrite Eq.
  by case: (Hna q erefl Har).
rewrite Hsto in Hst; have [Hn_notin Hsh] := Hns Hsto.
have {}Hft := Hft (or_introl erefl).
rewrite /= in Hev.
case Hlo: (aeval_atom (duals reals) (amap pd loP)) Hev
  => [[| l | | |] |] // Hev.
case Hhi: (aeval_atom (duals reals) (amap pd hiP)) Hev
  => [[| h | | |] |] // Hev.
case Hin: (aeval_atom (duals reals) (amap pd initP)) Hev => [s0 |] // Hev.
have [tr Htr] := fold_trace_exists _ _ _ _ _ Hev.
have Htape : state_live cv k (amap pa initP) bA = true ->
    store_get s2 (keyv (TapeOf n)) = Some (VTape (rev (map real_of tr))).
  move=> Hl; move: Hft; rewrite /fold_tape Hlo Hhi Hin => /(_ tr Htr) [Ht _].
  by apply: Ht => //; rewrite Er.
set N := count l h.
set dflt := VReal (Dual 0 0).
set st := fun jn => nth jn (tr ++ [ve]) dflt.
have [Hlen [Hst0 Hstep]] := fold_trace_step _ _ _ _ _ _ dflt Hev Htr.
set vr := fold_varied k (amap pa initP) bA.
have Hsta : forall aP, (aP = loP \/ aP = hiP \/ aP = initP) -> forall p,
    aP = AVar p -> static_ok k p.
  move=> aP HaP p E; apply: (static_in _ _ _ HL).
  by case: HaP => [Ea | [Ea | Ea]]; subst aP; auto.
have Hi3 : initP = loP \/ initP = hiP \/ initP = initP by right; right.
have Hstates : forall jn, (jn <= N)%nat ->
    has_type Real (st jn) /\ (vr = false -> zero (st jn)).
  elim=> [| jn IH] Hjn.
    rewrite /st Hst0; split.
      by rewrite -Er; exact: (atom_type k initP s0 (Hsta initP Hi3) Hin).
    move=> Hv; move: Hv; rewrite /vr /fold_varied => /orb_false_iff [Hvi _].
    exact: (atom_zero k initP _ (Hsta initP Hi3) Hvi Hin).
  have Hjn' : (jn <= N)%nat by lia.
  have [Hr0 Hz0] := IH Hjn'.
  have Hjl : (jn < count l h)%nat by rewrite /N in Hjn; lia.
  have Hs1 := Hstep jn Hjl.
  have Est : st jn = nth jn tr dflt by rewrite /st app_nth1 //; lia.
  rewrite Est in Hr0 Hz0.
  set ix := PV (fresh k) (VInfo k Integer None)
    (open_index (DBound (0%nat, 0%nat))) (VInt (l + Z.of_nat jn)) 0.
  set sx := PV (AV (S k) vr) (VInfo (S k) Real None)
    (TVar (DBound (0%nat, 0%nat)) Real None vr vr vr false None)
    (nth jn tr dflt) 0.
  have Hix : static_ok (S (S k)) ix.
    by repeat split; simpl; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    by repeat split; simpl; auto; try lia; discriminate.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    apply: Forall_cons Hsx _; apply: Forall_cons Hix _.
    apply: Forall_impl HL => p Hp; by apply: static_mono Hp _; lia.
  have [Hht Hz] := IHa ix sx (sx :: ix :: L) (S (S k)) wP PScalar
    (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bD (pd ix) (pd sx)) Real
    (st (S jn)) (HbA ix _ sx _) (HbW ix _ sx _) (HbD ix _ sx _) HL' HtB Hs1.
  split=> // Hv; apply: Hz.
  move: (Hv); rewrite /vr /fold_varied => /orb_false_iff [_ Hb'].
  by rewrite /sx /= Hv.
have Hlh : forall aP, (aP = loP \/ aP = hiP) -> forall p, aP = AVar p ->
    static_ok k p /\ store_get s2 (keyv (stored p)) = Some (primal (pd p)).
  move=> aP HaP p E.
  have HaP' : aP = loP \/ aP = hiP \/ aP = initP by case: HaP; auto.
  split; first exact: (Hsta aP HaP' p E).
  have Hp : In p L by case: HaP => Ea; subst aP; auto.
  apply: (Hrd p Hp); last by left.
    rewrite /vreads; cbn [value_needs fold_binders].
    case: (needs cv Replay (S (S k)) _) => u0 l0 /=.
    rewrite !atom_member_union.
    by case: HaP => Ea; rewrite -Ea E /= ?Nat.eqb_refl /= ?orb_true_r.
  rewrite /live_value /=.
  by case: HaP => Ea; rewrite -Ea E /= ?Nat.eqb_refl /= ?orb_true_r.
have Hslo := aspell_ok k s2 loP _ (Hlh loP (or_introl erefl)) Hlo.
have Hshi := aspell_ok k s2 hiP _ (Hlh hiP (or_intror erefl)) Hhi.
have Hve : st N = ve.
  by rewrite /st app_nth2 ?Hlen /N ?Nat.sub_diag //; lia.
have [HveR _] := Hstates N (le_n N); rewrite Hve in HveR.
destruct ve as [dv | | | |]; try contradiction.
rewrite /= in Hsh.
case Eb0: (barv s2 n) Hsh => [[b0 | | | |] |] // _.
set live := state_live cv k (amap pa initP) bA.
set dso := fun v : val (dual R) => match v with VReal d => dsnd d | _ => 0 end.
set body := ((if live then [DPop (TapeOf n) (DVar n)] else []) ++ fb ++
  [DDefine (DConstant Real) (BarOf r) (DVar (BarOf n));
   DAssign (DVar (BarOf n)) (DReal "0")] ++ rb)%list.
set P := fun (jn : nat) (s' : store R) =>
  (forall v, below c v -> consistent v -> is_primal v -> v <> n ->
     store_get s' (keyv v) = store_get s2 (keyv v)) /\
  tkeep c (Some n) s2 s' /\
  rev_frame_x c (inplace wP PTop) n
    ((TangentCorrect.tangent (VReal dv), n) :: O) s2 s' /\
  (live = true -> store_get s' (keyv (TapeOf n)) =
     Some (VTape (rev (map real_of (firstn jn tr))))) /\
  (forall t m, In (t, m) O -> shaped t (barv s' m)) /\
  exists b, barv s' n = Some (VReal b) /\
    pairing O s' + dso (st jn) * b = pairing O s2 + dsnd dv * b0.
have Hstep' : forall jn s, (jn < N)%nat -> P (S jn) s ->
    exists s', run body (store_set s (KVar (out_dvar nat i))
      (VInt (l + Z.of_nat jn))) = Some s' /\ P jn s'.
  move=> jn s Hjn [K0 [T0 [F0 [Tp0 [S0 [b1 [Eb1 P0]]]]]]].
  have run_pop : forall s t x v xs,
      store_get s (keyv (TapeOf t)) = Some (VTape (v :: xs)) ->
      run [DPop (TapeOf t) (DVar x)] s =
      Some (store_set (store_set s (keyv (TapeOf t)) (VTape xs)) (keyv x)
        (VReal v)).
    by move=> s' t x v xs Ht; rewrite /run /keyv /= in Ht *; rewrite Ht.
  set sj := nth jn tr dflt.
  have Esj : st jn = sj by rewrite /st /sj app_nth1 //; lia.
  have Hjn1 : (jn <= N)%nat by lia.
  have [Hrj Hzj] := Hstates jn Hjn1; rewrite Esj in Hrj Hzj.
  have Hjn2 : (S jn <= N)%nat by lia.
  have [Hrj' Hzj'] := Hstates (S jn) Hjn2.
  have Hbd := Hstep jn Hjn; rewrite -/sj in Hbd.
  case Edj: sj Hrj Hzj Hbd => [dj | | | |] // _ Hzj Hbd.
  set z := (l + Z.of_nat jn)%Z.
  set s'' := store_set s (keyv i) (VInt z).
  change (store_set s (KVar (out_dvar nat i)) (VInt z)) with s''.
  have Hci : consistent i by [].
  have Hcn : consistent n by [].
  have Hctn : consistent (TapeOf n) by [].
  have Kin : forall v, below c v -> consistent v -> keyv v <> keyv i.
    move=> v Hb Hcv K; have E := keyv_inj _ _ Hcv Hci K; subst v.
    by rewrite /i /= in Hb; lia.
  have Hbn : below c n by [].
  set sp := if live then store_set (store_set s'' (keyv (TapeOf n))
      (VTape (rev (map real_of (firstn jn tr))))) (keyv n) (VReal (dfst dj))
    else s''.
  have Rp : run (if live then [DPop (TapeOf n) (DVar n)] else []) s'' =
      Some sp.
    rewrite /sp; case El: (live) => //.
    apply: run_pop.
    rewrite /s'' store_get_set_other; first by move=> /(keyv_inj _ _ Hci Hctn).
    rewrite (Tp0 El).
    have Ef : forall (A : Type) (xs : list A) m d, (m < length xs)%nat ->
        firstn (S m) xs = (firstn m xs ++ [nth m xs d])%list.
      move=> A; elim=> [| x xs IH] [| m] d Hm //=; rewrite /= in Hm; try lia.
      by congr (_ :: _); apply: IH; lia.
    have Hjt : (jn < length tr)%nat by rewrite Hlen.
    by rewrite (Ef _ tr jn dflt Hjt) -/sj Edj map_app rev_app_distr.
  set ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c)))
    (VInt z) c.
  set sx := PV (AV (S k) vr) (VInfo (S k) Real None)
    (TVar n Real None vr vr vr false None) (VReal dj) j.
  have Hix : static_ok (S (S k)) ix.
    by repeat split; simpl; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    by repeat split; simpl; auto; try lia; discriminate.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    apply: Forall_cons Hsx _; apply: Forall_cons Hix _.
    apply: Forall_impl HL => p Hp; by apply: static_mono Hp _; lia.
  have Hrm : forall p, In p L -> forall l0,
      atom_member (AVar (pa p))
        (atom_remove (AVar (pa sx)) (atom_remove (AVar (pa ix)) l0)) =
      atom_member (AVar (pa p)) l0.
    move=> p Hp l0; have [Eid [Hk _]] := static_in _ _ _ HL Hp.
    rewrite !atom_member_remove_full /same_term.
    change (aid (pa sx)) with (S k); change (aid (pa ix)) with k.
    have Hk1 : k <> aid (pa p) by lia.
    have Hk2 : S k <> aid (pa p) by lia.
    by rewrite (proj2 (Nat.eqb_neq _ _) Hk1) (proj2 (Nat.eqb_neq _ _) Hk2).
  have Hreads : forall p, In p L ->
      tbr cv Replay (S (S k)) (bA (pa ix) (pa sx)) p ->
      vreads cv k (AFold ann (amap pa loP) (amap pa hiP) (amap pa initP) bA)
        p.
    move=> p Hp; rewrite /tbr /vreads; cbn [value_needs fold_binders].
    change (AV k false) with (pa ix).
    change (AV (S k) (fold_varied k (amap pa initP) bA)) with (pa sx).
    case: (needs cv Replay (S (S k)) (bA (pa ix) (pa sx))) => u l0 /= Ht.
    by rewrite atom_member_union (Hrm p Hp) Ht orb_true_r.
  have Hflows : forall p, In p L ->
      useful cv Replay (S (S k)) (bA (pa ix) (pa sx)) p ->
      vflows cv k (AFold ann (amap pa loP) (amap pa hiP) (amap pa initP) bA)
        p.
    move=> p Hp; rewrite /useful /vflows; cbn [value_needs fold_binders].
    change (AV k false) with (pa ix).
    change (AV (S k) (fold_varied k (amap pa initP) bA)) with (pa sx).
    case: (needs cv Replay (S (S k)) (bA (pa ix) (pa sx))) => u l0 /= Ht.
    by rewrite atom_member_union (Hrm p Hp) Ht orb_true_r.
  have Hlive_b : forall p, In p L ->
      live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None))
        p ->
      live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (amap pw initP) bW)
        p.
    move=> p Hp; rewrite /live_anf /live_value /=.
    rewrite -(live_cont2 L k bP bW ix sx (VInfo k Integer None)
      (VInfo (S k) Real None) _ HbW HL erefl erefl erefl erefl) => ->.
    by rewrite !orb_true_r.
  have Np : live = true -> store_get sp (keyv n) = Some (VReal (dfst dj)).
    by move=> El; rewrite /sp El store_get_set_same.
  have Isp : store_get sp (keyv i) = Some (VInt z).
    rewrite /sp; case: (live); last exact: store_get_set_same.
    rewrite store_get_set_other.
      by move=> /(keyv_inj _ _ Hcn Hci) [] *; lia.
    rewrite store_get_set_other; first by move=> /(keyv_inj _ _ Hctn Hci).
    exact: store_get_set_same.
  have Hsp : forall v, below c v -> consistent v -> ~ is_tape v -> v <> n ->
      store_get sp (keyv v) = store_get s (keyv v).
    move=> v Hb Hcv Htv Hne; rewrite /sp; case: (live).
      rewrite store_get_set_other.
        by move=> /(keyv_inj _ _ Hcn Hcv) E; apply: Hne.
      rewrite store_get_set_other.
        by move=> /(keyv_inj _ _ Hctn Hcv) E; subst v; exact: Htv I.
      by rewrite /s'' store_get_set_other //; apply/not_eq_sym/Kin.
    by rewrite /s'' store_get_set_other //; apply/not_eq_sym/Kin.
  have Tsp : tkeep c (Some n) s sp.
    apply: (tkeep_trans _ _ _ s'').
      by rewrite /s''; apply: tkeep_set => //=; tauto.
    rewrite /sp; case: (live); last exact: tkeep_refl.
    apply: (tkeep_trans _ _ _ (store_set s'' (keyv (TapeOf n))
      (VTape (rev (map real_of (firstn jn tr)))))).
      by apply: tkeep_set_tape => //; right.
    by apply: tkeep_set => //=; tauto.
  have Tpsp : live = true -> store_get sp (keyv (TapeOf n)) =
      Some (VTape (rev (map real_of (firstn jn tr)))).
    move=> El; rewrite /sp El store_get_set_other.
      by move=> /(keyv_inj _ _ Hcn Hctn).
    exact: store_get_set_same.
  have Hctx : actx (sx :: ix :: L) (S (S k)) (S (S c)) sp wP PScalar
      (live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None)))
      (tbr cv Replay (S (S k)) (bA (pa ix) (pa sx))) Real.
    constructor.
    - apply: sctx_scalar; first exact: HL'.
      + move=> p q [<- | [<- | Hp]] [<- | [<- | Hq]] E //; rewrite /= in E;
          try lia;
          try (have [_ [Hq' _]] := static_in _ _ _ HL Hq; rewrite /= in E; lia);
          try (have [_ [Hp' _]] := static_in _ _ _ HL Hp; rewrite /= in E; lia).
        exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
      + move=> p [<- | [<- | Hp]] /=; [lia | lia |].
        by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
      move=> a0 /(s_written _ _ _ _ _ _ _ Hs) [y [-> [Hy Hv]]].
      by exists y; split=> //; split; [right; right |].
    - by move=> p [<- | [<- | Hp]] //; exact: Hbar.
    - move=> p [<- | [<- | Hp]] Ht.
      + exact: (Np Ht).
      + exact: Isp.
      have Hlb : live_anf (S (S k))
          (bW (VInfo k Integer None) (VInfo (S k) Real None)) p.
        exact: (tbr_occurs (sx :: ix :: L) (S (S k)) (bP ix sx)
          (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) Replay p
          (HbA ix _ sx _) (HbW ix _ sx _) HL' (or_intror (or_intror Hp))
          (or_introl Ht)).
      have Hpc := s_num _ _ _ _ _ _ _ Hs _ Hp.
      have Hbp : below c (stored p) by [].
      have Htp' : ~ is_tape (stored p) by rewrite /=; tauto.
      rewrite (Hsp (stored p) Hbp erefl Htp' (Hst p Hp)).
      rewrite (K0 (stored p) Hbp erefl I (Hst p Hp)).
      exact: (Hrd p Hp (Hreads p Hp Ht) (Hlive_b p Hp Hlb) (or_introl I)).
    - move=> p [<- | [<- | Hp]] Hrc //.
      have [lt Hlt] := Htp p Hp Hrc.
      exact: (proj1 (tkeep_trans _ _ _ _ _ T0 Tsp) _ _ Hlt).
    - by [].
    by [].
  rewrite -/(st (S jn)) in Hbd.
  case Est': (st (S jn)) Hrj' Hbd => [dj' | | | |] // _ Hbd.
  have := IHb ix sx (sx :: ix :: L) (S (S k)) (S (S c)) sp wP PScalar Replay
    (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bT (pt ix) (pt sx))
    (bD (pd ix) (pd sx)) Real (VReal dj') (DVar (BarOf r)) vo
    (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _) Hctx I HtB
    Hbd.
  have Hnf : forall P : Prop, Replay = Forward -> P by [].
  have Hpb : Replay = Replay -> PScalar <> PTop by [].
  move=> /(_ (Hnf _) (Hnf _) (Hnf _) Hpb (Hnf _)).
  rewrite Hob => -[_ [_ [s1 [R1 [F1 [T1 [_ Hrev]]]]]]].
  cbn [inplace owner option_map sweep_eqb] in F1, T1, Hrev.
  have Hnb : forall v, ~ is_tape v -> below (S (S c)) v -> consistent v ->
      store_get s1 (keyv v) = store_get sp (keyv v).
    by move=> v Ht Hb Hcv; exact: (F1 v Hb Hcv Ht).
  have Hbn2 : below (S (S c)) n by rewrite /n /=; lia.
  have Hntn : ~ is_tape n by rewrite /=; tauto.
  have Hntb : ~ is_tape (BarOf n) by rewrite /=; tauto.
  have B1 : barv s1 n = Some (VReal b1).
    rewrite /barv (Hnb (BarOf n) Hntb Hbn2 erefl).
    have Hnen : BarOf n <> n by [].
    by rewrite (Hsp (BarOf n) Hbn erefl Hntb Hnen); exact: Eb1.
  set smid := store_set (store_set s1 (keyv (BarOf r)) (VReal b1))
    (keyv (BarOf n)) (VReal 0).
  have Rm : run ([DDefine (DConstant Real) (BarOf r) (DVar (BarOf n));
      DAssign (DVar (BarOf n)) (DReal "0")] ++ rb)%list s1 = run rb smid.
    rewrite -[(_ ++ rb)%list]/([_] ++ (_ :: rb))%list run_app.
    rewrite (run_define s1 (DConstant Real) (BarOf r) (DVar (BarOf n))
      (VReal b1) B1).
    by apply: run_assign_var; rewrite xev_DReal lit_0.
  have Hcr : consistent r by [].
  have Hown_b : forall t m, In (t, m) O -> barv smid m = barv s m.
    move=> t m Hi; have [jm [Em Hjm]] := r_below _ _ _ _ _ _ _ Hr t m Hi.
    subst m.
    have Hcm : consistent (DBound (jm, jm)) by [].
    have Hrjm : r <> DBound (jm, jm) by move=> [] *; lia.
    have Hnm : n <> DBound (jm, jm).
      move=> E; apply: Hn_notin; rewrite E; apply/in_map_iff.
      by exists (t, DBound (jm, jm)).
    rewrite /smid (barv_set_other _ _ _ _ Hcn Hcm Hnm).
    rewrite (barv_set_other _ _ _ _ Hcr Hcm Hrjm).
    have Hbm2 : below (S (S c)) (BarOf (DBound (jm, jm))) by rewrite /=; lia.
    have Hbm : below c (BarOf (DBound (jm, jm))) by [].
    have Htm : ~ is_tape (BarOf (DBound (jm, jm))) by rewrite /=; tauto.
    have Hnm' : BarOf (DBound (jm, jm)) <> n by [].
    by rewrite /barv (Hnb _ Htm Hbm2 erefl) (Hsp _ Hbm erefl Htm Hnm').
  set O' := (TangentCorrect.tangent (VReal dj), n) :: O.
  have Hr1 : rctx (sx :: ix :: L) (S (S c)) wP PScalar O'
      (useful cv Replay (S (S k)) (bA (pa ix) (pa sx))) smid.
    constructor.
    - by constructor; [exact: Hn_notin | exact: (r_nodup _ _ _ _ _ _ _ Hr)].
    - move=> t m [[<- <-] | Hi].
        by rewrite /smid barv_set_same.
      by rewrite (Hown_b t m Hi); exact: S0.
    - move=> t m [[_ <-] | Hi].
        by exists j; split=> //; lia.
      have [jm [E Hjm]] := r_below _ _ _ _ _ _ _ Hr t m Hi.
      by exists jm; split=> //; lia.
    - move=> p [<- | [<- | Hp]] Hu Hv //; first by left.
      by right; exact: (r_useful _ _ _ _ _ _ _ Hr p Hp (Hflows p Hp Hu) Hv).
    - move=> p t [<- | [<- | Hp]] Hu [E | Hio].
      + by case: E => <-.
      + by exfalso; apply: Hn_notin; apply/in_map_iff; exists (t, n).
      + by case: E => *; lia.
      + have [jm [E Hjm]] := r_below _ _ _ _ _ _ _ Hr _ _ Hio.
        by case: E => *; lia.
      + by case: E => _ E2 _; have := Hst p Hp; rewrite /n E2.
      exact: (r_value _ _ _ _ _ _ _ Hr p t Hp (Hflows p Hp Hu) Hio).
    - by [].
    - move=> p ny0 r0 [<- | [<- | Hp]] Hv //.
      exact: (r_args _ _ _ _ _ _ _ Hr p ny0 r0 Hp Hv).
    exact: (r_written _ _ _ _ _ _ _ Hr).
  have Kbr : forall x v : dvar W, consistent v -> ~ is_bar v ->
      keyv (BarOf x) <> keyv v.
    move=> x v Hcv Hb.
    by case: v Hcv Hb => [[? ?] | ? | ? | ? |] //= _ _; rewrite /keyv.
  have Hmid : forall v, consistent v -> ~ is_bar v ->
      store_get smid (keyv v) = store_get s1 (keyv v).
    by move=> v Hcv Hb; rewrite /smid !store_get_set_other //; apply: Kbr.
  have Tmid : tkeep (S (S c)) None s1 smid.
    apply: (tkeep_trans _ _ _ (store_set s1 (keyv (BarOf r)) (VReal b1))).
      by apply: tkeep_set => //=; tauto.
    by apply: tkeep_set => //=; tauto.
  have Hcbn : consistent (BarOf n) by [].
  have Hcbr : consistent (BarOf r) by [].
  have Ebr : barv smid r = Some (VReal b1).
    rewrite /smid /barv store_get_set_other.
      by move=> /(keyv_inj _ _ Hcbn Hcbr) [] *; lia.
    exact: store_get_set_same.
  have Hseed : seed_ok (S (S c)) Real (DVar (BarOf r)) smid.
    split.
      by move=> y /= [<- | []]; split; [rewrite /r /=; lia |].
    by move=> _; exists b1; exact: Ebr.
  have Hag : agree_prim c2 None s1 smid.
    split.
      move=> v _ Hcv Hp; apply: Hmid => //.
      by case: v Hp {Hcv} => //=; tauto.
    by move=> v _ Hcv; apply: Hmid => //=; tauto.
  have Htp1 : tapes_ok (sx :: ix :: L) smid.
    move=> p [<- | [<- | Hp]] Hrc //.
    have [lt Hlt] := Htp p Hp Hrc.
    have [l1 Hl1] := proj1 (tkeep_trans _ _ _ _ _ T0 Tsp) _ _ Hlt.
    have [l2 Hl2] := proj1 T1 _ _ Hl1.
    exact: (proj1 Tmid _ _ Hl2).
  have [s3 [R3 [_ [_ [T3 [F3 [S3 [P3 _]]]]]]]] :=
    Hrev smid O' Hag Hr1 Hseed Htp1 (no_tail_tape_scalar _ _ _ _ _ _ _).
  exists s3; split.
    by rewrite /body run_app Rp run_app R1 Rm R3.
  have Hbc : forall v, below c v -> below (S (S c)) v.
    by move=> v Hb; apply: (below_mono c) Hb _; lia.
  have Hm2 : forall v, below c v -> consistent v -> v <> BarOf n ->
      store_get smid (keyv v) = store_get s1 (keyv v).
    move=> v Hb Hcv Hne; rewrite /smid store_get_set_other.
      by move=> /(keyv_inj _ _ Hcbn Hcv) E; apply: Hne.
    rewrite store_get_set_other //.
    by move=> /(keyv_inj _ _ Hcbr Hcv) E; subst v; rewrite /r /= in Hb; lia.
  have Hnone : forall v : dvar W, None <> Some v by [].
  split.
    move=> v Hb Hcv Hp Hne.
    have Hnt : ~ is_tape v by case: v Hp {Hcv Hb Hne} => //=; tauto.
    have Hnb' : ~ is_bar v by case: v Hp {Hcv Hb Hne Hnt} => //=; tauto.
    have Hbo : forall m, v = BarOf m -> ~ In m (map snd O').
      by move=> m E; move: Hp; rewrite E.
    rewrite (F3 v (Hbc v Hb) Hcv Hnt (Hnone v) Hbo) (Hmid v Hcv Hnb').
    rewrite (Hnb v Hnt (Hbc v Hb) Hcv) (Hsp v Hb Hcv Hnt Hne).
    exact: (K0 v Hb Hcv Hp Hne).
  split.
    apply: (tkeep_trans _ _ _ s); first exact: T0.
    apply: (tkeep_trans _ _ _ sp); first exact: Tsp.
    have Hle : (c <= S (S c))%nat by lia.
    apply: (tkeep_trans _ _ _ s1).
      exact: (tkeep_none _ _ _ _ (tkeep_mono c (S (S c)) None sp s1 T1 Hle)).
    apply: (tkeep_trans _ _ _ smid).
      exact: (tkeep_none _ _ _ _
        (tkeep_mono c (S (S c)) None s1 smid Tmid Hle)).
    exact: (tkeep_none _ _ _ _ (tkeep_mono c (S (S c)) None smid s3 T3 Hle)).
  split.
    move=> v Hne Hb Hcv Ht Hex Hbo.
    have Hbo' : forall m, v = BarOf m -> ~ In m (map snd O').
      by move=> m E; exact: (Hbo m E).
    rewrite (F3 v (Hbc v Hb) Hcv Ht (Hnone v) Hbo').
    have Hnbn : v <> BarOf n by move=> E; apply: (Hbo n E); left.
    rewrite (Hm2 v Hb Hcv Hnbn) (Hnb v Ht (Hbc v Hb) Hcv).
    rewrite (Hsp v Hb Hcv Ht Hne).
    exact: (F0 v Hne Hb Hcv Ht Hex Hbo).
  split.
    move=> El.
    rewrite (proj2 T3 n (Hbc n Hbn) erefl) //.
    rewrite (proj2 Tmid n (Hbc n Hbn) erefl) //.
    rewrite (proj2 T1 n (Hbc n Hbn) erefl) //.
    exact: (Tpsp El).
  split; first by move=> t m Hi; exact: (S3 t m (or_intror Hi)).
  have Shn := S3 _ _ (or_introl erefl); rewrite /= in Shn.
  case Ebn: (barv s3 n) Shn => [[bn | | | |] |] // _.
  exists bn; split=> //.
  have Esv : seed_value (DVar (BarOf r)) smid = b1.
    rewrite /seed_value.
    by change (xev smid (DVar (BarOf r))) with (barv smid r); rewrite Ebr.
  have Ebn0 : barv smid n = Some (VReal 0) by rewrite /smid barv_set_same.
  rewrite /result_pairing Esv in P3.
  rewrite -[pairing O' s3]/(inner (TangentCorrect.tangent (VReal dj))
    (barv s3 n) + pairing O s3) in P3.
  rewrite -[pairing O' smid]/(inner (TangentCorrect.tangent (VReal dj))
    (barv smid n) + pairing O smid) in P3.
  rewrite Ebn Ebn0 (pairing_ext_own O smid s Hown_b) in P3.
  by rewrite Esj Edj; rewrite Est' /= in P0; rewrite /= in P3 *; lra.
have HP : P N s2.
  split=> //; split; first exact: tkeep_refl.
  split=> //; split.
    by move=> El; rewrite firstn_all2 ?Hlen //; exact: (Htape El).
  split; first exact: (r_shape _ _ _ _ _ _ _ Hr).
  by exists b0; split=> //; rewrite Hve.
have [sf [Hex [K [Tk [F [_ [Sh [b [Ebf Pp]]]]]]]]] :=
  exec_down_loop_from (run body) (out_dvar nat i) l N P Hstep' N s2 (le_n N)
    HP.
have Hdown : exec_down R (run body) (out_dvar nat i) (h - 1) (count l h) s2 =
    Some sf.
  case: (Nat.eq_dec N 0) => [E0 | Hn0].
    by rewrite -/N E0 in Hex *.
  have -> : (h - 1)%Z = (l + Z.of_nat N - 1)%Z.
    by rewrite /N count_nat in Hn0 *; lia.
  exact: Hex.
have Hrun : run (rev_loop W i (spell (amap pt loP)) (spell (amap pt hiP))
    (if live then [DPop (TapeOf n) (DVar n)] else [])
    [DDefine (DConstant Real) (BarOf r) (DVar (BarOf n));
     DAssign (DVar (BarOf n)) (DReal "0")] (fb, rb)) s2 = Some sf.
  cbn [rev_loop]; rewrite (run_forback _ _ _ _ _ _ l h Hslo Hshi).
  by rewrite Hdown.
have Hpi : pairing (oput O n (TangentCorrect.tangent (VReal dv))) s2 =
    dsnd dv * b0 + pairing O s2.
  by rewrite (oput_notin O _ _ Hn_notin) /= Eb0.
have H0N : (0 <= N)%nat by lia.
have [Hs0R Hs0Z] := Hstates 0%nat H0N.
rewrite /st Hst0 in Hs0R Hs0Z Pp.
destruct s0 as [d0 | | | |]; try contradiction.
rewrite (oput_notin O _ _ Hn_notin) in Hpi *.
case Ebar: (bar (amap pt initP)) => [bi |]; last first.
  (* no adjoint for the initial value: its tangent is zero *)
  have Hvi : varied (amap pa initP) = false.
    move: Ebar H13; case: (initP) => [q | ? | ?] //= Ebar H13.
    have Hq : In q L by auto.
    by rewrite -(Hbar q Hq); move: Ebar; case: (tbar (pt q)).
  have Hz0 : dsnd d0 = 0.
    exact: (atom_zero k initP _ (Hsta initP Hi3) Hvi Hin).
  exists sf; split; first by rewrite app_nil_r.
  split; first exact: K.
  split; first by move=> _ Hs'; case: Hs'.
  split; first by move=> _ Hs'; case: Hs'.
  split; first exact: Tk.
  split; first exact: F.
  split; first exact: Sh.
  split; last by move=> _ Hs'; case: Hs'.
  by rewrite Hpi; rewrite /= Hz0 in Pp; lra.
(* the initial value has an adjoint: it receives the adjoint of the first
   state *)
destruct initP as [q | |]; rewrite /= in Ebar; try discriminate.
have Hq : In q L by auto.
have [_ [_ [Hsq _]]] := static_in _ _ _ HL Hq.
case Etb: (tbar (pt q)) Ebar => // -[<-]; rewrite Hsq.
have Havq : avaried (pa q) = true by rewrite -(Hbar q Hq).
have Hvf : vflows cv k (AFold ann (amap pa loP) (amap pa hiP)
    (amap pa (AVar q)) bA) q.
  rewrite /vflows; cbn [value_needs fold_binders].
  case: (needs cv Replay (S (S k)) _) => u0 l0 /=.
  by rewrite atom_member_union /= Nat.eqb_refl.
have HqO : In (TangentCorrect.tangent (pd q), stored q) O.
  exact: (r_useful _ _ _ _ _ _ _ Hr q Hq Hvf Havq).
rewrite /= in Hin; case: Hin => Epq.
have Shq := Sh _ _ HqO; rewrite Epq /= in Shq.
case Ebq: (barv sf (stored q)) Shq => [[bq | | | |] |] // _.
set s3 := store_set sf (keyv (BarOf (stored q))) (VReal (bq + b)).
exists s3; split.
  by rewrite run_app Hrun; exact: (run_incr_bar sf (stored q) n bq b Ebq Ebf).
have Hcbq : consistent (BarOf (stored q)) by [].
have Kb : forall v, ~ is_bar v -> consistent v ->
    store_get s3 (keyv v) = store_get sf (keyv v).
  move=> v Hv Hcv; rewrite /s3 store_get_set_other //.
  by move=> /(keyv_inj _ _ Hcbq Hcv) E; subst v; exact: Hv I.
split.
  move=> v Hb0 Hcv Hp Hne.
  have Hnb : ~ is_bar v by case: v Hp {Hb0 Hcv Hne} => //=; tauto.
  by rewrite Kb //; exact: (K v Hb0 Hcv Hp Hne).
split; first by move=> _ Hs'; case: Hs'.
split; first by move=> _ Hs'; case: Hs'.
split.
  apply: (tkeep_trans _ _ _ sf); first exact: Tk.
  by rewrite /s3; apply: tkeep_set => //=; tauto.
split.
  move=> v Hne Hb0 Hcv Ht Hexv Hbo.
  case: (dvar_eq_dec_c v (BarOf (stored q))) => [Ev | Hvq].
    exfalso; apply: (Hbo (stored q) Ev); right; apply/in_map_iff.
    by exists (TangentCorrect.tangent (pd q), stored q).
  rewrite /s3 store_get_set_other.
    by move=> /(keyv_inj _ _ Hcbq Hcv) E; apply: Hvq.
  exact: (F v Hne Hb0 Hcv Ht Hexv Hbo).
split.
  move=> t m Hi; rewrite /s3.
  apply: (shaped_set O sf (TangentCorrect.tangent (pd q)) (stored q)
    (VReal (bq + b)) (rctx_owners_ok _ _ _ _ _ _ _ Hr) Sh HqO) Hi.
  move=> t' Hi'; rewrite (r_value _ _ _ _ _ _ _ Hr q t' Hq Hvf Hi').
  by rewrite Epq.
split; last by move=> _ Hs'; case: Hs'.
rewrite /s3 (pairing_set_in O sf _ (stored q) _
  (rctx_owners_ok _ _ _ _ _ _ _ Hr) (r_nodup _ _ _ _ _ _ _ Hr) HqO).
by rewrite Ebq Hpi Epq /=; rewrite /= in Pp; lra.
Qed.

(* A scalar fold computes a real, of zero tangent when its state is not varied.
  *)
Lemma act_fold a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (forall p, initP = AVar p -> ~ is_array (vty (pw p))) ->
  (forall x y, act_body (bP x y)) -> act_value (AFold a loP hiP initP bP).
Proof.
move=> Hna IHa L k wP pp tail eA eW eD te ve HA HW HD HL Htc Hev.
destruct eA, eW, eD; simpl in HA, HW, HD; try contradiction;
graph_split.
rename b into bA, b0 into bW, b1 into bD.
match goal with
  H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ =>
  rename H into HbA end.
match goal with
  H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ =>
  rename H into HbW end.
match goal with
  H : forall (i1 : pv) (i2 : val (dual R)) (s1 : pv) (s2 : val (dual R)),
      _ |- _ =>
  rename H into HbD end.
have Hsti : forall p, initP = AVar p -> static_ok k p.
  move=> p E; apply: (static_in _ _ _ HL).
  match goal with Hx : forall p, initP = AVar p -> In p L |- _ =>
    exact: (Hx p E) end.
rewrite /= in Htc.
case Eb: (ty_eqb (of_atom (amap pw loP)) Integer &&
  ty_eqb (of_atom (amap pw hiP)) Integer) Htc => // Htc.
case Er: (ty_eqb (of_atom (amap pw initP)) Real) Htc => Htc; last first.
  exfalso; move: Htc; case Eo: (of_atom (amap pw initP)) Er => [| | | nA] //.
  move=> _; move: Eo; case: (initP) Hna => [q | ? | ?] Hna //= Eo.
  have Har : is_array (vty (pw q)) by rewrite Eo.
  by move=> _; exact: (Hna q erefl Har).
move/ty_eqb_true: Er => Er.
destruct pp as [| | | ix0 sx0]; rewrite /= in Htc; try discriminate.
case HtB: (typecheck (option_map (amap pw) wP) ScalarBody (S (S k))
  (bW (VInfo k Integer None) (VInfo (S k) Real None))) Htc
  => [tb [| mm]] // Htc.
rewrite /= in Htc; case Etb: (ty_eqb tb Real) Htc => // -[Ete]; subst te.
move/ty_eqb_true: Etb HtB => -> HtB.
rewrite /= in Hev.
case: (aeval_atom (duals reals) (amap pd loP)) Hev => [[| l | | |] |] // Hev.
case: (aeval_atom (duals reals) (amap pd hiP)) Hev => [[| h | | |] |] // Hev.
case Hin: (aeval_atom (duals reals) (amap pd initP)) Hev => [s0 |] // Hev.
set vr := fold_varied k (amap pa initP) bA.
have Hloop : forall nn z st, has_type Real st -> (vr = false -> zero st) ->
    eval_fold (fun v w => aeval (duals reals) (bD v w)) z nn st = Some ve ->
    has_type Real ve /\ (vr = false -> zero ve).
  elim=> [| nn IH] z st Ht Hz /= Hf.
    by case: Hf => <-.
  case Hs1: (aeval (duals reals) (bD (VInt z) st)) Hf => [st' |] // Hf.
  set ix := PV (fresh k) (VInfo k Integer None)
    (open_index (DBound (0%nat, 0%nat))) (VInt z) 0.
  set sx := PV (AV (S k) vr) (VInfo (S k) Real None)
    (TVar (DBound (0%nat, 0%nat)) Real None vr vr vr false None) st 0.
  have Hix : static_ok (S (S k)) ix.
    by repeat split; simpl; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    by repeat split; simpl; auto; try lia; discriminate.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    apply: Forall_cons Hsx _; apply: Forall_cons Hix _.
    apply: Forall_impl HL => p Hp; by apply: static_mono Hp _; lia.
  have [Hht Hzz] := IHa ix sx (sx :: ix :: L) (S (S k)) wP PScalar
    (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bD (pd ix) (pd sx)) Real st'
    (HbA ix _ sx _) (HbW ix _ sx _) (HbD ix _ sx _) HL' HtB Hs1.
  apply: (IH (z + 1)%Z st' Hht) Hf => Hv; apply: Hzz.
  move: (Hv); rewrite /vr /fold_varied => /orb_false_iff [_ Hb'].
  by rewrite /sx /= Hv.
have Hs0 : has_type Real s0.
  by rewrite -Er; exact: (atom_type k initP s0 Hsti Hin).
have Hz0 : vr = false -> zero s0.
  move=> Hv; move: Hv; rewrite /vr /fold_varied => /orb_false_iff [Hvi _].
  exact: (atom_zero k initP _ Hsti Hvi Hin).
have [Ht Hz] := Hloop _ _ _ Hs0 Hz0 Hev.
by split=> //; split.
Qed.

Lemma inplace_map (loP hiP : atom pv) (bP : pv -> anf pv bare) : inplace_only cv
  (AMap loP hiP bP).
Proof.
move=> L k wP pp tail eA eW te HA HW HL _ Htc Hst Hl Hargs Hwr o Ho Hoin.
case: eW HW Htc => // loW hiW bW HW Htc.
have [Epp [Etl [Elo [h [Ehi [_ [_ Hy]]]]]]] :=
  map_typing _ _ _ _ _ _ _ _ Htc; subst pp tail.
destruct wP as [[o' | |] |]; rewrite /= in Ho; try discriminate.
case Ey: (vty (pw o')) Ho => [| | | ny] // [Eo]; subst o'.
have [Hni Hnocc] := Hy (pw o) erefl.
(* the written array of a map is dependent: not varied *)
have Hav : avaried (pa o) = false.
  have [nm [r [Hvg Hw]]] := Hwr o erefl.
  rewrite (Hargs o nm r Hoin Hvg).
  by have := Hni nm r Hvg; clear Hvg; move: Hw; case: r.
split; last by split=> //; rewrite Hav.
(* the map does not read it: it does not occur in the body *)
case: eA HA => // loA hiA bA [HlA [HhA HbA]].
case: HW => [HlW [HhW HbW]].
move/atom_graph: HlA => [Ela _]; move/atom_graph: HhA => [Eha _].
move/atom_graph: HlW => [Elw _]; move/atom_graph: HhW => [Ehw _].
subst loA hiA loW hiW.
case: loP Elw {Hst} => [? | ? | l0] //= _.
case: hiP Ehw => [? | ? | h0] //= _.
rewrite /vreads; cbn [value_needs] => Hrd.
set ix := PV (fresh k) (VInfo k Integer None)
  (open_index (DBound (0%nat, 0%nat))) (VInt 0%Z) 0.
have Hix : static_ok (S k) ix.
  by repeat split; simpl; auto; try lia; discriminate.
have HL' : Forall (static_ok (S k)) (ix :: L).
  apply: Forall_cons Hix _.
  apply: Forall_impl HL => p Hp; by apply: static_mono Hp _; lia.
have [Eid [Hk _]] := static_in _ _ _ HL Hoin.
have Ht : tbr cv Replay (S k) (bA (fresh k)) o.
  rewrite /tbr; case: (needs cv Replay (S k) (bA (fresh k))) Hrd => u l1 /=.
  rewrite atom_member_union atom_member_remove_full /= /same_term /fresh /=.
  have Hko : k <> aid (pa o) by lia.
  by rewrite (proj2 (Nat.eqb_neq _ _) Hko).
have := tbr_occurs (ix :: L) (S k) (bP ix) (bA (fresh k))
  (bW (VInfo k Integer None)) Replay o (HbA ix (pa ix)) (HbW ix (pw ix)) HL'
  (or_intror Hoin) (or_introl Ht).
rewrite /live_anf.
rewrite (live_cont L k bP bW ix (VInfo k Integer None) _ HbW HL erefl erefl).
by rewrite Hnocc.
Qed.

Lemma inplace_fold a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (forall p, initP = AVar p -> ~ is_array (vty (pw p))) -> inplace_only cv
    (AFold a loP hiP initP bP).
Proof.
move=> Hna L k wP pp tail eA eW te _ _ _ _ _ Hst; exfalso; apply: Hst.
move: Hna; case: (initP) => [q | ? | ?] //= Hna.
case Eq: (vty (pw q)) => [| | | nq] //.
have Har : is_array (vty (pw q)) by rewrite Eq.
by case: (Hna q erefl Har).
Qed.

Lemma owner_fold a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (forall p, initP = AVar p -> ~ is_array (vty (pw p))) -> act_owner (AFold a
    loP hiP initP bP).
Proof.
move=> Hna L k c wP pp live ty tail eA eW eD ve o _ _ _ _ _.
move: Hna; case: (initP) => [q | ? | ?] //= Hna.
case Eq: (vty (pw q)) => [| | | nq] //.
have Har : is_array (vty (pw q)) by rewrite Eq.
by case: (Hna q erefl Har).
Qed.

(* Bodies of straight lets, branches, maps and scalar folds: an assignment is
   in no branch, a map or a fold is at the top, and branches, maps and folds
   hold no assignment, map or fold. *)
Fixpoint branchy (top : bool) (b : anf pv bare) : Prop :=
  match b with
  | ALet _ e b' => branchy_value top e /\ forall x, branchy top (b' x)
  | ARet _ => True
  end
with branchy_value (top : bool) (e : value pv bare) : Prop :=
  match e with
  | AOp1 _ _ | AOp2 _ _ _ | AGet _ _ => True
  | ASet _ _ _ => top = true
  | AIte _ t e => branchy false t /\ branchy false e
  | AMap _ _ b => top = true /\ forall x, branchy false (b x)
  | AFold _ _ _ init b =>
      top = true /\ (forall p, init = AVar p -> ~ is_array (vty (pw p))) /\
        forall x y, branchy false (b x y)
  end.

End Branch.
