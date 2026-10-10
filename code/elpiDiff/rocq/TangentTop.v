(* TangentTop.v — theorem 1 at the level of a function
   (tangent_simulates_duals): the arguments are opened, the body simulated
   (TangentLoops.v), the statements checked to follow the scoping discipline
   (TangentGood.v), and the result stored as tangent_result says. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Tangent Simplify Scoping
  AnfEquiv Correctness SimplifyCorrect TangentCorrect TangentLoops TangentGood
  Smooth.
From Corelib Require Import ssreflect ssrbool ssrfun.

Import ListNotations.
Open Scope list_scope.

(* ---------------------------------------------------------------------------
   Opening the arguments of a definition of L1 at the pv instance: the k-th
   argument has identity k, is stored in the k-th parameter, and has the k-th
   dual argument as its value. The arguments are accumulated last first. *)

Definition arg_pv (n : string) (t : ty) (r : role) (k : nat) (x : val (dual R)) : pv :=
  let vr := varied_role r in
  PV (AV k vr) (VInfo k t (Some (n, r))) (TVar (DBound (k, k)) t (Some (n, r)) vr vr vr false (Some (S k))) x k.

Fixpoint open_P (d : adefinition pv bare) (k : nat) (xs : list (val (dual R))) (L : list pv)
  : option (list pv * aresult pv * anf pv bare) :=
  match d, xs with
  | AArg n t r f, x :: xs' => open_P (f (arg_pv n t r k x)) (S k) xs' (arg_pv n t r k x :: L)
  | ABody res b, [] => Some (L, res, b)
  | _, _ => None
  end.

(* The analyses open the arguments as open_P does, in either mode. *)
Lemma annotate_open_cv cv (dP : adefinition pv bare) :
  forall L k xs L' res bP dA,
  adefinition_eq (gA L) dP dA -> open_P dP k xs L = Some (L', res, bP) ->
  exists bA, anf_eq (gA L') bP bA /\
    annotate_definition_t cv k dA =
    annotate_body_t cv Forward (k + length xs) bA.
Proof.
elim: dP => [n t r f IH | rP bP0] L k xs L' res bP [n' t' r' fA | rA bA] //=.
- move=> [? [? [? HA]]]; subst n' t' r'; case: xs => [|x xs] //= Ho.
  have [bA [H1 H2]] := IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs
    L' res bP (fA (AV k (varied_role r))) (HA _ _) Ho.
  by exists bA; split=> //=; rewrite H2; f_equal; lia.
- move=> [_ HA]; case: xs => //= - [? ? ?]; subst L' res bP.
  by exists bA; rewrite /= Nat.add_0_r.
Qed.

Lemma annotate_open (dP : adefinition pv bare) : forall L k xs L' res bP dA,
  adefinition_eq (gA L) dP dA -> open_P dP k xs L = Some (L', res, bP) ->
  exists bA, anf_eq (gA L') bP bA /\
    annotate_definition_t false k dA =
    annotate_body_t false Forward (k + length xs) bA.
Proof. exact: annotate_open_cv. Qed.

Lemma wf_open (dP : adefinition pv bare) : forall L k xs L' res bP dW decls,
  adefinition_eq (gW L) dP dW -> open_P dP k xs L = Some (L', res, bP) ->
  exists resW bW, aresult_eq (gW L') res resW /\ anf_eq (gW L') bP bW /\
    well_formed_definition decls k dW = well_formed_result decls resW bW (k + length xs).
Proof.
elim: dP => [n t r f IH | rP bP0] L k xs L' res bP [n' t' r' fW | rW bW] decls
  //=.
- move=> [? [? [? HW]]]; subst n' t' r'; case: xs => [|x xs] //= Ho.
  have [resW [bW [H1 [H2 H3]]]] :=
    IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs L' res bP
      (fW (VInfo k t (Some (n, r)))) decls (HW _ _) Ho.
  by exists resW, bW; do 2!split=> //=; rewrite H3; f_equal; lia.
- move=> [HrW HbW]; case: xs => //= - [? ? ?]; subst L' res bP.
  by exists rW, bW; rewrite /= Nat.add_0_r.
Qed.

Lemma eval_open (dP : adefinition pv bare) : forall L k xs L' res bP dD,
  adefinition_eq (gD L) dP dD -> open_P dP k xs L = Some (L', res, bP) ->
  exists bD, anf_eq (gD L') bP bD /\ aeval_definition (duals reals) dD xs = aeval (duals reals) bD.
Proof.
elim: dP => [n t r f IH | rP bP0] L k xs L' res bP [n' t' r' fD | rD bD] //=.
- move=> [? [? [? HD]]]; subst n' t' r'; case: xs => [|x xs] //= Ho.
  exact: (IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs L' res bP
           (fD x) (HD _ _) Ho).
- move=> [_ HD]; case: xs => //= - [? ? ?]; subst L' res bP.
  by exists bD.
Qed.

(* An argument as the tangent pass records it: its declaration and its
   stored variable. *)
Definition arg_entry (p : pv) : decl * dvar W :=
  match varg (pw p) with
  | Some (n, r) => (Decl n (vty (pw p)) r, stored p)
  | None => (Decl "" Real Passive, stored p)
  end.

Lemma tangent_open {A : Type} (dP : adefinition pv bare) : forall L k xs L' res bP dT tr
  (K : list (decl * dvar W) -> aresult (tvar W) -> anf (tvar W) ann -> option (atom (tvar W)) -> scoped W A),
  adefinition_eq (gT L) dP dT -> open_P dP k xs L = Some (L', res, bP) ->
  exists resT bT, aresult_eq (gT L') res resT /\ anf_eq (gT L') bP bT /\
    open_pairs (open_arguments W (rebuild_definition _ dT tr) k (map arg_entry L) K) k =
    open_pairs (K (rev (map arg_entry L')) resT (rebuild _ bT tr)
                  (match resT with AWrites y => Some y | AReturns _ => None end)) (k + length xs).
Proof.
elim: dP => [n t r f IH | rP bP0] L k xs L' res bP [n' t' r' fT | rT bT] tr K
  //=.
- move=> [? [? [? HT]]]; subst n' t' r'; case: xs => [|x xs] //= Ho.
  have [resT [bT [H1 [H2 H3]]]] :=
    IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs L' res bP
      (fT (pt (arg_pv n t r k x))) tr K (HT _ _) Ho.
  by exists resT, bT; do 2!split=> //; rewrite -Nat.add_succ_comm -H3.
- move=> [HrT HbT]; case: xs => //= - [? ? ?]; subst L' res bP.
  by exists rT, bT; do 2!split=> //; rewrite Nat.add_0_r; case: rT HrT.
Qed.

Lemma decls_open (dP : adefinition pv bare) : forall (G : list (pv * unit)) L k xs L' res bP dU,
  adefinition_eq G dP dU -> open_P dP k xs L = Some (L', res, bP) ->
  map (fun p => fst (arg_entry p)) (rev L) ++ declarations dU = map (fun p => fst (arg_entry p)) (rev L').
Proof.
elim: dP => [n t r f IH | rP bP0] G L k xs L' res bP [n' t' r' fU | rU bU] //=.
- move=> [? [? [? HU]]]; subst n' t' r'; case: xs => [|x xs] //= Ho.
  rewrite -(IH (arg_pv n t r k x) _ (arg_pv n t r k x :: L) (S k) xs L' res bP
              (fU tt) (HU _ _) Ho).
  by rewrite /= map_app -app_assoc.
- move=> _; case: xs => //= - [? ? ?]; subst L' res bP.
  exact: app_nil_r.
Qed.

(* What open_P gives: the arguments, last first, each opened by arg_pv. *)
Lemma open_P_args (dP : adefinition pv bare) : forall k xs L L' res bP,
  open_P dP k xs L = Some (L', res, bP) ->
  exists new, L' = new ++ L /\ length new = length xs /\
    forall i p, nth_error (rev new) i = Some p ->
    exists n t r x, p = arg_pv n t r (k + i) x /\ nth_error xs i = Some x.
Proof.
elim: dP => [n t r f IH | rP bP0] k [|x xs] L L' res bP //=.
- move=> /IH [new [-> [Hl Hn]]].
  exists (new ++ [arg_pv n t r k x]); split; first by rewrite -app_assoc.
  split; first by rewrite length_app /=; lia.
  move=> [|i] p; rewrite rev_app_distr /=.
  + by case=> <-; exists n, t, r, x; split=> //; f_equal; lia.
  + move=> /Hn [n' [t' [r' [x' [E1 E2]]]]]; exists n', t', r', x'.
    by split=> //; rewrite E1; f_equal; lia.
- case=> ? ? ?; subst L' res bP.
  by exists []; repeat split=> //; case.
Qed.

(* ---------------------------------------------------------------------------
   The layout of the tangent function: its arguments and its outputs. *)

(* The declarations of the arguments of f, in order. *)
Definition decls (f : function) : list decl := declarations (afdef (normalize f) unit).

(* An argument with a tangent parameter (tangent_dot). *)
Definition has_dot (d : decl) : bool :=
  let 'Decl _ t r := d in
  match t, r with Integer, _ => false | _, Passive => false | _, _ => true end.

(* The arguments fit their declarations: an array has its extent. *)
Definition fits (d : decl) (v : val R) : Prop :=
  let 'Decl _ t _ := d in
  match t, v with
  | Real, VReal _ | Integer, VInt _ | Boolean, VBool _ => True
  | Array n, VArray l => length l = Z.to_nat n
  | _, _ => False
  end.

(* The number of reals of a value: one for a real, the extent of an array. *)
Definition nreals (v : val R) : nat :=
  match v with VReal _ => 1 | VArray l => length l | _ => 0 end.

(* The seed of the tangents: dx on the reals of the independent and inout
   arguments, 0 on the others (dependent and passive). *)
Fixpoint seed (ds : list decl) (x : list (val R)) (dx : list R) : list R :=
  match ds, x with
  | Decl _ _ r :: ds', v :: x' =>
      let m := nreals v in
      (if varied_role r then firstn m dx else repeat 0%R m) ++ seed ds' x' (skipn m dx)
  | _, _ => []
  end.

(* The reals l with the tangents t, 0 when t is short. *)
Fixpoint pair_with (l t : list R) : list (dual R) :=
  match l with
  | [] => []
  | r :: l' => Dual r (hd 0%R t) :: pair_with l' (tl t)
  end.

(* A value with the tangents t on its reals. *)
Definition val_dual (v : val R) (t : list R) : val (dual R) :=
  match v with
  | VReal r => VReal (Dual r (hd 0%R t))
  | VInt z => VInt z
  | VBool b => VBool b
  | VArray l => VArray (pair_with l t)
  | VTape l => VTape (map (fun r => Dual r 0%R) l)
  end.

(* The arguments as dual numbers, seeded. *)
Fixpoint seed_args (ds : list decl) (x : list (val R)) (dx : list R) : list (val (dual R)) :=
  match ds, x with
  | Decl _ _ r :: ds', v :: x' =>
      let m := nreals v in
      val_dual v (if varied_role r then firstn m dx else repeat 0%R m) :: seed_args ds' x' (skipn m dx)
  | _, _ => []
  end.

(* The arguments of the tangent function: the primal arguments x, then the
   tangent of each argument that has one, then the tangent of a returned
   real (its initial value is not read). *)
Definition tangent_inputs (ds : list decl) (x : list (val R)) (dx : list R) : list (val R) :=
  let xs := seed_args ds x dx in
  map primal xs ++
  concat (map (fun '(d, v) => if has_dot d then [tangent v] else []) (combine ds xs)) ++
  (if existsb written_decl ds then [] else [VReal 0%R]).

(* An argument whose tangent parameter is an output only: a written
   dependent argument. *)
Definition dot_out (d : decl) : bool :=
  let 'Decl _ _ r := d in match r with Dependent => true | _ => false end.

(* The arguments of the tangent function with any initial values in its
   output-only tangent parameters: dd v for a written dependent argument of
   primal v, r0 for the tangent of a returned real. *)
Definition tangent_inputs_with (dd : val R -> val R) (r0 : val R)
  (ds : list decl) (x : list (val R)) (dx : list R) : list (val R) :=
  let xs := seed_args ds x dx in
  map primal xs ++
  concat (map (fun '(d, v) =>
                 if has_dot d then
                   [if dot_out d then dd (primal v) else tangent v]
                 else []) (combine ds xs)) ++
  (if existsb written_decl ds then [] else [r0]).

(* The zero tangent of a value. *)
Definition zero_dot (v : val R) : val R := tangent (val_dual v []).

Fixpoint index_of_written (ds : list decl) (i : nat) : option nat :=
  match ds with
  | [] => None
  | d :: ds' => if written_decl d then Some i else index_of_written ds' (S i)
  end.

(* The value and the tangent the tangent function computes: the returned
   value and the last parameter (result_dot), or the written argument and its
   tangent parameter. *)
Definition tangent_output (ds : list decl) (out : list (val R) * list (val R)) : option (val R * val R) :=
  let '(finals, rets) := out in
  match index_of_written ds 0 with
  | None => match rets, last finals (VInt 0) with [v], d => Some (v, d) | _, _ => None end
  | Some j =>
      match nth_error finals j, nth_error finals (length ds + length (filter has_dot (firstn j ds))) with
      | Some v, Some d => Some (v, d)
      | _, _ => None
      end
  end.

(* ---------------------------------------------------------------------------
   Theorem 1, for a function. *)

Lemma open_P_some (dP : adefinition pv bare) : forall L k xs dD v,
  adefinition_eq (gD L) dP dD -> aeval_definition (duals reals) dD xs = Some v ->
  exists L' res bP, open_P dP k xs L = Some (L', res, bP).
Proof.
elim: dP => [n t r f IH | rP bP0] L k xs [n' t' r' fD | rD bD] v //=.
- move=> [? [? [? HD]]]; subst n' t' r'; case: xs => [|x xs] //= He.
  exact: (IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs (fD x) v
           (HD _ _) He).
- by move=> _; case: xs => //=; eauto.
Qed.



(* ---------------------------------------------------------------------------
   The seeded arguments. *)

Lemma primal_val_dual v t : primal (val_dual v t) = v.
Proof.
case: v => [r | z | b | l | l] //=.
- by congr VArray; elim: l t => [|r l IH] t //=; rewrite IH.
- by congr VTape; elim: l => [|r l IH] //=; rewrite IH.
Qed.

Lemma pair_with_length l t : length (pair_with l t) = length l.
Proof. by elim: l t => [|a l IH] t //=; rewrite IH. Qed.

Lemma fits_type n t r v tg : fits (Decl n t r) v -> has_type t (val_dual v tg).
Proof. by case: t; case: v => //= l z H; rewrite pair_with_length. Qed.

Lemma zero_val_dual v m : zero (val_dual v (repeat 0%R m)).
Proof.
case: v => [r | z | b | l | l] //=.
- by case: m.
- elim: l m => [|r l IH] m /=; first by constructor.
  constructor; first by case: m.
  by case: m => [|m] /=; [exact: (IH 0%nat) | exact: IH].
Qed.

Lemma fits_tangent d w tg : fits d w -> fits d (tangent (val_dual w tg)).
Proof.
case: d => nm t r; case: t; case: w => //= l z.
by rewrite length_map pair_with_length.
Qed.

Lemma tangent_val_dual_zero v m :
  tangent (val_dual v (repeat 0%R m)) = zero_dot v.
Proof.
rewrite /zero_dot; case: v => [r | z | b | l | l] //=.
  by case: m.
congr VArray; elim: l m => [|a l IH] m //=.
by case: m => [|m] /=; rewrite ?(IH 0%nat) ?IH.
Qed.

(* tangent_inputs gives zeros to the output-only tangent parameters. *)
Lemma tangent_inputs_zero ds x dx :
  tangent_inputs ds x dx = tangent_inputs_with zero_dot (VReal 0%R) ds x dx.
Proof.
rewrite /tangent_inputs /tangent_inputs_with; congr (_ ++ _ ++ _).
elim: ds x dx => [|[nm t r] ds IH] [|v x] dx //=.
rewrite IH; congr (_ ++ _).
by case: r; case: t => //=;
  rewrite ?primal_val_dual ?tangent_val_dual_zero.
Qed.

Lemma seed_args_nth ds x dx i n t r :
  Forall2 fits ds x -> nth_error ds i = Some (Decl n t r) ->
  exists v tg, nth_error x i = Some v /\ nth_error (seed_args ds x dx) i = Some (val_dual v tg) /\
               fits (Decl n t r) v /\ (varied_role r = false -> zero (val_dual v tg)).
Proof.
move=> H; elim: H i dx => [|[n' t' r'] v ds' x' Hf Hfs IH] i dx.
  by case: i.
case: i => [|i] /= Hi; last exact: IH.
case: Hi => ? ? ?; subst n' t' r'.
exists v, (if varied_role r then firstn (nreals v) dx
          else repeat 0%R (nreals v)).
do 2!split=> //.
by split=> // Hv; rewrite Hv; exact: zero_val_dual.
Qed.

Lemma seed_args_length ds x dx : Forall2 fits ds x -> length (seed_args ds x dx) = length ds.
Proof.
by move=> H; elim: H dx => [|[n t r] v ds' x' Hf Hfs IH] dx //=; rewrite IH.
Qed.

(* ---------------------------------------------------------------------------
   The initial store of the tangent function. *)

Definition prim_entries (AL : list pv) : store R :=
  map (fun p => (KVar (DBound (pn p)), primal (pd p))) AL.

(* The initial tangent of an argument: dd of its primal for a written
   dependent argument, its seeded tangent otherwise. *)
Definition dot_val (dd : val R -> val R) (p : pv) : val R :=
  if dot_out (fst (arg_entry p)) then dd (primal (pd p)) else tangent (pd p).

Definition dot_in dd (p : pv) : list (val R) :=
  if has_dot (fst (arg_entry p)) then [dot_val dd p] else [].

Definition dot_entries dd (AL : list pv) : store R :=
  concat (map (fun p => if has_dot (fst (arg_entry p))
                        then [(KVar (DotOf (DBound (pn p))), dot_val dd p)]
                        else []) AL).

Lemma combine_app {A B : Type} (a1 a2 : list A) (b1 b2 : list B) :
  length a1 = length b1 -> combine (a1 ++ a2) (b1 ++ b2) = combine a1 b1 ++ combine a2 b2.
Proof. by elim: a1 b1 => [|x a1 IH] [|y b1] //= H; rewrite IH //; lia. Qed.

Lemma tangent_dot_entry p :
  varg (pw p) <> None ->
  tangent_dot W (arg_entry p) =
  if has_dot (fst (arg_entry p)) then [match tangent_dot W (arg_entry p) with
                                       | [d] => d | _ => DParam ByValue Real ResultVar end] else [].
Proof.
rewrite /arg_entry; case: (varg (pw p)) => [[nm r]|] // _.
by case: (vty (pw p)); case: r.
Qed.

(* The store exec_scoped builds from the parameters and the arguments of the
   tangent function. *)
Lemma initial_store dd (AL : list pv) eps ein :
  Forall (fun p => tstored (pt p) = stored p /\ varg (pw p) <> None) AL ->
  length eps = length ein ->
  map (fun '(DParam _ _ x, a) => (KVar x, a))
    (combine (map (out_dparam nat)
                (map (tangent_primal W) (map arg_entry AL) ++ concat (map (tangent_dot W) (map arg_entry AL)) ++ eps))
             (map (fun p => primal (pd p)) AL ++ concat (map (dot_in dd) AL) ++
                ein)) =
  prim_entries AL ++ dot_entries dd AL ++
  map (fun '(DParam _ _ x, a) => (KVar x, a)) (combine (map (out_dparam nat) eps) ein).
Proof.
move=> HAL Hl.
have Hd :
    length (map (out_dparam nat)
              (concat (map (tangent_dot W) (map arg_entry AL)))) =
    length (concat (map (dot_in dd) AL)).
  rewrite length_map; elim: HAL {Hl} => [|p AL' [_ Hg] HAL' IH] //=.
  by rewrite !length_app IH (tangent_dot_entry _ Hg) /dot_in; case: (has_dot _).
rewrite !map_app combine_app ?length_map // combine_app // !map_app.
congr (_ ++ _ ++ _).
- rewrite /prim_entries; elim: HAL {Hl Hd} => [|p AL' [_ Hg] HAL' IH] //=.
  rewrite IH; congr (_ :: _).
  rewrite /arg_entry; case: (varg (pw p)) Hg => [[nm r]|] // _.
  by rewrite /stored; case: (vty (pw p)) => //=; case: (written_role r).
- rewrite /dot_entries; elim: HAL {Hl Hd} => [|p AL' [_ Hg] HAL' IH] //=.
  rewrite map_app -IH /dot_in (tangent_dot_entry _ Hg) /arg_entry.
  by case: (varg (pw p)) Hg => [[nm r]|] // _; case: (vty (pw p)); case: r.
Qed.

Lemma store_get_app (s1 s2 : store R) k :
  store_get (s1 ++ s2) k = match store_get s1 k with Some v => Some v | None => store_get s2 k end.
Proof. by elim: s1 => [|[k0 v0] s1 IH] //=; case: (key_eqb k0 k). Qed.

Lemma prim_lookup AL p :
  NoDup (map pn AL) -> In p AL -> store_get (prim_entries AL) (KVar (DBound (pn p))) = Some (primal (pd p)).
Proof.
elim: AL => [|q AL IH] //= /NoDup_cons_iff [Hq Hnd] [-> | Hp].
- by rewrite Nat.eqb_refl.
- case: (Nat.eqb_spec (pn q) (pn p)) => [E|_]; last by apply: IH.
  by exfalso; apply: Hq; rewrite E; apply: in_map.
Qed.

Lemma prim_lookup_dot AL v : store_get (prim_entries AL) (KVar (DotOf v)) = None.
Proof. by elim: AL. Qed.

Lemma prim_lookup_none AL j : (forall p, In p AL -> pn p <> j) -> store_get (prim_entries AL) (KVar (DBound j)) = None.
Proof.
elim: AL => [|q AL IH] H //=.
case: (Nat.eqb_spec (pn q) j) => [E|_].
  by exfalso; apply: (H q (or_introl erefl)).
by apply: IH => p Hp; apply: H; right.
Qed.

Lemma dot_lookup dd AL p :
  NoDup (map pn AL) -> In p AL -> has_dot (fst (arg_entry p)) = true ->
  store_get (dot_entries dd AL) (KVar (DotOf (DBound (pn p)))) =
  Some (dot_val dd p).
Proof.
elim: AL => [|q AL IH] //= /NoDup_cons_iff [Hq Hnd] [-> | Hp] Hd;
  rewrite /dot_entries /= store_get_app.
- by rewrite Hd /= Nat.eqb_refl.
- case: (has_dot (fst (arg_entry q))) => /=; last by apply: IH.
  case: (Nat.eqb_spec (pn q) (pn p)) => [E|_]; last by apply: IH.
  by exfalso; apply: Hq; rewrite E; apply: in_map.
Qed.

Lemma dot_lookup_none dd AL k : (forall j, k <> KVar (DotOf (DBound j))) ->
  store_get (dot_entries dd AL) k = None.
Proof.
move=> H; elim: AL => [|q AL IH] //.
move: IH; rewrite /dot_entries /= store_get_app => ->.
case: (has_dot (fst (arg_entry q))) => //=.
case: k H => [[x | [x | | | |] | | |] |] //= H.
case: (Nat.eqb_spec (pn q) x) => [E|//].
by exfalso; apply: (H (pn q)); rewrite E.
Qed.

Lemma dot_lookup_absent dd AL j : (forall p, In p AL -> pn p <> j) ->
  store_get (dot_entries dd AL) (KVar (DotOf (DBound j))) = None.
Proof.
elim: AL => [|q AL IH] H //.
have {IH} := IH (fun p Hp => H p (or_intror Hp)).
rewrite /dot_entries /= store_get_app => ->.
case: (has_dot (fst (arg_entry q))) => //=.
case: (Nat.eqb_spec (pn q) j) => // E.
by exfalso; apply: (H q (or_introl erefl)).
Qed.

Lemma non_real_varied_none ds nm t r :
  non_real_varied ds = None -> In (Decl nm t r) ds -> varied_role r = true -> real_or_array t.
Proof.
elim: ds => [|[nm' t' r'] ds IH] //=.
case E: (varied_role r' && _) => // H [[? ? ?] | Hin] Hv; last first.
  exact: (IH H Hin Hv).
subst nm' t' r'.
by move: E {IH}; rewrite Hv; case: t.
Qed.

(* What well_formed says of the result of a function. *)
Lemma wf_result_facts ds resW bW k :
  well_formed_result ds resW bW k = Ok ->
  (resW = AReturns Real /\ existsb written_decl ds = false /\ typecheck None Top k bW = (Real, Ok)) \/
  (exists w nm role, resW = AWrites (AVar w) /\ varg w = Some (nm, role) /\ written_role role = true /\
     length (filter written_decl ds) = 1%nat /\ real_or_array (vty w) /\
     typecheck (Some (AVar w)) Top k bW = (vty w, Ok) /\
     (role = Dependent -> occurs_anf (vid w) k bW = false) /\ (role = Inout -> occurs_anf (vid w) k bW = true)).
Proof.
case: resW => [[| | | z] | [w | | ]] //=.
- move=> H; left; move: H; case: (existsb written_decl ds) => //.
  case: (typecheck None Top k bW) => [t [|mm]] //=.
  by case E: (ty_eqb t Real) => // _; rewrite (ty_eqb_true _ _ E).
- move=> H; right; move: H; case Eg: (varg w) => [[nm role]|] //.
  case Er: (written_role role) => //.
  case: (Nat.eqb_spec (length (filter written_decl ds)) 1) => //= El.
  case Et: (ty_eqb (vty w) Real || ty_is_array (vty w)) => //=.
  case Htc: (typecheck (Some (AVar w)) Top k bW) => [t [|mm]] //=.
  case Etw: (ty_eqb t (vty w)) => //= H.
  move: Htc; rewrite (ty_eqb_true _ _ Etw) => Htc.
  exists w, nm, role; do 5!split=> //.
  + by move: Et; case: (vty w).
  + by split=> //; split=> E; move: H; rewrite E;
      case: (occurs_anf (vid w) k bW).
Qed.

(* The final values of the parameters, when each is in the store. *)
Lemma finals_some (s : store R) (ps : list (dparam nat)) :
  (forall pw t x, In (DParam pw t x) ps -> exists v, store_get s (KVar x) = Some v) ->
  exists fs, fold_right (fun o acc => match o with
                                      | Some v => match acc with Some l => Some (v :: l) | None => None end
                                      | None => None end) (Some [])
               (map (fun '(DParam _ _ x) => store_get s (KVar x)) ps) = Some fs /\
             length fs = length ps /\
             forall i pw t x, nth_error ps i = Some (DParam pw t x) -> nth_error fs i = store_get s (KVar x).
Proof.
elim: ps => [|[pw t x] ps IH] H /=.
  by exists []; do 2!split=> //; case.
have [v Hv] := H pw t x (or_introl erefl).
have [|fs [Hf [Hl Hn]]] := IH.
  by move=> pw' t' x' Hin; apply: (H pw' t' x'); right.
rewrite Hv Hf; exists (v :: fs); do 2!split=> //=; first by rewrite Hl.
by case=> [|i] pw' t' x' /= Hi; [case: Hi => _ _ <- | exact: Hn Hi].
Qed.

Lemma nth_error_last {A : Type} (l : list A) d x :
  nth_error l (length l - 1) = Some x -> last l d = x.
Proof.
elim: l => [|a [|b l] IH] //=; first by case.
by move=> E; apply: IH; rewrite /= Nat.sub_0_r.
Qed.

Lemma params_app ps1 ps2 : params (ps1 ++ ps2) = params ps1 ++ params ps2.
Proof. exact: map_app. Qed.

Lemma params_primal AL : params (map (tangent_primal W) (map arg_entry AL)) = map stored AL.
Proof.
elim: AL => [|p AL IH] //; move: IH; rewrite /params /= => ->; congr (_ :: _).
rewrite /arg_entry; case: (varg (pw p)) => [[nm r]|] //=.
by case: (vty (pw p)) => //; case: (written_role r).
Qed.

Lemma params_dots AL :
  Forall (fun p => varg (pw p) <> None) AL ->
  params (concat (map (tangent_dot W) (map arg_entry AL))) =
  concat (map (fun p => if has_dot (fst (arg_entry p)) then [DotOf (stored p)] else []) AL).
Proof.
elim=> [|p AL' Hg HAL IH] //=; rewrite params_app IH; congr (_ ++ _).
rewrite /arg_entry; case: (varg (pw p)) Hg => [[nm r]|] // _.
by case: (vty (pw p)); case: r.
Qed.

Lemma in_dots AL p :
  In p AL -> has_dot (fst (arg_entry p)) = true ->
  In (DotOf (stored p)) (concat (map (fun p => if has_dot (fst (arg_entry p)) then [DotOf (stored p)] else []) AL)).
Proof.
move=> Hp Hd; apply/in_concat; exists [DotOf (stored p)]; split; last by left.
by apply/in_map_iff; exists p; rewrite Hd.
Qed.

Lemma in_dots_inv AL y :
  In y (concat (map (fun p => if has_dot (fst (arg_entry p)) then [DotOf (stored p)] else []) AL)) ->
  exists p, In p AL /\ y = DotOf (stored p) /\ has_dot (fst (arg_entry p)) = true.
Proof.
move=> /in_concat [l [/in_map_iff [p [<- Hp]] Hy]].
by move: Hy; case E: (has_dot _) => //= -[<- | []]; exists p.
Qed.

Lemma in_rev_iff {A : Type} (x : A) l : In x (rev l) <-> In x l.
Proof. by rewrite -in_rev. Qed.

Lemma dvar_eq_dec (a b : dvar W) : {a = b} + {a <> b}.
Proof. decide equality; destruct x, x0; decide equality; apply Nat.eq_dec. Qed.

Lemma index_of_written_none ds i : existsb written_decl ds = false -> index_of_written ds i = None.
Proof.
by elim: ds i => [|d ds IH] i //=; case: (written_decl d) => //= /IH.
Qed.

Lemma inputs_eq dd r0 ds x dx (AL : list pv) :
  seed_args ds x dx = map pd AL -> ds = map (fun p => fst (arg_entry p)) AL ->
  tangent_inputs_with dd r0 ds x dx =
  map (fun p => primal (pd p)) AL ++ concat (map (dot_in dd) AL) ++
  (if existsb written_decl ds then [] else [r0]).
Proof.
move=> Hx Hd; rewrite /tangent_inputs_with Hx map_map; congr (_ ++ _ ++ _).
by rewrite {1}Hd {Hx Hd}; elim: AL => [|p AL IH] //=; rewrite IH.
Qed.

Lemma index_of_written_unique ds j d k :
  nth_error ds j = Some d -> written_decl d = true -> length (filter written_decl ds) = 1%nat ->
  index_of_written ds k = Some (k + j)%nat.
Proof.
elim: ds j k => [|d0 ds IH] [|j] k //= Hj Hw.
- by case: Hj => ->; rewrite Hw Nat.add_0_r.
- case E0: (written_decl d0) => /= H1.
  + have Hin : In d (filter written_decl ds).
      by apply/filter_In; split=> //; exact: nth_error_In Hj.
    by move: H1 Hin; case: (filter written_decl ds).
  + by rewrite (IH j (S k) Hj Hw H1) Nat.add_succ_r.
Qed.

Lemma dot_param_position (AL : list pv) j p :
  Forall (fun p => varg (pw p) <> None) AL -> nth_error AL j = Some p -> has_dot (fst (arg_entry p)) = true ->
  exists pw0 t0, nth_error (concat (map (tangent_dot W) (map arg_entry AL)))
                   (length (filter has_dot (firstn j (map (fun q => fst (arg_entry q)) AL)))) =
                 Some (DParam pw0 t0 (DotOf (stored p))).
Proof.
move=> HAL; elim: HAL j => [|q AL' Hg HAL IH] j; first by case: j.
case: j => [|j] /= Hj Hd.
- case: Hj => ?; subst q; rewrite (tangent_dot_entry _ Hg) Hd /=.
  move: Hd; rewrite /arg_entry; case: (varg (pw p)) Hg => [[nm r]|] // _.
  by case: (vty (pw p)); case: r => //=; eauto.
- rewrite (tangent_dot_entry _ Hg).
  case: (has_dot (fst (arg_entry q))) => /=; last exact: IH.
  by have [pw0 [t0 H]] := IH j Hj Hd; eauto.
Qed.

(* The arguments opened by open_P at the seeded arguments: their positions,
   distinct numbers, static facts, and their dual values. *)
Lemma open_args_facts ds x dx (L : list pv) n :
  Forall2 fits ds x -> non_real_varied ds = None ->
  ds = map (fun p => fst (arg_entry p)) (rev L) ->
  length L = n -> length (seed_args ds x dx) = n ->
  (forall i p, nth_error (rev L) i = Some p -> exists nm t r x0,
     p = arg_pv nm t r (0 + i) x0 /\
     nth_error (seed_args ds x dx) i = Some x0) ->
  (forall p, In p L -> exists i nm t r x0, p = arg_pv nm t r i x0 /\
     nth_error (seed_args ds x dx) i = Some x0 /\
     nth_error ds i = Some (Decl nm t r) /\ (i < n)%nat) /\
  NoDup (map pn (rev L)) /\ Forall (static_ok n) L /\ ids_unique L /\
  (forall p, In p L -> (pn p < n)%nat) /\
  (forall p q, In p L -> In q L -> pn p = pn q -> p = q) /\
  seed_args ds x dx = map pd (rev L).
Proof.
move=> Hfit Hnrv Hds Hlen Hn Hargs.
set xs := seed_args ds x dx in Hn Hargs *.
have Hargs' : forall p, In p L ->
    exists i nm t r x0, p = arg_pv nm t r i x0 /\ nth_error xs i = Some x0 /\
      nth_error ds i = Some (Decl nm t r) /\ (i < n)%nat.
  move=> p /(in_rev L) /(In_nth_error _ _) [i Hi].
  have [nm [t [r [x0 [Ep Hx0]]]]] := Hargs i p Hi; subst p.
  exists i, nm, t, r, x0; do 2!split=> //.
  split; first by rewrite Hds nth_error_map Hi.
  by rewrite -Hn; apply/nth_error_Some; rewrite Hx0.
have Hpn_inj : forall p q, In p L -> In q L -> pn p = pn q -> p = q.
  move=> p q /Hargs' [i [? [? [? [? [-> [Hx [Hd _]]]]]]]].
  move=> /Hargs' [i' [? [? [? [? [-> [Hx' [Hd' _]]]]]]]] /= E; subst i'.
  by move: Hx' Hd'; rewrite Hx Hd => -[->] [-> -> ->].
split; first exact: Hargs'.
split.
  apply/NoDup_nth_error => i j; rewrite length_map => Hi.
  case Ep: (nth_error (rev L) i) => [p|]; last by move/nth_error_None: Ep; lia.
  rewrite !nth_error_map Ep /=.
  case Eq: (nth_error (rev L) j) => [q|] //= [E].
  have [? [? [? [? [Ep' _]]]]] := Hargs i p Ep.
  have [? [? [? [? [Eq' _]]]]] := Hargs j q Eq.
  by move: E; rewrite Ep' Eq' /=; lia.
split.
  apply/Forall_forall => p /Hargs' [i [nm [t [r [x0 [-> [Hx0 [Hd Hi]]]]]]]].
  have [v0 [tg [_ [Hxs [Hf0 Hz0]]]]] := seed_args_nth ds x dx i nm t r Hfit Hd.
  move: Hxs; rewrite -/xs Hx0 => -[->].
  repeat split=> //=; last exact: fits_type Hf0.
  by apply: (non_real_varied_none _ nm t r Hnrv); exact: nth_error_In Hd.
split.
  move=> p q /Hargs' [i [nm [t [r [x0 [-> [Hx [Hd _]]]]]]]].
  move=> /Hargs' [i' [nm' [t' [r' [x0' [-> [Hx' [Hd' _]]]]]]]] /= E; subst i'.
  by move: Hx' Hd'; rewrite Hx Hd => -[->] [-> -> ->].
split; first by move=> p /Hargs' [? [? [? [? [? [-> [_ [_ Hi]]]]]]]].
split; first exact: Hpn_inj.
apply: nth_error_ext => i; rewrite nth_error_map.
case Ep: (nth_error (rev L) i) => [p|] /=.
  by have [nm [t [r [x0 [-> Hx0]]]]] := Hargs i p Ep; rewrite Hx0.
by apply/nth_error_None; move/nth_error_None: Ep; rewrite length_rev; lia.
Qed.

(* Running the tangent program over the reals, from the primal arguments and
   the seeded tangents, computes the value and the tangent of the dual
   evaluation of the normal form of f; its statements follow the discipline
   of simplify. *)
Theorem tangent_simulates_duals_with (dd : val R -> val R) (r0 : val R)
  (f : function) (x : list (val R)) (dx : list R) (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  (forall i d w, nth_error (decls f) i = Some d -> nth_error x i = Some w ->
     dot_out d = true -> fits d (dd w)) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out,
    open_pairs (dfbody (Tangent.tangent (annotate false (normalize f))) W) 0 = (DBody r ps ss, k) /\
    Forall consistent (params ps) /\ good (params ps) (params ps) ss /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (tangent_inputs_with dd r0 (decls f) x dx) = Some out /\
    tangent_output (decls f) out = Some (primal v, tangent v).
Proof.
move=> Hpar Hwf Hfit Hdd Hev.
set xs := seed_args (decls f) x dx in Hev *.
have Hnp := normalize_parametric f Hpar.
set dP := afdef (normalize f) pv.
have HD := Hnp pv (val (dual R)); rewrite -/dP in HD.
rewrite /aeval_function in Hev.
have [L [res [bP Ho]]] := open_P_some dP [] 0 xs _ v HD Hev.
have [new [EL [Hlen Hargs]]] := open_P_args dP 0 xs [] L res bP Ho.
rewrite app_nil_r in EL; subst new.
(* the bodies of the five instances *)
have [bA [HbA Htr]] := annotate_open dP [] 0 xs L res bP _ (Hnp pv avar) Ho.
have [resW [bW [HrW [HbW Hwfd]]]] :=
  wf_open dP [] 0 xs L res bP _ (decls f) (Hnp pv vinfo) Ho.
have [bD [HbD HevD]] := eval_open dP [] 0 xs L res bP _ HD Ho.
rewrite HevD in Hev.
have Hds : decls f = map (fun p => fst (arg_entry p)) (rev L)
  by exact: (decls_open dP (map (fun p => (p, tt)) []) [] 0 xs L res bP _
               (Hnp pv unit) Ho).
rewrite Nat.add_0_l in Htr Hwfd.
set n := length xs in Htr Hwfd *.
set tr := annotate_definition_t false 0 (afdef (normalize f) avar) in Htr *.
have [resT [bT [HrT [HbT Hopen]]]] :=
  tangent_open dP [] 0 xs L res bP (afdef (normalize f) (tvar W)) tr
    (tangent_body W) (Hnp pv (tvar W)) Ho.
rewrite Nat.add_0_l -/n in Hopen.
(* well_formed *)
rewrite /well_formed -/(decls f) in Hwf.
case Hnrv: (non_real_varied (decls f)) Hwf => [//|] Hwf.
rewrite Hwfd in Hwf.
(* the arguments *)
have [Hargs' [HnL [Hstat [Huniq [Hnum [Hpn_inj Hxs]]]]]] :=
  open_args_facts _ _ _ _ n Hfit Hnrv Hds Hlen erefl Hargs.
rewrite -/xs in Hargs' Hxs.
have Hdot : forall p, In p L -> tdot (pt p) = true ->
    has_dot (fst (arg_entry p)) = true.
  move=> p /Hargs' [i [nm [t [r [x0 [-> [_ [Hd _]]]]]]]] /= Ht.
  have := non_real_varied_none _ nm t r Hnrv (nth_error_In _ _ Hd) Ht.
  by case: r Ht {Hd}; case: t.
set ext := if existsb written_decl (decls f) then []
           else [(KVar (DotOf ResultVar), r0)].
set s0 := prim_entries (rev L) ++ dot_entries dd (rev L) ++ ext.
have Hs0 : forall p, In p L ->
    store_get s0 (keyv (stored p)) = Some (primal (pd p)) /\
    (has_dot (fst (arg_entry p)) = true ->
     store_get s0 (keyv (DotOf (stored p))) = Some (dot_val dd p)).
  move=> p Hp; have Hp' : In p (rev L) by rewrite -in_rev.
  rewrite /s0 /keyv /stored /= !store_get_app (prim_lookup _ _ HnL Hp').
  split=> // Hd.
  by rewrite prim_lookup_dot (dot_lookup _ _ _ HnL Hp' Hd).
have Hdv : forall p, In p L -> tdot (pt p) = true ->
    dot_val dd p = tangent (pd p).
  move=> p /Hargs' [i [nm [t [r [x0 [-> _]]]]]] /= Ht.
  by rewrite /dot_val /=; case: r Ht.
have Hsok : forall p, In p L -> store_ok s0 p.
  move=> p Hp; have [S1 S2] := Hs0 p Hp; split=> // Ht.
  by rewrite -(Hdv p Hp Ht); apply/S2/Hdot.
(* the tangent function, opened *)
change
  (open_pairs (dfbody (Tangent.tangent (annotate false (normalize f))) W) 0)
  with (open_pairs
          (open_arguments W
             (rebuild_definition (tvar W) (afdef (normalize f) (tvar W)) tr) 0
             (map arg_entry []) (tangent_body W)) 0).
rewrite Hopen /tangent_body open_pairs_sbind Htr.
set wT := match resT with AWrites y => Some y | AReturns _ => None end.
case Hob: (open_pairs (tan W wT (rebuild (tvar W) bT
                                   (annotate_body_t false Forward n bA))) n)
  => [[sb [ve de]] c'].
have HAL :
    Forall (fun p => tstored (pt p) = stored p /\ varg (pw p) <> None) (rev L).
  apply/Forall_forall => p; rewrite in_rev_iff.
  by move=> /Hargs' [? [? [? [? [? [-> _]]]]]].
have HAL' : Forall (fun p => varg (pw p) <> None) (rev L).
  by apply: Forall_impl HAL => p [].
set pps := map (tangent_primal W) (rev (map arg_entry L)) ++
           concat (map (tangent_dot W) (rev (map arg_entry L))).
have Hpps : params pps = map stored (rev L) ++
    concat (map (fun p => if has_dot (fst (arg_entry p))
                          then [DotOf (stored p)] else []) (rev L)).
  by rewrite /pps params_app -map_rev params_primal (params_dots _ HAL').
have Hpps_ok : forall y, In y (params pps) -> below n y /\ consistent y.
  move=> y; rewrite Hpps => /(in_app_or _ _ _)
    [/(in_map_iff _ _ _) [p [<- Hp]] | /in_dots_inv [p [Hp [-> _]]]];
    move: Hp; rewrite in_rev_iff => /Hnum Hp; rewrite /stored /=;
    split=> //; lia.
have Hreads : forall p, In p L -> In (stored p) (params pps) /\
    (tdot (pt p) = true -> In (DotOf (stored p)) (params pps)).
  move=> p Hp; have Hp' : In p (rev L) by rewrite -in_rev.
  rewrite Hpps; split=> [|Ht]; apply: in_or_app; first by left; exact: in_map.
  by right; apply: in_dots Hp' _; exact: Hdot.
case: (wf_result_facts _ _ _ _ Hwf) => [[EW [Hnw HtcB]] |
  [w [nm [role [EW [Hg [Hwr [H1w [Hraw [HtcB [Hdep Hinout]]]]]]]]]]].
- (* the function returns a real *)
  subst resW; destruct res as [tR | yP]; rewrite /= in HrW; last by [].
  subst tR; destruct resT as [tT | yT]; rewrite /= in HrT; last by [].
  subst tT.
  have Hctx : ctx_ok L n n s0 None PTop (live_anf n bW) Real.
    constructor=> //.
    by move=> p Hp _; exact: Hsok.
  have := (proj1 simulation) bP L n n s0 None PTop Forward bA bW bT bD Real v
            HbA HbW HbT HbD Hctx I HtcB Hev.
  rewrite Hob => -[Hcc [Hht [_ [Hrv1 [Hrv2 [s1 [Hrun1 [Hfr1 [Hve Hde]]]]]]]]].
  case: v Hev Hht Hve Hde => [dv | | | |] Hev Hht Hve Hde //.
  (* the scoping discipline *)
  set rps : list (dparam W) := [DParam ByRef Real (DotOf ResultVar)].
  set sc := params (pps ++ rps).
  have Hsc_ok : forall y, In y sc -> below n y /\ consistent y.
    move=> y; rewrite /sc params_app.
    by move=> /(in_app_or _ _ _) [/Hpps_ok // | [<- | []]].
  have Hscope : scope_ok L n None PTop (live_anf n bW) sc sc.
    split; first exact/Forall_forall.
    split; first exact: incl_refl.
    split=> [p Hp _ | o //].
    have [R1 R2] := Hreads p Hp; rewrite /sc params_app.
    by split=> [|Hd]; apply: in_or_app; left; [exact: R1 | exact: R2].
  have := (proj1 scoping) bP L n n None PTop Forward bA bW bT Real sc sc
            HbA HbW HbT (ctx_sctx _ _ _ _ _ _ _ _ Hctx) Hscope I HtcB.
  rewrite Hob => -[_ Hgk] /=.
  set tail : list (dstmt W) :=
    [DAssign (DVar (DotOf ResultVar)) de; DReturn ve].
  (* the run *)
  set s2 := store_set s1 (keyv (DotOf ResultVar)) (VReal (dsnd dv)).
  set s3 := store_set s2 Returned (VReal (dfst dv)).
  have Hve2 : xev s2 ve = Some (VReal (dfst dv)).
    rewrite /s2 xev_set_other //.
    move=> y Hy; case: (Hrv1 y Hy) => [[p [_ [_ [-> | ->]]]] | [Hb Hcy]] E //.
    by move/(keyv_inj y (DotOf ResultVar) Hcy I): E => Ey; subst y; apply: Hb.
  have Hrun : run (sb ++ tail) s0 = Some s3.
    rewrite run_app Hrun1 /tail.
    rewrite (run_assign_var _ _ _ (VReal (dsnd dv)) _ Hde) -/s2.
    by move: Hve2; rewrite /run /xev /= => ->.
  have Hin : tangent_inputs_with dd r0 (decls f) x dx =
      map (fun p => primal (pd p)) (rev L) ++
      concat (map (dot_in dd) (rev L)) ++
      [r0].
    by rewrite (inputs_eq _ _ _ _ _ (rev L) Hxs Hds) Hnw.
  have Hlenp : length (map (out_dparam nat) (pps ++ rps)) =
               length (tangent_inputs_with dd r0 (decls f) x dx).
    have Hcl : length (concat (map (tangent_dot W) (map arg_entry (rev L)))) =
               length (concat (map (dot_in dd) (rev L))).
      move: HAL'; elim: (rev L) => [|p AL IH] //=.
      move=> /Forall_cons_iff [Hg /IH {}IH].
      rewrite !length_app IH (tangent_dot_entry _ Hg) /dot_in.
      by case: (has_dot _).
    rewrite Hin length_map /pps /rps -map_rev !length_app !length_map Hcl /=.
    by lia.
  have Hs0eq : map (fun '(DParam _ _ x, a) => (KVar x, a))
                 (combine (map (out_dparam nat) (pps ++ rps))
                    (tangent_inputs_with dd r0 (decls f) x dx)) = s0.
    rewrite Hin /pps -map_rev -app_assoc.
    by rewrite (initial_store dd (rev L) rps [r0] HAL erefl) /s0 /ext Hnw.
  (* every parameter has a final value *)
  have Hfin : forall pw t y,
      In (DParam pw t y) (map (out_dparam nat) (pps ++ rps)) ->
      exists w, store_get s3 (KVar y) = Some w.
    move=> pp0 t0 y /(in_map_iff _ _ _) [[pp1 t1 y'] [[_ _ <-] Hy']].
    have Hy2 : In y' sc.
      rewrite /sc /params; apply/(in_map_iff _ _ _).
      by exists (DParam pp1 t1 y').
    rewrite /s3 /s2 store_get_set_other //.
    move: Hy2; rewrite /sc params_app.
    move=> /(in_app_or _ _ _) [Hy2 | [<- | []]]; last first.
      by rewrite store_get_set_same; eauto.
    have Hne : y' <> DotOf ResultVar.
      move=> Ey; move: Hy2; rewrite Ey Hpps.
      by move=> /(in_app_or _ _ _)
        [/(in_map_iff _ _ _) [? [E _]] | /in_dots_inv [? [_ [E _]]]].
    have [Hb Hc] := Hpps_ok _ Hy2.
    rewrite store_get_set_other.
      by move/(keyv_inj (DotOf ResultVar) y' I Hc)/esym.
    rewrite -/(keyv y') (Hfr1 y' Hb Hc) //.
    move: Hy2; rewrite Hpps => /(in_app_or _ _ _)
      [/(in_map_iff _ _ _) [p [<- Hp]] | /in_dots_inv [p [Hp [-> Hd]]]];
      rewrite in_rev_iff in Hp.
      by have [S1 _] := Hs0 p Hp; eauto.
    by have [_ S2] := Hs0 p Hp; eauto.
  have [fs [Hfs [Hlfs Hnth]]] := finals_some s3 _ Hfin.
  exists DReturnsReal, (pps ++ rps), (sb ++ tail), c', (fs, [VReal (dfst dv)]).
  split; first by rewrite /pps /rps -app_assoc.
  split; first by apply/Forall_forall => y /Hsc_ok [].
  split.
    apply: Hgk => sc' wr' I1 I2 _ _ [Q1 Q2]; rewrite /tail.
    apply: GoodAssign;
      [apply: I2; rewrite /sc params_app; apply: in_or_app; right; by left
      | exact: Q2 |].
    by apply: GoodReturn; [exact: Q1 | constructor].
  split.
    rewrite Hlenp Nat.eqb_refl /=.
    by rewrite Hs0eq -/(run (sb ++ tail) s0) Hrun /= Hfs /s3 store_get_set_same.
  rewrite /= index_of_written_none //.
  have Hlast : nth_error (map (out_dparam nat) (pps ++ rps)) (length fs - 1) =
               Some (DParam ByRef Real (DotOf ResultVar)).
    rewrite Hlfs map_app length_app length_map /=.
    rewrite nth_error_app2; first by rewrite length_map; lia.
    rewrite length_map.
    by have -> : (length pps + 1 - 1 - length pps = 0)%nat by lia.
  rewrite (nth_error_last fs (VInt 0) (VReal (dsnd dv))) //.
  rewrite (Hnth _ _ _ _ Hlast) /s3 store_get_set_other //.
  by rewrite /s2 store_get_set_same.
- (* the function writes an argument *)
  subst resW; destruct res as [tR | yP]; rewrite /= in HrW; first by [].
  destruct yP as [y | | ]; rewrite /= in HrW; try by [].
  move/in_gW: HrW => [HyL Ew]; subst w.
  destruct resT as [tT | yT]; rewrite /= in HrT; first by [].
  destruct yT as [yt | | ]; rewrite /= in HrT; try by [].
  move/in_gT: HrT => [_ Eyt]; subst yt.
  have [j [nm' [t [r [x0 [Ey [Hxj [Hdj Hj]]]]]]]] := Hargs' y HyL.
  have Hvy : vty (pw y) = t by rewrite Ey.
  have Hpy : pn y = j by rewrite Ey.
  rewrite Ey /= in Hg; case: Hg => ? ?; subst nm role.
  have Hdecl_y : fst (arg_entry y) = Decl nm' t r by rewrite Ey.
  have Hnw : existsb written_decl (decls f) = true.
    apply/existsb_exists; exists (Decl nm' t r); split=> //.
    exact: nth_error_In Hdj.
  have Hdy : has_dot (fst (arg_entry y)) = true.
    rewrite Hdecl_y; move: Hraw Hwr; rewrite Hvy.
    by case: (t) => //= _; case: (r).
  rewrite Hvy in HtcB.
  have Hown_cases :
      owner (Some (AVar y)) PTop =
      match t with Array _ => Some y | _ => None end
    by rewrite /= Hvy.
  (* the initial tangent of y fits its declaration *)
  have Hfy : fits (Decl nm' t r) (dot_val dd y).
    have [w [tg [Hw [Hxs' [Hf _]]]]] :=
      seed_args_nth _ _ dx j nm' t r Hfit Hdj.
    move: Hxs'; rewrite -/xs Hxj => -[Ex0].
    rewrite /dot_val Hdecl_y.
    have -> : pd y = val_dual w tg by rewrite Ey.
    case Eo: (dot_out (Decl nm' t r)); last exact: fits_tangent.
    by apply: (Hdd j _ _ Hdj _ Eo); rewrite primal_val_dual.
  have Hctx : ctx_ok L n n s0 (Some (AVar y)) PTop (live_anf n bW) t.
  { constructor=> //.
    + by move=> p Hp _; exact: Hsok.
    + by move=> a0 [<-]; exists y; split=> //; split=> //; rewrite Ey.
    + move=> o p; rewrite Hown_cases; case: (t) => // _ [<-] Hp E.
      by left; exact: Hpn_inj Hp HyL E.
    + move=> o p; rewrite Hown_cases; case: (t) => // _ [<-] Hp Lp E.
      rewrite (Hpn_inj p y Hp HyL E) in Lp *.
      have [S1 S2] := Hs0 y HyL; split=> //.
      rewrite (S2 Hdy) /dot_val Hdecl_y.
      case Er: (r) Hwr => //= _.
      by move: Lp; rewrite /live_anf Hdep.
    + move=> p o Hp Lp Ha [Hg' | [<-]]; last first.
        by rewrite Hown_cases; case: (t) => // _ [<-].
      by have [? [? [? [? [? [Ep _]]]]]] := Hargs' p Hp; move: Hg'; rewrite Ep.
    + by move=> Ha; rewrite Hown_cases; case: (t) Ha.
    + move=> y' _ [<-] Ha; split; first by rewrite Hvy.
      split.
        case Er: (r) Hwr => //= _.
          by move=> Ly; move: Ly; rewrite /live_anf Hdep.
        by rewrite Ey Er.
      have [_ [_ [_ [_ [_ [_ [_ [_ [Ht _]]]]]]]]] := static_in _ _ _ Hstat HyL.
      have [S1 /(_ Hdy) S2] := Hs0 y HyL.
      move: Ha Ht S1 S2 Hfy; rewrite Hvy; case: (t) => // z _.
      case: (pd y) => // l Ht S1 S2.
      case: (dot_val dd y) S2 => // l2 S2 /= Hl2.
      by exists (map dfst l), l2; rewrite !length_map; auto. }
  have Hra' : real_or_array t by rewrite -Hvy.
  have := (proj1 simulation) bP L n n s0 (Some (AVar y)) PTop Forward
            bA bW bT bD t v HbA HbW HbT HbD Hctx Hra' HtcB Hev.
  rewrite Hob => -[Hcc [Hht [_ [Hrv1 [Hrv2 [s1 [Hrun1 [Hfr1 Hres]]]]]]]].
  (* the scoping discipline *)
  set sc := params pps.
  have Hscope : scope_ok L n (Some (AVar y)) PTop (live_anf n bW) sc sc.
    split; first exact/Forall_forall.
    split; first exact: incl_refl.
    split=> [p Hp _ | o]; first exact: Hreads.
    rewrite Hown_cases; case: (t) => // _ [<-].
    have [R1 R2] := Hreads y HyL; split=> //.
    rewrite /sc Hpps; apply: in_or_app; right; apply: in_dots Hdy.
    by rewrite in_rev_iff.
  have := (proj1 scoping) bP L n n (Some (AVar y)) PTop Forward bA bW bT t
            sc sc HbA HbW HbT (ctx_sctx _ _ _ _ _ _ _ _ Hctx) Hscope Hra' HtcB.
  rewrite Hob => -[_ Hgk].
  (* the arguments of the tangent function *)
  have Hin : tangent_inputs_with dd r0 (decls f) x dx =
      map (fun p => primal (pd p)) (rev L) ++
      concat (map (dot_in dd) (rev L)) ++ [].
    by rewrite (inputs_eq _ _ _ _ _ (rev L) Hxs Hds) Hnw.
  have Hlenp : length (map (out_dparam nat) (pps ++ [])) =
               length (tangent_inputs_with dd r0 (decls f) x dx).
    have Hcl : length (concat (map (tangent_dot W) (map arg_entry (rev L)))) =
               length (concat (map (dot_in dd) (rev L))).
      move: HAL'; elim: (rev L) => [|p AL IH] //=.
      move=> /Forall_cons_iff [Hg /IH {}IH].
      rewrite !length_app IH (tangent_dot_entry _ Hg) /dot_in.
      by case: (has_dot _).
    by rewrite Hin length_map /pps -map_rev !length_app !length_map Hcl /=; lia.
  have Hs0eq : map (fun '(DParam _ _ x, a) => (KVar x, a))
                 (combine (map (out_dparam nat) (pps ++ []))
                    (tangent_inputs_with dd r0 (decls f) x dx)) = s0.
    rewrite Hin /pps -map_rev -app_assoc.
    by rewrite (initial_store dd (rev L) [] [] HAL erefl) /s0 /ext Hnw.
  have Hidx : index_of_written (decls f) 0 = Some j
    by exact: (index_of_written_unique (decls f) j _ 0 Hdj Hwr H1w).
  have HLn : length L = n by rewrite /n Hxs length_map length_rev.
  have Hlds : length (decls f) = n by rewrite Hds length_map length_rev HLn.
  have Hry : nth_error (rev L) j = Some y.
    case Eq: (nth_error (rev L) j) => [q|]; last first.
      by move/nth_error_None: Eq; rewrite length_rev; lia.
    have [n0 [t0 [rq [x1 [Eq' Hx']]]]] := Hargs j q Eq; subst q.
    move: Hx' Hdj; rewrite Hxj Hds nth_error_map Eq /= => -[<-] [-> -> ->].
    by rewrite Ey.
  have Hprim_j : nth_error (map (out_dparam nat) pps) j =
                 Some (out_dparam nat (tangent_primal W (arg_entry y))).
    rewrite /pps map_app nth_error_app1.
      by rewrite !length_map length_rev length_map; lia.
    by rewrite -map_rev !nth_error_map Hry.
  have Hdot_j : exists pw0 t0,
      nth_error (map (out_dparam nat) pps)
        (length (decls f) + length (filter has_dot (firstn j (decls f)))) =
      Some (out_dparam nat (DParam pw0 t0 (DotOf (stored y)))).
    have [pw0 [t0 Hpos]] := dot_param_position (rev L) j y HAL' Hry Hdy.
    exists pw0, t0; rewrite /pps map_app nth_error_app2.
      by rewrite !length_map length_rev length_map; lia.
    rewrite !length_map length_rev length_map HLn Hlds.
    have -> : (n + length (filter has_dot (firstn j (decls f))) - n =
               length (filter has_dot (firstn j (decls f))))%nat by lia.
    by rewrite -map_rev nth_error_map Hds Hpos.
  (* the parameters keep a value *)
  have Hs0p : forall y0, In y0 (params pps) ->
      exists w, store_get s0 (keyv y0) = Some w.
    move=> y0; rewrite Hpps => /(in_app_or _ _ _)
      [/(in_map_iff _ _ _) [p [<- Hp]] | /in_dots_inv [p [Hp [-> Hd]]]];
      rewrite in_rev_iff in Hp.
      by have [S1 _] := Hs0 p Hp; eauto.
    by have [_ S2] := Hs0 p Hp; eauto.
  have Hs1p : forall y0, In y0 (params pps) ->
      exists w, store_get s1 (keyv y0) = Some w.
    move=> y0 Hy0; have [Hb Hc] := Hpps_ok y0 Hy0.
    case Ein: (inplace (Some (AVar y)) PTop) Hfr1 Hres => [m|] Hfr1 Hres;
      last first.
      by rewrite (Hfr1 y0 Hb Hc) //; exact: Hs0p.
    case: (dvar_eq_dec y0 m) => [-> | Hn1];
      last case: (dvar_eq_dec y0 (DotOf m)) => [-> | Hn2]; last first.
      by rewrite (Hfr1 y0 Hb Hc); [move=> m' [<-] | exact: Hs0p].
      by move: Ein Hres; rewrite /inplace Hown_cases;
        case: (t) => // z [<-] [o [[<-] [R1 R2]]]; eauto.
    by move: Ein Hres; rewrite /inplace Hown_cases;
      case: (t) => // z [<-] [o [[<-] [R1 R2]]]; eauto.
  have Hty_y : tty (pt y) = t by rewrite Ey.
  have Hst_y : tstored (pt y) = stored y by rewrite Ey.
  rewrite [tangent_result _ _ _ _]/= Hty_y Hst_y.
  destruct t as [| | | z]; try destruct Hra'.
  + (* a written real *)
    case: Hres => Hve Hde.
    case: v Hev Hht Hve Hde => [dv | | | |] Hev Hht Hve Hde //.
    set tail : list (dstmt W) :=
      [DAssign (DVar (stored y)) ve; DAssign (DVar (DotOf (stored y))) de].
    set s2 := store_set s1 (keyv (stored y)) (VReal (dfst dv)).
    set s3 := store_set s2 (keyv (DotOf (stored y))) (VReal (dsnd dv)).
    have Hde2 : xev s2 de = Some (VReal (dsnd dv)).
      rewrite /s2 xev_set_other //.
      move=> y0 Hy0; case: (Hrv2 y0 Hy0) => [[p [_ [_ ->]]] | [Hb Hcy]] E //.
      move/(keyv_inj y0 (stored y) Hcy erefl): E => Ey0; subst y0.
      by apply: Hb; rewrite /= Hpy.
    have Hrun : run (sb ++ tail) s0 = Some s3.
      rewrite run_app Hrun1 /tail.
      rewrite (run_assign_var _ _ _ (VReal (dfst dv)) _ Hve) -/s2.
      by rewrite (run_assign_var _ _ _ (VReal (dsnd dv)) _ Hde2).
    have Hfin : forall pw0 t0 y0,
        In (DParam pw0 t0 y0) (map (out_dparam nat) (pps ++ [])) ->
        exists w, store_get s3 (KVar y0) = Some w.
      move=> pp0 t0 y0; rewrite app_nil_r.
      move=> /(in_map_iff _ _ _) [[pp1 t1 y'] [[_ _ <-] Hy']].
      have Hy2 : In y' (params pps).
        by rewrite /params; apply/(in_map_iff _ _ _); exists (DParam pp1 t1 y').
      rewrite -/(keyv y') /s3 /s2 !store_get_set.
      case: (key_eqb (keyv (DotOf (stored y))) (keyv y')); first by eauto.
      case: (key_eqb (keyv (stored y)) (keyv y')); first by eauto.
      exact: Hs1p.
    have [fs [Hfs [Hlfs Hnth]]] := finals_some s3 _ Hfin.
    exists DVoid, (pps ++ []), (sb ++ tail), c', (fs, []).
    split; first by rewrite /pps -app_assoc.
    split; first by apply/Forall_forall => y0; rewrite app_nil_r => /Hpps_ok [].
    split.
      rewrite app_nil_r; apply: Hgk => sc' wr' I1 I2 _ _ [Q1 Q2]; rewrite /tail.
      have [R1 _] := Hreads y HyL.
      apply: GoodAssign; [by apply: I2 | exact: Q1 |].
      apply: GoodAssign;
        [apply: I2; rewrite /sc Hpps; apply: in_or_app; right;
         apply: in_dots Hdy; by rewrite in_rev_iff
        | exact: Q2 | constructor].
    split.
      rewrite /= Hlenp Nat.eqb_refl /= Hs0eq -/(run (sb ++ tail) s0) Hrun /=.
      by rewrite Hfs.
    rewrite /= Hidx.
    have [pw0 [t0 Hdj']] := Hdot_j.
    rewrite app_nil_r in Hnth.
    have Hpj : nth_error (map (out_dparam nat) pps) j =
               Some (DParam ByRef Real (DBound (pn y)))
      by rewrite Hprim_j Ey; case: (r) Hwr.
    have Hdj2 :
        nth_error (map (out_dparam nat) pps)
          (length (decls f) + length (filter has_dot (firstn j (decls f))))
        = Some (DParam pw0 t0 (DotOf (DBound (pn y)))) by rewrite Hdj'.
    rewrite (Hnth _ _ _ _ Hpj) (Hnth _ _ _ _ Hdj2).
    rewrite -/(keyv (DotOf (stored y))) -/(keyv (stored y)).
    by rewrite /s3 /s2 store_get_set_same store_get_set_other //
      store_get_set_same.
  + (* a written array, updated in place *)
    case: Hres => o [Eo [R1 R2]].
    rewrite /inplace Hown_cases in Eo; case: Eo => Eo; subst o.
    have Hrun : run (sb ++ []) s0 = Some s1 by rewrite app_nil_r.
    have Hfin : forall pw0 t0 y0,
        In (DParam pw0 t0 y0) (map (out_dparam nat) (pps ++ [])) ->
        exists w, store_get s1 (KVar y0) = Some w.
      move=> pp0 t0 y0; rewrite app_nil_r.
      move=> /(in_map_iff _ _ _) [[pp1 t1 y'] [[_ _ <-] Hy']].
      apply: Hs1p; rewrite /params; apply/(in_map_iff _ _ _).
      by exists (DParam pp1 t1 y').
    have [fs [Hfs [Hlfs Hnth]]] := finals_some s1 _ Hfin.
    exists DVoid, (pps ++ []), (sb ++ []), c', (fs, []).
    split; first by rewrite /pps -app_assoc.
    split; first by apply/Forall_forall => y0; rewrite app_nil_r => /Hpps_ok [].
    split; first by rewrite app_nil_r; apply: Hgk => *; constructor.
    split.
      rewrite /= Hlenp Nat.eqb_refl /= Hs0eq -/(run (sb ++ []) s0) Hrun /=.
      by rewrite Hfs.
    rewrite /= Hidx.
    have [pw0 [t0 Hdj']] := Hdot_j.
    rewrite app_nil_r in Hnth.
    have Hpj : nth_error (map (out_dparam nat) pps) j =
               Some (DParam ByRef (Array z) (DBound (pn y)))
      by rewrite Hprim_j Ey; case: (r) Hwr.
    have Hdj2 :
        nth_error (map (out_dparam nat) pps)
          (length (decls f) + length (filter has_dot (firstn j (decls f))))
        = Some (DParam pw0 t0 (DotOf (DBound (pn y)))) by rewrite Hdj'.
    rewrite (Hnth _ _ _ _ Hpj) (Hnth _ _ _ _ Hdj2).
    rewrite -/(keyv (DotOf (stored y))) -/(keyv (stored y)).
    by rewrite R1 R2.
Qed.

(* Theorem 1, with zeros in the output-only tangent parameters. *)
Lemma zero_dot_fits ds x : Forall2 fits ds x ->
  forall i d w, nth_error ds i = Some d -> nth_error x i = Some w ->
  dot_out d = true -> fits d (zero_dot w).
Proof.
move=> Hfit i [nm t r] w Hd Hw _.
have [w' [_ [Hw' [_ [Hf _]]]]] := seed_args_nth _ _ [] i nm t r Hfit Hd.
by move: Hw'; rewrite Hw => -[->]; exact: fits_tangent.
Qed.

Theorem tangent_simulates_duals (f : function) (x : list (val R))
  (dx : list R) (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) =
    Some v ->
  exists r ps ss k out,
    open_pairs (dfbody (Tangent.tangent (annotate false (normalize f))) W) 0 =
      (DBody r ps ss, k) /\
    Forall consistent (params ps) /\ good (params ps) (params ps) ss /\
    exec_scoped reals
      (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (tangent_inputs (decls f) x dx) = Some out /\
    tangent_output (decls f) out = Some (primal v, tangent v).
Proof.
move=> Hpar Hwf Hfit Hev; rewrite tangent_inputs_zero.
by apply: tangent_simulates_duals_with => //; exact: zero_dot_fits.
Qed.
