(* AdjointTop.v — the adjoint simulation at the level of a function: the
   arguments are opened, their adjoints given (AdjointSpec.v), the body
   simulated (AdjointCorrect.v) from the forward sweep to the reverse sweep,
   and the final adjoints read back as the gradient. The pairing of the owners
   (the arguments that carry an adjoint) at the end of the reverse sweep, minus
   the initial adjoints, is the dot product of the tangent of the seed with
   the gradient; the simulation of the body makes it the tangent of the
   result times the seed. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint Simplify Scoping
  AnfEquiv Correctness TangentCorrect TangentTop AdjointCorrect AdjointBranch AdjointSpec DualsDerive
  AdjointFold AdjointFoldy AdjointNestFwd AdjointNesty.

From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

(* At the top, the body is no loop body: there is no tail tape to give. *)
Lemma no_tail_tape_top cv k L b bA bD s (B : dvar W -> Prop) :
  forall ix sx n0, PTop = PArray ix sx -> B n0 ->
  tail_tape cv k L b bA bD s n0.
Proof. by []. Qed.

(* The analyses open the arguments as open_P does, in either mode. *)
Lemma annotate_open_cv cv (dP : adefinition pv bare) : forall L k xs L' res bP dA,
  adefinition_eq (gA L) dP dA -> open_P dP k xs L = Some (L', res, bP) ->
  exists bA, anf_eq (gA L') bP bA /\
             annotate_definition_t cv k dA = annotate_body_t cv Forward (k + length xs) bA.
Proof.
elim: dP => [n t r f IH | rP bP0] L k xs L' res bP dA HA Ho.
  case: dA HA => [n' t' r' fA |] //= [En [Et [Er HA]]]; subst n' t' r'.
  case: xs Ho => [| x xs] //= Ho.
  have [bA [H1 H2]] := IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs L'
    res bP (fA (AV k (varied_role r))) (HA _ _) Ho.
  by exists bA; split=> //=; rewrite H2; congr annotate_body_t; lia.
case: dA HA => [| rA bA] //= HA.
case: xs Ho => [| ? ?] //= [EL Er Eb]; subst L' res bP.
by exists bA; split; [exact: (proj2 HA) | rewrite /= Nat.add_0_r].
Qed.

(* ---------------------------------------------------------------------------
   Stores with distinct keys. *)

Lemma store_get_in (s : store R) k v : NoDup (map fst s) -> In (k, v) s -> store_get s k = Some v.
Proof.
elim: s => [| [k0 v0] s IH] // /NoDup_cons_iff [Hk Hnd] /= [[-> ->] | Hin].
  by rewrite key_eqb_refl.
case E: (key_eqb k0 k); last by apply: IH.
move/key_eqb_eq: E => E; subst k0; case: Hk.
by apply/in_map_iff; exists (k, v).
Qed.

Lemma store_get_notin (s : store R) k : ~ In k (map fst s) -> store_get s k = None.
Proof.
elim: s => [| [k0 v0] s IH] //= Hn.
case E: (key_eqb k0 k).
  by move/key_eqb_eq: E => E; subst k0; case: Hn; left.
by apply: IH => H; apply: Hn; right.
Qed.

(* A key in the store stays in it: the statements only set keys. *)
Definition keeps (s s' : store R) : Prop := forall k, store_get s k <> None -> store_get s' k <> None.

Lemma keeps_set s k v : keeps s (store_set s k v).
Proof. by move=> k' H; rewrite store_get_set; case: (key_eqb k k'). Qed.

Lemma keeps_trans s1 s2 s3 : keeps s1 s2 -> keeps s2 s3 -> keeps s1 s3.
Proof. by move=> H1 H2 k H; apply/H2/H1. Qed.

Lemma assign_keeps s l v s' : assign reals s l v = Some s' -> keeps s s'.
Proof.
rewrite /assign => E.
repeat match type of E with
       | context [match ?e with _ => _ end] => destruct e
       end; try discriminate.
all: by case: E => <-; apply: keeps_set.
Qed.

Lemma exec_up_keeps (body : store R -> option (store R)) i lo n s s' :
  (forall s1 s2, body s1 = Some s2 -> keeps s1 s2) -> exec_up R body i lo n s = Some s' -> keeps s s'.
Proof.
move=> Hb; elim: n lo s => [| n IH] lo s /= E.
  by case: E => <-.
case E1: (body _) E => [s1 |] // E.
apply: (keeps_trans _ (store_set s (KVar i) (VInt lo))); first exact: keeps_set.
exact: keeps_trans (Hb _ _ E1) (IH _ _ E).
Qed.

Lemma exec_down_keeps (body : store R -> option (store R)) i hi n s s' :
  (forall s1 s2, body s1 = Some s2 -> keeps s1 s2) -> exec_down R body i hi n s = Some s' -> keeps s s'.
Proof.
move=> Hb; elim: n hi s => [| n IH] hi s /= E.
  by case: E => <-.
case E1: (body _) E => [s1 |] // E.
apply: (keeps_trans _ (store_set s (KVar i) (VInt hi))); first exact: keeps_set.
exact: keeps_trans (Hb _ _ E1) (IH _ _ E).
Qed.

Fixpoint exec_keeps (st : dstmt nat) : forall s s', exec reals st s = Some s' -> keeps s s'.
Proof.
(* Ltac assert: with ssr have, Qed fails "Cannot guess decreasing argument" *)
assert (Hl : forall l s s',
    (fix exec_stmts (l : list (dstmt nat)) (s : store R) : option (store R) :=
       match l with
       | [] => Some s
       | st' :: l' =>
           match exec reals st' s with
           | Some s1 => exec_stmts l' s1
           | None => None
           end
       end) l s = Some s' -> keeps s s').
  elim=> [| st0 l IHl] s s' /=; first by case=> <-.
  case E1: (exec reals st0 s) => [s1 |] // E.
  exact: keeps_trans (exec_keeps st0 s s1 E1) (IHl s1 s' E).
move=> sa sb E; destruct st; cbn [exec] in E;
  repeat match type of E with
         | context [match ?e with _ => _ end] =>
             lazymatch e with
             | assign _ _ _ _ => fail
             | exec_up _ _ _ _ _ _ => fail
             | exec_down _ _ _ _ _ _ => fail
             | _ => destruct e
             end
         end; try discriminate;
  try (injection E as <-; apply: keeps_set);
  try exact: (Hl _ _ _ E);
  try exact: (assign_keeps _ _ _ _ E).
- exact: (exec_up_keeps _ _ _ _ _ _ (Hl _) E).
- exact: (exec_down_keeps _ _ _ _ _ _ (Hl _) E).
exact: keeps_trans (keeps_set _ _ _) (assign_keeps _ _ _ _ E).
Qed.

(* The store exec_scoped builds from the parameters and the arguments. *)
Definition param_store (ps : list (dparam nat)) (args : list (val R)) : store R :=
  map (fun '(DParam _ _ x, a) => (KVar x, a)) (combine ps args).

Definition pvar (p : dparam nat) : dvar nat := let 'DParam _ _ x := p in x.

Lemma param_store_keys ps args :
  length ps = length args -> map fst (param_store ps args) = map (fun p => KVar (pvar p)) ps.
Proof.
elim: ps args => [| [pw t y] ps IH] [| a args] //= Hl.
by congr (_ :: _); apply: IH; lia.
Qed.

Lemma param_store_get ps args i pw t y a :
  length ps = length args -> NoDup (map pvar ps) -> nth_error ps i = Some (DParam pw t y) -> nth_error args i = Some a ->
  store_get (param_store ps args) (KVar y) = Some a.
Proof.
move=> Hl Hnd Hp Ha; apply: store_get_in.
  rewrite param_store_keys // -(map_map pvar (fun x => KVar x)).
  apply: (NoDup_map_inv
    (fun k0 => match k0 with KVar x => x | Returned => ResultVar end)).
  by rewrite map_map /= map_id.
rewrite /param_store; apply/in_map_iff; exists (DParam pw t y, a); split=> //.
clear Hnd; elim: ps args i Hl Ha Hp => [| q ps IH] [| b args] [| i] //= Hl.
  by move=> [->] [->]; left.
by move=> Ha Hp; right; apply: (IH args i) => //; lia.
Qed.

(* ---------------------------------------------------------------------------
   Dot products. *)

Lemma dotl_nil_l b : dotl [] b = 0.
Proof. by []. Qed.

Lemma dotl_cons a l b m : dotl (a :: l) (b :: m) = (a * b + dotl l m)%R.
Proof. by []. Qed.

Lemma dotl_app a1 a2 b1 b2 :
  length a1 = length b1 -> dotl (a1 ++ a2) (b1 ++ b2) = (dotl a1 b1 + dotl a2 b2)%R.
Proof.
elim: a1 b1 => [| a a1 IH] [| b b1] //= H.
  by rewrite dotl_nil_l Rplus_0_l.
rewrite !dotl_cons IH; [ring | lia].
Qed.

Lemma dotl_lsub a r q :
  length a = length r -> length r = length q -> dotl a (lsub r q) = (dotl a r - dotl a q)%R.
Proof.
elim: a r q => [| a l IH] [| r rs] [| q qs] //= H1 H2.
  by rewrite /dotl /lsub /=; ring.
change (lsub (r :: rs) (q :: qs)) with ((r - q)%R :: lsub rs qs).
rewrite !dotl_cons IH; [ring | lia | lia].
Qed.

Lemma dotl_repeat0 a m : dotl a (repeat 0%R m) = 0%R.
Proof.
elim: a m => [| a l IH] [| m] //=.
by rewrite dotl_cons IH; ring.
Qed.

Lemma inner_dotl t b : shaped t (Some b) -> inner t (Some b) = dotl (reals_of_val t) (reals_of_val b).
Proof. by case: t; case: b => //= *; rewrite /dotl /=; ring. Qed.

Lemma nreals_length v : nreals v = length (reals_of_val v).
Proof. by case: v. Qed.

(* The tangents of the seeded arguments, laid in one list, are the seed. *)
Lemma pair_with_tangent l B : length B = length l -> map dsnd (pair_with l B) = B.
Proof.
elim: l B => [| r l IH] [| b B] //= H.
by congr (_ :: _); apply: IH; lia.
Qed.

Lemma tangent_val_dual v B : length B = nreals v -> reals_of_val (TangentCorrect.tangent (val_dual v B)) = B.
Proof.
case: v => [r | z | bo | l | l] /= H.
- by case: B H => [| b [|]].
- by case: B H.
- by case: B H.
- exact: pair_with_tangent.
by case: B H.
Qed.

Lemma seed_tangents ds x dx :
  Forall2 fits ds x -> length dx = in_dim x ->
  seed ds x dx = concat (map (fun d => reals_of_val (TangentCorrect.tangent d)) (seed_args ds x dx)).
Proof.
rewrite /in_dim /reals_of_args => H.
elim: H dx => {ds x} [| [nm t r] v ds x Hf Hfs IH] dx //.
cbn [map concat]; rewrite length_app => Hl.
change (seed (Decl nm t r :: ds) (v :: x) dx) with
  ((if varied_role r then firstn (nreals v) dx else repeat 0%R (nreals v)) ++
   seed ds x (skipn (nreals v) dx)).
change (seed_args (Decl nm t r :: ds) (v :: x) dx) with
  (val_dual v (if varied_role r then firstn (nreals v) dx
               else repeat 0%R (nreals v)) ::
   seed_args ds x (skipn (nreals v) dx)).
cbn [map concat]; rewrite tangent_val_dual; last first.
  case: (varied_role r);
    by rewrite ?length_firstn ?repeat_length ?nreals_length; lia.
by congr (_ ++ _); apply: IH; rewrite length_skipn nreals_length; lia.
Qed.

(* ---------------------------------------------------------------------------
   The gradient against the seed. *)

Definition decl_role (d : decl) : role := let 'Decl _ _ r := d in r.

Definition slice (d : decl) (v : val R) (dx : list R) : list R :=
  if varied_role (decl_role d) then firstn (nreals v) dx else repeat 0%R (nreals v).

(* The sum the gradient computes against the seed: for each argument with an
   adjoint, the tangent times its final adjoint, minus the tangent times its
   initial adjoint (the seed of a written argument excepted). *)
Fixpoint grad_rhs (ds : list decl) (x : list (val R)) (xb dx : list R) (bars : list (val R)) : R :=
  match ds, x with
  | d :: ds', v :: x' =>
      let m := nreals v in
      if has_dot d then
        match bars with
        | b :: bars' =>
            (dotl (slice d v dx) (reals_of_val b) - (if written_decl d then 0 else dotl (slice d v dx) (firstn m xb))
             + grad_rhs ds' x' (skipn m xb) (skipn m dx) bars')%R
        | [] => 0%R
        end
      else grad_rhs ds' x' (skipn m xb) (skipn m dx) bars
  | _, _ => 0%R
  end.

(* The final adjoints have the shape of their arguments. *)
Fixpoint bars_fit (ds : list decl) (x : list (val R)) (bars : list (val R)) : Prop :=
  match ds, x with
  | d :: ds', v :: x' =>
      if has_dot d then
        match bars with
        | b :: bars' => length (reals_of_val b) = nreals v /\ bars_fit ds' x' bars'
        | [] => False
        end
      else bars_fit ds' x' bars
  | [], [] => bars = []
  | _, _ => False
  end.

Lemma gradient_dotl ds x xb dx bars :
  Forall2 fits ds x -> length xb = in_dim x -> length dx = in_dim x -> bars_fit ds x bars ->
  exists g, gradient ds x xb bars = Some g /\ length g = in_dim x /\
            dotl (seed ds x dx) g = grad_rhs ds x xb dx bars.
Proof.
rewrite /in_dim /reals_of_args => H.
elim: H xb dx bars => {ds x} [| [nm t r] v ds x Hf Hfs IH] xb dx bars
  Hxb Hdx Hb.
  by exists [].
rewrite /= length_app in Hxb Hdx.
set m := nreals v.
have Hm : m = length (reals_of_val v) by apply: nreals_length.
have Hsl : length (slice (Decl nm t r) v dx) = m.
  rewrite /slice /=; case: (varied_role r);
    by rewrite ?length_firstn ?repeat_length; lia.
change (seed (Decl nm t r :: ds) (v :: x) dx) with
  (slice (Decl nm t r) v dx ++ seed ds x (skipn m dx)).
cbn [gradient grad_rhs bars_fit] in Hb |- *.
have Hxb' : length (skipn m xb) = length (concat (map reals_of_val x)).
  by rewrite length_skipn; lia.
have Hdx' : length (skipn m dx) = length (concat (map reals_of_val x)).
  by rewrite length_skipn; lia.
case Hd: (has_dot (Decl nm t r)) Hb => Hb; last first.
  have [g [Hg [Hlg Hdg]]] := IH (skipn m xb) (skipn m dx) bars Hxb' Hdx' Hb.
  rewrite -/m Hg /=.
  exists (repeat 0%R m ++ g); split=> //.
  split; first by cbn [map concat]; rewrite !length_app repeat_length; lia.
  rewrite dotl_app; last by rewrite repeat_length; lia.
  by rewrite dotl_repeat0 Hdg; ring.
case: bars Hb => [| b bars] // [Hlb Hb].
have [g [Hg [Hlg Hdg]]] := IH (skipn m xb) (skipn m dx) bars Hxb' Hdx' Hb.
rewrite -/m Hg.
set piece := if written_decl (Decl nm t r) then reals_of_val b
             else lsub (reals_of_val b) (firstn m xb).
have Hlp : length piece = m.
  rewrite /piece; case: (written_decl (Decl nm t r)); first lia.
  by rewrite /lsub length_map length_combine length_firstn; lia.
exists (piece ++ g); split=> //.
split; first by cbn [map concat]; rewrite !length_app; lia.
rewrite dotl_app; last lia.
rewrite Hdg /piece; case: (written_decl (Decl nm t r)); first ring.
by rewrite dotl_lsub ?length_firstn; [ring | lia | lia].
Qed.

Lemma run_keeps ss s s' : run ss s = Some s' -> keeps s s'.
Proof.
rewrite /run; move: (map (Simplify.out_dstmt nat) ss) => l {ss}.
elim: l s => [| st l IH] s /=; first by case=> <-.
case E1: (exec reals st s) => [s1 |] // E.
exact: keeps_trans (exec_keeps st s s1 E1) (IH s1 E).
Qed.

(* ---------------------------------------------------------------------------
   The arguments that carry an adjoint, the owners of the pairing. *)

Definition dname (p : pv) : decl := fst (arg_entry p).

Fixpoint owners_of (Ls : list pv) : owners :=
  match Ls with
  | [] => []
  | p :: Ls' => (if has_dot (dname p) then [(TangentCorrect.tangent (pd p), stored p)] else []) ++ owners_of Ls'
  end.

(* The tangents times the initial adjoints, the seed excepted. *)
Fixpoint init_sum (Ls : list pv) (s : store R) : R :=
  match Ls with
  | [] => 0%R
  | p :: Ls' =>
      ((if has_dot (dname p) && negb (written_decl (dname p))
        then inner (TangentCorrect.tangent (pd p)) (barv s (stored p)) else 0) + init_sum Ls' s)%R
  end.

(* The adjoints of the arguments, in order, have the shape of their tangents. *)
Fixpoint bars_in (Ls : list pv) (s : store R) (bars : list (val R)) : Prop :=
  match Ls with
  | [] => bars = []
  | p :: Ls' =>
      if has_dot (dname p) then
        match bars with
        | b :: bars' => barv s (stored p) = Some b /\ shaped (TangentCorrect.tangent (pd p)) (Some b) /\ bars_in Ls' s bars'
        | [] => False
        end
      else bars_in Ls' s bars
  end.

Lemma pairing_app O1 O2 s : pairing (O1 ++ O2) s = (pairing O1 s + pairing O2 s)%R.
Proof. by elim: O1 => [| [t n] O1 IH] /=; [ring | rewrite IH; ring]. Qed.

Lemma shaped_length t b : shaped t (Some b) -> length (reals_of_val b) = length (reals_of_val t).
Proof. by case: t; case: b. Qed.


Lemma grad_rhs_pairing ds x xb yb dx Ls s0 s3 bars :
  Forall2 fits ds x -> length xb = in_dim x -> length dx = in_dim x ->
  map dname Ls = ds -> map pd Ls = seed_args ds x dx ->
  bars_in Ls s3 bars -> bars_in Ls s0 (bar_inputs ds x xb yb) ->
  grad_rhs ds x xb dx bars = (pairing (owners_of Ls) s3 - init_sum Ls s0)%R.
Proof.
rewrite /in_dim /reals_of_args => H.
elim: H xb dx Ls bars => {ds x} [| [nm t r] v ds x Hf Hfs IH] xb dx Ls bars
  Hxb Hdx Hd Hp H3 H0.
  by case: Ls Hd H3 {Hp H0} => //= _ _; ring.
case: Ls Hd Hp H3 H0 => [| p Ls] // [Hd1 Hd] Hp H3 H0.
cbn [seed_args map] in Hp; case: Hp => Hp1 Hp.
rewrite /= length_app in Hxb Hdx.
set m := nreals v in Hxb Hdx H0 *.
have Hm : m = length (reals_of_val v) by apply: nreals_length.
have Hsl : reals_of_val (TangentCorrect.tangent (pd p)) =
           slice (Decl nm t r) v dx.
  rewrite Hp1; apply: tangent_val_dual; rewrite /slice /=.
  by case: (varied_role r); rewrite ?length_firstn ?repeat_length //; lia.
have Hm' : length (slice (Decl nm t r) v dx) = m.
  rewrite /slice /=; case: (varied_role r);
    by rewrite ?length_firstn ?repeat_length; lia.
cbn [bars_in owners_of init_sum] in H3, H0 |- *; rewrite Hd1 in H3 H0 *.
change (bar_inputs (Decl nm t r :: ds) (v :: x) xb yb) with
  ((if has_dot (Decl nm t r)
    then [with_list v (if written_decl (Decl nm t r) then yb else firstn m xb)]
    else []) ++
   bar_inputs ds x (skipn m xb) yb) in H0.
have Hxb' : length (skipn m xb) = length (concat (map reals_of_val x)).
  by rewrite length_skipn; lia.
have Hdx' : length (skipn m dx) = length (concat (map reals_of_val x)).
  by rewrite length_skipn; lia.
have {}IH bs := IH (skipn m xb) (skipn m dx) Ls bs Hxb' Hdx' Hd Hp.
cbn [grad_rhs]; rewrite -/m.
case Edot: (has_dot (Decl nm t r)) H3 H0 => H3 H0; last first.
  by rewrite (IH bars H3 H0) /=; ring.
case: bars H3 => [| b bars] // [B3 [S3 H3]].
case: H0 => [B0 [S0 H0]].
rewrite (IH bars H3 H0) pairing_app; cbn [pairing fold_right].
rewrite B3 (inner_dotl _ _ S3) Hsl.
case: (written_decl (Decl nm t r)) S0 B0 => /= S0 B0; first ring.
rewrite B0 (inner_dotl _ _ S0) Hsl.
have Hw : reals_of_val (with_list v (firstn m xb)) = firstn m xb.
  rewrite Hp1 in S0; rewrite /m in S0 *; move: Hxb S0; clear.
  case: v => [rv | | | l |] //=.
    by case: xb => [| x0 xb] /=; [lia | ].
  by rewrite firstn_firstn Nat.min_id.
by rewrite Hw; ring.
Qed.

(* The final adjoints fit the arguments. *)
Lemma bars_in_fit ds x dx Ls s bars :
  Forall2 fits ds x -> map dname Ls = ds -> map pd Ls = seed_args ds x dx -> bars_in Ls s bars -> bars_fit ds x bars.
Proof.
move=> H; elim: H dx Ls bars => {ds x} [| [nm t r] v ds x Hf Hfs IH] dx Ls bars
  Hd Hp Hb.
  by case: Ls Hd Hb {Hp}.
case: Ls Hd Hp Hb => [| p Ls] // [Hd1 Hd] Hp Hb.
cbn [seed_args map] in Hp; case: Hp => Hp1 Hp.
cbn [bars_in] in Hb; rewrite Hd1 in Hb; cbn [bars_fit].
case: (has_dot (Decl nm t r)) Hb => Hb; last exact: IH _ _ _ Hd Hp Hb.
case: bars Hb => [| b bars] // [_ [Sb Hb]].
split; last exact: IH _ _ _ Hd Hp Hb.
rewrite (shaped_length _ _ Sb) Hp1; rewrite Hp1 in Sb.
case: v {Hf Hp Hp1} Sb => [rv | | | l |] //= _.
by rewrite length_map pair_with_length.
Qed.

(* ---------------------------------------------------------------------------
   The store at the start of the adjoint function: the primal arguments, the
   adjoints of the arguments that carry one, then the seed of a returned real. *)

Lemma param_store_app ps1 ps2 a1 a2 :
  length ps1 = length a1 -> param_store (ps1 ++ ps2) (a1 ++ a2) = param_store ps1 a1 ++ param_store ps2 a2.
Proof. by move=> H; rewrite /param_store combine_app // map_app. Qed.

Lemma primal_store cv Ls :
  param_store (map (out_dparam nat) (map (adjoint_primal W cv) (map arg_entry Ls))) (map (fun p => primal (pd p)) Ls) =
  prim_entries Ls.
Proof.
elim: Ls => [| p Ls IH] //=; move: IH; rewrite /param_store /= => ->.
congr (_ :: _); rewrite /arg_entry.
by case: (varg (pw p)) => [[nm r] |] //=; case: (vty (pw p)); case: r; case: cv.
Qed.

Lemma adjoint_bar_entry p :
  varg (pw p) <> None ->
  exists pw0 t0, @map (dparam W) _ (out_dparam nat) (adjoint_bar W (arg_entry p)) =
                 if has_dot (dname p) then [DParam pw0 t0 (BarOf (DBound (pn p)))] else [].
Proof.
rewrite /dname /arg_entry; case: (varg (pw p)) => [[nm r] |] // _.
case: (vty (pw p)); case: r => /=;
  first [by exists ByValue, Real | by do 2 eexists].
Qed.

Definition decl_ty (d : decl) : ty := let 'Decl _ t _ := d in t.

(* The adjoints given to the function are in the store, in order. *)
Lemma bar_store ds x xb yb dx Ls s :
  Forall2 fits ds x -> length xb = in_dim x ->
  Forall2 (fun d v => written_decl d = true -> (nreals v <= length yb)%nat) ds x ->
  Forall (fun d => has_dot d = true -> real_or_array (decl_ty d)) ds ->
  map dname Ls = ds -> map pd Ls = seed_args ds x dx -> Forall (fun p => varg (pw p) <> None) Ls ->
  (forall k v, In (k, v) (param_store (map (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls))))
                                     (bar_inputs ds x xb yb)) -> store_get s k = Some v) ->
  length (concat (map (adjoint_bar W) (map arg_entry Ls))) = length (bar_inputs ds x xb yb) /\
  bars_in Ls s (bar_inputs ds x xb yb).
Proof.
rewrite /in_dim /reals_of_args => H.
elim: H xb dx Ls => {ds x} [| [nm t r] v ds x Hf Hfs IH] xb dx Ls
  Hxb Hyb Hra Hd Hp Hg Hs.
  by case: Ls Hd {Hp Hg Hs}.
case: Ls Hd Hp Hg Hs => [| p Ls] // [Hd1 Hd] Hp Hg Hs.
cbn [seed_args map] in Hp; case: Hp => Hp1 Hp.
move/Forall2_cons_iff: Hyb => [Hy Hyb'].
move/Forall_cons_iff: Hg => [Hg1 Hg'].
move/Forall_cons_iff: Hra => [Hra1 Hra'].
rewrite /= length_app in Hxb.
set m := nreals v in Hxb Hy Hs *.
have Hm : m = length (reals_of_val v) by apply: nreals_length.
change (bar_inputs (Decl nm t r :: ds) (v :: x) xb yb) with
  ((if has_dot (Decl nm t r)
    then [with_list v (if written_decl (Decl nm t r) then yb else firstn m xb)]
    else []) ++
   bar_inputs ds x (skipn m xb) yb) in Hs |- *.
cbn [map concat] in Hs |- *.
have [pw0 [t0 Eb]] := adjoint_bar_entry p Hg1.
rewrite map_app Eb in Hs; rewrite length_app.
have Hlb : length (adjoint_bar W (arg_entry p)) =
           if has_dot (Decl nm t r) then 1%nat else 0%nat.
  rewrite -(length_map (out_dparam nat)) Eb Hd1.
  by case: (has_dot (Decl nm t r)).
rewrite Hd1 param_store_app in Hs; last by case: (has_dot _).
have Hxb' : length (skipn m xb) = length (concat (map reals_of_val x)).
  by rewrite length_skipn; lia.
have [IHl IHb] := IH (skipn m xb) (skipn m dx) Ls Hxb' Hyb' Hra' Hd Hp Hg'
  (fun k0 v0 Hin => Hs k0 v0 (in_or_app _ _ _ (or_intror Hin))).
rewrite Hlb IHl; cbn [bars_in]; rewrite Hd1.
case Edot: (has_dot (Decl nm t r)) Hs Hra1 => Hs Hra1 //.
split=> //; split; last split=> //.
  by rewrite /barv /keyv /stored /=; apply: Hs; left.
have {}Hra1 := Hra1 erefl; rewrite /= in Hra1.
rewrite /m in Hy *; rewrite Hp1; move: Hf Hy Hxb; clear -Hra1.
case: v => [rv | z | b | l | l'] /= Hf Hy Hxb //; try by case: t Hra1 Hf Hy.
rewrite length_map pair_with_length length_firstn.
case: (written_role r) Hy => Hy.
  by have := Hy erefl; lia.
by rewrite length_firstn; lia.
Qed.

Lemma map_primal_seed ds x dx : Forall2 fits ds x -> map TangentCorrect.primal (seed_args ds x dx) = x.
Proof.
move=> H; elim: H dx => {ds x} [| [nm t r] v ds x _ _ IH] dx //=.
by rewrite primal_val_dual IH.
Qed.

(* The keys of the adjoints given to the function. *)
Lemma bar_keys Ls :
  Forall (fun p => varg (pw p) <> None) Ls ->
  map pvar (@map (dparam W) _ (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls)))) =
  map (fun p => BarOf (DBound (pn p))) (filter (fun p => has_dot (dname p)) Ls).
Proof.
elim=> {Ls} [| p Ls Hg _ IH] //.
cbn [map concat]; rewrite !map_app.
have [pw0 [t0 E]] := adjoint_bar_entry p Hg; rewrite E IH /=.
by case: (has_dot (dname p)).
Qed.

(* The pairing of the owners: the initial part, and the written argument. *)
Fixpoint written_sum (Ls : list pv) (s : store R) : R :=
  match Ls with
  | [] => 0%R
  | p :: Ls' =>
      ((if has_dot (dname p) && written_decl (dname p)
        then inner (TangentCorrect.tangent (pd p)) (barv s (stored p)) else 0) + written_sum Ls' s)%R
  end.

Lemma pairing_split Ls s : pairing (owners_of Ls) s = (init_sum Ls s + written_sum Ls s)%R.
Proof.
elim: Ls => [| p Ls IH] /=; first ring.
rewrite pairing_app IH.
by case: (has_dot (dname p)); case: (written_decl (dname p)) => /=; ring.
Qed.

Lemma init_sum_ext Ls s s' :
  (forall p, In p Ls -> has_dot (dname p) = true -> written_decl (dname p) = false -> barv s' (stored p) = barv s (stored p)) ->
  init_sum Ls s' = init_sum Ls s.
Proof.
elim: Ls => [| p Ls IH] H //=.
rewrite IH; last by move=> q Hq; apply: H; right.
case E1: (has_dot (dname p)); case E2: (written_decl (dname p)) => //=.
by rewrite (H p (or_introl erefl) E1 E2).
Qed.

Lemma written_sum_none Ls s : (forall p, In p Ls -> written_decl (dname p) = false) -> written_sum Ls s = 0%R.
Proof.
elim: Ls => [| p Ls IH] H //=.
rewrite (H p (or_introl erefl)) andb_false_r IH; first ring.
by move=> q Hq; apply: H; right.
Qed.

Lemma written_sum_one Ls s w :
  NoDup Ls -> In w Ls -> has_dot (dname w) = true -> written_decl (dname w) = true ->
  (forall p, In p Ls -> written_decl (dname p) = true -> p = w) ->
  written_sum Ls s = inner (TangentCorrect.tangent (pd w)) (barv s (stored w)).
Proof.
elim: Ls => [| p Ls IH] // /NoDup_cons_iff [Hp Hnd'] /= Hw Hd Hwd H.
case: Hw => [Epw | Hw].
  subst p; have Hz : written_sum Ls s = 0%R.
    apply: written_sum_none => q Hq.
    case E: (written_decl (dname q)) => //.
    by have Eqw := H q (or_intror Hq) E; subst q.
  by rewrite Hz Hd Hwd /=; ring.
rewrite (IH Hnd' Hw Hd Hwd (fun q Hq => H q (or_intror Hq))).
case E: (has_dot (dname p) && written_decl (dname p)); last ring.
move/andb_true_iff: E => [_ E].
by have Eqw := H p (or_introl erefl) E; subst p.
Qed.

(* The final adjoints of the arguments, in order. *)
Definition bars_list (Ls : list pv) (s : store R) : list (val R) :=
  concat (map (fun p => if has_dot (dname p) then match barv s (stored p) with Some b => [b] | None => [] end else []) Ls).

Lemma bars_from_store Ls s :
  (forall p, In p Ls -> has_dot (dname p) = true ->
     exists b, barv s (stored p) = Some b /\ shaped (TangentCorrect.tangent (pd p)) (Some b)) ->
  bars_in Ls s (bars_list Ls s).
Proof.
elim: Ls => [| p Ls IH] H //.
rewrite /bars_list; cbn [map concat bars_in]; rewrite -/(bars_list Ls s).
have H' : forall q, In q Ls -> has_dot (dname q) = true ->
    exists b, barv s (stored q) = Some b /\
              shaped (TangentCorrect.tangent (pd q)) (Some b).
  by move=> q Hq; apply: H; right.
case E: (has_dot (dname p)); last exact: IH H'.
have [b [Hb Hs]] := H p (or_introl erefl) E; rewrite Hb /=.
by split=> //; split=> //; apply: IH H'.
Qed.

Lemma bar_inputs_length ds x xb yb :
  length ds = length x -> length (bar_inputs ds x xb yb) = length (filter has_dot ds).
Proof.
elim: ds x xb => [| d ds IH] [| v x] xb //= Hl.
cbn [bar_inputs filter]; rewrite length_app IH; last lia.
by case: (has_dot d).
Qed.

Lemma bar_params_length Ls :
  Forall (fun p => varg (pw p) <> None) Ls ->
  length (concat (map (adjoint_bar W) (map arg_entry Ls))) = length (filter (fun p => has_dot (dname p)) Ls).
Proof.
move=> H; rewrite -(length_map (out_dparam nat)) -(length_map pvar).
by rewrite bar_keys // length_map.
Qed.

Lemma filter_dname Ls : length (filter has_dot (map dname Ls)) = length (filter (fun p => has_dot (dname p)) Ls).
Proof.
by elim: Ls => [| p Ls IH] //=; case: (has_dot (dname p)) => /=; rewrite IH.
Qed.

(* The store at the start, laid out. *)
Lemma s0_shape cv Ls ds x xb yb eps ein :
  Forall (fun p => varg (pw p) <> None) Ls -> map dname Ls = ds -> length Ls = length x ->
  param_store (map (out_dparam nat) (map (adjoint_primal W cv) (map arg_entry Ls) ++
                                     concat (map (adjoint_bar W) (map arg_entry Ls)) ++ eps))
              (map (fun p => TangentCorrect.primal (pd p)) Ls ++ bar_inputs ds x xb yb ++ ein) =
  prim_entries Ls ++ param_store (map (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls))))
                                 (bar_inputs ds x xb yb) ++
  param_store (map (out_dparam nat) eps) ein.
Proof.
move=> Hg Hd Hl; rewrite !map_app.
rewrite param_store_app; last by rewrite !length_map.
rewrite primal_store; congr (_ ++ _).
apply: param_store_app.
rewrite length_map bar_params_length // bar_inputs_length; last first.
  by rewrite -Hd length_map.
by rewrite -Hd filter_dname.
Qed.

Lemma bar_params_inputs Ls ds x xb yb :
  Forall (fun p => varg (pw p) <> None) Ls -> map dname Ls = ds -> length Ls = length x ->
  length (@map (dparam W) _ (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls)))) =
  length (bar_inputs ds x xb yb).
Proof.
move=> Hg Hd Hl.
rewrite length_map bar_params_length // bar_inputs_length; last first.
  by rewrite -Hd length_map.
by rewrite -Hd filter_dname.
Qed.

Lemma prim_entries_bar Ls v : store_get (prim_entries Ls) (KVar (BarOf v)) = None.
Proof.
apply: store_get_notin; rewrite /prim_entries map_map.
by move=> /(in_map_iff _ _ _) [? [E _]].
Qed.

Lemma bar_entries_nodup Ls ds x xb yb :
  Forall (fun p => varg (pw p) <> None) Ls -> NoDup (map pn Ls) -> map dname Ls = ds -> length Ls = length x ->
  NoDup (map fst (param_store (map (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls))))
                              (bar_inputs ds x xb yb))).
Proof.
move=> Hg Hnd Hd Hl.
rewrite param_store_keys; last exact: bar_params_inputs.
rewrite -(map_map pvar (fun y => KVar y)) bar_keys // map_map.
apply: (NoDup_map_inv (fun k => match k with
                                | KVar (BarOf (DBound i)) => i
                                | _ => 0%nat end)).
rewrite map_map /=.
elim: Ls Hnd {Hg Hd Hl} => [| p Ls IH] /=; first by constructor.
move=> /NoDup_cons_iff [Hp Hnd'].
case: (has_dot (dname p)) => /=; last exact: IH.
constructor; last exact: IH.
move=> /(in_map_iff _ _ _) [q [E /filter_In [Hq _]]].
by apply: Hp; rewrite -E; apply: in_map.
Qed.

Lemma store_get_mid (A B E : store R) k v :
  store_get A k = None -> NoDup (map fst B) -> In (k, v) B -> store_get (A ++ B ++ E) k = Some v.
Proof.
move=> HA HB Hin.
by rewrite store_get_app HA store_get_app (store_get_in B k v HB Hin).
Qed.

(* The arguments that carry an adjoint are reals or arrays. *)
Lemma has_dot_ra ds :
  non_real_varied ds = None -> (forall d, In d ds -> written_decl d = true -> real_or_array (decl_ty d)) ->
  Forall (fun d => has_dot d = true -> real_or_array (decl_ty d)) ds.
Proof.
move=> Hn Hw; apply/Forall_forall => -[nm t r] Hin Hd.
case: r Hin Hd => Hin Hd.
- exact: (non_real_varied_none ds nm t Independent Hn Hin erefl).
- exact: (Hw _ Hin).
- exact: (non_real_varied_none ds nm t Inout Hn Hin erefl).
by case: t Hin Hd.
Qed.

Lemma bars_in_get Ls s bars p :
  bars_in Ls s bars -> In p Ls -> has_dot (dname p) = true ->
  exists b, barv s (stored p) = Some b /\ shaped (TangentCorrect.tangent (pd p)) (Some b).
Proof.
elim: Ls bars => [| q Ls IH] bars Hb // Hp Hd.
cbn [bars_in] in Hb; case: Hp => [Eqp | Hp].
  subst q; rewrite Hd in Hb.
  by case: bars Hb => [| b bars] // [B [S _]]; exists b.
case: (has_dot (dname q)) Hb => Hb; last exact: IH Hb Hp Hd.
by case: bars Hb => [| b bars] // [_ [_ Hb]]; exact: IH Hb Hp Hd.
Qed.

Lemma in_owners Ls t m :
  In (t, m) (owners_of Ls) -> exists p, In p Ls /\ has_dot (dname p) = true /\ t = TangentCorrect.tangent (pd p) /\ m = stored p.
Proof.
elim: Ls => [| p Ls IH] //= /(in_app_or _ _ _) [H | H].
  case Ed: (has_dot (dname p)) H => //= -[E | //].
  by case: E => <- <-; exists p; split; [left | ].
by have [q [Hq R]] := IH H; exists q; split; [right | ].
Qed.

Lemma owners_intro Ls p :
  In p Ls -> has_dot (dname p) = true -> In (TangentCorrect.tangent (pd p), stored p) (owners_of Ls).
Proof.
elim: Ls => [| q Ls IH] // Hp Hd /=; apply: in_or_app.
case: Hp => [Eqp | Hp]; last by right; exact: IH Hp Hd.
by subst q; left; rewrite Hd; left.
Qed.

Lemma owners_nodup Ls : NoDup (map pn Ls) -> NoDup (map snd (owners_of Ls)).
Proof.
elim: Ls => [| p Ls IH] /=; first by constructor.
move=> /NoDup_cons_iff [Hp Hnd']; rewrite map_app.
case: (has_dot (dname p)) => /=; last exact: IH.
constructor; last exact: IH.
move=> /(in_map_iff _ _ _) [[t m] [/= Em H]]; subst m.
have [q [Hq [_ [_ E]]]] := in_owners _ _ _ H.
case: E => E _; apply Hp; rewrite E; exact: in_map.
Qed.

Lemma pairing_ext O s s' : (forall t m, In (t, m) O -> barv s' m = barv s m) -> pairing O s' = pairing O s.
Proof.
elim: O => [| [t m] O IH] H //=.
rewrite (H t m (or_introl erefl)) IH // => t' m' Hi.
by apply: (H t'); right.
Qed.

Lemma store_get_in_map (s : store R) k : store_get s k <> None -> exists v, In (k, v) s.
Proof.
elim: s => [| [k0 v0] s IH] //= H.
case E: (key_eqb k0 k) H => H.
  by move/key_eqb_eq: E => E; subst k0; exists v0; left.
by have [v1 Hv] := IH H; exists v1; right.
Qed.

Lemma key_some (s : store R) k : In k (map fst s) -> store_get s k <> None.
Proof.
elim: s => [| [k0 v0] s IH] //= [E | H]; case Ek: (key_eqb k0 k) => //.
  by subst k0; rewrite key_eqb_refl in Ek.
exact: IH H.
Qed.

(* The final values of the parameters, as a map. *)
Definition final_of (s : store R) (q : dparam nat) : val R :=
  match store_get s (KVar (pvar q)) with Some w => w | None => VInt 0 end.

Lemma finals_map (s : store R) ps fs :
  length fs = length ps -> (forall i pw t x, nth_error ps i = Some (DParam pw t x) -> nth_error fs i = store_get s (KVar x)) ->
  (forall q, In q ps -> store_get s (KVar (pvar q)) <> None) -> fs = map (final_of s) ps.
Proof.
move=> Hl Hn Hs; apply: nth_error_ext => i; rewrite nth_error_map.
case E: (nth_error ps i) => [[pw t y] |] /=.
  rewrite (Hn i pw t y E) /final_of /=.
  have := Hs _ (nth_error_In _ _ E); rewrite /=.
  by case: (store_get s (KVar y)).
by apply/nth_error_None; move/nth_error_None: E; lia.
Qed.

Lemma bars_list_map Ls s :
  Forall (fun p => varg (pw p) <> None) Ls ->
  (forall p, In p Ls -> has_dot (dname p) = true -> barv s (stored p) <> None) ->
  bars_list Ls s = map (final_of s) (@map (dparam W) _ (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls)))).
Proof.
elim=> {Ls} [| p Ls Hg HL IH] H //.
rewrite /bars_list; cbn [map concat]; rewrite -/(bars_list Ls s) !map_app.
rewrite IH; last by move=> q Hq; apply: H; right.
congr (_ ++ _).
have [pw0 [t0 E]] := adjoint_bar_entry p Hg; rewrite E.
case Ed: (has_dot (dname p)) => //.
have := H p (or_introl erefl) Ed; rewrite /barv /keyv /stored /final_of /=.
by case: (store_get s (KVar (BarOf (DBound (pn p))))).
Qed.

(* Running the body of a function: the finals of the parameters. *)
Lemma finish_exec (ps : list (dparam W)) (ss : list (dstmt W)) args s0 sF r :
  length (map (out_dparam nat) ps) = length args -> param_store (map (out_dparam nat) ps) args = s0 ->
  run ss s0 = Some sF ->
  exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0 args =
  match r with
  | DReturnsReal => option_map (fun w => (map (final_of sF) (map (out_dparam nat) ps), [w])) (store_get sF Returned)
  | DVoid => Some (map (final_of sF) (map (out_dparam nat) ps), [])
  end.
Proof.
move=> Hl Hs0 Hr; cbn [exec_scoped]; rewrite Hl Nat.eqb_refl.
cbv iota beta; simpl negb; cbv iota.
change (map (fun '(DParam _ _ x, a) => (KVar x, a))
          (combine (map (out_dparam nat) ps) args)) with
  (param_store (map (out_dparam nat) ps) args).
rewrite Hs0.
change (exec_stmts reals (map (out_dstmt nat) ss) s0) with (run ss s0).
rewrite Hr.
have Hin : forall q, In q (map (out_dparam nat) ps) ->
    store_get sF (KVar (pvar q)) <> None.
  move=> q Hq; apply: (run_keeps ss s0 sF Hr); rewrite -Hs0; apply: key_some.
  by rewrite param_store_keys //; apply/in_map_iff; exists q.
have Hex : forall pw0 t0 y, In (DParam pw0 t0 y) (map (out_dparam nat) ps) ->
    exists w, store_get sF (KVar y) = Some w.
  move=> pw0 t0 y /Hin /=.
  by case: (store_get sF (KVar y)) => [w |] // _; exists w.
have [fs [Hfs [Hlfs Hnth]]] := finals_some sF (map (out_dparam nat) ps) Hex.
cbv zeta; rewrite Hfs.
rewrite (finals_map sF (map (out_dparam nat) ps) fs Hlfs Hnth Hin).
by case: r => //; case: (store_get sF Returned).
Qed.

(* The final adjoints of the arguments, read from the finals. *)
Lemma output_bars cv Ls ds eps (sF : store R) :
  Forall (fun p => varg (pw p) <> None) Ls -> map dname Ls = ds ->
  (forall p, In p Ls -> has_dot (dname p) = true -> barv sF (stored p) <> None) ->
  firstn (length (filter has_dot ds)) (skipn (length ds)
    (map (final_of sF) (@map (dparam W) _ (out_dparam nat)
       (map (adjoint_primal W cv) (map arg_entry Ls) ++ concat (map (adjoint_bar W) (map arg_entry Ls)) ++ eps)))) =
  bars_list Ls sF.
Proof.
move=> Hg Hd Hb; subst ds; rewrite !map_app.
rewrite skipn_app skipn_all2; last by rewrite !length_map.
rewrite !length_map Nat.sub_diag skipn_O app_nil_l firstn_app.
have E : length (filter has_dot (map dname Ls)) =
         length (map (final_of sF) (@map (dparam W) _ (out_dparam nat)
           (concat (map (adjoint_bar W) (map arg_entry Ls))))).
  by rewrite !length_map bar_params_length // filter_dname.
rewrite E firstn_all Nat.sub_diag firstn_O app_nil_r.
by rewrite bars_list_map.
Qed.

(* ---------------------------------------------------------------------------
   The written argument. *)

Lemma filter_none {A : Type} (P : A -> bool) l c : length (filter P l) = 0%nat -> In c l -> P c = true -> False.
Proof.
move=> H Hc Hp; case E: (filter P l) H => [| ? ?] // _.
have Hin : In c (filter P l) by apply/filter_In.
by rewrite E in Hin.
Qed.

Lemma written_unique (Ls : list pv) a b :
  NoDup Ls -> length (filter written_decl (map dname Ls)) = 1%nat -> In a Ls -> In b Ls ->
  written_decl (dname a) = true -> written_decl (dname b) = true -> a = b.
Proof.
elim: Ls => [| q Ls IH] // /NoDup_cons_iff [Hq Hnd'] /= H1 Ha Hb Wa Wb.
case Eq: (written_decl (dname q)) H1 => /= H1.
  case: H1 => H0.
  have Hr : forall c, In c Ls -> written_decl (dname c) = true -> False.
    move=> c Hc Wc.
    by apply: (filter_none written_decl (map dname Ls) (dname c) H0);
      [apply: in_map | ].
  case: Ha => [Eqa | Ha]; last by case: (Hr a Ha Wa).
  by case: Hb => [Eqb | Hb]; [subst | case: (Hr b Hb Wb)].
case: Ha => [Eqa | Ha]; first by subst; rewrite Wa in Eq.
case: Hb => [Eqb | Hb]; first by subst; rewrite Wb in Eq.
exact: IH Hnd' H1 Ha Hb Wa Wb.
Qed.

Lemma oset_app O1 O2 m t : oset (O1 ++ O2) m t = oset O1 m t ++ oset O2 m t.
Proof. exact: map_app. Qed.

(* The pairing where the written argument holds the result. *)
Lemma pairing_oset_owners Ls w tv s :
  NoDup (map pn Ls) -> In w Ls -> has_dot (dname w) = true -> written_decl (dname w) = true ->
  (forall p, In p Ls -> written_decl (dname p) = true -> p = w) ->
  pairing (oset (owners_of Ls) (stored w) tv) s = (init_sum Ls s + inner tv (barv s (stored w)))%R.
Proof.
elim: Ls => [| p Ls IH] // Hnd Hw Hd Hwd Hu.
rewrite /= in Hnd Hw; move/NoDup_cons_iff: Hnd => [Hp Hnd'].
cbn [owners_of init_sum]; rewrite oset_app pairing_app.
case: Hw => [Epw | Hw].
  subst p; rewrite Hd Hwd; cbn [negb andb].
  rewrite {1}/oset; cbn [map pairing fold_right].
  rewrite {1 2}/stored; cbn [Simplify.dvar_eq]; rewrite Nat.eqb_refl.
  rewrite oset_notin; first last.
  - move=> /(in_map_iff _ _ _) [[t m] [/= Em Hi]]; subst m.
    have [q [Hq [_ [_ E]]]] := in_owners _ _ _ Hi.
    by case: E => E _; apply Hp; rewrite E; apply: in_map.
  - by [].
  - by move=> t m /in_owners [q [_ [_ [_ ->]]]].
  rewrite pairing_split written_sum_none; first ring.
  move=> q Hq; case E: (written_decl (dname q)) => //.
  by have Eqw := Hu q (or_intror Hq) E; subst q; case: Hp; apply: in_map.
have Hpw : written_decl (dname p) = false.
  case E: (written_decl (dname p)) => //.
  by have Eqw := Hu p (or_introl erefl) E; subst p; case: Hp; apply: in_map.
rewrite (IH Hnd' Hw Hd Hwd (fun q Hq => Hu q (or_intror Hq))) Hpw.
case: (has_dot (dname p)); rewrite {1}/oset;
  cbn [map pairing fold_right negb andb]; last ring.
rewrite {1 2 3}/stored; cbn [Simplify.dvar_eq].
case E: (Nat.eqb (pn w) (pn p)).
  by move/Nat.eqb_eq: E => E; case: Hp; rewrite -E; apply: in_map.
by cbv zeta beta iota; rewrite -/(stored p); ring.
Qed.

(* The initial adjoint of the written argument is the seed. *)
Lemma bars_in_written ds x xb yb dx Ls s w :
  Forall2 fits ds x -> map dname Ls = ds -> map pd Ls = seed_args ds x dx ->
  bars_in Ls s (bar_inputs ds x xb yb) -> In w Ls -> has_dot (dname w) = true -> written_decl (dname w) = true ->
  barv s (stored w) = Some (with_list (TangentCorrect.primal (pd w)) yb).
Proof.
move=> H; elim: H xb dx Ls => {ds x} [| [nm t r] v ds x Hf Hfs IH] xb dx Ls
  Hd Hp Hb Hw Hdw Hww.
  by case: Ls Hd Hw {Hp Hb}.
case: Ls Hd Hp Hb Hw => [| p Ls] // [Hd1 Hd] Hp Hb Hw.
cbn [seed_args map] in Hp; case: Hp => Hp1 Hp.
change (bar_inputs (Decl nm t r :: ds) (v :: x) xb yb) with
  ((if has_dot (Decl nm t r)
    then [with_list v (if written_decl (Decl nm t r) then yb
                       else firstn (nreals v) xb)]
    else []) ++
   bar_inputs ds x (skipn (nreals v) xb) yb) in Hb.
cbn [bars_in] in Hb; rewrite Hd1 in Hb.
case: Hw => [Epw | Hw].
  subst p; rewrite Hd1 in Hdw Hww; rewrite Hdw Hww in Hb; case: Hb => [B _].
  by rewrite B Hp1 primal_val_dual.
case: (has_dot (Decl nm t r)) Hb => [[_ [_ Hb]] | Hb];
  exact: IH _ _ _ Hd Hp Hb Hw Hdw Hww.
Qed.

Definition ty_size (t : ty) : nat := match t with Real => 1 | Array z => Z.to_nat z | _ => 0 end.

Lemma has_type_size t v : has_type t v -> real_or_array t -> length (reals_of_val (TangentCorrect.primal v)) = ty_size t.
Proof. by case: t; case: v => //= l z H _; rewrite length_map. Qed.

Lemma fits_size nm t r v : fits (Decl nm t r) v -> real_or_array t -> nreals v = ty_size t.
Proof. by case: t; case: v. Qed.

Lemma pvar_primal cv p : pvar (out_dparam nat (adjoint_primal W cv (arg_entry p))) = DBound (pn p).
Proof.
rewrite /arg_entry; case: (varg (pw p)) => [[nm r] |] //=.
by case: (vty (pw p)); case: r; case: cv.
Qed.

Lemma forall2_map {A B C : Type} (f : A -> B) (g : A -> C) (P : B -> C -> Prop) l :
  Forall (fun a => P (f a) (g a)) l -> Forall2 P (map f l) (map g l).
Proof. by elim=> //= *; constructor. Qed.

(* The arguments of a function are inout as its declarations say. *)
Lemma has_inout_eq {V1 : Type} (G : list (V1 * unit)) (d1 : adefinition V1 bare) (d2 : adefinition unit bare) x1 :
  adefinition_eq G d1 d2 -> has_inout d1 x1 = writes_inout (declarations d2).
Proof.
elim: d1 G d2 => [n t r f IH | rr b] G [n' t' r' f2 | rr' b'] //=.
move=> [En [Et [Er H]]]; subst n' t' r'; case: r => //=.
all: exact: (IH x1 ((x1, tt) :: G)).
Qed.

Lemma annotate_cv_decls cv f :
  parametric f -> annotate_cv cv (normalize f) = (cv && negb (writes_inout (decls f)))%bool.
Proof.
move=> Hp; rewrite /annotate_cv /decls; congr (_ && negb _).
exact: (has_inout_eq [] _ _ _ (normalize_parametric f Hp avar unit)).
Qed.

(* The adjoint function, opened at the numbers simplify uses, from the
   primal arguments, their adjoints and the seed: it computes the gradient,
   the transpose of the tangent of the dual evaluation applied to the seed. *)
Theorem adjoint_simulates_duals (cv : bool) (f : function) (x : list (val R)) (xb yb dx : list R)
  (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x -> length yb = length (reals_of_val (primal v)) -> length dx = in_dim x ->
  (forall L res bP, open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] = Some (L, res, bP) ->
     asim_body (annotate_cv cv (normalize f)) bP) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out g,
    open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 = (DBody r ps ss, k) /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb = dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
move=> Hpar Hwf Hfit Hlxb Hlyb Hldx Hsim Hev.
have Ecva := annotate_cv_decls cv f Hpar.
set cva := annotate_cv cv (normalize f) in Hsim Ecva *.
set xs := seed_args (decls f) x dx in Hsim Hev *.
have Hnp := normalize_parametric f Hpar.
set dP := afdef (normalize f) pv.
have HD := Hnp pv (val (dual R)); rewrite -/dP in HD.
rewrite /aeval_function in Hev.
have [L [res [bP Ho]]] := open_P_some dP [] 0 xs _ v HD Hev.
have {}Hsim := Hsim L res bP Ho.
have [new [EL [Hlen Hargs]]] := open_P_args dP 0 xs [] L res bP Ho.
rewrite app_nil_r in EL; subst new.
have [bA [HbA Htr]] :=
  annotate_open_cv cva dP [] 0 xs L res bP _ (Hnp pv avar) Ho.
have [resW [bW [HrW [HbW Hwfd]]]] :=
  wf_open dP [] 0 xs L res bP _ (decls f) (Hnp pv vinfo) Ho.
have [bD [HbD HevD]] := eval_open dP [] 0 xs L res bP _ HD Ho.
rewrite HevD in Hev.
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
change (open_pairs
          (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0)
  with (open_pairs (open_arguments W (rebuild_definition (tvar W)
          (afdef (normalize f) (tvar W)) tr) 0
          (map arg_entry []) (adjoint_body W cv)) 0).
rewrite Hopen /adjoint_body Htr.
(* the arguments *)
have Hargs' : forall p, In p L -> exists i nm t r x0,
    p = arg_pv nm t r i x0 /\ nth_error xs i = Some x0 /\
    nth_error (decls f) i = Some (Decl nm t r) /\ (i < n)%nat.
  move=> p /(in_rev L) /(In_nth_error _ _) [i Hi].
  have [nm [t [r [x0 [Ep Hx0]]]]] := Hargs i p Hi; subst p.
  exists i, nm, t, r, x0; split=> //; split=> //; split.
    by rewrite Hds nth_error_map Hi.
  by apply/(nth_error_Some xs); rewrite Hx0.
have HnL : NoDup (map pn (rev L)).
  apply/NoDup_nth_error => i j Hi E.
  rewrite length_map in Hi.
  case Ep: (nth_error (rev L) i) => [p |]; last by move/nth_error_None: Ep; lia.
  rewrite !nth_error_map Ep /= in E.
  case Eq: (nth_error (rev L) j) E => [q |] // [E].
  have [? [? [? [? [Epa _]]]]] := Hargs i p Ep.
  have [? [? [? [? [Eqa _]]]]] := Hargs j q Eq.
  by subst p q; rewrite /= in E; lia.
have Hstat : Forall (static_ok n) L.
  apply/Forall_forall => p Hp.
  have [i [nm [t [r [x0 [Ep [Hx0 [Hd Hi]]]]]]]] := Hargs' p Hp; subst p.
  have [v0 [tg [_ [Hxs [Hf0 Hz0]]]]] :=
    seed_args_nth (decls f) x dx i nm t r Hfit Hd.
  rewrite -/xs Hx0 in Hxs; case: Hxs => Ex0; subst x0.
  repeat split; simpl; auto; try discriminate.
  - move=> Hv; apply: (non_real_varied_none (decls f) nm t r Hnrv _ Hv).
    exact: nth_error_In Hd.
  exact: fits_type nm t r v0 tg Hf0.
have Huniq : ids_unique L.
  move=> p q Hp Hq E.
  have [i [nm [t [r [x0 [Ep [Hx [Hd _]]]]]]]] := Hargs' p Hp.
  have [i' [nm' [t' [r' [x0' [Eq [Hx' [Hd' _]]]]]]]] := Hargs' q Hq.
  subst p q; rewrite /= in E; subst i'.
  rewrite Hx in Hx'; case: Hx' => Ex; subst x0'.
  by rewrite Hd in Hd'; case: Hd' => <- <- <-.
have Hnum : forall p, In p L -> (pn p < n)%nat.
  move=> p Hp; have [i [? [? [? [? [-> [_ [_ Hi]]]]]]]] := Hargs' p Hp.
  exact: Hi.
have Hxs : xs = map pd (rev L).
  apply: nth_error_ext => i.
  case Ep: (nth_error (rev L) i) => [p |].
    have [nm [t [r [x0 [Epa Hx0]]]]] := Hargs i p Ep.
    by rewrite Hx0 nth_error_map Ep Epa.
  rewrite nth_error_map Ep; apply/nth_error_None; move/nth_error_None: Ep.
  by rewrite length_rev; lia.
have HAL : Forall (fun p => tstored (pt p) = stored p /\ varg (pw p) <> None)
    (rev L).
  apply/Forall_forall => p Hp; rewrite in_rev_iff in Hp.
  by have [? [? [? [? [? [-> _]]]]]] := Hargs' p Hp; split.
have HAL' : Forall (fun p => varg (pw p) <> None) (rev L).
  by apply: Forall_impl HAL => p [_ H].
have Hpn_inj : forall p q, In p L -> In q L -> pn p = pn q -> p = q.
  move=> p q Hp Hq E.
  have [i [? [? [? [? [Ep [Hx [Hd _]]]]]]]] := Hargs' p Hp.
  have [i' [? [? [? [? [Eq [Hx' [Hd' _]]]]]]]] := Hargs' q Hq.
  subst p q; rewrite /= in E; subst i'.
  rewrite Hx in Hx'; case: Hx' => Ex; subst.
  by rewrite Hd in Hd'; case: Hd' => <- <- <-.
have Hnd : NoDup (rev L) by apply: (NoDup_map_inv pn).
have Hdn : map dname (rev L) = decls f by rewrite Hds.
have Hpd : map pd (rev L) = seed_args (decls f) x dx by rewrite -Hxs.
have Hxp : map (fun p => TangentCorrect.primal (pd p)) (rev L) = x.
  by have := map_primal_seed (decls f) x dx Hfit; rewrite -Hpd map_map.
have HLn : length (rev L) = length x by rewrite -Hxp length_map.
have Hprim : forall p, In p L -> store_get (prim_entries (rev L))
    (keyv (stored p)) = Some (TangentCorrect.primal (pd p)).
  by move=> p Hp; apply: prim_lookup => //; apply/in_rev_iff.
have HBnd := bar_entries_nodup (rev L) (decls f) x xb yb HAL' HnL Hdn HLn.
rewrite -map_rev.
have [[EW [Hnw HtcB]] | [w [nm [role [EW [Hg [Hwr [H1w [Hraw [HtcB
    [Hdep Hinout]]]]]]]]]]] := wf_result_facts _ _ _ _ Hwf.
  (* the function returns a real *)
  subst resW; destruct res as [tR | yP]; simpl in HrW;
    [subst tR | contradiction].
  destruct resT as [tT | yT]; simpl in HrT; [subst tT | contradiction].
  have Hwio : writes_inout (decls f) = false.
    case E: (writes_inout (decls f)) => //.
    move/existsb_exists: E => [[nm0 t0 r0] [Hd0 E]]; case: r0 Hd0 E => // Hd0 _.
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
  (* the store at the start *)
  set bps := concat (map (adjoint_bar W) (map arg_entry (rev L))) in HBnd *.
  set B := param_store (map (out_dparam nat) bps) (bar_inputs (decls f) x xb yb)
    in HBnd *.
  set s0 := prim_entries (rev L) ++ B ++
    [(KVar (BarOf ResultVar), VReal (hd 0%R yb))].
  set ps := map (adjoint_primal W cv) (map arg_entry (rev L)) ++ bps ++
    [DParam ByValue Real (BarOf ResultVar)].
  have Hin : adjoint_inputs (decls f) x xb yb =
      map (fun p => TangentCorrect.primal (pd p)) (rev L) ++
      bar_inputs (decls f) x xb yb ++ [VReal (hd 0%R yb)].
    by rewrite /adjoint_inputs Hnw Hxp.
  have Hs0eq : param_store (map (out_dparam nat) ps)
      (adjoint_inputs (decls f) x xb yb) = s0.
    by rewrite Hin /ps s0_shape.
  have Hkey_bar : forall k w0, In (k, w0) B ->
      exists i, k = KVar (BarOf (DBound i)).
    move=> k w0 /(in_map fst) /= Hk; rewrite /B in Hk.
    rewrite param_store_keys in Hk; last first.
      exact: (bar_params_inputs (rev L) (decls f) x xb yb HAL' Hdn HLn).
    rewrite -(map_map pvar (fun y => KVar y)) /bps bar_keys // in Hk.
    move: Hk => /(in_map_iff _ _ _) [y [<- /(in_map_iff _ _ _) [p [<- _]]]].
    by exists (pn p).
  have HB : forall k w0, In (k, w0) B -> store_get s0 k = Some w0.
    move=> k w0 Hk; have [i Ek] := Hkey_bar k w0 Hk; subst k.
    by apply: store_get_mid => //; apply: prim_entries_bar.
  have Hs0p : forall p, In p L ->
      store_get s0 (keyv (stored p)) = Some (TangentCorrect.primal (pd p)).
    by move=> p Hp; rewrite /s0 store_get_app (Hprim p Hp).
  have Hra_ds : Forall (fun d => has_dot d = true -> real_or_array (decl_ty d))
      (decls f).
    apply: has_dot_ra => // d Hd Hw.
    have : existsb written_decl (decls f) = true.
      by apply/existsb_exists; exists d.
    by rewrite Hnw.
  have Hnw' : forall p, In p (rev L) -> written_decl (dname p) = false.
    move=> p Hp; case E: (written_decl (dname p)) => //.
    have : existsb written_decl (decls f) = true.
      apply/existsb_exists; exists (dname p); split=> //.
      by rewrite -Hdn; apply: in_map.
    by rewrite Hnw.
  have Hwyb : Forall2 (fun d v0 => written_decl d = true ->
      (nreals v0 <= length yb)%nat) (decls f) x.
    have Hw0 : forall d, In d (decls f) -> written_decl d = false.
      move=> d Hd; case E: (written_decl d) => //.
      have : existsb written_decl (decls f) = true.
        by apply/existsb_exists; exists d.
      by rewrite Hnw.
    move: Hw0; clear -Hfit.
    elim: Hfit => [| d v0 ds x0 _ _ IH] Hw0; constructor.
    - by move=> Hw; rewrite (Hw0 d (or_introl erefl)) in Hw.
    by apply: IH => d' Hd'; apply: Hw0; right.
  have [_ Hbars0] := bar_store (decls f) x xb yb dx (rev L) s0 Hfit Hlxb Hwyb
    Hra_ds Hdn Hpd HAL' HB.
  (* the forward sweep *)
  have Hparg : forall p, In p L -> exists nm0 t0 r0 i0 x0,
      p = arg_pv nm0 t0 r0 i0 x0.
    move=> p Hp; have [i0 [nm0 [t0 [r0 [x0 [-> _]]]]]] := Hargs' p Hp.
    by exists nm0, t0, r0, i0, x0.
  have Hactx :
      actx L n n s0 None PTop (live_anf n bW) (tbr cv Forward n bA) Real.
    constructor.
    - by constructor; auto; try (intros; discriminate); try exact I; case.
    - by move=> p /Hparg [? [? [? [? [? ->]]]]].
    - by move=> p Hp _; exact: Hs0p.
    - by move=> p /Hparg [? [? [? [? [? ->]]]]].
    - by [].
    by [].
  have Hvo : Forward = Forward -> PTop = PTop /\ (vo = None <-> cv = false) /\
      (forall y, vo = Some (AWrites y) -> option_map (amap pt) None = Some y) /\
      (forall t, vo = Some (AReturns t) -> @None (atom pv) = None).
    move=> _; rewrite /vo; split=> //; split; first by case: (cv); split.
    by split=> //; case: (cv).
  have Hvt : Forward = Forward -> forall p, In p L -> live_anf n bW p ->
      vo_target vo <> Some (stored p).
    by move=> _ p _ _; rewrite /vo; case: (cv).
  have Hvb : Forward = Forward -> forall t, vo_target vo = Some t ->
      below n t /\ consistent t /\ is_primal t.
    by move=> _ t; rewrite /vo; case: (cv) => //= -[<-]; repeat split.
  have HS := Hsim L n n s0 None PTop Forward bA bW bT bD Real v se vo HbA HbW
    HbT HbD Hactx I HtcB Hev Hvo Hvt Hvb.
  have Hfr : Forward = Replay -> PTop <> PTop by [].
  have Hav : Forward = Forward -> cv = true -> forall o,
      owner None PTop = Some o -> avaried (pa o) = false by [].
  have := HS Hfr Hav; rewrite Hob.
  move=> -[Hcc [Hhty [s1 [R1 [F1 [T1 [V1 Hrev]]]]]]].
  clear HS.
  (* the reverse sweep *)
  set O := owners_of (rev L).
  have HinL : forall p, In p (rev L) -> In p L by move=> p /in_rev_iff.
  have Hvt0 : forall y, vo_target vo <> Some (BarOf y).
    by move=> y; rewrite /vo; case: (cv).
  have Hbars1 : forall p, In p (rev L) ->
      barv s1 (stored p) = barv s0 (stored p).
    move=> p Hp; rewrite /barv.
    apply: F1; [exact: Hnum (HinL p Hp) | by [] | by simpl; tauto | by []
               | exact: Hvt0].
  have Hs0r : store_get s0 (keyv (BarOf ResultVar)) = Some (VReal (hd 0%R yb)).
    rewrite /s0 /keyv /= store_get_app prim_entries_bar store_get_app.
    case EB: (store_get B (KVar (BarOf ResultVar))) => [w0 |]; last first.
      by cbn [store_get]; rewrite key_eqb_refl.
    have Hn : store_get B (KVar (BarOf ResultVar)) <> None by rewrite EB.
    have [w1 Hk] := store_get_in_map B _ Hn.
    by have [i E] := Hkey_bar _ _ Hk.
  have Hs1r : store_get s1 (keyv (BarOf ResultVar)) = Some (VReal (hd 0%R yb)).
    rewrite -Hs0r.
    apply: F1; [exact: I | exact: I | by simpl; tauto | by [] | exact: Hvt0].
  have Hag : agree_prim c' (inplace None PTop) s1 s1 by apply: agree_prim_refl.
  have Hr : rctx L n None PTop O (useful cv Forward n bA) s1.
    constructor.
    - exact: owners_nodup.
    - move=> t m /in_owners [p [Hp [Hd [-> ->]]]].
      rewrite (Hbars1 p Hp).
      by have [b [Eb Sb]] := bars_in_get _ _ _ p Hbars0 Hp Hd; rewrite Eb.
    - move=> t m /in_owners [p [Hp [_ [_ ->]]]]; exists (pn p).
      by split=> //; exact: Hnum (HinL p Hp).
    - move=> p Hp _ Hv; apply: owners_intro; first by apply/in_rev_iff.
      have [i0 [nm0 [t0 [r0 [x0 [Ep [_ [Hd _]]]]]]]] := Hargs' p Hp; subst p.
      rewrite /= in Hv.
      have Hra := non_real_varied_none (decls f) nm0 t0 r0 Hnrv
        (nth_error_In _ _ Hd) Hv.
      rewrite /dname /arg_entry /=.
      by destruct t0; try destruct Hra; destruct r0; rewrite /= in Hv;
        try discriminate.
    - move=> p t Hp _ /in_owners [q [Hq [_ [-> E]]]].
      case: E => E _.
      by rewrite (Hpn_inj q p (HinL q Hq) Hp (esym E)).
    - by [].
    - move=> p ny ro Hp; have [? [? [? [? [? [Ep _]]]]]] := Hargs' p Hp.
      by subst p; rewrite /= => -[_ <-].
    by [].
  have Hseed : seed_ok n Real se s1.
    split; first by move=> y [<- | []].
    by move=> _; exists (hd 0%R yb); exact: Hs1r.
  have Htp : tapes_ok L s1.
    move=> p Hp Hrp; have [? [? [? [? [? Ep]]]]] := Hparg p Hp.
    by subst p; discriminate.
  have [s3 [R3 [K3 [X3 [T3 [F3 [S3 [P3 _]]]]]]]] :=
    Hrev s1 O Hag Hr Hseed Htp (no_tail_tape_top _ _ _ _ _ _ _ _).
  destruct v as [d | | | |]; try (simpl in Hhty; contradiction).
  have P3' : pairing O s3 = (init_sum (rev L) s0 + dsnd d * hd 0%R yb)%R.
    rewrite P3 /result_pairing /seed_value; simpl inplace.
    change (xev s1 se) with (store_get s1 (keyv (BarOf ResultVar))).
    rewrite Hs1r /O pairing_split written_sum_none //.
    have -> : init_sum (rev L) s1 = init_sum (rev L) s0.
      by apply: init_sum_ext => p Hp _ _; apply: Hbars1.
    ring.
  (* the end of the function *)
  set sF := if cv then store_set s3 Returned (VReal (dfst d)) else s3.
  have Hres3 : cv = true ->
      store_get s3 (keyv ResultVar) = Some (VReal (dfst d)).
    move=> Ecv.
    have Hvr : vo_target vo = Some ResultVar by rewrite /vo Ecv.
    have Hnb : ~ is_bar (@ResultVar W) by simpl; tauto.
    by rewrite (K3 erefl ResultVar Hvr Hnb) (V1 erefl ResultVar Hvr).
  set ss := if cv then fw ++ [] ++ rv ++ [DReturn (DVar ResultVar)]
            else fw ++ [] ++ rv.
  have Hss : run ss s0 = Some sF.
    rewrite /ss /sF; case Ecv: (cv); last first.
      by rewrite run_app R1 run_app run_nil R3.
    rewrite run_app R1 run_app run_nil run_app R3 /run.
    cbn [map Simplify.out_dstmt Simplify.out_dexpr Simplify.out_dvar exec_stmts
      exec xeval].
    change (KVar ResultVar) with (keyv (@ResultVar W)).
    by rewrite (Hres3 Ecv).
  have Hb3F : forall m, barv sF m = barv s3 m.
    move=> m; rewrite /sF /barv; case: (cv) => //.
    by rewrite store_get_set_other.
  have HbF : forall p, In p (rev L) -> has_dot (dname p) = true ->
      exists b, barv sF (stored p) = Some b /\
                shaped (TangentCorrect.tangent (pd p)) (Some b).
    move=> p Hp Hd; rewrite Hb3F.
    have Sh := S3 _ _ (owners_intro _ _ Hp Hd).
    case: (barv s3 (stored p)) Sh => [b |] Sh; first by exists b.
    by move: Sh; case: (TangentCorrect.tangent (pd p)).
  have HbinF := bars_from_store (rev L) sF HbF.
  have Hfb := bars_in_fit (decls f) x dx (rev L) sF (bars_list (rev L) sF) Hfit
    Hdn Hpd HbinF.
  have [g [Hg [Hlg Hdg]]] := gradient_dotl (decls f) x xb dx
    (bars_list (rev L) sF) Hfit Hlxb Hldx Hfb.
  have Hgr := grad_rhs_pairing (decls f) x xb yb dx (rev L) s0 sF
    (bars_list (rev L) sF) Hfit Hlxb Hldx Hdn Hpd HbinF Hbars0.
  have HpF : pairing O sF = pairing O s3.
    by apply: pairing_ext => t m _; apply: Hb3F.
  have Hlen_ps : length (map (out_dparam nat) ps) =
      length (adjoint_inputs (decls f) x xb yb).
    have Hbl := bar_params_inputs (rev L) (decls f) x xb yb HAL' Hdn HLn.
    rewrite -/bps length_map in Hbl.
    by rewrite Hin /ps !map_app !length_app /= !length_map Hbl.
  have Hex := finish_exec ps ss (adjoint_inputs (decls f) x xb yb) s0 sF
    (if cv then DReturnsReal else DVoid) Hlen_ps Hs0eq Hss.
  exists (if cv then DReturnsReal else DVoid), ps, ss, c',
    (map (final_of sF) (map (out_dparam nat) ps),
     if cv then [VReal (dfst d)] else []), g.
  split; first by rewrite /ss /ps /bps; case: (cv).
  split.
    by rewrite Hex /sF; case: (cv); rewrite ?store_get_set_same.
  split.
    rewrite /adjoint_output /ps /bps; cbn beta iota; rewrite -Hg.
    congr (gradient _ _ _ _).
    apply: (output_bars cv (rev L) (decls f)
      [DParam ByValue Real (BarOf ResultVar)] sF HAL' Hdn).
    by move=> p Hp Hd; have [b [-> _]] := HbF p Hp Hd.
  split; first exact: Hlg.
  split.
    rewrite Hdg Hgr -/O HpF P3'; rewrite /= in Hlyb.
    destruct yb as [| y0 [|]]; rewrite /= in Hlyb; try discriminate.
    by rewrite /dotl /=; ring.
  by move=> Ecv _; rewrite /value_given (index_of_written_none _ _ Hnw) Ecv.
(* the function writes an argument *)
subst resW; destruct res as [tR | yP]; simpl in HrW; [contradiction |].
destruct yP as [y | | ]; simpl in HrW; try contradiction.
move/in_gW: HrW => [HyL Ew]; subst w.
destruct resT as [tT | yT]; simpl in HrT; [contradiction |].
destruct yT as [yt | | ]; simpl in HrT; try contradiction.
move/in_gT: HrT => [_ Eyt]; subst yt.
have [j [nm' [t [r [x0 [Ey [Hxj [Hdj Hj]]]]]]]] := Hargs' y HyL.
have Hvy : vty (pw y) = t by rewrite Ey.
rewrite Ey /= in Hg; case: Hg => Enm Erole; subst nm role.
have Hdecl_y : dname y = Decl nm' t r by rewrite Ey.
rewrite Hvy in Hraw HtcB.
have Hnw : existsb written_decl (decls f) = true.
  apply/existsb_exists; exists (Decl nm' t r); split=> //.
  exact: nth_error_In Hdj.
have Hywr : written_decl (dname y) = true by rewrite Hdecl_y.
have Hdy : has_dot (dname y) = true.
  by rewrite Hdecl_y; move: Hraw Hwr; case: (t); case: (r).
have HinL : forall p, In p (rev L) -> In p L by move=> p /in_rev_iff.
have HyR : In y (rev L) by apply/in_rev_iff.
have Hu : forall p, In p (rev L) -> written_decl (dname p) = true -> p = y.
  move=> p Hp Wp; apply: (written_unique (rev L) p y Hnd) => //.
  by rewrite Hdn.
have Hwio : writes_inout (decls f) =
    match r with Inout => true | _ => false end.
  have Hno : writes_inout (decls f) = true -> r = Inout.
    move/existsb_exists => [[nm0 t0 r0] [Hd0 E]].
    case: r0 Hd0 E => // Hd0 _.
    rewrite -Hdn in Hd0; move: Hd0 => /(in_map_iff _ _ _) [p [Ep Hp]].
    have Wp : written_decl (dname p) = true by rewrite Ep.
    by move: Ep; rewrite (Hu p Hp Wp) Hdecl_y => -[_ _ ->].
  case E: (writes_inout (decls f)); first by rewrite (Hno E).
  case Er: (r) => //.
  rewrite -E; apply/existsb_exists; exists (Decl nm' t Inout); split=> //.
  by rewrite -Er; exact: nth_error_In Hdj.
have Hir : inout_result W (AWrites (AVar (pt y))) =
    match r with Inout => true | _ => false end.
  by rewrite Ey; case: (r).
rewrite Hir.
move Hcvw : (cv && ~~ match r with Inout => true | _ => false end) => cvw.
have Ecvw : cva = cvw by rewrite Ecva Hwio.
clearbody cva; clear Ecva; subst cva.
set vo := (if cvw then Some (AWrites (AVar (pt y))) else None)
  : option (aresult (tvar W)).
case Eseed: (adjoint_seed W (AWrites (AVar (pt y)))) => [[extra pro] se].
have Hextra : extra = [].
  move: Eseed; rewrite /adjoint_seed Ey /=.
  by case: (t) => [| | | z]; case: (r); case=> <-.
subst extra; rewrite open_pairs_sbind.
case Hob: (open_pairs (adj W (Some (AVar (pt y))) vo Forward
  (rebuild (tvar W) bT (annotate_body_t cvw Forward n bA)) se) n)
  => [[fw rv] c'].
(* the store at the start *)
set bps := concat (map (adjoint_bar W) (map arg_entry (rev L))) in HBnd *.
set B := param_store (map (out_dparam nat) bps) (bar_inputs (decls f) x xb yb)
  in HBnd *.
set s0 := prim_entries (rev L) ++ B ++ [].
set ps := map (adjoint_primal W cv) (map arg_entry (rev L)) ++ bps ++ [].
have Hin : adjoint_inputs (decls f) x xb yb =
    map (fun p => TangentCorrect.primal (pd p)) (rev L) ++
    bar_inputs (decls f) x xb yb ++ [].
  by rewrite /adjoint_inputs Hnw Hxp.
have Hs0eq : param_store (map (out_dparam nat) ps)
    (adjoint_inputs (decls f) x xb yb) = s0.
  by rewrite Hin /ps s0_shape.
have Hkey_bar : forall k w0, In (k, w0) B ->
    exists i, k = KVar (BarOf (DBound i)).
  move=> k w0 /(in_map fst) /= Hk; rewrite /B in Hk.
  rewrite param_store_keys in Hk; last first.
    exact: (bar_params_inputs (rev L) (decls f) x xb yb HAL' Hdn HLn).
  rewrite -(map_map pvar (fun y => KVar y)) /bps bar_keys // in Hk.
  move: Hk => /(in_map_iff _ _ _) [y0 [<- /(in_map_iff _ _ _) [p [<- _]]]].
  by exists (pn p).
have HB : forall k w0, In (k, w0) B -> store_get s0 k = Some w0.
  move=> k w0 Hk; have [i Ek] := Hkey_bar k w0 Hk; subst k.
  by apply: store_get_mid => //; apply: prim_entries_bar.
have Hs0p : forall p, In p L ->
    store_get s0 (keyv (stored p)) = Some (TangentCorrect.primal (pd p)).
  by move=> p Hp; rewrite /s0 store_get_app (Hprim p Hp).
have Hra_ds : Forall (fun d => has_dot d = true -> real_or_array (decl_ty d))
    (decls f).
  apply: has_dot_ra => // d Hd Wd.
  rewrite -Hdn in Hd; move: Hd => /(in_map_iff _ _ _) [p [Ep Hp]]; subst d.
  by rewrite (Hu p Hp Wd) Hdecl_y.
(* the forward sweep *)
have Hparg : forall p, In p L -> exists nm0 t0 r0 i0 x1,
    p = arg_pv nm0 t0 r0 i0 x1.
  move=> p Hp; have [i0 [nm0 [t0 [r0 [x1 [-> _]]]]]] := Hargs' p Hp.
  by exists nm0, t0, r0, i0, x1.
have Hown_cases : owner (Some (AVar y)) PTop =
    match t with Array _ => Some y | _ => None end.
  by rewrite /= Hvy.
have Hactx : actx L n n s0 (Some (AVar y)) PTop (live_anf n bW)
    (tbr cvw Forward n bA) t.
  constructor.
  - constructor.
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
      move=> Ly; destruct r; rewrite /= in Hwr; try discriminate.
      * by move: Ly; rewrite /live_anf Hdep.
      by rewrite Ey.
  - by move=> p /Hparg [? [? [? [? [? ->]]]]].
  - by move=> p Hp _; exact: Hs0p.
  - by move=> p /Hparg [? [? [? [? [? ->]]]]].
  - move=> o Eo0 _; rewrite Hown_cases in Eo0.
    by case: (t) Eo0 => // z [Eo]; subst o; exact: Hs0p y HyL.
  move=> o Eo0 _; rewrite Hown_cases in Eo0.
  by case: (t) Eo0 => // z [Eo]; subst o; rewrite Ey.
have Hvo : Forward = Forward -> PTop = PTop /\ (vo = None <-> cvw = false) /\
    (forall y', vo = Some (AWrites y') ->
       option_map (amap pt) (Some (AVar y)) = Some y') /\
    (forall t', vo = Some (AReturns t') -> Some (AVar y) = None).
  move=> _; rewrite /vo; split=> //; split; first by case: (cvw); split.
  split; first by case: (cvw) => // y' [<-].
  by case: (cvw).
have Hvtg : vo_target vo = if cvw then match r, t with
    | Dependent, (Real | Array _) => Some (stored y)
    | _, _ => None end else None.
  by rewrite /vo; case: (cvw) => //; rewrite Ey /=; case: (r); case: (t).
have Hvt : Forward = Forward -> forall p, In p L -> live_anf n bW p ->
    vo_target vo <> Some (stored p).
  move=> _ p Hp Lp E; rewrite Hvtg in E; case: (cvw) E => // E.
  move: E; case Er: (r); case: (t) => [| | | z] //=;
    case=> Epn _; move: Lp; rewrite (Hpn_inj p y Hp HyL (esym Epn));
    by rewrite /live_anf Hdep.
have Hvb : Forward = Forward -> forall t', vo_target vo = Some t' ->
    below n t' /\ consistent t' /\ is_primal t'.
  move=> _ t' E; rewrite Hvtg in E; case: (cvw) E => // E.
  move: E; case: (r); case: (t) => [| | | z] //= [<-];
    by rewrite /stored /=; split; [exact: Hnum y HyL | ].
have Hvi : Forward = Forward -> cvw = true -> forall o,
    owner (Some (AVar y)) PTop = Some o -> avaried (pa o) = false.
  move=> _ Hcv o; rewrite Hown_cases; case: (t) => // z [<-].
  move: Hcvw Hwr; rewrite Ey Hcv; case: (r) => //=.
  by rewrite andb_false_r.
have HS := Hsim L n n s0 (Some (AVar y)) PTop Forward bA bW bT bD t v se vo
  HbA HbW HbT HbD Hactx Hraw HtcB Hev Hvo Hvt Hvb.
have Hfr : Forward = Replay -> PTop <> PTop by [].
have := HS Hfr Hvi; rewrite Hob => -[Hcc [Hhty [s1 [R1 [F1 [T1 [V1 Hrev]]]]]]].
clear HS.
(* the adjoints at the start *)
have [_ [_ [_ [_ [_ [_ [_ [_ [Hhy _]]]]]]]]] := static_in _ _ _ Hstat HyL.
rewrite Hvy in Hhy.
have Hwyb : Forall2 (fun d v0 => written_decl d = true ->
    (nreals v0 <= length yb)%nat) (decls f) x.
  rewrite -Hdn -Hxp; apply: forall2_map; apply/Forall_forall => p Hp Wp.
  rewrite (Hu p Hp Wp) nreals_length (has_type_size t (pd y) Hhy Hraw) Hlyb.
  by rewrite (has_type_size t v Hhty Hraw).
have [_ Hbars0] := bar_store (decls f) x xb yb dx (rev L) s0 Hfit Hlxb Hwyb
  Hra_ds Hdn Hpd HAL' HB.
(* the prologue *)
set OW := owners_of (rev L).
set ex := inplace (Some (AVar y)) PTop.
have Hex_bar : forall m, ex <> Some (BarOf m).
  by move=> m; rewrite /ex /inplace Hown_cases; case: (t).
have Hvt0 : forall m, vo_target vo <> Some (BarOf m).
  by move=> m; rewrite Hvtg; case: (cvw); case: (r); case: (t).
have Hbars1 : forall p, In p (rev L) ->
    barv s1 (stored p) = barv s0 (stored p).
  move=> p Hp; rewrite /barv.
  apply: F1; [exact: Hnum (HinL p Hp) | by [] | by simpl; tauto
             | exact: Hex_bar | exact: Hvt0].
have Hcase : exists s2, run pro s1 = Some s2 /\ agree_prim c' ex s1 s2 /\
    seed_ok n t se s2 /\
    (forall p, In p (rev L) -> p <> y ->
       barv s2 (stored p) = barv s1 (stored p)) /\
    (exists b, barv s2 (stored y) = Some b /\
       shaped (TangentCorrect.tangent (pd y)) (Some b)) /\
    vo_kept vo s1 s2 /\
    result_pairing OW t ex v se s2 = (init_sum (rev L) s0 +
      dotl (reals_of_val (TangentCorrect.tangent v)) yb)%R.
  have Hby1 : barv s1 (stored y) =
      Some (with_list (TangentCorrect.primal (pd y)) yb).
    rewrite (Hbars1 y HyR).
    exact: (bars_in_written (decls f) x xb yb dx (rev L) s0 y Hfit Hdn Hpd
      Hbars0 HyR Hdy Hywr).
  have [Htst [Htty Htarg]] : tstored (pt y) = stored y /\ tty (pt y) = t /\
      targ (pt y) = Some (nm', r) by rewrite Ey.
  rewrite /adjoint_seed /role_of /stored_of /tof Htty Htarg Htst in Eseed.
  have [_ [_ [_ [_ [_ [_ [_ [_ [_ Hzy]]]]]]]]] := static_in _ _ _ Hstat HyL.
  have Hav : avaried (pa y) = varied_role r by rewrite Ey.
  have Hseedv : forall s, barv s (stored y) = Some (VReal (hd 0%R yb)) ->
      xev s (DVar (BarOf (stored y))) = Some (VReal (hd 0%R yb)) by [].
  destruct t as [| | | z]; try destruct Hraw; last first.
    (* an array *)
    have Hexa : ex = Some (stored y) by rewrite /ex /inplace Hown_cases.
    case: Eseed => <- <-.
    exists s1; split=> //.
    split; first exact: agree_prim_refl.
    split; first by split=> [? [] |].
    split; first by [].
    split.
      have [b [Eb Sb]] := bars_in_get _ _ _ y Hbars0 HyR Hdy.
      by exists b; rewrite (Hbars1 y HyR).
    split; first exact: vo_kept_refl.
    rewrite /result_pairing Hexa /OW.
    rewrite (pairing_oset_owners (rev L) y _ s1 HnL HyR Hdy Hywr Hu) Hby1.
    have -> : init_sum (rev L) s1 = init_sum (rev L) s0.
      by apply: init_sum_ext => p Hp _ _; apply: Hbars1.
    congr (_ + _)%R.
    destruct v as [| | | lv |]; try (simpl in Hhty; contradiction).
    destruct (pd y) as [| | | ly |] eqn:Epd; try (simpl in Hhy; contradiction).
    rewrite /= in Hhty Hhy Hlyb *; rewrite length_map in Hlyb.
    by rewrite length_map Hhy -Hhty -Hlyb firstn_all.
  (* a real *)
  have Hexn : ex = None by rewrite /ex /inplace Hown_cases.
  destruct v as [d | | | |]; try (simpl in Hhty; contradiction).
  destruct (pd y) as [dy | | | |] eqn:Epd; try (simpl in Hhy; contradiction).
  rewrite /= in Hby1.
  have Hyb1 : dotl (reals_of_val (TangentCorrect.tangent (VReal d))) yb =
      (dsnd d * hd 0%R yb)%R.
    rewrite /= in Hlyb.
    destruct yb as [| y0 [|]]; rewrite /= in Hlyb; try discriminate.
    by rewrite /dotl /=; ring.
  destruct r; rewrite /= in Hwr; try discriminate.
    (* dependent *)
    rewrite /= in Eseed; case: Eseed => <- <-.
    exists s1; split=> //.
    split; first exact: agree_prim_refl.
    split.
      split; first by move=> y0 [<- | []]; split; [exact: Hnum y HyL |].
      by move=> _; exists (hd 0%R yb); exact: Hseedv s1 Hby1.
    split; first by [].
    split; first by exists (VReal (hd 0%R yb)).
    split; first exact: vo_kept_refl.
    rewrite /result_pairing ?Hexn /seed_value (Hseedv s1 Hby1) Hyb1.
    rewrite /OW pairing_split.
    rewrite (written_sum_one (rev L) s1 y Hnd HyR Hdy Hywr Hu) Epd Hby1.
    have -> : init_sum (rev L) s1 = init_sum (rev L) s0.
      by apply: init_sum_ext => p Hp _ _; apply: Hbars1.
    have {}Hzy := Hzy Hav; rewrite /= in Hzy.
    by rewrite /= Hzy; ring.
  (* inout *)
  rewrite /= in Eseed; case: Eseed => <- <-.
  set sa := store_set s1 (keyv (BarOf ResultVar)) (VReal (hd 0%R yb)).
  set s2 := store_set sa (keyv (BarOf (stored y))) (VReal 0%R).
  have Hky : forall p, In p (rev L) -> p <> y ->
      keyv (BarOf (stored y)) <> keyv (BarOf (stored p)).
    move=> p Hp Hne; rewrite /keyv /stored /= => -[E].
    by case: Hne; exact: Hpn_inj p y (HinL p Hp) HyL (esym E).
  exists s2; split.
    change [DDefine (DConstant Real) (BarOf ResultVar)
              (DVar (BarOf (stored y)));
            DAssign (DVar (BarOf (stored y))) (DReal "0")]
      with ([DDefine (DConstant Real) (BarOf ResultVar)
               (DVar (BarOf (stored y)))] ++
            [DAssign (DVar (BarOf (stored y))) (DReal "0")]).
    rewrite run_app (run_define s1 _ _ _ (VReal (hd 0%R yb)) (Hseedv s1 Hby1)).
    have Hx : xev sa (DReal "0") = Some (VReal 0%R) by rewrite xev_DReal lit_0.
    by rewrite -/sa (run_assign_var sa _ _ (VReal 0%R) [] Hx).
  split.
    exact: (agree_prim_set_bar c' ex s1 sa (stored y) (VReal 0%R)
      (agree_prim_set_bar c' ex s1 s1 ResultVar _ (agree_prim_refl _ _ _) I)
      erefl).
  split.
    split; first by move=> y0 [<- | []].
    move=> _; exists (hd 0%R yb).
    change (xev s2 (DVar (BarOf ResultVar))) with
      (store_get s2 (keyv (BarOf ResultVar))).
    by rewrite /s2 store_get_set_other // /sa store_get_set_same.
  split.
    move=> p Hp Hne; rewrite /barv /s2 /sa.
    rewrite (store_get_set_other _ _ _ _ (Hky p Hp Hne)).
    by rewrite store_get_set_other.
  split.
    by exists (VReal 0%R); rewrite /barv /s2 store_get_set_same.
  split; first by apply: (vo_kept_trans _ _ sa); apply: vo_kept_set_bar.
  rewrite /result_pairing ?Hexn /seed_value.
  change (xev s2 (DVar (BarOf ResultVar))) with
    (store_get s2 (keyv (BarOf ResultVar))).
  rewrite /s2 store_get_set_other // /sa store_get_set_same -/sa -/s2 Hyb1.
  rewrite /OW pairing_split (written_sum_one (rev L) s2 y Hnd HyR Hdy Hywr Hu).
  have Hb2y : barv s2 (stored y) = Some (VReal 0%R).
    by rewrite /barv /s2 store_get_set_same.
  rewrite Hb2y inner_zero.
  have -> : init_sum (rev L) s2 = init_sum (rev L) s0; last ring.
  apply: init_sum_ext => p Hp _ Wp.
  have Hne : p <> y by move=> Epy; subst p; rewrite Hywr in Wp.
  rewrite /barv /s2 /sa (store_get_set_other _ _ _ _ (Hky p Hp Hne)).
  by rewrite store_get_set_other //; exact: Hbars1.
have [s2 [R2 [Hag [Hseed [Hb2 [Hby [K2 Hres]]]]]]] := Hcase.
(* the reverse sweep *)
have Hr : rctx L n (Some (AVar y)) PTop OW (useful cvw Forward n bA) s2.
  constructor.
  - exact: owners_nodup.
  - move=> t0 m /in_owners [p [Hp [Hd [-> ->]]]].
    case: (Nat.eq_dec (pn p) (pn y)) => [Epy | Hne'].
      rewrite (Hpn_inj p y (HinL p Hp) HyL Epy).
      by have [b [Eb Sb]] := Hby; rewrite Eb.
    have Hne : p <> y by move=> Epy; subst p; case: Hne'.
    rewrite (Hb2 p Hp Hne) (Hbars1 p Hp).
    by have [b [Eb Sb]] := bars_in_get _ _ _ p Hbars0 Hp Hd; rewrite Eb.
  - move=> t0 m /in_owners [p [Hp [_ [_ ->]]]]; exists (pn p).
    by split=> //; exact: Hnum (HinL p Hp).
  - move=> p Hp _ Hv; apply: owners_intro; first by apply/in_rev_iff.
    have [i0 [nm0 [t0 [r0 [x1 [Ep [_ [Hd _]]]]]]]] := Hargs' p Hp; subst p.
    rewrite /= in Hv.
    have Hra := non_real_varied_none (decls f) nm0 t0 r0 Hnrv
      (nth_error_In _ _ Hd) Hv.
    rewrite /dname /arg_entry /=.
    by destruct t0; try destruct Hra; destruct r0; rewrite /= in Hv;
      try discriminate.
  - move=> p t0 Hp _ /in_owners [q [Hq [_ [-> E]]]].
    case: E => E _.
    by rewrite (Hpn_inj q p (HinL q Hq) Hp (esym E)).
  - move=> o E; rewrite Hown_cases in E.
    by case: (t) E => // z [<-]; exact: owners_intro _ _ HyR Hdy.
  - move=> p ny ro Hp; have [? [? [? [? [? [Ep _]]]]]] := Hargs' p Hp.
    by subst p; rewrite /= => -[_ <-].
  by move=> y' [<-]; exists nm', r; rewrite Ey.
have Htp : tapes_ok L s2.
  move=> p Hp Hrp; have [? [? [? [? [? Ep]]]]] := Hparg p Hp.
  by subst p; discriminate.
have [s3 [R3 [K3 [X3 [T3 [F3 [S3 [P3 _]]]]]]]] :=
  Hrev s2 OW Hag Hr Hseed Htp (no_tail_tape_top _ _ _ _ _ _ _ _).
rewrite -/ex Hres in P3.
(* the end of the function *)
set ss := fw ++ pro ++ rv.
have Hss : run ss s0 = Some s3 by rewrite /ss run_app R1 run_app R2.
have HbF : forall p, In p (rev L) -> has_dot (dname p) = true ->
    exists b, barv s3 (stored p) = Some b /\
              shaped (TangentCorrect.tangent (pd p)) (Some b).
  move=> p Hp Hd; have Sh := S3 _ _ (owners_intro _ _ Hp Hd).
  case: (barv s3 (stored p)) Sh => [b |] Sh; first by exists b.
  by move: Sh; case: (TangentCorrect.tangent (pd p)).
have HbinF := bars_from_store (rev L) s3 HbF.
have Hfb := bars_in_fit (decls f) x dx (rev L) s3 (bars_list (rev L) s3) Hfit
  Hdn Hpd HbinF.
have [g [Hg [Hlg Hdg]]] := gradient_dotl (decls f) x xb dx
  (bars_list (rev L) s3) Hfit Hlxb Hldx Hfb.
have Hgr := grad_rhs_pairing (decls f) x xb yb dx (rev L) s0 s3
  (bars_list (rev L) s3) Hfit Hlxb Hldx Hdn Hpd HbinF Hbars0.
have Hlen_ps : length (map (out_dparam nat) ps) =
    length (adjoint_inputs (decls f) x xb yb).
  have Hbl := bar_params_inputs (rev L) (decls f) x xb yb HAL' Hdn HLn.
  rewrite -/bps length_map in Hbl.
  by rewrite Hin /ps !map_app !length_app /= !length_map Hbl.
have Hex := finish_exec ps ss (adjoint_inputs (decls f) x xb yb) s0 s3 DVoid
  Hlen_ps Hs0eq Hss.
exists DVoid, ps, ss, c', (map (final_of s3) (map (out_dparam nat) ps), []), g.
split; first by rewrite /ss /ps /bps; case: (cv).
split; first exact: Hex.
split.
  rewrite /adjoint_output /ps /bps; cbn beta iota; rewrite -Hg.
  congr (gradient _ _ _ _).
  apply: (output_bars cv (rev L) (decls f) [] s3 HAL' Hdn).
  by move=> p Hp Hd; have [b [-> _]] := HbF p Hp Hd.
split; first exact: Hlg.
split; first by rewrite Hdg Hgr -/OW P3; ring.
(* the value in adjoint-value *)
move=> Ecv Hio.
have Er : r = Dependent.
  case Er: (r) Hwr => // _.
  by rewrite Hwio Er in Hio.
subst r.
have Ecw : cvw = true by rewrite -Hcvw Ecv.
rewrite /value_given (index_of_written_unique (decls f) j _ 0 Hdj Hwr H1w).
rewrite Nat.add_0_l Hdj !nth_error_map /ps.
have Hjl : (j < length (map (adjoint_primal W cv) (map arg_entry (rev L))))%nat.
  by rewrite !length_map length_rev; lia.
rewrite (nth_error_app1 _ _ Hjl) !nth_error_map.
have Hry : nth_error (rev L) j = Some y.
  case Eq: (nth_error (rev L) j) => [q |]; last first.
    by move/nth_error_None: Eq; rewrite length_rev; lia.
  have [nq [tq [rq [xq [Eqa Hx']]]]] := Hargs j q Eq; subst q.
  rewrite Hxj in Hx'; case: Hx' => Exq; subst xq.
  move: Hdj; rewrite Hds nth_error_map Eq /= => -[Enq Etq Erq].
  by subst nq tq rq; rewrite Ey.
rewrite Hry; cbn [option_map]; rewrite /final_of pvar_primal.
have Hvt_y : vo_target vo = Some (stored y).
  by rewrite Hvtg Ecw; case: (t) Hraw.
change (KVar (DBound (pn y))) with (keyv (stored y)).
have Hnb : ~ is_bar (stored y) by simpl; tauto.
rewrite (K3 erefl (stored y) Hvt_y Hnb) (K2 (stored y) Hvt_y Hnb).
by rewrite (V1 erefl (stored y) Hvt_y).
Qed.

(* Milestone M1: the adjoint function of a straight-line function (lets of
   operations, reads and updates of arrays) computes the gradient. *)
Corollary adjoint_straight_duals (cv : bool) (f : function) (x : list (val R)) (xb yb dx : list R)
  (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x -> length yb = length (reals_of_val (primal v)) -> length dx = in_dim x ->
  (forall L res bP, open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] = Some (L, res, bP) -> straight bP) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out g,
    open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 = (DBody r ps ss, k) /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb = dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
move=> Hp Hw Hf Hxb Hyb Hdx Hs Hev.
apply: adjoint_simulates_duals => // L res bP Ho.
exact: asim_straight (Hs L res bP Ho).
Qed.

(* Milestones M2, M3 and M4: the same with branches, maps and scalar folds
   (an assignment is in no branch; a map writes the result at the end of the
   function; a scalar fold records its state on a tape when its reverse loop
   reads it). *)
Corollary adjoint_branchy_duals (cv : bool) (f : function) (x : list (val R)) (xb yb dx : list R)
  (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x -> length yb = length (reals_of_val (primal v)) -> length dx = in_dim x ->
  (forall L res bP, open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] = Some (L, res, bP) -> branchy true bP) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out g,
    open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 = (DBody r ps ss, k) /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb = dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
move=> Hp Hw Hf Hxb Hyb Hdx Hs Hev.
apply: adjoint_simulates_duals => // L res bP Ho.
exact: (proj1 (proj1 (asim_branchy _) bP true (Hs L res bP Ho))).
Qed.

(* Milestone M5: the same with, at the top, folds updating the written array
   in place, their bodies binding scalars and ending with a set of the state
   (abody). *)
Corollary adjoint_foldy_duals (cv : bool) (f : function) (x : list (val R)) (xb yb dx : list R)
  (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x -> length yb = length (reals_of_val (primal v)) -> length dx = in_dim x ->
  (forall L res bP, open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] = Some (L, res, bP) -> foldy true bP) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out g,
    open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 = (DBody r ps ss, k) /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb = dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
move=> Hp Hw Hf Hxb Hyb Hdx Hs Hev.
apply: adjoint_simulates_duals => // L res bP Ho.
exact: (proj1 (proj1 (asim_foldy _) bP true (Hs L res bP Ho))).
Qed.

(* Milestone M5b: the same with, at the top, also nests of in-place folds:
   an in-place fold whose body ends with an inner in-place fold on its
   state (fbody). *)
Corollary adjoint_nesty_duals (cv : bool) (f : function) (x : list (val R)) (xb yb dx : list R)
  (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x -> length yb = length (reals_of_val (primal v)) -> length dx = in_dim x ->
  (forall L res bP, open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] = Some (L, res, bP) -> nesty true bP) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out g,
    open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 = (DBody r ps ss, k) /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb = dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
move=> Hp Hw Hf Hxb Hyb Hdx Hs Hev.
apply: adjoint_simulates_duals => // L res bP Ho.
exact: (proj1 (proj1 (asim_nesty _) bP true (Hs L res bP Ho))).
Qed.
