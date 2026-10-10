(* AdjointNesty.v — the adjoint simulation of the bodies with branches,
   maps, scalar folds, in-place folds and nests of in-place folds (nesty).

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint Simplify Scoping
  AnfEquiv Correctness TangentCorrect TangentLoops TangentGood AdjointCorrect AdjointBranch
  AdjointFold AdjointFoldy AdjointNBody.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Section Nesty.
Variable cv : bool.

(* As foldy, with also, at the top, a fold updating its array in place
   whose steps are the bodies of in-place loops of any depth (nbody). *)
Fixpoint nesty (top : bool) (b : anf pv bare) : Prop :=
  match b with
  | ALet _ e b' => nesty_value top e /\ forall x, nesty top (b' x)
  | ARet _ => True
  end
with nesty_value (top : bool) (e : value pv bare) : Prop :=
  match e with
  | AOp1 _ _ | AOp2 _ _ _ | AGet _ _ => True
  | ASet _ _ _ => top = true
  | AIte _ t e => nesty false t /\ nesty false e
  | AMap _ _ b => top = true /\ forall x, nesty false (b x)
  | AFold _ _ _ init b =>
      top = true /\
      ((forall p, init = AVar p -> ~ is_array (vty (pw p))) /\
         (forall x y, nesty false (b x y)) \/
       (exists q, init = AVar q /\ is_array (vty (pw q))) /\
         (forall x y, nbody y (b x y)))
  end.

Theorem asim_nesty :
  (forall b : anf pv bare, forall top, nesty top b ->
     asim_body cv b /\ act_body b /\ (top = false -> psim_body cv b)) /\
  (forall e : value pv bare, forall top, nesty_value top e ->
     asim_fwd cv e /\ asim_rev cv e /\ inplace_only cv e /\ act_value e /\
     act_owner e /\ (top = false -> forall wP tail, storage wP tail e = None)).
Proof.
apply: (anf_value_ind pv bare
  (fun b => forall top, nesty top b ->
     asim_body cv b /\ act_body b /\ (top = false -> psim_body cv b))
  (fun e => forall top, nesty_value top e ->
     asim_fwd cv e /\ asim_rev cv e /\ inplace_only cv e /\ act_value e /\
     act_owner e /\ (top = false -> forall wP tail, storage wP tail e = None))).
- move=> a e IHe b IHb top [He Hb].
  have [Hf [Hr [Hi [Ha [Ho Hst]]]]] := IHe top He.
  split.
    by apply: asim_let; auto => x; exact: (proj1 (IHb x top (Hb x))).
  split.
    by apply: act_let; auto => x; exact: (proj1 (proj2 (IHb x top (Hb x)))).
  move=> Et; apply: psim_let; [exact: Hf | exact: Ha | exact: (Hst Et) | |].
    by move=> a0 i0 y0 E; subst e; rewrite /= in He; congruence.
  by move=> x; exact: (proj2 (proj2 (IHb x top (Hb x))) Et).
- move=> x top _; split; first exact: asim_ret.
  by split; [exact: act_ret | move=> _; exact: psim_ret].
- move=> f x top _; split; first exact: afwd_op1.
  split.
    apply: asim_rev_bars; first exact: arev_op1.
      by apply: straight_rev_bars.
    by apply: straight_no_top.
    by [].
  split; first by apply: inplace_straight.
  by split; [exact: act_op1 | split; [exact: owner_op1 |]].
- move=> f x y top _; split; first exact: afwd_op2.
  split.
    apply: asim_rev_bars; first exact: arev_op2.
      by apply: straight_rev_bars.
    by apply: straight_no_top.
    by [].
  split; first by apply: inplace_straight.
  by split; [exact: act_op2 | split; [exact: owner_op2 |]].
- move=> x i top _; split; first exact: afwd_get.
  split.
    apply: asim_rev_bars; first exact: arev_get.
      by apply: straight_rev_bars.
    by apply: straight_no_top.
    by [].
  split; first by apply: inplace_straight.
  by split; [exact: act_get | split; [exact: owner_get |]].
- move=> x i y top /= Et; subst top; split; first exact: afwd_set.
  split.
    apply: asim_rev_bars; first exact: arev_set.
      by apply: straight_rev_bars.
    by apply: straight_no_top.
    by [].
  split; first by apply: inplace_straight.
  by split; [exact: act_set | split; [exact: owner_set |]].
- move=> c t IHt e IHe top [Ht He].
  have [At [Ct Pt]] := IHt false Ht; have [Ae [Ce Pe]] := IHe false He.
  split; first by apply: afwd_ite; auto.
  split; first by apply: arev_ite; auto.
  split; first exact: inplace_ite.
  by split; [apply: act_ite; auto | split; [exact: owner_ite |]].
- move=> lo hi b IHb top [Et Hb]; subst top.
  have Hpb : forall x, psim_body cv (b x).
    by move=> x; exact: (proj2 (proj2 (IHb x false (Hb x))) erefl).
  split; first exact: afwd_map.
  split; first by apply: arev_map => x; exact: (proj1 (IHb x false (Hb x))).
  split; first exact: inplace_map.
  have Ham : act_value (AMap lo hi b).
    by apply: act_map => x; exact: (proj1 (proj2 (IHb x false (Hb x)))).
  by split=> //; split=> //; apply: owner_map.
move=> a lo hi init b IHb top [Et [[Hna Hb] | [Hq Hnb]]]; subst top.
(* a scalar fold *)
  have Hpb : forall x y, psim_body cv (b x y).
    by move=> x y; exact: (proj2 (proj2 (IHb x y false (Hb x y))) erefl).
  have Hacb : forall x y, act_body (b x y).
    by move=> x y; exact: (proj1 (proj2 (IHb x y false (Hb x y)))).
  have Hsb : forall x y, asim_body cv (b x y).
    by move=> x y; exact: (proj1 (IHb x y false (Hb x y))).
  split; first exact: afwd_fold.
  split; first exact: arev_fold.
  split; first exact: inplace_fold.
  split; first exact: act_fold.
  by split; [exact: owner_fold |].
(* a fold updating its array in place, possibly nested *)
have Hact : forall x y, act_body (b x y).
  by move=> x y; exact: nbody_act (Hnb x y).
have Hsb : forall x y, asim_body cv (b x y).
  by move=> x y; exact: nbody_asim (Hnb x y).
split; first exact: afwd_fold_nbody.
split; first exact: arev_fold_nbody.
split; first exact: inplace_fold_gen.
split; first exact: act_fold_gen.
by split; [exact: owner_fold_gen |].
Qed.

End Nesty.
