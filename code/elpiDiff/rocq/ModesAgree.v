(* ModesAgree.v — the reverse mode agrees with the tangent mode: for the same
   function and arguments, the tangent program and the adjoint program that
   elpiDiff generates are adjoint to each other.

   The two mode theorems (TangentMode.v, AdjointMode.v) each give a Fréchet
   derivative of f at x; the derivative is unique, so they speak of the same
   linear map.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Normalize WellFormed Annotate Adjoint Tangent Simplify Correctness Smooth.
From ElpiDiff Require TangentTop.
From ElpiDiff Require Import Euclidean DualsDerive AdjointSpec TangentMode
  AdjointMode.
From Coquelicot Require Import Coquelicot.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

(* ---------------------------------------------------------------------------
   The Fréchet derivative is unique. *)

(* A linear map that is small at x, in o(y - x), is zero. *)
Lemma linear_small_zero {U V : NormedModule R_AbsRing} (l : U -> V) (x : U) :
  is_linear l ->
  is_domin (locally x) (fun y => minus y x) (fun y => l (minus y x)) ->
  forall h, l h = zero.
Proof.
move=> Hl Hd h.
apply: norm_eq_zero.
apply: Rle_antisym; last exact: norm_ge_0.
apply: le_epsilon => eps Heps.
case: (Req_dec (norm h) 0) => [Eh | Nh].
  have -> : h = zero by apply: norm_eq_zero.
  by rewrite (linear_zero l Hl) norm_zero; lra.
have Hnh : 0 < norm h by have := norm_ge_0 h; lra.
(* the direction h, at a distance t small enough *)
have [d Hdd] := Hd (mkposreal _ (Rdiv_lt_0_compat _ _ Heps Hnh)).
set t := d / (2 * norm h).
have Ht : 0 < t by apply: Rdiv_lt_0_compat; [exact: cond_pos | lra].
have Ey : minus (plus x (scal t h)) x = scal t h.
  by rewrite /minus plus_comm plus_assoc plus_opp_l plus_zero_l.
have Hb : ball x d (plus x (scal t h)).
  apply: norm_compat1; rewrite Ey.
  apply: (Rle_lt_trans _ _ _ (norm_scal t h)).
  rewrite /abs /= Rabs_pos_eq; last lra.
  rewrite /t; field_simplify; last lra.
  by have := cond_pos d; lra.
have := Hdd _ Hb; rewrite Ey (linear_scal l Hl t h) /= => Hs.
(* |t| |l h| <= |l (t h)| <= eps / |h| * |t h| <= eps |t| *)
have Hlow : t * norm (l h) <= norm (scal t (l h)).
  have E : l h = scal (/ t) (scal t (l h)).
    by rewrite scal_assoc /mult /= Rinv_l ?scal_one //; lra.
  have := norm_scal (/ t) (scal t (l h)); rewrite -E /abs /=.
  rewrite Rabs_pos_eq; last by apply/Rlt_le/Rinv_0_lt_compat.
  move=> H; apply: (Rmult_le_reg_l (/ t)); first exact: Rinv_0_lt_compat.
  by rewrite -Rmult_assoc Rinv_l ?Rmult_1_l; lra.
have Hup : norm (scal t h) <= t * norm h.
  by have := norm_scal t h; rewrite /abs /= Rabs_pos_eq //; lra.
have : t * norm (l h) <= t * eps.
  apply: (Rle_trans _ _ _ Hlow); apply: (Rle_trans _ _ _ Hs) => /=.
  apply: (Rle_trans _ (eps / norm h * (t * norm h))).
    by apply: Rmult_le_compat_l => //; apply/Rlt_le/Rdiv_lt_0_compat.
  by field_simplify; lra.
by move=> H; have := Rmult_le_reg_l _ _ _ Ht H; lra.
Qed.

(* Two derivatives of f at x are the same linear map. *)
Lemma filterdiff_locally_unique {U V : NormedModule R_AbsRing} (f : U -> V)
  (x : U) (l1 l2 : U -> V) :
  filterdiff f (locally x) l1 -> filterdiff f (locally x) l2 ->
  forall h, l1 h = l2 h.
Proof.
move=> H1 H2 h.
have [Hl Hd] := filterdiff_minus_fct _ _ _ _ H1 H2.
have E : minus (l1 h) (l2 h) = zero.
  apply: (linear_small_zero _ x Hl) => eps.
  apply: filter_imp (Hd x (fun P HP => HP) eps) => y.
  by rewrite !minus_eq_zero /minus plus_zero_l norm_opp.
by apply: (plus_reg_r (opp (l2 h))); rewrite plus_opp_r.
Qed.

(* ---------------------------------------------------------------------------
   The two modes agree. *)

(* The code elpiDiff generates: the tangent program, and the adjoint program
   (giving the value of f back when cv). *)
Definition tangent_code (f : function) : dfunction :=
  simplify (tangent (annotate false (normalize f))).

Definition adjoint_code (cv : bool) (f : function) : dfunction :=
  simplify (adjoint cv (annotate cv (normalize f))).

(* Corollary of tangent_mode_correct and adjoint_mode_correct: the two
   generated programs are adjoint to each other. Let f be a parametric,
   well-formed function, defined at the arguments x. Run the simplified
   tangent program on x and a tangent dx: it gives a tangent output w. Run
   the simplified adjoint program on x, initial adjoints xb and a seed yb: it
   gives a gradient g. Then <w, yb> = <seed dx, g>, where seed masks the
   arguments that carry no derivative on entry. *)
Corollary adjoint_tangent_agree (cv : bool) (f : function)
  (x : list (val R)) :
  parametric f -> well_formed (normalize f) = Ok ->
  Forall2 fits (decls f) x -> defined f x ->
  forall dx xb yb,
    length dx = in_dim x -> length xb = in_dim x -> length yb = out_dim f x ->
  exists tout v w aout g,
    exec_dfunction reals (tangent_code f) (tangent_inputs (decls f) x dx) =
      Some tout /\
    tangent_output (decls f) tout = Some (v, w) /\
    exec_dfunction reals (adjoint_code cv f)
      (adjoint_inputs (decls f) x xb yb) = Some aout /\
    adjoint_output (decls f) x xb aout = Some g /\
    ⟨reals_of_val w, yb⟩ = ⟨seed (decls f) x dx, g⟩.
Proof.
move=> Hpar Hwf Hfit Hdef dx xb yb Hdx Hxb Hyb.
have [v [df [_ [Hd Htan]]]] := tangent_mode_correct f x Hpar Hwf Hfit Hdef.
have [v' [df' [_ [Hd' Hadj]]]] :=
  adjoint_mode_correct cv f x Hpar Hwf Hfit Hdef.
have [tout [w [Ht [Hto Hw]]]] := Htan dx Hdx.
have [aout [g [Ha [Hao [_ [_ Hdot]]]]]] := Hadj xb yb Hxb Hyb.
exists tout, v, w, aout, g; split=> //; split=> //; split=> //; split=> //.
rewrite Hw -(Hdot dx Hdx).
by rewrite (filterdiff_locally_unique _ _ _ _ Hd Hd').
Qed.
