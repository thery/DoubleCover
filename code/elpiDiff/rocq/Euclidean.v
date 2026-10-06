(* Euclidean.v — the spaces R^n, as normed modules of Coquelicot, for stating
   that a program is differentiable (DualsDerive.v).

   Coquelicot provides the reals and the products of normed modules, but no
   R^n: we build it as R × (R × (… × unit)), from a zero space on unit,
   with the norms of the products (Euclidean up to a constant factor). A
   vector converts to and from the list of its coordinates; a coordinate is
   a linear map; and a function into R^m is differentiable when each of its m
   components is (`filterdiff_vec`). *)

From Coquelicot Require Import Coquelicot.
From Stdlib Require Import Reals List Lia Lra.
Import ListNotations.
Open Scope R_scope.

(* --- the zero space, on unit ------------------------------------------------ *)
Definition unit_AbelianMonoid_mixin : AbelianMonoid.mixin_of unit :=
  AbelianMonoid.Mixin unit (fun _ _ => tt) tt
    (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun x => match x with tt => eq_refl end).
Canonical unit_AbelianMonoid := AbelianMonoid.Pack unit unit_AbelianMonoid_mixin unit.
Definition unit_AbelianGroup_mixin : AbelianGroup.mixin_of unit_AbelianMonoid :=
  AbelianGroup.Mixin unit_AbelianMonoid (fun _ => tt) (fun _ => eq_refl).
Canonical unit_AbelianGroup :=
  AbelianGroup.Pack unit (AbelianGroup.Class _ unit_AbelianMonoid_mixin unit_AbelianGroup_mixin) unit.
Definition unit_ModuleSpace_mixin : ModuleSpace.mixin_of R_AbsRing unit_AbelianGroup :=
  ModuleSpace.Mixin R_AbsRing unit_AbelianGroup (fun _ _ => tt)
    (fun _ _ _ => eq_refl) (fun x => match x with tt => eq_refl end) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl).
Canonical unit_ModuleSpace :=
  ModuleSpace.Pack R_AbsRing unit (ModuleSpace.Class _ _ (AbelianGroup.class unit_AbelianGroup) unit_ModuleSpace_mixin) unit.
Definition unit_UniformSpace_mixin : UniformSpace.mixin_of unit :=
  UniformSpace.Mixin unit tt (fun _ _ _ => True) (fun _ _ => I) (fun _ _ _ _ => I) (fun _ _ _ _ _ _ _ => I).
Canonical unit_UniformSpace := UniformSpace.Pack unit unit_UniformSpace_mixin unit.
Canonical unit_NormedModuleAux :=
  NormedModuleAux.Pack R_AbsRing unit
    (NormedModuleAux.Class R_AbsRing unit (ModuleSpace.class _ unit_ModuleSpace) unit_UniformSpace_mixin) unit.
Lemma unit_NormedModule_mixin : NormedModule.mixin_of R_AbsRing unit_NormedModuleAux.
Proof.
  apply (NormedModule.Mixin R_AbsRing unit_NormedModuleAux (fun _ => 0) 1).
  - intros; simpl; lra.
  - intros; simpl. rewrite Rmult_0_r; apply Rle_refl.
  - intros; exact I.
  - intros x y eps _; simpl; rewrite Rmult_1_l; apply cond_pos.
  - intros [] _; reflexivity.
Qed.
Canonical unit_NormedModule :=
  NormedModule.Pack R_AbsRing unit (NormedModule.Class R_AbsRing unit _ unit_NormedModule_mixin) unit.

(* --- R^n -------------------------------------------------------------------- *)

(* R^n: R × R^(n-1), ending with the zero space. *)
Fixpoint Rn (n : nat) : NormedModule R_AbsRing :=
  match n with
  | O => unit_NormedModule
  | S n => prod_NormedModule R_AbsRing R_NormedModule (Rn n)
  end.

(* The vector of the first n reals of a list, padded with zeros. *)
Fixpoint vec_of_list (n : nat) (l : list R) : Rn n :=
  match n return Rn n with
  | O => tt
  | S n => match l with
           | [] => (0, vec_of_list n [])
           | a :: l => (a, vec_of_list n l)
           end
  end.

(* The coordinates of a vector, in order. *)
Fixpoint list_of_vec (n : nat) : Rn n -> list R :=
  match n return Rn n -> list R with
  | O => fun _ => []
  | S n => fun v : R * Rn n => fst v :: list_of_vec n (snd v)
  end.

Lemma list_of_vec_length n (v : Rn n) : length (list_of_vec n v) = n.
Proof. induction n as [| n IH]; simpl; [reflexivity | now rewrite IH]. Qed.

Lemma list_of_vec_of_list n l : length l = n -> list_of_vec n (vec_of_list n l) = l.
Proof.
  revert l; induction n as [| n IH]; intros [| a l] H; simpl in *; try discriminate; auto.
  now rewrite IH by lia.
Qed.

(* The j-th coordinate of a vector, a linear map. *)
Definition coord (n j : nat) (v : Rn n) : R := nth j (list_of_vec n v) 0.

Lemma coord_linear n j : is_linear (coord n j).
Proof.
  revert j; induction n as [| n IH]; intros j.
  - unfold coord; simpl; destruct j;
      exact (@is_linear_zero _ (Rn 0) R_NormedModule).
  - destruct j as [| j]; unfold coord; simpl.
    + apply is_linear_fst.
    + apply (is_linear_comp (fun t : R * Rn n => snd t) (coord n j)); [apply is_linear_snd | apply IH].
Qed.

Section Componentwise.
Context {E : NormedModule R_AbsRing}.

(* A function into R^m, given by m real functions, is differentiable where
   each of them is, with the vector of their derivatives as derivative. *)
Lemma filterdiff_vec (e0 : E) (ps : list ((E -> R) * (E -> R))%type) :
  List.Forall (fun p => filterdiff (fst p) (locally e0) (snd p)) ps ->
  filterdiff (fun y => vec_of_list (length ps) (map (fun p => fst p y) ps)) (locally e0)
             (fun h => vec_of_list (length ps) (map (fun p => snd p h) ps)).
Proof.
  induction 1 as [| p ps Hp Hps IH]; simpl.
  - apply (filterdiff_ext_lin _ (fun _ => zero)); [apply filterdiff_const | now intros].
  - apply (filterdiff_comp'_2 (fst p) _ (fun (a : R) (v : Rn (length ps)) => (a, v)) e0 (snd p) _
             (fun (a : R) (v : Rn (length ps)) => (a, v))); auto.
    apply filterdiff_linear, is_linear_prod; [apply is_linear_fst | apply is_linear_snd].
Qed.
(* The same, into R^m for any m equal to the number of functions. *)
Lemma filterdiff_vec_length (e0 : E) m (ps : list ((E -> R) * (E -> R))%type) :
  length ps = m -> List.Forall (fun p => filterdiff (fst p) (locally e0) (snd p)) ps ->
  filterdiff (fun y => vec_of_list m (map (fun p => fst p y) ps)) (locally e0)
             (fun h => vec_of_list m (map (fun p => snd p h) ps)).
Proof. intros <-; apply filterdiff_vec. Qed.

End Componentwise.
