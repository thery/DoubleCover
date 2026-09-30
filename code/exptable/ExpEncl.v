(** * The enclosure of exp given by Interval *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Interval Require Import Xreal Basic Specific_bigint Specific_ops.
From ExpTable Require Import ExpCheck.

Open Scope R_scope.

(* A positive float with a radix-2 exponent is p 2^e. *)
Lemma FtoR_pos p e : FtoR radix2 false p e = IZR (Z.pos p) * bp e.
Proof.
unfold bp; destruct e as [|q|q]; cbv beta iota zeta delta [FtoR bpow].
- lra.
- rewrite mult_IZR; reflexivity.
- reflexivity.
Qed.

(* The value of a float read by getF. *)
Lemma getF_val f p e : getF f = Some (p, e) ->
  SFBI2.toX f = Xreal (IZR (Z.pos p) * bp e).
Proof.
unfold getF, SFBI2.toX.
destruct (SFBI2.toF f) as [| |[|] p' e']; try discriminate.
intros H; injection H; intros <- <-; simpl FtoX; rewrite <- FtoR_pos.
reflexivity.
Qed.

Lemma encl_ok N mL fL mU fU : encl N = Some (mL, fL, mU, fU) ->
  (0 < mL)%Z /\ (0 < mU)%Z /\
  IZR mL * bp fL <= exp (IZR N * u) <= IZR mU * bp fU.
Proof.
unfold encl.
destruct (SFBI2.valid_lb (xpt N)) eqn:VL; [|discriminate].
destruct (SFBI2.valid_ub (xpt N)) eqn:VU; [|discriminate].
destruct (getF (xpt N)) as [[p e]|] eqn:GX; [|discriminate].
destruct (Z.eqb_spec (Z.pos p) N) as [HN|]; [|discriminate].
destruct (Z.eqb_spec e uexp) as [He|]; [|discriminate].
simpl andb; cbv iota.
(* The point interval contains N u. *)
assert (Hc : Interval.contains
  (I.convert (Float.Ibnd (xpt N) (xpt N))) (Xreal (IZR N * u))).
{ unfold I.convert; change I.F.valid_lb with SFBI2.valid_lb.
  change I.F.valid_ub with SFBI2.valid_ub; rewrite VL, VU.
  change I.F.toX with SFBI2.toX; rewrite (getF_val _ _ _ GX), HN, He.
  unfold u; simpl; lra. }
generalize (I.exp_correct prec _ _ Hc).
destruct (I.exp prec (Float.Ibnd (xpt N) (xpt N))) as [|lo up];
  [discriminate|].
unfold I.convert.
change I.F.valid_lb with SFBI2.valid_lb.
change I.F.valid_ub with SFBI2.valid_ub.
change (SFBI2.valid_lb lo) with true; rewrite Bool.andb_true_l.
destruct (SFBI2.valid_ub up); [|intros _ H; discriminate H].
destruct (getF lo) as [[pL fL']|] eqn:GL; [|intros _ H; discriminate H].
destruct (getF up) as [[pU fU']|] eqn:GU; [|intros _ H; discriminate H].
change I.F.toX with SFBI2.toX.
rewrite (getF_val _ _ _ GL), (getF_val _ _ _ GU).
intros [H1 H2] H; injection H; intros <- <- <- <-.
split; [lia|split; [lia|]].
split; assumption.
Qed.
