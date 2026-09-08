From Coq Require Import ZArith Reals.
From Coq Require Import Floats Psatz PrimInt63.
From Flocq Require Import Zaux Raux BinarySingleNaN PrimFloat Sterbenz Mult_error.
From dwarith Require Import dwarith.

From Interval Require Import Xreal.
From Interval Require Import Basic.
From Interval Require Import Sig.
From Interval Require Generic_proof.
From Interval Require Import Primitive_ops.

Module DwFloat <: FloatOps.

Definition radix := radix2.
Definition sensible_format := true.
Definition type := dwarith.dwfloat.

Definition toF x : float radix2 :=
  let: DWFloat xh xl := x in  
  Generic.Fadd_exact (PrimitiveFloat.toF xh) (PrimitiveFloat.toF xh).

(* What is the precision for DW ???? *)
Definition precision := Z.
Definition sfactor := Z. (* TODO: change to Int63? *)
Definition prec p := match p with Zpos q => q | _ => xH end.
Definition PtoP p := Zpos p.
Definition ZtoS (x : Z) := x.
Definition StoZ (x : Z) := x.
Definition incr_prec p i := Zplus p (Zpos i).

Definition zero := DWFloat zero zero.
Definition nan := DWFloat nan PrimitiveFloat.zero.

Definition fromZ x := DWFloat (PrimitiveFloat.fromZ x) 0.

Definition fromZ_UP (p : precision) x :=
  DWFloat (PrimitiveFloat.fromZ_UP p x) 0.

Definition fromZ_DN (p : precision) x :=
  DWFloat (PrimitiveFloat.fromZ_UP p x) 0.

Definition fromF (f : float radix) :=
  DWFloat (PrimitiveFloat.fromF f) 0.

Definition classify x :=
  let: DWFloat xh xl := x in 
  match PrimitiveFloat.classify xh with
  | Sig.Fnan => Sig.Fnan
  | Fpinfty => Fpinfty
  | Fminfty => Fminfty
  | _ => 
    match PrimitiveFloat.classify xl with
    | Sig.Fnan => Sig.Fnan
    | Fpinfty => Fpinfty
    | Fminfty => Fminfty
    | _ => Freal
    end
  end.

Definition real x :=
  let: DWFloat xh xl := x in 
  match PrimFloat.classify xh with
  | PInf | NInf | NaN => false
  | _ =>  match PrimFloat.classify xl with
          | PInf | NInf | NaN => false
          | _ => true
          end
  end.

Definition is_nan x :=
  let: DWFloat xh xl := x in 
  match PrimFloat.classify xh with
  | NaN => true
  | _ =>  match PrimFloat.classify xl with
          | NaN => true
          | _ => false
          end
  end.

Definition mag x :=
  let: DWFloat xh xl := x in PrimitiveFloat.mag xh.

Definition valid_ub x :=
  let: DWFloat xh xl := x in 
  (wellFormed x &&  
   negb (PrimFloat.eqb xh neg_infinity) && 
   negb (PrimFloat.eqb xl neg_infinity))%bool.

Definition valid_lb x := 
  let: DWFloat xh xl := x in 
  (wellFormed x &&  
   negb (PrimFloat.eqb xh infinity) && 
   negb (PrimFloat.eqb xl infinity))%bool.

Definition Xcomparison_of_float_comparison c :=
  match c with
  | FEq => Xeq
  | FLt => Xlt
  | FGt => Xgt
  | FNotComparable => Xund
  end.

Definition cmp x y := 
  let: DWFloat xh xl := x in 
  let: DWFloat yh yl := y in 
  match PrimitiveFloat.cmp xh yh with 
  | Xeq => PrimitiveFloat.cmp xl yl
  | Xlt => Xlt 
  | Xgt => Xgt
  | Xund => Xund
  end.

Definition min x y :=
  match cmp x y with
  | Xeq | Xlt => x
  | Xgt => y
  | Xund => nan
  end.

Definition max x y :=
  match cmp x y with
  | Xeq | Xgt => x
  | Xlt => y
  | Xund => nan
  end.

Definition neg x := 
  let: DWFloat xh xl := x in 
  DWFloat (- xh) (- xl). 
  
Definition abs x :=
  let: DWFloat xh xl := x in 
  DWFloat (abs xh) (abs xl).

Definition pow2_UP (p : precision) e :=
  DWFloat (PrimitiveFloat.pow2_UP p e) PrimitiveFloat.zero.

Definition div2 x :=
  let: DWFloat xh xl := x in 
  DWFloat (xh / 2)%float (xl / 2)%float.


(* HERE *)
Parameter add_UP (_ : precision) x y := next_up (x + y).

Definition add_DN (_ : precision) x y := next_down (x + y).

Definition sub_UP (_ : precision) x y := next_up (x - y).

Definition sub_DN (_ : precision) x y := next_down (x - y).

Definition mul_UP (_ : precision) x y := next_up (x * y).

Definition mul_DN (_ : precision) x y := next_down (x * y).

Definition div_UP (_ : precision) x y := next_up (x / y).

Definition div_DN (_ : precision) x y := next_down (x / y).

Definition sqrt_UP (_ : precision) x := next_up (PrimFloat.sqrt x).

Definition sqrt_DN (_ : precision) x := next_down (PrimFloat.sqrt x).

Definition nearbyint default (mode : rounding_mode) (f : type) :=
  if real f then
    let '(f', e) := frshiftexp f in
    if Int63.leb (of_Z (FloatOps.prec + FloatOps.shift))%int63 e then f else
      let m := normfr_mantissa f' in
      let d := (of_Z (FloatOps.prec + FloatOps.shift) - e)%int63 in
      let mh := (m >> d)%int63 in
      match mode with
      | rnd_ZR => if get_sign f then (- (of_int63 mh))%float else of_int63 mh
      | rnd_DN =>
        if get_sign f then
          let f'' := (- (of_int63 mh))%float in
          if PrimFloat.ltb f f'' then (- (of_int63 (mh + 1)))%float else f''
        else
          of_int63 mh
      | rnd_UP =>
        if get_sign f then
          PrimFloat.opp (of_int63 mh)
        else
          let f'' := of_int63 mh in
          if PrimFloat.ltb f'' f then of_int63 (mh + 1) else f''
      | rnd_NE =>
        let fl := of_int63 mh in
        let f' :=
            match (abs f - fl ?= 0.5)%float with
            | FLt => fl
            | FGt => of_int63 (mh + 1)
            | FEq | FNotComparable (* never happens *) =>
                if Int63.eqb (mh land 1) 0 then fl else of_int63 (mh + 1)
            end in
        if get_sign f then (- f')%float else f'
      end
  else default.

Definition nearbyint_UP := nearbyint infinity.

Definition nearbyint_DN := nearbyint neg_infinity.

Definition midpoint (x y : type) :=
  let z := ((x + y) / 2)%float in
  if is_infinity z then (x / 2 + y / 2)%float else z.

Definition toX x := FtoX (toF x).
Definition toR x := proj_val (toX x).
Definition convert x := FtoX (toF x).

Lemma ZtoS_correct:
  forall prec z,
  (z <= StoZ (ZtoS z))%Z \/ toX (pow2_UP prec (ZtoS z)) = Xnan.
Proof. now left. Qed.

Lemma zero_correct : toX zero = Xreal 0.
Proof. reflexivity. Qed.

Lemma nan_correct : classify nan = Sig.Fnan.
Proof. reflexivity. Qed.

Definition BtoX (x : binary_float FloatOps.prec emax) :=
  match x with
  | B754_zero _ => Xreal 0
  | B754_finite s m e _ => Xreal (FtoR radix2 s m e)
  | _ => Xnan
  end.

Lemma BtoX_B2R x r : BtoX x = Xreal r -> r = B2R x.
Proof.
Qed.

Lemma B2R_BtoX x r : is_finite x = true -> B2R x = r -> BtoX x = Xreal r.
Proof.
Qed.

Lemma toX_Prim2B x : toX x = BtoX (Prim2B x).
Proof. now unfold toX, toF; rewrite <-B2SF_Prim2B; case Prim2B. Qed.

Lemma BtoX_Bopp x : BtoX (Bopp x) = (- (BtoX x))%XR.
Proof.
Qed.

Lemma valid_lb_correct :
  forall f, valid_lb f = match classify f with Fpinfty => false | _ => true end.
Proof.
Qed.

Lemma valid_ub_correct :
  forall f, valid_ub f = match classify f with Fminfty => false | _ => true end.
Proof.
Qed.

Lemma classify_correct :
  forall f, real f = match classify f with Freal => true | _ => false end.
Proof. now intro f; unfold real, classify; case PrimFloat.classify. Qed.

Lemma real_correct :
  forall f, real f = match toX f with Xnan => false | _ => true end.
Proof.
Qed.

Lemma is_nan_correct :
  forall f, is_nan f = match classify f with Sig.Fnan => true | _ => false end.
Proof. now intro f; unfold is_nan, classify; case PrimFloat.classify. Qed.

Lemma real_is_finite x : real (B2Prim x) = is_finite x.
Proof.
Qed.

Local Existing Instance Hprec.
Local Existing Instance Hmax.

Lemma of_int63_exact i :
  (Int63.to_Z i <= 2^53)%Z ->
  toX (of_int63 i) = Xreal (IZR (Int63.to_Z i)).
Proof.
Qed.

Lemma of_int63_of_pos_exact p :
  (p < 2^53)%positive ->
  toX (of_int63 (Int63.of_pos p)) = Xreal (IZR (Zpos p)).
Proof.
Qed.

Lemma toX_neg x : toX (- x) = (- (toX x))%XR.
Proof.
Qed.

Lemma fromZ_correct :
  forall n,
  (Z.abs n <= 256)%Z -> toX (fromZ n) = Xreal (IZR n).
Proof.
Qed.

Lemma valid_ub_next_up x : valid_ub (next_up x) = true.
Proof.
Qed.

Lemma valid_lb_next_down x : valid_lb (next_down x) = true.
Proof.
Qed.

Lemma shiftr_pos p :
  let d := Z.log2 (Z.pos p) in
  let s := Z.shiftr (Z.pos p) (d - 52) in
  (0 <= d - 52 ->
   (s * 2 ^ (d - 52) <= Z.pos p < (s + 1) * 2 ^ (d - 52)
    /\  s < 2^53))%Z.
Proof.
Qed.

Lemma Bsign_pos x r : BtoX x = Xreal r -> (0 < r)%R -> Bsign x = false.
Proof.
Qed.

Lemma fromZ_UP_correct :
  forall p n,
  valid_ub (fromZ_UP p n) = true /\ le_upper (Xreal (IZR n)) (toX (fromZ_UP p n)).
Proof.
Qed.

Lemma fromZ_DN_correct :
  forall p n,
  valid_lb (fromZ_DN p n) = true /\ le_lower (toX (fromZ_DN p n)) (Xreal (IZR n)).
Proof.
Qed.

Lemma cmp_correct :
  forall x y,
  cmp x y =
  match classify x, classify y with
  | Sig.Fnan, _ | _, Sig.Fnan => Xund
  | Fminfty, Fminfty => Xeq
  | Fminfty, _ => Xlt
  | _, Fminfty => Xgt
  | Fpinfty, Fpinfty => Xeq
  | _, Fpinfty => Xlt
  | Fpinfty, _ => Xgt
  | Freal, Freal => Xcmp (toX x) (toX y)
  end.
Proof.
Qed.

Definition float_comparison_of_Xcomparison c :=
  match c with
  | Xeq => FEq
  | Xlt => FLt
  | Xgt => FGt
  | Xund => FNotComparable
  end.

Lemma compare_cmp x y : compare x y = float_comparison_of_Xcomparison (cmp x y).
Proof. now unfold cmp; case compare. Qed.

Lemma min_correct :
  forall x y,
  match classify x, classify y with
  | Sig.Fnan, _ | _, Sig.Fnan => classify (min x y) = Sig.Fnan
  | Fminfty, _ | _, Fminfty => classify (min x y) = Fminfty
  | Fpinfty, _ => min x y = y
  | _, Fpinfty => min x y = x
  | Freal, Freal => toX (min x y) = Xmin (toX x) (toX y)
  end.
Proof.
Qed.

(* TODO: move in Flocq.Raux *)
Lemma Rmax_compare x y :
  Rmax x y = match Rcompare x y with Lt => y | _ => x end.
Proof.
Qed.

Lemma max_correct :
  forall x y,
  match classify x, classify y with
  | Sig.Fnan, _ | _, Sig.Fnan => classify (max x y) = Sig.Fnan
  | Fpinfty, _ | _, Fpinfty => classify (max x y) = Fpinfty
  | Fminfty, _ => max x y = y
  | _, Fminfty => max x y = x
  | Freal, Freal => toX (max x y) = Xmax (toX x) (toX y)
  end.
Proof.
Qed.

Lemma neg_correct :
  forall x,
  match classify x with
  | Freal => toX (neg x) = Xneg (toX x)
  | Sig.Fnan => classify (neg x) = Sig.Fnan
  | Fminfty => classify (neg x) = Fpinfty
  | Fpinfty => classify (neg x) = Fminfty
  end.
Proof.
Qed.

Lemma abs_correct :
  forall x, toX (abs x) = Xabs (toX x) /\ (valid_ub (abs x) = true).
Proof.
Qed.

Local Existing Instance PrimFloat.Hprec.
Local Existing Instance PrimFloat.Hmax.

Lemma Bdiv2_correct x :
  is_finite x = true ->
  let x2 := Bdiv mode_NE x (Prim2B 2) in
  B2R x2 =
    Generic_fmt.round radix2
      (FLT.FLT_exp (3 - emax - FloatOps.prec) FloatOps.prec)
      (round_mode mode_NE)
      (B2R x / 2)
  /\ is_finite x2 = true
  /\ Bsign x2 = Bsign x
  /\ (Rabs (B2R x2) <= Rabs (B2R x))%R.
Proof.
Qed.

Lemma div2_correct :
  forall x, sensible_format = true ->
  (1 / 256 <= Rabs (toR x))%R ->
  toX (div2 x) = Xdiv (toX x) (Xreal 2).
Proof.
Qed.

Lemma le_upper_succ_finite s m e B :
  le_upper (@FtoX radix2 (Basic.Float s m e))
    (@FtoX radix2
       match B2SF (Bsucc (B754_finite s m e B)) with
       | S754_zero _ => Fzero
       | S754_finite s m e => Basic.Float s m e
       | _ => Basic.Fnan
       end).
Proof.
Qed.

Lemma add_UP_correct :
  forall p x y, valid_ub x = true -> valid_ub y = true
    -> (valid_ub (add_UP p x y) = true
       /\ le_upper (Xadd (toX x) (toX y)) (toX (add_UP p x y))).
Proof.
Qed.

Lemma le_lower_pred_finite s m e B :
  le_lower
    (@FtoX radix2
       match B2SF (Bpred (B754_finite s m e B)) with
       | S754_zero _ => Fzero
       | S754_finite s m e => Basic.Float s m e
       | _ => Basic.Fnan
       end)
    (@FtoX radix2 (Basic.Float s m e)).
Proof.
Qed.

Lemma add_DN_correct :
  forall p x y, valid_lb x = true -> valid_lb y = true
    -> (valid_lb (add_DN p x y) = true
       /\ le_lower (toX (add_DN p x y)) (Xadd (toX x) (toX y))).
Proof.
Qed.

Lemma sub_UP_correct :
  forall p x y, valid_ub x = true -> valid_lb y = true
    -> (valid_ub (sub_UP p x y) = true
       /\ le_upper (Xsub (toX x) (toX y)) (toX (sub_UP p x y))).
Proof.
Qed.

Lemma sub_DN_correct :
  forall p x y, valid_lb x = true -> valid_ub y = true
    -> (valid_lb (sub_DN p x y) = true
       /\ le_lower (toX (sub_DN p x y)) (Xsub (toX x) (toX y))).
Proof.
Qed.

Definition is_non_neg x :=
  valid_ub x = true
  /\ match toX x with Xnan => True | Xreal r => (0 <= r)%R end.

Definition is_pos x :=
  valid_ub x = true
  /\ match toX x with Xnan => True | Xreal r => (0 < r)%R end.

Definition is_non_pos x :=
  valid_lb x = true
  /\ match toX x with Xnan => True | Xreal r => (r <= 0)%R end.

Definition is_neg x :=
  valid_lb x = true
  /\ match toX x with Xnan => True | Xreal r => (r < 0)%R end.

Definition is_non_neg_real x :=
  match toX x with Xnan => False | Xreal r => (0 <= r)%R end.

Definition is_pos_real x :=
  match toX x with Xnan => False | Xreal r => (0 < r)%R end.

Definition is_non_pos_real x :=
  match toX x with Xnan => False | Xreal r => (r <= 0)%R end.

Definition is_neg_real x :=
  match toX x with Xnan => False | Xreal r => (r < 0)%R end.

Lemma mul_UP_correct :
  forall p x y,
    ((is_non_neg x /\ is_non_neg y)
     \/ (is_non_pos x /\ is_non_pos y)
     \/ (is_non_pos_real x /\ is_non_neg_real y)
     \/ (is_non_neg_real x /\ is_non_pos_real y))
    -> (valid_ub (mul_UP p x y) = true
        /\ le_upper (Xmul (toX x) (toX y)) (toX (mul_UP p x y))).
Proof.
Qed.

Lemma mul_DN_correct :
  forall p x y,
    ((is_non_neg_real x /\ is_non_neg_real y)
     \/ (is_non_pos_real x /\ is_non_pos_real y)
     \/ (is_non_neg x /\ is_non_pos y)
     \/ (is_non_pos x /\ is_non_neg y))
    -> (valid_lb (mul_DN p x y) = true
        /\ le_lower (toX (mul_DN p x y)) (Xmul (toX x) (toX y))).
Proof.
Qed.

Lemma pow2_UP_correct :
  forall p s, (valid_ub (pow2_UP p s) = true /\
              le_upper (Xscale radix2 (Xreal 1) (StoZ s)) (toX (pow2_UP p s))).
Proof.
Qed.

Lemma div_UP_correct :
  forall p x y,
    ((is_non_neg x /\ is_pos_real y)
     \/ (is_non_pos x /\ is_neg_real y)
     \/ (is_non_neg_real x /\ is_neg_real y)
     \/ (is_non_pos_real x /\ is_pos_real y))
    -> (valid_ub (div_UP p x y) = true
        /\ le_upper (Xdiv (toX x) (toX y)) (toX (div_UP p x y))).
Proof.
Qed.

Lemma div_DN_correct :
  forall p x y,
    ((is_non_neg x /\ is_neg_real y)
     \/ (is_non_pos x /\ is_pos_real y)
     \/ (is_non_neg_real x /\ is_pos_real y)
     \/ (is_non_pos_real x /\ is_neg_real y))
    -> (valid_lb (div_DN p x y) = true
        /\ le_lower (toX (div_DN p x y)) (Xdiv (toX x) (toX y))).
Proof.
Qed.

Lemma sqrt_UP_correct :
  forall p x,
  valid_ub (sqrt_UP p x) = true
  /\ le_upper (Xsqrt (toX x)) (toX (sqrt_UP p x)).
Proof.
Qed.

Lemma sqrt_DN_correct :
  forall p x,
    valid_lb x = true
    -> (valid_lb (sqrt_DN p x) = true
        /\ le_lower (toX (sqrt_DN p x)) (Xsqrt (toX x))).
Proof.
Qed.

(* TODO: use the one from Flocq when we'll require Flocq >= 3.3.2
   (which will imply Coq >= 8.12) *)
Lemma Bnormfr_mantissa_correct :
  forall f : binary_float FloatOps.prec emax,
  (/ 2 <= Rabs (B2R f) < 1)%R ->
  match f with
  | B754_finite _ m e _ =>
    Bnormfr_mantissa f = N.pos m
    /\ Z.pos (digits2_pos m) = FloatOps.prec /\ (e = - FloatOps.prec)%Z
  | _ => False
  end.
Proof.
Qed.

Lemma nearbyint_correct :
  forall default mode x,
  real x = true ->
  Xnearbyint mode (toX x) = toX (nearbyint default mode x).
Proof.
Qed.

Lemma nearbyint_UP_correct :
  forall mode x,
  valid_ub (nearbyint_UP mode x) = true
  /\ le_upper (Xnearbyint mode (toX x)) (toX (nearbyint_UP mode x)).
Proof.
Qed.

Lemma nearbyint_DN_correct :
  forall mode x,
  valid_lb (nearbyint_DN mode x) = true
  /\ le_lower (toX (nearbyint_DN mode x)) (Xnearbyint mode (toX x)).
Proof.
Qed.

Lemma midpoint_correct :
  forall x y,
  sensible_format = true ->
  real x = true -> real y = true -> (toR x <= toR y)%R
  -> real (midpoint x y) = true /\ (toR x <= toR (midpoint x y) <= toR y)%R.
Proof.
Qed.

End PrimitiveFloat.
