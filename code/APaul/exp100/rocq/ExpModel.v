(** * exp100.c as a function on integers

    The contract between the pure part of the proof (the real x from its
    bits, the error bound, the decision) and the program proofs (VST,
    Capla).  [core_Z], [exp_encl_Z] and [maybe_hard_Z] compute on [Z]
    what [exp_core], [exp_encl_bits] and [maybe_hard_bits] of ../exp100.c
    compute, step by step: the same floors, the same two corrections of
    the guess of n, the same run-time checks and the same return codes.
    A number is one integer, not a list of limbs; the constants are
    [valZ] of the lists of ExpTable.v, computed once.

    The functions compute with shifts and masks, which [vm_compute]
    evaluates several times faster than divisions by powers of 2; each
    helper has a lemma ([...E]) giving it as a division or a modulo.

    Nothing wraps here.  The C agrees because none of its steps overflows
    a word or a number of 192 bits: X < 2^170, the guess of n is below
    2^17, n + 1 <= 2^17, the Horner values are below 2^161 and y below
    2^162.  These bounds are for the program proofs to show.

    [model_test/] checks the two against each other on test inputs. *)

From Stdlib Require Import Bool ZArith Lia List.
From Exp100 Require Import ExpTable ExpConsts.
Import ListNotations.

Open Scope Z_scope.

(** ** Parameters, as in exp100.h and exp100.c *)

Definition D : Z := 16.          (* EXP100_D, the error bound in units of 2^s *)
Definition m_hard : Z := 42.     (* M_HARD: hard means within 2^-42 *)
Definition emin : Z := -1022.    (* EMIN, the smallest normal exponent *)
Definition prec : Z := 53.       (* PREC, the bits of a double *)
Definition inv_shift : Z := 25.  (* INV is 64/ln2 2^25 *)
Definition K : Z := 6.           (* TAB = 2^K *)
Definition N_bias : Z := 2 ^ 17. (* N + 2^17 is unsigned in the C *)
Definition hN_bias : Z := N_bias / TAB.  (* 2048, so that hN = h *)
Definition num_bits : Z := limb_bits * Z.of_nat NL.  (* 192 *)
Definition f_min : Z := 64.      (* the range of f the filter accepts *)
Definition f_max : Z := num_bits - 8.

(** The return codes of [exp_core]. *)
Definition rc_big : Z := 1.      (* |x| >= 1024, infinity, NaN *)
Definition rc_reduce : Z := 2.   (* the check q(n) <= X < q(n+1) fails *)
Definition rc_rmax : Z := 3.     (* the check r < RMAX fails *)

(** ** Shifts and masks *)

(** The k last bits of p, read off its binary digits. *)
Fixpoint pos_low (p : positive) (k : nat) {struct k} : Z :=
  match k with
  | O => 0
  | S k' =>
      match p with
      | xH => 1
      | xO p' => Z.double (pos_low p' k')
      | xI p' => Z.succ_double (pos_low p' k')
      end
  end.

Lemma pos_lowE p n : pos_low p n = Zpos p mod 2 ^ Z.of_nat n.
Proof.
revert p; induction n as [|n IH]; intros p; [cbn; symmetry; apply Z.mod_1_r|].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
assert (H2 : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
destruct p as [p|p|]; cbn [pos_low];
  rewrite ?Z.double_spec, ?Z.succ_double_spec, ?IH.
- rewrite Pos2Z.inj_xI.
  apply Z.mod_unique with (q := Zpos p / 2 ^ Z.of_nat n); [left|].
  + pose proof (Z.mod_pos_bound (Zpos p) _ H2); lia.
  + pose proof (Z.div_mod (Zpos p) _ (Z.neq_sym _ _ (Z.lt_neq _ _ H2))); lia.
- rewrite (Pos2Z.inj_xO p), Z.mul_mod_distr_l; lia.
- symmetry; apply Z.mod_small; lia.
Qed.

(** floor(a / 2^k), a mod 2^k and 2^k, for 0 <= k. *)
Definition low (a k : Z) : Z :=
  match a with Zpos p => pos_low p (Z.to_nat k) | _ => a mod 2 ^ k end.
Definition shr (a k : Z) : Z := Z.shiftr a k.
Definition pow2 (k : Z) : Z := Z.shiftl 1 k.

Lemma shrE a k : 0 <= k -> shr a k = a / 2 ^ k.
Proof. exact (Z.shiftr_div_pow2 a k). Qed.

Lemma lowE a k : 0 <= k -> low a k = a mod 2 ^ k.
Proof.
intros Hk; destruct a as [|p|p]; try reflexivity.
unfold low; rewrite pos_lowE, Z2Nat.id; auto.
Qed.

Lemma pow2E k : 0 <= k -> pow2 k = 2 ^ k.
Proof. intros Hk; unfold pow2; rewrite Z.shiftl_1_l; reflexivity. Qed.

(** ** The constants, as integers *)

Definition LN2v : Z := Eval vm_compute in valZ LN2.
Definition RMAXv : Z := Eval vm_compute in valZ RMAX.
Definition Cs : list Z := Eval vm_compute in map valZ C.
Definition Ts : list Z := Eval vm_compute in map valZ T.

Lemma LN2vE : LN2v = valZ LN2.
Proof. vm_compute; reflexivity. Qed.

Lemma RMAXvE : RMAXv = valZ RMAX.
Proof. vm_compute; reflexivity. Qed.

(** C_i and T_j. *)
Definition Cv (i : nat) : Z := nth i Cs 0.
Definition Tv (j : Z) : Z := nth (Z.to_nat j) Ts 0.

Lemma CvE i : Cv i = valZ (nth i C []).
Proof.
unfold Cv; replace Cs with (map valZ C) by (vm_compute; reflexivity).
exact (map_nth valZ C [] i).
Qed.

Lemma TvE j : Tv j = valZ (nth (Z.to_nat j) T []).
Proof.
unfold Tv; replace Ts with (map valZ T) by (vm_compute; reflexivity).
exact (map_nth valZ T [] (Z.to_nat j)).
Qed.

(** ** The bits of a double *)

Definition sign_bit : Z := 63.
Definition mant_bits : Z := 52.
Definition expo_bits : Z := 11.
Definition expo_shift : Z := 1075.  (* |x| = m 2^(be - 1075) *)
Definition be_big : Z := 1033.      (* be >= 1033: |x| >= 1024 *)

(** The sign, the biased exponent and the stored mantissa of [xb]. *)
Definition xsign (xb : Z) : Z := shr xb sign_bit.
Definition xbexp (xb : Z) : Z := low (shr xb mant_bits) expo_bits.
Definition xmant0 (xb : Z) : Z := low xb mant_bits.

Lemma xsignE xb : xsign xb = xb / 2 ^ sign_bit.
Proof. apply shrE; discriminate. Qed.

Lemma xbexpE xb : xbexp xb = (xb / 2 ^ mant_bits) mod 2 ^ expo_bits.
Proof. unfold xbexp; rewrite lowE, shrE; [reflexivity|discriminate..]. Qed.

Lemma xmant0E xb : xmant0 xb = xb mod 2 ^ mant_bits.
Proof. apply lowE; discriminate. Qed.

(** The exponent and the mantissa with the implicit bit: a subnormal x
    has exponent 1 and no implicit bit. *)
Definition xexpo (xb : Z) : Z := if xbexp xb =? 0 then 1 else xbexp xb.
Definition xmant (xb : Z) : Z :=
  if xbexp xb =? 0 then xmant0 xb else xmant0 xb + pow2 mant_bits.

(** [num_scale]: floor(v 2^e). *)
Definition scale (v e : Z) : Z :=
  if 0 <=? e then Z.shiftl v e else shr v (- e).

Lemma scaleE v e :
  scale v e = if 0 <=? e then v * 2 ^ e else v / 2 ^ (- e).
Proof.
unfold scale; destruct (Z.leb_spec 0 e) as [He|He].
- apply Z.shiftl_mul_pow2, He.
- apply shrE; lia.
Qed.

(** X = floor(|x| 2^P). *)
Definition xfix (xb : Z) : Z := scale (xmant xb) (xexpo xb - expo_shift + P).

(** ** The reduction *)

(** [mul_ln2]: q(n) = floor(n LN2 / 2^32). *)
Definition q (n : Z) : Z := shr (n * LN2v) limb_bits.

Lemma qE n : q n = n * valZ LN2 / 2 ^ limb_bits.
Proof. unfold q; rewrite LN2vE; apply shrE; discriminate. Qed.

(** [guess_n]: floor(X INV / 2^(P + 25)). *)
Definition guess (X : Z) : Z := shr (X * INV) (P + inv_shift).

Lemma guessE X : guess X = X * INV / 2 ^ (P + inv_shift).
Proof. apply shrE; discriminate. Qed.

(** The guess, lowered once if too big, raised once if too small, then
    checked: [Some n] with q(n) <= X < q(n+1), or [None]. *)
Definition reduce (X : Z) : option Z :=
  let g := guess X in
  let n1 := if (X <? q g) && (0 <? g) then g - 1 else g in
  let n := if X <? q (n1 + 1) then n1 else n1 + 1 in
  if (X <? q n) || negb (X <? q (n + 1)) then None else Some n.

(** r and N + 2^17: for x >= 0, N = n and r = X - q(n); for x < 0,
    N = -(n+1) and r = q(n+1) - X. *)
Definition rarg (xb n : Z) : Z :=
  if xsign xb =? 0 then xfix xb - q n else q (n + 1) - xfix xb.

Definition Nu (xb n : Z) : Z :=
  if xsign xb =? 0 then N_bias + n else N_bias - (n + 1).

(** j = N mod 64 and hN = floor(N / 64) - 2048. *)
Definition jidx (N : Z) : Z := low N K.
Definition hidx (N : Z) : Z := shr N K - hN_bias.

Lemma jidxE N : jidx N = N mod TAB.
Proof. apply lowE; discriminate. Qed.

Lemma hidxE N : hidx N = N / TAB - hN_bias.
Proof. unfold hidx; rewrite shrE; [reflexivity|discriminate]. Qed.

(** ** Horner's rule and the table *)

(** [num_mulshr]: floor(a b / 2^P). *)
Definition mulshr (a b : Z) : Z := shr (a * b) P.

Lemma mulshrE a b : mulshr a b = a * b / 2 ^ P.
Proof. apply shrE; discriminate. Qed.

(** The loop of [exp_core], from h = H_k down to H_0, with
    H_i = floor(H_(i+1) r / 2^P) + C_i. *)
Fixpoint horner_from (r h : Z) (k : nat) : Z :=
  match k with
  | O => h
  | S i => horner_from r (mulshr h r + Cv i) i
  end.

(** H_0, from H_DEG = C_DEG. *)
Definition horner (r : Z) : Z := horner_from r (Cv DEG) DEG.

(** ** The core, the enclosure and the filter *)

(** [exp_core]: [inl rc] on failure, else [inr (y, hN)] with
    y = floor(T_j H_0 / 2^P), j = N mod 64, hN = floor(N / 64) - 2048. *)
Definition core_Z (xb : Z) : Z + (Z * Z) :=
  if be_big <=? xbexp xb then inl rc_big else
  match reduce (xfix xb) with
  | None => inl rc_reduce
  | Some n =>
      let r := rarg xb n in
      if negb (r <? RMAXv) then inl rc_rmax else
      let N := Nu xb n in
      inr (mulshr (Tv (jidx N)) (horner r), hidx N)
  end.

(** [exp_encl_bits]: [inl rc] on failure, else [inr (M, s)] with
    |exp x - M 2^s| <= D 2^s (to be proved). *)
Definition exp_encl_Z (xb : Z) : Z + (Z * Z) :=
  match core_Z xb with
  | inl rc => inl rc
  | inr (y, hN) => inr (y, hN - P)
  end.

(** The return code of [exp_encl_bits], and its outputs when it is 0. *)
Definition exp_rc_Z (xb : Z) : Z :=
  match exp_encl_Z xb with inl rc => rc | inr _ => 0 end.

Definition exp_core_Z (xb : Z) : option (Z * Z) :=
  match exp_encl_Z xb with inl _ => None | inr ms => Some ms end.

(** [num_bitlen]: 0 for 0, else b with 2^(b-1) <= v < 2^b. *)
Definition bitlen (v : Z) : Z := if v <=? 0 then 0 else Z.log2 v + 1.

(** The decision of [maybe_hard_bits] on y and hN, once [exp_core] has
    returned 0: 0 only when every value of [y - D, y + D] has the bit
    length of y and, with e = s + bitlen y - 1 and
    f = max(e, emin) - prec - s, f is in [f_min, f_max] and y is at
    distance more than 2^(f-42) + D from the multiples of 2^f. *)
Definition decide_Z (y hN : Z) : Z :=
  let s := hN - P in
  let b := bitlen y in
  if negb ((bitlen (y - D) =? b) && (bitlen (y + D) =? b)) then 1 else
  let e := s + b - 1 in
  let f := Z.max e emin - prec - s in
  if (f <? f_min) || (f_max <? f) then 1 else
  let lo := low y f in
  let hi := pow2 f - lo in
  let d := if lo <? hi then lo else hi in
  if pow2 (f - m_hard) + D <? d then 0 else 1.

(** [maybe_hard_bits]. *)
Definition maybe_hard_Z (xb : Z) : Z :=
  match core_Z xb with
  | inl _ => 1
  | inr (y, hN) => decide_Z y hN
  end.

(** ** The relation, for the program proofs and the error bound *)

Definition core_rel (xb y hN : Z) : Prop := core_Z xb = inr (y, hN).

(** What [core_rel] says, step by step. *)
Lemma core_relP xb y hN : core_rel xb y hN ->
  exists n,
    xbexp xb < be_big /\ q n <= xfix xb < q (n + 1) /\
    rarg xb n < valZ RMAX /\
    y = mulshr (Tv (Nu xb n mod TAB)) (horner (rarg xb n)) /\
    hN = Nu xb n / TAB - hN_bias.
Proof.
unfold core_rel, core_Z.
destruct (Z.leb_spec be_big (xbexp xb)) as [_|Hbe]; [discriminate|].
unfold reduce; set (X := xfix xb); set (g := guess X).
set (n1 := if (X <? q g) && (0 <? g) then g - 1 else g).
set (n := if X <? q (n1 + 1) then n1 else n1 + 1).
destruct (Z.ltb_spec X (q n)) as [|Hlo]; [discriminate|].
destruct (Z.ltb_spec X (q (n + 1))) as [Hhi|]; [|discriminate].
cbn [orb negb].
destruct (Z.ltb_spec (rarg xb n) RMAXv) as [Hr|]; [|discriminate].
(* injection would put the tables in head normal form: project instead *)
cbn [negb]; intros Heq.
apply (f_equal (fun s : Z + Z * Z =>
  match s with inl _ => (0, 0) | inr p => p end)) in Heq.
cbv beta iota in Heq; apply pair_equal_spec in Heq; destruct Heq as [<- <-].
exists n; rewrite <- jidxE, <- hidxE, <- RMAXvE; repeat split; auto.
Qed.

(** And the other way: the enclosure and the decision read [core_Z]. *)
Lemma exp_core_ZE xb M s :
  exp_core_Z xb = Some (M, s) <-> core_rel xb M (s + P).
Proof.
unfold exp_core_Z, exp_encl_Z, core_rel.
destruct (core_Z xb) as [rc|[y hN]]; split; try discriminate.
- intros Heq; injection Heq as <- <-; do 2 f_equal; lia.
- intros Heq; injection Heq as -> ->; do 2 f_equal; lia.
Qed.

Lemma maybe_hard_ZE xb :
  maybe_hard_Z xb = 0 ->
  exists y hN, core_rel xb y hN /\ decide_Z y hN = 0.
Proof.
unfold maybe_hard_Z, core_rel.
destruct (core_Z xb) as [rc|[y hN]]; [discriminate|].
intros H; exists y, hN; split; [reflexivity|exact H].
Qed.
