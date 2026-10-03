(** * The statements of the 16 functions of exp100.c

    A number is [num sh a p] with [Zlength a = NL] and [Forall limb a];
    its value is [valZ a].  Inputs take a readable share, outputs a
    writable one, and they are separate SEP items: no call of exp100.c
    passes the same array twice.  The three top functions are stated with
    the integer model of ExpModel.v: [core_Z], [exp_encl_Z] and
    [maybe_hard_Z]; the helpers with its [mulshr], [bitlen], [pow2],
    [low], [scale], [q] and [guess]. *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common.
Require Exp100.ExpTable Exp100.ExpConsts Exp100.ExpModel.

(** ** Bounds the statements need *)

(** Bits of a number. *)
Definition num_bits : Z := limb_bits * NL.

(** Bits of the mantissa of a double, with the implicit bit. *)
Definition mant_bits : Z := 53.

(** [num_scale] writes cell e / 32 + 2: e < 128. *)
Definition scale_emax : Z := 128.

(** ** Numbers *)

(* a = 0 *)
Definition num_zero_spec : ident * funspec :=
 DECLARE _num_zero
 WITH sh : share, p : val
 PRE [ tptr tulong ]
   PROP (writable_share sh) PARAMS (p)
   SEP (data_at_ sh (tarray tulong NL) p)
 POST [ tvoid ]
   PROP () RETURN ()
   SEP (num sh (Zrepeat 0 NL) p).

(* a = b *)
Definition num_copy_spec : ident * funspec :=
 DECLARE _num_copy
 WITH sha : share, shb : share, pa : val, pb : val, b : list Z
 PRE [ tptr tulong, tptr tulong ]
   PROP (writable_share sha; readable_share shb; Zlength b = NL)
   PARAMS (pa; pb)
   SEP (data_at_ sha (tarray tulong NL) pa; num shb b pb)
 POST [ tvoid ]
   PROP () RETURN ()
   SEP (num sha b pa; num shb b pb).

(* a = a + b, when the sum fits *)
Definition num_add_spec : ident * funspec :=
 DECLARE _num_add
 WITH sha : share, shb : share, pa : val, pb : val, a : list Z, b : list Z
 PRE [ tptr tulong, tptr tulong ]
   PROP (writable_share sha; readable_share shb;
         Zlength a = NL; Zlength b = NL; Forall limb a; Forall limb b;
         (valZ a + valZ b < 2 ^ num_bits)%Z)
   PARAMS (pa; pb)
   SEP (num sha a pa; num shb b pb)
 POST [ tvoid ]
   EX a' : list Z,
   PROP (Zlength a' = NL; Forall limb a'; (valZ a' = valZ a + valZ b)%Z)
   RETURN ()
   SEP (num sha a' pa; num shb b pb).

(* a = a - b, for a >= b *)
Definition num_sub_spec : ident * funspec :=
 DECLARE _num_sub
 WITH sha : share, shb : share, pa : val, pb : val, a : list Z, b : list Z
 PRE [ tptr tulong, tptr tulong ]
   PROP (writable_share sha; readable_share shb;
         Zlength a = NL; Zlength b = NL; Forall limb a; Forall limb b;
         (valZ b <= valZ a)%Z)
   PARAMS (pa; pb)
   SEP (num sha a pa; num shb b pb)
 POST [ tvoid ]
   EX a' : list Z,
   PROP (Zlength a' = NL; Forall limb a'; (valZ a' = valZ a - valZ b)%Z)
   RETURN ()
   SEP (num sha a' pa; num shb b pb).

(* 1 if a < b, else 0 *)
Definition num_lt_spec : ident * funspec :=
 DECLARE _num_lt
 WITH sha : share, shb : share, pa : val, pb : val, a : list Z, b : list Z
 PRE [ tptr tulong, tptr tulong ]
   PROP (readable_share sha; readable_share shb;
         Zlength a = NL; Zlength b = NL; Forall limb a; Forall limb b)
   PARAMS (pa; pb)
   SEP (num sha a pa; num shb b pb)
 POST [ tint ]
   PROP ()
   RETURN (Vint (Int.repr (if valZ a <? valZ b then 1 else 0)))
   SEP (num sha a pa; num shb b pb).

(* p = a w, on NP limbs, for a limb w *)
Definition num_mul_small_spec : ident * funspec :=
 DECLARE _num_mul_small
 WITH shp : share, sha : share, pp : val, pa : val, a : list Z, w : Z
 PRE [ tptr tulong, tptr tulong, tulong ]
   PROP (writable_share shp; readable_share sha;
         Zlength a = NL; Forall limb a; limb w)
   PARAMS (pp; pa; Vlong (Int64.repr w))
   SEP (data_at_ shp (tarray tulong NP) pp; num sha a pa)
 POST [ tvoid ]
   EX p' : list Z,
   PROP (Zlength p' = NP; Forall limb p'; (valZ p' = valZ a * w)%Z)
   RETURN ()
   SEP (data_at shp (tarray tulong NP) (vwords p') pp; num sha a pa).

(* r = floor(a b / 2^P), when it fits *)
Definition num_mulshr_spec : ident * funspec :=
 DECLARE _num_mulshr
 WITH shr : share, sha : share, shb : share, pr : val, pa : val, pb : val,
      a : list Z, b : list Z
 PRE [ tptr tulong, tptr tulong, tptr tulong ]
   PROP (writable_share shr; readable_share sha; readable_share shb;
         Zlength a = NL; Zlength b = NL; Forall limb a; Forall limb b;
         (valZ a * valZ b < 2 ^ (Exp100.ExpConsts.P + num_bits))%Z)
   PARAMS (pr; pa; pb)
   SEP (data_at_ shr (tarray tulong NL) pr; num sha a pa; num shb b pb)
 POST [ tvoid ]
   EX r' : list Z,
   PROP (Zlength r' = NL; Forall limb r';
         valZ r' = Exp100.ExpModel.mulshr (valZ a) (valZ b))
   RETURN ()
   SEP (num shr r' pr; num sha a pa; num shb b pb).

(** ** Bits *)

(* the number of bits of a *)
Definition num_bitlen_spec : ident * funspec :=
 DECLARE _num_bitlen
 WITH sha : share, pa : val, a : list Z
 PRE [ tptr tulong ]
   PROP (readable_share sha; Zlength a = NL; Forall limb a)
   PARAMS (pa)
   SEP (num sha a pa)
 POST [ tint ]
   PROP ()
   RETURN (Vint (Int.repr (Exp100.ExpModel.bitlen (valZ a))))
   SEP (num sha a pa).

(* a = 2^f *)
Definition num_pow2_spec : ident * funspec :=
 DECLARE _num_pow2
 WITH sha : share, pa : val, f : Z
 PRE [ tptr tulong, tint ]
   PROP (writable_share sha; (0 <= f < num_bits)%Z)
   PARAMS (pa; Vint (Int.repr f))
   SEP (data_at_ sha (tarray tulong NL) pa)
 POST [ tvoid ]
   EX a' : list Z,
   PROP (Zlength a' = NL; Forall limb a';
         valZ a' = Exp100.ExpModel.pow2 f)
   RETURN ()
   SEP (num sha a' pa).

(* a = b mod 2^f *)
Definition num_low_spec : ident * funspec :=
 DECLARE _num_low
 WITH sha : share, shb : share, pa : val, pb : val, b : list Z, f : Z
 PRE [ tptr tulong, tptr tulong, tint ]
   PROP (writable_share sha; readable_share shb;
         Zlength b = NL; Forall limb b; (0 <= f < num_bits)%Z)
   PARAMS (pa; pb; Vint (Int.repr f))
   SEP (data_at_ sha (tarray tulong NL) pa; num shb b pb)
 POST [ tvoid ]
   EX a' : list Z,
   PROP (Zlength a' = NL; Forall limb a';
         valZ a' = Exp100.ExpModel.low (valZ b) f)
   RETURN ()
   SEP (num sha a' pa; num shb b pb).

(* a = floor(v 2^e) *)
Definition num_scale_spec : ident * funspec :=
 DECLARE _num_scale
 WITH sha : share, pa : val, v : Z, e : Z
 PRE [ tptr tulong, tulong, tint ]
   PROP (writable_share sha; (0 <= v < 2 ^ mant_bits)%Z;
         (Int.min_signed <= e < scale_emax)%Z)
   PARAMS (pa; Vlong (Int64.repr v); Vint (Int.repr e))
   SEP (data_at_ sha (tarray tulong NL) pa)
 POST [ tvoid ]
   EX a' : list Z,
   PROP (Zlength a' = NL; Forall limb a';
         valZ a' = Exp100.ExpModel.scale v e)
   RETURN ()
   SEP (num sha a' pa).

(** ** The reduction *)

(* q = floor(n LN2 / 2^32) *)
Definition mul_ln2_spec : ident * funspec :=
 DECLARE _mul_ln2
 WITH gv : globals, sh : share, pq : val, n : Z
 PRE [ tptr tulong, tulong ]
   PROP (writable_share sh; limb n)
   PARAMS (pq; Vlong (Int64.repr n)) GLOBALS (gv)
   SEP (data_at_ sh (tarray tulong NL) pq;
        num Ers Exp100.ExpTable.LN2 (gv _LN2))
 POST [ tvoid ]
   EX q' : list Z,
   PROP (Zlength q' = NL; Forall limb q';
         valZ q' = Exp100.ExpModel.q n)
   RETURN ()
   SEP (num sh q' pq; num Ers Exp100.ExpTable.LN2 (gv _LN2)).

(* the first guess of n: floor(X INV / 2^(P + 25)) *)
Definition guess_n_spec : ident * funspec :=
 DECLARE _guess_n
 WITH gv : globals, sh : share, px : val, X : list Z
 PRE [ tptr tulong ]
   PROP (readable_share sh; Zlength X = NL; Forall limb X)
   PARAMS (px) GLOBALS (gv)
   SEP (num sh X px;
        data_at Ers tulong (Vlong (Int64.repr Exp100.ExpTable.INV)) (gv _INV))
 POST [ tulong ]
   PROP ()
   RETURN (Vlong (Int64.repr (Exp100.ExpModel.guess (valZ X))))
   SEP (num sh X px;
        data_at Ers tulong (Vlong (Int64.repr Exp100.ExpTable.INV)) (gv _INV)).

(** ** The core and the two entry points *)

(* y and hN as core_Z gives them; on failure y and s are not written *)
Definition exp_core_spec : ident * funspec :=
 DECLARE _exp_core
 WITH gv : globals, sh : share, xb : Z, py : val, ps : val
 PRE [ tulong, tptr tulong, tptr tlong ]
   PROP (writable_share sh; (0 <= xb <= Int64.max_unsigned)%Z)
   PARAMS (Vlong (Int64.repr xb); py; ps) GLOBALS (gv)
   SEP (data_at_ sh (tarray tulong NL) py; data_at_ sh tlong ps; consts gv)
 POST [ tint ]
   EX rc : Z, EX ys : list Z, EX hN : Z,
   PROP ((rc = 0)%Z -> Exp100.ExpModel.core_Z xb = inr (valZ ys, hN) /\
                   Zlength ys = NL /\ Forall limb ys;
         (rc <> 0)%Z -> Exp100.ExpModel.core_Z xb = inl rc)
   RETURN (Vint (Int.repr rc))
   SEP (if rc =? 0
        then (num sh ys py * data_at sh tlong (Vlong (Int64.repr hN)) ps)%logic
        else (data_at_ sh (tarray tulong NL) py * data_at_ sh tlong ps)%logic;
        consts gv).

(* M and s as exp_encl_Z gives them; on failure M and s are not written *)
Definition exp_encl_bits_spec : ident * funspec :=
 DECLARE _exp_encl_bits
 WITH gv : globals, shM : share, shs : share, xb : Z, pM : val, ps : val
 PRE [ tulong, tptr tulong, tptr tlong ]
   PROP (writable_share shM; writable_share shs;
         (0 <= xb <= Int64.max_unsigned)%Z)
   PARAMS (Vlong (Int64.repr xb); pM; ps) GLOBALS (gv)
   SEP (data_at_ shM (tarray tulong NM) pM; data_at_ shs tlong ps; consts gv)
 POST [ tint ]
   EX rc : Z, EX ms : list Z, EX s : Z,
   PROP ((rc = 0)%Z -> Exp100.ExpModel.exp_encl_Z xb = inr (valW ms, s) /\
                   Zlength ms = NM /\ Forall word ms;
         (rc <> 0)%Z -> Exp100.ExpModel.exp_encl_Z xb = inl rc)
   RETURN (Vint (Int.repr rc))
   SEP (if rc =? 0
        then (data_at shM (tarray tulong NM) (vwords ms) pM *
              data_at shs tlong (Vlong (Int64.repr s)) ps)%logic
        else (data_at_ shM (tarray tulong NM) pM *
              data_at_ shs tlong ps)%logic;
        consts gv).

(* the filter: maybe_hard_Z *)
Definition maybe_hard_bits_spec : ident * funspec :=
 DECLARE _maybe_hard_bits
 WITH gv : globals, xb : Z
 PRE [ tulong ]
   PROP ((0 <= xb <= Int64.max_unsigned)%Z)
   PARAMS (Vlong (Int64.repr xb)) GLOBALS (gv)
   SEP (consts gv)
 POST [ tint ]
   PROP ()
   RETURN (Vint (Int.repr (Exp100.ExpModel.maybe_hard_Z xb)))
   SEP (consts gv).

(** The 16 statements, for every body proof and for the final semax_func. *)
Definition Gprog : funspecs := [
  num_zero_spec; num_copy_spec; num_add_spec; num_sub_spec; num_lt_spec;
  num_mul_small_spec; num_mulshr_spec; num_bitlen_spec; num_pow2_spec;
  num_low_spec; num_scale_spec; mul_ln2_spec; guess_n_spec;
  exp_core_spec; exp_encl_bits_spec; maybe_hard_bits_spec].
