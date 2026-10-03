Pick-up: T6, exp_encl_bits and maybe_hard_bits
===============================================

Files
-----
  TopLemmas.v   (380 lines, all Qed)  the helper lemmas and body_exp_encl_bits.
  Verif_top.v   (135 lines)  body_maybe_hard_bits only, ending in
                `admit. Admitted.` (line 134).
  Makefile      has TopLemmas.vo in PROOFS, `TopLemmas.vo: Spec.vo` and
                `Verif_top.vo: TopLemmas.vo`.
Spec.v, Common.v and the funspecs are unchanged.

What is proved
--------------
- body_exp_encl_bits (TopLemmas.v), no admit.
- Every helper lemma in TopLemmas.v.
- 2^P <= y and y + D < 2^192 come from the model, through
  ExpModel.core_relP: the post of exp_core did NOT need to change.

Helper lemmas (TopLemmas.v)
---------------------------
  zpow (Ltac)       writes each 2^k (numeral k) as a numeral, for lia.
  proj_inl (Ltac)   projects an `inl r = inl rc` without injection.
  core_Z_rc         core_Z xb = inl rc -> 1 <= rc <= 3.
  core_bounds       core_Z xb = inr (y, hN) ->
                    2^160 <= y < 2^162 /\ -2^12 <= hN <= 2^12.
    from: Cs_bound, Ts_bound, Ts_length, Cv0, RMAXv_lt, LN2v_ge (vm_compute
    on the constant lists, never on core_Z), Cv_all, Tv_all, mulshr_bound,
    horner_from_S, horner_from_bound, horner_bound, xfix_bound, qE',
    n_bound.
  pack, Znth_pack, valW_pack, pack_word, or_shl, upd_prefix   (M words).
  Dl, Dl_num        D = 16 as a number [16;0;0;0;0;0].
  bitlen_range      0 <= v < 2^192 -> 0 <= bitlen v <= 192.
  valZ_range        a number of 6 limbs is below 2^192.
  num_free          num sh xs p |-- data_at_ sh (tarray tulong 6) p.
  decide_bits       bitlen (y-16) <> bitlen y \/ bitlen (y+16) <> bitlen y ->
                    decide_Z y hN = 1.
  decide_f          once the two bit lengths agree, with
                    f = Z.max (hN - 160 + bitlen y - 1) (-1022) - 53 - (hN - 160),
                    decide_Z y hN = if (f <? 64) || (184 <? f) then 1 else
                    (lo := low y f, hi := pow2 f - lo, d := min) the test
                    pow2 (f - 43) + 16 <? d.

Where body_maybe_hard_bits stands
---------------------------------
Done, in order: exp_core and its two outcomes; num_zero(d) + d[0] = 16
(replace_SEP to num Tsh Dl v_d); lo = y - D; hi = y + D; b = bitlen y; the
`||` test on the bit lengths (forward_if [temp _t'4 ...]) and its return 1;
e, ve, f (Int64 expressions rewritten to Int64.repr of Z); the f range
test (forward_if [temp _t'7 ...]) and its return 1.

The hole (Verif_top.v line 133-134) is just before the C statement
  num_low(lo, y, (int) f);
Context then: Hcore, Hl, Hf (ys), lo1/hi1 with their values, b, Hb,
Eb1/Eb2 (the two bit lengths are b), f with Hfz and Ec : 64 <= f /\ f <= 184,
and Hd : decide_Z (valZ ys) hN = (if pow2 (f-43) + 16 <? d then 0 else 1)
with d written out with low/pow2.  SEP: num Tsh lo1 v_lo; num Tsh ys v_y;
num Tsh hi1 v_hi; num Tsh Dl v_d; data_at hN; consts gv; data_at_ v_t.

Plan for the rest
-----------------
1. forward_call (Tsh, Tsh, v_lo, v_y, ys, f).  It leaves 3 side goals
   (seen): the argument `(int) f`  -> entailer!, then
   Int.repr (Int64.unsigned (Int64.repr f)) = Int.repr f by unsigned_repr
   (64 <= f <= 184); the frame num Tsh lo1 v_lo |-- data_at_  -> sep_apply
   num_free (or unfold num; cancel with data_at_data_at_); 0 <= f < num_bits
   -> change num_bits with 192; lia.  Intros lo2.
2. num_pow2(hi, f): same pattern, Intros hi2 (valZ hi2 = pow2 f).
3. num_sub(hi, lo): pre low y f <= pow2 f by M.lowE, M.pow2E and
   Z.mod_pos_bound.  Intros hi3.
4. num_lt(lo, hi) then the if with two num_copy into d: needs a full
   post, forward_if (EX dd, PROP (Zlength dd = 6; Forall limb dd;
   valZ dd = if lo <? hi then lo else hi) LOCAL (...) SEP (...)).
5. num_pow2(t, (int) f - 43): arg Int.sub (Int.repr f) (Int.repr 43);
   21 <= f - 43.  num_zero(hi); hi[0] = 16; replace_SEP to num Tsh Dl v_hi;
   num_add(t, hi): pow2 (f-43) + 16 < 2^192.
6. num_lt(t, d): forward_if; return 0 / return 1.  Post: unfold
   M.maybe_hard_Z; rewrite Hcore, Hd, then the values; then
   repeat sep_apply num_free; cancel.

Traps met
---------
- `&&` and `||` are VST notations (andp, orp): write andb / orb.
- `[H|->]` does not parse under VST (`|->`): write `[H| ->]`.
- forward_call already absorbs the `_b = _t'2` that follows a call.
- forward_call returns `EX vret` as a tuple: Intros vret; destruct vret as
  [[rc ys] hN]; cbn [fst snd] in *.
- destruct (Z.eqb_spec rc 0) also rewrites `rc =? 0` in the SEP.
- The false branch of `if (rc)` needs rc in int range: core_Z_rc.
- forward_if refuses without a post when code follows: give
  [temp _x v] (list form) when only a temp differs.
- At return the locals must become data_at_: num_free + sep_apply + cancel.
- list_solve on lists built from `pack ys` hangs (> 400 s): prove the list
  step as a separate lemma on an abstract L (upd_prefix).
- `*s = hN - P` asks Int64.min_signed <= hN - 160 <= Int64.max_signed:
  core_bounds.
- The comparison `f > 184` is Int64.lt (repr 184) (repr f): zlt 184 f.
- The scratchpad is shared with other agents: never write `out.txt` there,
  use a private name (t6_out.txt).

Rebuild
-------
  cd code/APaul/vst/exp100
  eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst) && \
    nice -n 19 make Verif_top.vo
Measured: TopLemmas.v + Verif_top.v about 60 s; Verif_top.v alone about
42 s on the desktop.
