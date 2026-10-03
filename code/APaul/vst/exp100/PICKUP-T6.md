Pick-up: T6, exp_encl_bits and maybe_hard_bits
===============================================

Files
-----
  TopLemmas.v   (380 lines, all Qed)  the helper lemmas and body_exp_encl_bits.
  Verif_top.v   (215 lines, Qed)  body_maybe_hard_bits.
  Makefile      has TopLemmas.vo in PROOFS, `TopLemmas.vo: Spec.vo` and
                `Verif_top.vo: TopLemmas.vo`.
Spec.v, Common.v and the funspecs are unchanged.

What is proved
--------------
- body_exp_encl_bits (TopLemmas.v), no admit.
- body_maybe_hard_bits (Verif_top.v), no admit.  It uses only the
  funspecs of Gprog.  Print Assumptions: the standard axioms of VST
  (prop_ext, functional_extensionality_dep, eq_rect_eq, classic,
  Extensionality_Ensembles) and the two of ClassicalDedekindReals
  (sig_not_dec, sig_forall_dec); nothing of exp100.
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

How body_maybe_hard_bits goes
-----------------------------
exp_core and its two outcomes; num_zero(d) + d[0] = 16 (replace_SEP to
num Tsh Dl v_d); lo = y - D; hi = y + D; b = bitlen y; the `||` test on
the bit lengths and its return 1; e, ve, f (Int64 expressions rewritten
to Int64.repr of Z); the f range test and its return 1; decide_f gives
decide_Z as the last test.  Then hypotheses that mention f's definition
are cleared (entailer! would substitute f otherwise); num_low,
num_pow2, num_sub; num_lt and the `if` with the two num_copy, through
an explicit post (EX dd, valZ dd = min); num_pow2(t, f - 43); num_zero(hi)
+ hi[0] = 16; num_add(t, hi); maybe_hard_Z xb = (t <? d ? 0 : 1) from
Hcore and decide_f; num_lt(t, d) and the two returns.

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
- entailer! substitutes an equation `f = expr`: clear it (Hfz) before
  the calls whose argument is (int) f.
- `sep_apply num_free` takes the FIRST num of the SEP: name the one to
  free, `sep_apply (num_free Tsh hi1 v_hi)`.
- The argument (int) f - 43 leaves a range goal on Int.signed first,
  then the argument equality.
- rocq-mcp needs a _CoqProject (-Q . E -Q exp100-model Exp100) and a
  workspace under /home/thery/claudeExp; this directory has none.
- The scratchpad is shared with other agents: never write `out.txt` there,
  use a private name (t6_out.txt).

Rebuild
-------
  cd code/APaul/vst/exp100
  eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst) && \
    nice -n 19 make Verif_top.vo
Measured: Verif_top.v alone 85 s wall on the desktop (nice 19, while
another Rocq compile ran).
