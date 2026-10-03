Pick-up: T5, the body of exp_core
=================================

Files: Verif_core.v (361 lines), CoreBounds.v (269 lines, new, pure Z, no
VST).  The Makefile lists CoreBounds.vo before Verif_core.vo, and
Verif_core.vo depends on it.  Both files build.  body_exp_core ends in one
`admit.` (line 360) followed by Admitted.

Rebuild
-------
  eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
  cd code/APaul/vst/exp100
  nice -n 19 make CoreBounds.vo      # a few seconds
  nice -n 19 make Verif_core.vo      # 67 s on the desktop, almost all body

What is proved
--------------
CoreBounds.v, all closed (no Admitted):
- zpow: an Ltac that rewrites every 2^k with k a numeral into its value
  (lia does not evaluate 2^52 here).
- Sizes: X_bits 170, n_bits 17, r_bits 154, h_bits 161, t_bits 161.
- The bits: xexpo_0, xexpo_n (the two cases of `if (be == 0)`),
  xmant0_bound, xbexp_bound, xsign_bound (< 2), xmant_bound (< 2^53),
  xexpo_bound (1 <= be < 1033), xfixE, xfix_bound (0 <= X < 2^170).
- The reduction: guess_bound (g < 2^17); red1, red2, red_n (the n of
  reduce, before its check) with reduceE, red1_bound, red2_bound,
  red_n_bound (n <= 2^17); LN2v_ge (2^185 <= LN2v, vm_compute);
  checked_n_bound (q n <= X < 2^170 -> n < 2^17); reduce_some, reduce_none.
- Horner: RMAXv_lt (RMAXv < 2^154, vm_compute); Cv_bound (C_i <= 2^160,
  from C_ok); horner_step (h < 2^161, r < 2^154 -> h r < 2^352,
  mulshr h r >= 0, mulshr h r + C_i < 2^161); horner_from_S,
  horner_from_0, horner_start.
- rarg_pos, rarg_neg (r and Nu in the two signs); Nu_bound (Nu < 2^18).
- Ts_bound, Tv_bound (0 <= T_j < 2^161, vm_compute on Ts).
- The outcomes of core_Z, proved by rewriting, never by computing:
  core_Z_big (inl 1), core_Z_reduce (inl 2), core_Z_rmax (inl 3),
  core_Z_ok (inr (mulshr (Tv (jidx Nu)) (horner r), hidx Nu)).

Verif_core.v, helpers (all closed): and_ones, shru_repr, or_top (word
lemmas); gt0_val (the C test n > 0); num_data_at_ (num |-- data_at_);
rows_but and table_row (row i of T or C as `num Ers (Znth i tab)
(offset_val (48 * i) p)` times the rest); Zlength_T, Zlength_C; Cv_Znth,
Tv_Znth.

body_exp_core, done up to the Horner loop:
- the bits of xb (neg, be, mx), the return 1 (|x| >= 1024);
- be == 0 join; num_scale; guess_n; the two corrections (&& and the
  second mul_ln2 + num_lt), each a forward_if (temp ...) join;
- the two last mul_ln2 and the || check; the return 2;
- the sign branch (forward_if with an EX rl postcondition giving
  valZ rl = M.rarg xb n and temp _Nu = M.Nu xb n); num_copy, num_sub;
- num_lt(r, RMAX) and the return 3;
- num_copy(h, C[16]) and the refold of C.

Where the proof stands
----------------------
Line 360, `admit.`, just before the C statement
  for (int i = DEG - 1; i >= 0; i--) { ... }
In the context: Bx (xbexp < 1033), Hred (M.reduce X = Some n), Bn'
(n < 2^17), HrR (M.rarg xb n < M.RMAXv), Br (0 <= rarg < 2^154), HlC,
HfC.  The goal is a semax whose SEP is
  num Tsh (Znth 16 C) v_h; num Tsh rl v_r; num Ers RMAX (gv _RMAX);
  num Tsh Xl v_X; num Tsh q2l v_q; num Tsh q3l v_q1;
  data_at Ers ... (map vwords T) (gv _T);
  data_at Ers ... (map vwords C) (gv _C);
  data_at_ Tsh v_t; data_at_ sh py; data_at_ sh tlong ps;
  num Ers LN2 (gv _LN2); data_at Ers tulong ... (gv _INV)
and LOCAL has temp _Nu (Vlong (Int64.repr (M.Nu xb n))), the six lvars,
gvars gv, temp _y py, temp _s ps (and the old temps t'k).  FT is thawed.

Remaining hole: the end of body_exp_core
----------------------------------------
Plan, written once and not yet run to the end:
1. `forward.` for i = 15, then forward_loop with three assertions (the
   first try failed with "Use [forward_loop Inv]": check whether the
   `forward` for `_i = 16 - 1` is needed before it, or whether the Sset is
   part of the loop statement VST expects; look at the goal first):
   - Inv: EX i hl, PROP (-1 <= i < 16; Zlength hl = NL; Forall limb hl;
     valZ hl < 2^h_bits;
     M.horner_from r (valZ hl) (Z.to_nat (i + 1)) = M.horner r),
     LOCAL temp _i, temp _Nu, six lvars, gvars, _y, _s; the SEP above
     with num Tsh hl v_h.
   - continue: the same with 0 <= i < 16 and Z.to_nat i.
   - break: EX hl with valZ hl = M.horner r.
   Entry: hl = Znth 16 C, by Cv_Znth, horner_start, Cv_bound.
   Body: num_mulshr(t, h, r) (PRE from horner_step, unfold num_bits);
   table_row for C at i, Intros, num_add(t, C[i]) (PRE from horner_step,
   Cv_Znth), gather_SEP and rewrite <- table_row; sep_apply
   num_data_at_ for h, num_copy(h, t); sep_apply num_data_at_ for t;
   the new invariant by horner_from_S and Z2Nat (Z.to_nat (i+1) =
   S (Z.to_nat i)).  Break branch: horner_from_0.
2. j = Nu & 63: rewrite with and_ones (k = 6), so j = Nu mod 64 =
   M.jidx Nu (M.jidxE, TAB = 64); Nu_bound gives the range.
3. table_row for T at j, num_mulshr(y, T[j], h) with sh, Ers, Tsh
   (PRE from Tv_bound, Tv_Znth and valZ h < 2^161); check how VST
   evaluates `T[j]` with a long index (C[i] with an int index came out
   directly as offset_val (48 * i)).
4. *s = (long)(Nu >> 6) - 2048: shru_repr, sub64_repr; equals
   M.hidx Nu by M.hidxE (hN_bias = 2048).
5. return 0: Exists 0 yl (M.hidx (M.Nu xb n)); core_Z_ok xb n Bx Hred HrR,
   M.jidxE, Tv_Znth; free the stack with sep_apply num_data_at_ on the
   six local arrays; thaw nothing (FT is already thawed), unfold consts,
   refold T with table_row.

The bounds chosen
-----------------
X < 2^170; g < 2^17; n1 < 2^17; n <= 2^17 before the check, n < 2^17
after it (so n + 1 < 2^32 for mul_ln2 and 131072 - (n + 1) >= 0);
r < RMAXv < 2^154; every Horner value < 2^161 (C_i <= 2^160); T_j < 2^161;
Nu < 2^18.  No bound on y is needed: num_mulshr's POST gives a num.

Traps met
---------
- The model functions in LOCAL make forward_if hang (seen with
  `Int.repr (M.xbexp xb)`): the file sets `Local Opaque` on the ExpModel
  functions and on the tables T, C, LN2, RMAX.  Then `unfold` refuses them
  ("red1 is opaque"): keep definitions you need to unfold (red1, red2,
  red_n) transparent, and use the ...E lemmas for the others.
- The tables in SEP: freeze them (`freeze FT := ...`) until they are
  needed.
- `&&` inside a VST assertion is the separation-logic and: write
  `andb a b`.
- A call whose PRE asks data_at_ on an array that holds a num is not
  matched: `sep_apply (num_data_at_ Tsh xs p)` first.  The same at every
  return, for the local arrays.
- `forward_call` of a function with a result already does the following
  `_n = _t'1;`: no extra `forward`.
- `entailer!` substitutes `set` variables (X := M.xfix xb) back: inside
  a branch, name M.xfix xb, not X.
- After `entailer!`, goals like `Vlong (Int64.repr (g - 1)) =
  Vlong (Int64.repr (g - 1))` are left: `reflexivity`; `rewrite add64_repr`
  then fails (VST has already rewritten it).
- In forward_if branches the hypothesis is `Int.repr (if b then 1 else 0)
  = Int.zero` or `<> Int.zero`: destruct b, then `discriminate` or
  `contradiction H0; reflexivity`.
- `Timeout` is a command: inside a tactic write `timeout 10 tac`.
- Coqc output to a shared scratchpad file name was overwritten by another
  agent's build: use a file name of your own.
