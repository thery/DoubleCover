Pick-up: T5, the body of exp_core
=================================

State: DONE.  `body_exp_core` (Verif_core.v) ends in Qed; no admit, no
Admitted in Verif_core.v or CoreBounds.v.  `Print Assumptions
body_exp_core` lists only the usual VST axioms (sig_not_dec,
sig_forall_dec, prop_ext, functional_extensionality_dep, eq_rect_eq,
classic, Extensionality_Ensembles).  The proof uses only the funspecs of
Spec.v (Gprog).

Files: Verif_core.v (532 lines), CoreBounds.v (269 lines, pure Z,
no VST).  The Makefile builds CoreBounds.vo before Verif_core.vo.

Rebuild
-------
  eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
  cd code/APaul/vst/exp100
  nice -n 19 make CoreBounds.vo      # a few seconds
  nice -n 19 make Verif_core.vo      # 130 s on the desktop (measured)

The directory has no _CoqProject: to drive it from rocq-mcp, use a
workspace outside git (under /home/thery/claudeExp) holding a _CoqProject
with absolute paths `-Q <dir> E` and `-Q <dir>/exp100-model Exp100`, and a
copy of the .v file.

CoreBounds.v
------------
- zpow: an Ltac that rewrites every 2^k with k a numeral into its value
  (lia does not evaluate 2^52 here).
- Sizes: X_bits 170, n_bits 17, r_bits 154, h_bits 161, t_bits 161.
- The bits: xexpo_0, xexpo_n, xmant0_bound, xbexp_bound, xsign_bound,
  xmant_bound, xexpo_bound, xfixE, xfix_bound.
- The reduction: guess_bound; red1, red2, red_n with reduceE, red1_bound,
  red2_bound, red_n_bound; LN2v_ge; checked_n_bound; reduce_some,
  reduce_none.
- Horner: RMAXv_lt; Cv_bound (C_i <= 2^160); horner_step; horner_from_S,
  horner_from_0, horner_start.
- rarg_pos, rarg_neg; Nu_bound (Nu < 2^18); Ts_bound, Tv_bound.
- The outcomes of core_Z, by rewriting: core_Z_big, core_Z_reduce,
  core_Z_rmax, core_Z_ok.

Verif_core.v
------------
Helpers: and_ones, shru_repr, or_top, gt0_val, num_data_at_, rows_but,
table_row (row i of T or C as a num at offset 48 i, times the other
rows), Zlength_T, Zlength_C, Cv_Znth, Tv_Znth.  The model functions and
the tables are `Local Opaque`.

body_exp_core, in the order of the C:
- the bits of xb, return 1, the be == 0 join, num_scale, guess_n, the
  two corrections, the check and return 2, the sign branch, num_lt with
  RMAX and return 3, num_copy(h, C[16]);
- the Horner loop: forward_loop with three assertions.  Invariant: i in
  [-1, 16), h a number below 2^h_bits with
  horner_from r h (Z.to_nat (i + 1)) = horner r; continue: the same with
  i in [0, 16) and Z.to_nat i; break: h = horner r.  Body: num_mulshr,
  table_row for C at i, num_add, refold C, num_copy;
- j = Nu & 63 = jidx Nu (and_ones, jidxE); table_row for T at j;
  num_mulshr(y, T[j], h); *s = Nu / 64 - 2048 = hidx Nu (shru_repr,
  sub64_repr, hidxE); return 0 with core_Z_ok, T refolded with
  table_row, the local arrays freed with num_data_at_.

Traps met
---------
- A concrete row of a table (`Znth 16 C`) in a goal makes entailer! hang:
  prove the facts about it first, then `remember ... ; clear Ec` so the
  row is a variable.  A row at a variable index (`Znth i C`) is fine.
- The model functions in LOCAL make forward_if hang: keep them
  `Local Opaque`; use the ...E lemmas instead of unfolding.
- Freeze the tables while they are not needed.
- `&&` inside a VST assertion is the separation-logic and: write
  `andb a b`.
- A call whose PRE asks data_at_ on an array that holds a num is not
  matched: `sep_apply (num_data_at_ Tsh xs p)` first; the same at every
  return, for the local arrays.
- To refold a table split by table_row inside an entailment where the
  two pieces are not adjacent: `sep_apply (derives_refl' _ _ (eq_sym ET))`
  with ET the table_row equation.
- The store `*s = (long)(Nu >> 6) - 2048` leaves a typecheck goal (no
  signed overflow): shru_repr, Int64.signed_repr and the bound
  Nu / 2^6 < 2^12.
- `forward_call` of a function with a result already does the following
  `_n = _t'1;`.
- `entailer!` substitutes `set` variables back.
- In forward_if branches the hypothesis is `Int.repr (if b then 1 else 0)
  = Int.zero` or `<> Int.zero`: destruct b.
- `Timeout` is a command: inside a tactic write `timeout 10 tac`.
