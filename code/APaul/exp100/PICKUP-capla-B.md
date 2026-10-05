exp100 in Capla, group B: where it stands
=========================================

Group B now owns only NumMulProof.v (code/APaul/capla/exp100/proof/).
ReduceProof.v (mul_ln2, guess_n) and ExpCoreProof.v (exp_core) went to
other agents; group B never edited ReduceProof.v.

| spec               | file          | status                                  |
|--------------------|---------------|-----------------------------------------|
| num_mul_small_spec | NumMulProof.v | PROVED (Qed)                            |
| num_mulshr_spec    | NumMulProof.v | PROVED (Qed), on the patched Capla WP   |

Print Assumptions num_mulshr_spec: WP_sound, external_functions_sem and
the standard axioms (classic, functional_extensionality_dep,
sig_not_dec, sig_forall_dec). `nice -n 19 make NumMulProof.vo` takes 62 s.

How num_mulshr is proved (the VST invariants of Verif_mulshr.v)
--------------------------------------------------------------
- The alloc gives p = repeat 0 12 (the patched WP: alloc u64 fills with
  Vint64 0, as the semantics does).
- Outer loop on i: val32 p = val32 a_<i * val32 b, limbs i + 6 .. 11 of p
  are 0, p is 12 limbs.
- Inner loop on j: val32 p + c 2^(32 (i + j)) = val32 p0 + a_i val32 b_<j
  2^(32 i), c < 2^32; then p[i + 6] = c on a limb that was 0.
- Copy loop on i: r_q = p_(q + 5) for q < i; at the end r = limbs 5 .. 10
  of p, which is floor(a b / 2^160) since a b < 2^352.
- Arithmetic out of the WP context: val32_replace, base32_add,
  mul_add2_word (a b + p + c fits a word), num_mulshr_step,
  num_mulshr_top, num_mulshr_shift, copy_top, mulshr_final.

What ExpCoreProof.v holds (left as group B stopped, for its new owner)
-----------------------------------------------------------------------
- The callees as Section hypotheses (num_copy, num_sub, num_lt,
  num_scale, num_mulshr, mul_ln2, guess_n; num_add imported).
- apply_WP_stmt on the whole body of exp_core does not finish: the file
  defines WPc (WP kept folded, Opaque), WP_seq_c, WPcE and the tactics
  wpone / wpauto / wpenter / wpcase / summ, to run one statement at a time.
- `Opaque Tw Cw LN2w RMAXw` must come after intro_eval_funcall (intro
  needs the tables transparent), else simpl evaluates them.
- Two paths that meet again are merged with an assert HG over the env
  `PTree.set id v ... E` (equal to each branch's env by computation).
- Word lemmas there (shru_k, and_low, or_top, be_val, mx_val, be_merge0/1,
  core_big, rc_fail) were checked; core_small and scale_args were written
  but never checked; the proof stops after the merge of `be = 0`.

rocq-mcp notes
--------------
- rocq_check splits its timeout among the commands of a body: a long body
  times out at its first slow command (intro_eval_funcall takes ~30 s).
- A failing rocq_check returns the whole context (tens of KB for a WP
  goal): wrap uncertain steps as `first [tac | idtac "F"]`, or try them
  with rocq_step_multi, whose failures are one line.
