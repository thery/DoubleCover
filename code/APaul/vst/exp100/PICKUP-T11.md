Pick-up: T11, the whole program (semax_prog)
============================================

State: DONE.  No admit, no Admitted in the new files.  Spec.v, Common.v,
exp100.c and every file proved before T11 are unchanged.

Files
-----
  exp100_main.c        #include "../../exp100/exp100.c" plus
                       int main(void) { return maybe_hard(1.0); }
  exp100_main_clight.v generated: clightgen -normalize exp100_main.c
  InitConsts.v         the initial globals give consts gv
  Verif_main.v         the wrappers exp_encl, maybe_hard on the reals; main
  Verif_prog.v         exp100_main_correct: semax_prog
  Makefile             rules for exp100_main_clight.v, InitConsts.vo,
                       Verif_main.vo, Verif_prog.vo (all in PROOFS)

What is proved
--------------
InitConsts.v
- init_words_data_at, init_words_num, init_rows, init_word: the initial
  words of a global (one mapsto per word, as globvars2pred gives them)
  are the data_at of the array (2-D arrays via data_at_2darray_concat).
- globvars_consts: (forall i, at_start (gv i)) ->
    globvars2pred gv [(_T, v_T); (_C, v_C); (_LN2, v_LN2);
                      (_RMAX, v_RMAX); (_INV, v_INV)] |-- consts gv
  at_start p: p = Vundef or p = Vptr b Ptrofs.zero (what gvars gives).
Verif_main.v
- dreal x := B2R 53 1024 x; xreal_bits: xreal (unsigned (to_bits x)) =
  dreal x (for every double, NaN and infinities included: both are 0).
- exp_encl_spec (double x): rc in [0,3]; rc = 0 -> encl_real (dreal x)
  (valW ms) s, Zlength ms = NM, Forall word ms.  body_exp_encl.
- maybe_hard_spec (double x): r in [0,1]; r = 0 -> ~ hard (dreal x).
  body_maybe_hard.  Both bodies: the union store/load hack of VST, then
  the call with the Spec.v statement and ExpSpec.exp_encl_ok /
  maybe_hard_ok.
- main_spec: PRE main_pre prog tt gv; POST EX r, r in [0,1],
  r = 0 -> ~ hard 1, SEP (consts gv; TT).  body_main: main_pre is
  rewritten (main_pre_start_old) and globvars_consts applied BEFORE
  start_function3, then maybe_hard is called.  dreal_one: dreal 1.0 = 1.
Verif_prog.v
- Gmain := Gprog ++ [exp_encl_spec; maybe_hard_spec; main_spec].
- exp100_main_correct : semax_prog E.exp100_main_clight.prog tt Vprog Gmain.

How the 16 bodies are reused
----------------------------
clightgen names identifiers by string ($"..."), so the function bodies of
exp100_main_clight.v are the same terms as those of exp100_clight.v, and
the composites (the union exp100_bits) are the same: CompSpecs and Vprog
of Common.v serve for the new program.  Each body_* lemma (proved with
context Spec.Gprog) is lifted to Gmain by semax_body_subsumption' and
tycontext_subVG (computed once per context by try_prove_tycontext_subVG).
Floyd's semax_func_cons does this but its unification of the old body
against the new one does not end (killed after 590 s); the Ltac cons_body
of Verif_prog.v names the old body (change fnew with fold, then refine):
0.4-0.6 s per function.

Print Assumptions exp100_main_correct
-------------------------------------
The VST/Stdlib axioms (prop_ext, functional_extensionality_dep,
eq_rect_eq, classic, Extensionality_Ensembles, sig_forall_dec,
sig_not_dec) and the kernel primitives PrimInt63/Uint63Axioms/
Sint63Axioms/PrimFloat/FloatAxioms/PrimArray (from Interval, through
ExpSpec).  Nothing of exp100.

What is NOT proved
------------------
- main is a fixed call maybe_hard(1.0); the theorem says nothing about
  what main returns beyond r = 0 -> ~ hard 1.
- The bits functions keep their model statements in Gmain (Spec.v);
  their real statements are exp100_correct of Verif_all.v.  They cannot
  be put in Gmain: the 14 helper bodies are proved with context Spec.Gprog
  and a context can only be weakened to stronger statements.
- semax_prog is VST's partial correctness of the program in its initial
  state; linking with a C library is not involved (no external call).

Rebuild (measured on the desktop, nice 19, other agents running)
--------
  eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
  nice -n 19 make Verif_prog.vo
  InitConsts.v ~4 s, Verif_main.v 25 s, Verif_prog.v 137 s wall,
  2.3 GB peak (prove_semax_prog 24 s, the 19 cons_body ~10 s, Qed 33 s,
  Print Assumptions the rest).

Traps met
---------
- start_function on main runs expand_main_pre, which splits the tables
  into one mapsto per word: did not end in 10 min.  Do start_function1,
  start_function2, rewrite main_pre_start_old, semax_pre with consts gv,
  then start_function3.
- main_pre must name the program literally (E.exp100_main_clight.prog),
  not through a Definition.
- Float.of_bits is opaque: Local Transparent for dreal_one.
- rocq_start on a file whose last theorem runs prove_semax_prog timed out
  while that theorem sat in Verif_main.v: keep it in its own file.
