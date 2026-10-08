(** * The statements of the search of one line (../htr_filter.b)

    A statement reads the interpreter of Capla, [eval_func ge μ f args]:
    when the call returns [Some (r, rl)], [r] is the value returned and
    [rl] the final values of the mutable array parameters, in order.  An
    array of n words is a [{ffun 'I_n -> int64}], passed as
    [B <:: [u64; n]], with its length [m] as the next argument:
    [n = Z.to_nat (Int64.unsigned m)].  A statement holds for every fuel
    μ: it says nothing when the fuel runs out (the result is then [None]).

    The statements mirror the VST funspecs (../../../vst/Spec_add.v,
    Verif_sub.v, Verif_difftab.v, Verif_tstep.v, Spec_search.v); the
    numbers are those of HtrWords.v ([segv], [coefsA]), the table of
    differences and the candidates those of HtrDefs.v ([fdiff], [tstepZ],
    [cands]).  Each statement is a [Prop]; [name_ok : name_spec] is its
    proof, in the file of that function (AddProof.v for [add]). *)

From APaulRocq Require Import HtrDefs.
From compcert Require Import CaplaProof.
Require Import HtrFilterCapla.htr_filter HtrFilterCapla.HtrWords.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

Definition ge := genv_of_program program.

(** ** add and sub: B_ia <- B_ia +/- B_ib mod 2^(64 l)

    On one array at two disjoint offsets ia and ib; the words outside
    ia .. ia + l - 1 are left alone. *)

Definition add_spec : Prop :=
  forall μ (mm : nat) (m : int64), mm = Z.to_nat (Int64.unsigned m) ->
  forall (B : {ffun 'I_mm -> int64}) (ia ib l : int64) r rl,
    let IA := Z.to_nat (Int64.unsigned ia) in
    let IB := Z.to_nat (Int64.unsigned ib) in
    let L := Z.to_nat (Int64.unsigned l) in
    (IA + L <= mm)%nat -> (IB + L <= mm)%nat ->
    (IA + L <= IB \/ IB + L <= IA)%nat ->
    eval_func ge μ f_add
      [:: B <:: [u64; mm]; m <:: u64; ia <:: u64; ib <:: u64; l <:: u64]
      = Some (r, rl) ->
    exists B' : {ffun 'I_mm -> int64}, rl = [:: B' <:: [u64; mm]] /\
      segv B' IA L = (segv B IA L + segv B IB L) mod baseZ (Z.of_nat L) /\
      (forall q : 'I_mm, (q < IA \/ IA + L <= q)%nat -> B' q = B q).

Definition sub_spec : Prop :=
  forall μ (mm : nat) (m : int64), mm = Z.to_nat (Int64.unsigned m) ->
  forall (B : {ffun 'I_mm -> int64}) (ia ib l : int64) r rl,
    let IA := Z.to_nat (Int64.unsigned ia) in
    let IB := Z.to_nat (Int64.unsigned ib) in
    let L := Z.to_nat (Int64.unsigned l) in
    (IA + L <= mm)%nat -> (IB + L <= mm)%nat ->
    (IA + L <= IB \/ IB + L <= IA)%nat ->
    eval_func ge μ f_sub
      [:: B <:: [u64; mm]; m <:: u64; ia <:: u64; ib <:: u64; l <:: u64]
      = Some (r, rl) ->
    exists B' : {ffun 'I_mm -> int64}, rl = [:: B' <:: [u64; mm]] /\
      segv B' IA L = (segv B IA L - segv B IB L) mod baseZ (Z.of_nat L) /\
      (forall q : 'I_mm, (q < IA \/ IA + L <= q)%nat -> B' q = B q).

(** ** difftab: the table of differences

    The k coefficients of l words become their forward differences at 0,
    modulo 2^(64 l); the words from k l on are left alone. *)

Definition difftab_spec : Prop :=
  forall μ (mm : nat) (m : int64), mm = Z.to_nat (Int64.unsigned m) ->
  forall (B : {ffun 'I_mm -> int64}) (k l : int64) r rl,
    let K := Z.to_nat (Int64.unsigned k) in
    let L := Z.to_nat (Int64.unsigned l) in
    (K * L <= mm)%nat ->
    eval_func ge μ f_difftab
      [:: B <:: [u64; mm]; m <:: u64; k <:: u64; l <:: u64]
      = Some (r, rl) ->
    exists B' : {ffun 'I_mm -> int64}, rl = [:: B' <:: [u64; mm]] /\
      coefsA B' L K =
        [seq fdiff (coefsA B L K) j mod baseZ (Z.of_nat L) | j <- iota 0 K] /\
      (forall q : 'I_mm, (K * L <= q)%nat -> B' q = B q).

(** ** tstep: one step of the table

    Coefficient t becomes coefficient t plus coefficient t + 1, modulo
    2^(64 l), for t = 0 .. k-2; the words from k l on are left alone. *)

Definition tstep_spec : Prop :=
  forall μ (mm : nat) (m : int64), mm = Z.to_nat (Int64.unsigned m) ->
  forall (B : {ffun 'I_mm -> int64}) (k l : int64) r rl,
    let K := Z.to_nat (Int64.unsigned k) in
    let L := Z.to_nat (Int64.unsigned l) in
    (1 <= K)%nat -> (1 <= L)%nat -> (K * L <= mm)%nat ->
    eval_func ge μ f_tstep
      [:: B <:: [u64; mm]; m <:: u64; k <:: u64; l <:: u64]
      = Some (r, rl) ->
    exists B' : {ffun 'I_mm -> int64}, rl = [:: B' <:: [u64; mm]] /\
      coefsA B' L K =
        [seq z mod baseZ (Z.of_nat L) | z <- tstepZ (coefsA B L K)] /\
      (forall q : 'I_mm, (K * L <= q)%nat -> B' q = B q).

(** ** search: the candidates of one line

    The array holds the k values P(0) .. P(k-1) of a line, l words each.
    search returns the number of candidates j = 0 .. n-1 ([cands] of
    HtrDefs.v, in increasing order) and writes the first cap of them at
    the start of out. *)

Definition search_spec : Prop :=
  forall μ (mm : nat) (m : int64), mm = Z.to_nat (Int64.unsigned m) ->
  forall (cc : nat) (cap : int64), cc = Z.to_nat (Int64.unsigned cap) ->
  forall (B : {ffun 'I_mm -> int64}) (out : {ffun 'I_cc -> int64})
      (k l n err : int64) r rl,
    let K := Z.to_nat (Int64.unsigned k) in
    let L := Z.to_nat (Int64.unsigned l) in
    let N := Z.to_nat (Int64.unsigned n) in
    (1 <= K)%nat -> (1 <= L)%nat -> (K * L <= mm)%nat ->
    2 * Int64.unsigned err <= Int64.max_unsigned ->
    eval_func ge μ f_search
      [:: B <:: [u64; mm]; m <:: u64; k <:: u64; l <:: u64; n <:: u64;
          err <:: u64; out <:: [u64; cc]; cap <:: u64]
      = Some (r, rl) ->
    let cs := cands (Z.of_nat L) (Int64.unsigned err) (coefsA B L K) N in
    exists (B' : {ffun 'I_mm -> int64}) (out' : {ffun 'I_cc -> int64}),
      rl = [:: B' <:: [u64; mm]; out' <:: [u64; cc]] /\
      r = Vint64 (Int64.repr (Z.of_nat (size cs))) /\
      (forall i : 'I_cc, (i < size cs)%nat ->
         out' i = Int64.repr (Z.of_nat (nth 0%nat cs i))).
