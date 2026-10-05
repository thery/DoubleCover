(** * The statements of the 17 functions of the Capla exp100 (../exp100.b)

    A statement reads the interpreter of Capla, [eval_func ge μ f args]:
    when the call returns [Some (r, rl)], [r] is the value returned and
    [rl] the final values of the mutable array parameters, in order.  An
    array of n words is a [{ffun 'I_n -> int64}], passed as
    [a <:: [u64; n]]; a number is an array of [NL] limbs (Bridge.v).  A
    statement holds for every fuel μ: it says nothing when the fuel runs
    out (the result is then [None]).

    The statements mirror the VST funspecs (../../../vst/exp100/Spec.v)
    against the integer model of ExpModel.v: inputs are numbers of limbs,
    an output number is a new array of limbs whose value the model gives.
    Each statement is a [Prop]; [name_ok : name_spec] is its proof, in
    the file of that function (NumAddProof.v for [num_add]).

    Capla has no globals: [exp_core], [exp_encl_bits] and
    [maybe_hard_bits] take the tables T, C, LN2, RMAX as arguments, and
    [mul_ln2] takes LN2; [tables_ok] says that they hold the tables of
    ExpTable.v. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpTable ExpConsts ExpModel ExpModelBounds.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

Definition ge := genv_of_program program.

(** ** Sizes and bounds *)

(* Limbs of a product of a number by a limb. *)
Definition NP : nat := 7.

(* Words of 64 bits of the enclosure M. *)
Definition NM : nat := 3.

(* Rows of the table T, of the table C. *)
Definition TABn : nat := 64.
Definition CLn : nat := 17.

(* Bits of the mantissa of a double, with the implicit bit. *)
Definition mant_bits : Z := 53.

(* num_scale writes limb e / 32 + 2 of 6: e < 128. *)
Definition scale_emax : Z := 128.

(* A number, an array of NL limbs. *)
Notation numA := {ffun 'I_NL -> int64}.

(** ** The tables *)

(* The table arguments hold the tables of ExpTable.v, word by word. *)
Definition tables_ok (Ta : {ffun 'I_TABn -> numA}) (Ca : {ffun 'I_CLn -> numA})
    (L2 RM : numA) : Prop :=
  (forall j : 'I_TABn, words (Ta j) = nth [::] ExpTable.T j) /\
  (forall i : 'I_CLn, words (Ca i) = nth [::] ExpTable.C i) /\
  words L2 = ExpTable.LN2 /\ words RM = ExpTable.RMAX.

(** ** Numbers *)

(* a = 0 *)
Definition num_zero_spec : Prop :=
  forall μ (a : numA) r rl,
    eval_func ge μ f_num_zero [:: a <:: [u64; NL]] = Some (r, rl) ->
    rl = [:: [ffun _ => Int64.zero] <:: [u64; NL]].

(* a = b *)
Definition num_copy_spec : Prop :=
  forall μ (a b : numA) r rl,
    eval_func ge μ f_num_copy [:: a <:: [u64; NL]; b <:: [u64; NL]]
      = Some (r, rl) ->
    rl = [:: b <:: [u64; NL]].

(* a = a + b, when the sum fits *)
Definition num_add_spec : Prop :=
  forall μ (a b : numA) r rl,
    limbsA a -> limbsA b -> valA a + valA b < 2 ^ ExpModel.num_bits ->
    eval_func ge μ f_num_add [:: a <:: [u64; NL]; b <:: [u64; NL]]
      = Some (r, rl) ->
    exists a' : numA, rl = [:: a' <:: [u64; NL]] /\
      limbsA a' /\ valA a' = valA a + valA b.

(* a = a - b, for a >= b *)
Definition num_sub_spec : Prop :=
  forall μ (a b : numA) r rl,
    limbsA a -> limbsA b -> valA b <= valA a ->
    eval_func ge μ f_num_sub [:: a <:: [u64; NL]; b <:: [u64; NL]]
      = Some (r, rl) ->
    exists a' : numA, rl = [:: a' <:: [u64; NL]] /\
      limbsA a' /\ valA a' = valA a - valA b.

(* a < b *)
Definition num_lt_spec : Prop :=
  forall μ (a b : numA) r rl,
    limbsA a -> limbsA b ->
    eval_func ge μ f_num_lt [:: a <:: [u64; NL]; b <:: [u64; NL]]
      = Some (r, rl) ->
    r = Vbool (valA a <? valA b) /\ rl = [::].

(* p = a w on NP limbs, for a limb w *)
Definition num_mul_small_spec : Prop :=
  forall μ (p : {ffun 'I_NP -> int64}) (a : numA) w r rl,
    limbsA a -> limb (Int64.unsigned w) ->
    eval_func ge μ f_num_mul_small
      [:: p <:: [u64; NP]; a <:: [u64; NL]; w <:: u64] = Some (r, rl) ->
    exists p' : {ffun 'I_NP -> int64}, rl = [:: p' <:: [u64; NP]] /\
      limbsA p' /\ valA p' = valA a * Int64.unsigned w.

(* r = floor(a b / 2^P), when it fits *)
Definition num_mulshr_spec : Prop :=
  forall μ (rr a b : numA) r rl,
    limbsA a -> limbsA b ->
    valA a * valA b < 2 ^ (ExpConsts.P + ExpModel.num_bits) ->
    eval_func ge μ f_num_mulshr
      [:: rr <:: [u64; NL]; a <:: [u64; NL]; b <:: [u64; NL]] = Some (r, rl) ->
    exists rr' : numA, rl = [:: rr' <:: [u64; NL]] /\
      limbsA rr' /\ valA rr' = ExpModel.mulshr (valA a) (valA b).

(** ** Bits *)

(* the number of bits of a *)
Definition num_bitlen_spec : Prop :=
  forall μ (a : numA) r rl,
    limbsA a ->
    eval_func ge μ f_num_bitlen [:: a <:: [u64; NL]] = Some (r, rl) ->
    r = Vint64 (Int64.repr (ExpModel.bitlen (valA a))) /\ rl = [::].

(* a = 2^f, for f < 192 *)
Definition num_pow2_spec : Prop :=
  forall μ (a : numA) f r rl,
    Int64.unsigned f < ExpModel.num_bits ->
    eval_func ge μ f_num_pow2 [:: a <:: [u64; NL]; f <:: u64] = Some (r, rl) ->
    exists a' : numA, rl = [:: a' <:: [u64; NL]] /\
      limbsA a' /\ valA a' = ExpModel.pow2 (Int64.unsigned f).

(* a = b mod 2^f, for f < 192 *)
Definition num_low_spec : Prop :=
  forall μ (a b : numA) f r rl,
    limbsA b -> Int64.unsigned f < ExpModel.num_bits ->
    eval_func ge μ f_num_low
      [:: a <:: [u64; NL]; b <:: [u64; NL]; f <:: u64] = Some (r, rl) ->
    exists a' : numA, rl = [:: a' <:: [u64; NL]] /\
      limbsA a' /\ valA a' = ExpModel.low (valA b) (Int64.unsigned f).

(* a = floor(v 2^e), for v < 2^53 and e < 128 *)
Definition num_scale_spec : Prop :=
  forall μ (a : numA) v e r rl,
    Int64.unsigned v < 2 ^ mant_bits -> Int64.signed e < scale_emax ->
    eval_func ge μ f_num_scale
      [:: a <:: [u64; NL]; v <:: u64; e <:: i64] = Some (r, rl) ->
    exists a' : numA, rl = [:: a' <:: [u64; NL]] /\
      limbsA a' /\
      valA a' = ExpModel.scale (Int64.unsigned v) (Int64.signed e).

(** ** The reduction *)

(* q = floor(n LN2 / 2^32), for n < 2^32 *)
Definition mul_ln2_spec : Prop :=
  forall μ (qq L2 : numA) nn r rl,
    words L2 = ExpTable.LN2 -> limb (Int64.unsigned nn) ->
    eval_func ge μ f_mul_ln2
      [:: qq <:: [u64; NL]; nn <:: u64; L2 <:: [u64; NL]] = Some (r, rl) ->
    exists qq' : numA, rl = [:: qq' <:: [u64; NL]] /\
      limbsA qq' /\ valA qq' = ExpModel.q (Int64.unsigned nn).

(* the first guess of n: floor(X INV / 2^185) *)
Definition guess_n_spec : Prop :=
  forall μ (X : numA) r rl,
    limbsA X ->
    eval_func ge μ f_guess_n [:: X <:: [u64; NL]] = Some (r, rl) ->
    r = Vint64 (Int64.repr (ExpModel.guess (valA X))) /\ rl = [::].

(** ** The core, the decision and the two entry points *)

(* y and hs[0] = hN as core_Z gives them; X q q1 r h t are scratch *)
Definition exp_core_spec : Prop :=
  forall μ xb (y : numA) (hs : {ffun 'I_1 -> int64}) (X q q1 rr h t : numA)
      Ta Ca L2 RM r rl,
    tables_ok Ta Ca L2 RM ->
    eval_func ge μ f_exp_core
      [:: xb <:: u64; y <:: [u64; NL]; hs <:: [i64; 1];
          X <:: [u64; NL]; q <:: [u64; NL]; q1 <:: [u64; NL];
          rr <:: [u64; NL]; h <:: [u64; NL]; t <:: [u64; NL];
          Ta <:: [[u64; NL]; TABn]; Ca <:: [[u64; NL]; CLn];
          L2 <:: [u64; NL]; RM <:: [u64; NL]] = Some (r, rl) ->
    exists rc (y' : numA) (hs' : {ffun 'I_1 -> int64})
        (X' q' q1' rr' h' t' : numA),
      r = Vint64 rc /\
      rl = [:: y' <:: [u64; NL]; hs' <:: [i64; 1];
               X' <:: [u64; NL]; q' <:: [u64; NL]; q1' <:: [u64; NL];
               rr' <:: [u64; NL]; h' <:: [u64; NL]; t' <:: [u64; NL]] /\
      (Int64.unsigned rc <> 0 ->
         ExpModel.core_Z (Int64.unsigned xb) = inl (Int64.unsigned rc)) /\
      (Int64.unsigned rc = 0 ->
         limbsA y' /\
         ExpModel.core_Z (Int64.unsigned xb) =
           inr (valA y', Int64.signed (hs' ord0))).

(* M and s[0] as exp_encl_Z gives them, on success *)
Definition exp_encl_bits_spec : Prop :=
  forall μ xb (M : {ffun 'I_NM -> int64}) (s : {ffun 'I_1 -> int64})
      Ta Ca L2 RM r rl,
    tables_ok Ta Ca L2 RM ->
    eval_func ge μ f_exp_encl_bits
      [:: xb <:: u64; M <:: [u64; NM]; s <:: [i64; 1];
          Ta <:: [[u64; NL]; TABn]; Ca <:: [[u64; NL]; CLn];
          L2 <:: [u64; NL]; RM <:: [u64; NL]] = Some (r, rl) ->
    exists rc (M' : {ffun 'I_NM -> int64}) (s' : {ffun 'I_1 -> int64}),
      r = Vint64 rc /\ rl = [:: M' <:: [u64; NM]; s' <:: [i64; 1]] /\
      (Int64.unsigned rc <> 0 ->
         ExpModel.exp_encl_Z (Int64.unsigned xb) = inl (Int64.unsigned rc)) /\
      (Int64.unsigned rc = 0 ->
         ExpModel.exp_encl_Z (Int64.unsigned xb) =
           inr (valW (words M'), Int64.signed (s' ord0))).

(* the decision decide_Z on y and hN; lo hi d t are scratch *)
Definition decide_spec : Prop :=
  forall μ (y : numA) hN (lo hi d t : numA) r rl,
    limbsA y ->
    2 ^ ExpConsts.P <= valA y < 2 ^ ExpModelBounds.y_bits ->
    - 2 ^ ExpModelBounds.hN_bits <= Int64.signed hN <=
      2 ^ ExpModelBounds.hN_bits ->
    eval_func ge μ f_decide
      [:: y <:: [u64; NL]; hN <:: i64; lo <:: [u64; NL]; hi <:: [u64; NL];
          d <:: [u64; NL]; t <:: [u64; NL]] = Some (r, rl) ->
    r = Vint64 (Int64.repr (ExpModel.decide_Z (valA y) (Int64.signed hN))) /\
    exists lo' hi' d' t' : numA,
      rl = [:: lo' <:: [u64; NL]; hi' <:: [u64; NL];
               d' <:: [u64; NL]; t' <:: [u64; NL]].

(* the filter: maybe_hard_Z *)
Definition maybe_hard_bits_spec : Prop :=
  forall μ xb Ta Ca L2 RM r rl,
    tables_ok Ta Ca L2 RM ->
    eval_func ge μ f_maybe_hard_bits
      [:: xb <:: u64; Ta <:: [[u64; NL]; TABn]; Ca <:: [[u64; NL]; CLn];
          L2 <:: [u64; NL]; RM <:: [u64; NL]] = Some (r, rl) ->
    r = Vint64 (Int64.repr (ExpModel.maybe_hard_Z (Int64.unsigned xb))) /\
    rl = [::].
