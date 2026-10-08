(** * num_pow2: a = 2^f, for f < 192

    num_pow2 calls num_zero, then writes 1 << (f mod 32) at limb f / 32.
    The call goes through [num_zero_local], a proof of [num_zero_spec]
    kept here so that this file does not wait for NumZeroProof.v.  The
    words lemmas (shifts, f / 32, f mod 32) also serve NumLowProof.v. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpModel.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** Words *)

Section Words.
Transparent Int64.modu Int64.divu Int64.repr Int64.unsigned Int.repr
  Int.unsigned Int.modu.

(* The amount of a shift by a word k, cast to 32 bits. *)
Lemma amt_unsigned k : (Int64.unsigned k < 64)%Z ->
  Int.unsigned (Int.modu (Int64.loword k) Int64.iwordsize') = Int64.unsigned k.
Proof.
  move=> Hk; have := Int64.unsigned_range k => Hr.
  rewrite /Int.modu /Int64.loword.
  have E : Int.unsigned Int64.iwordsize' = 64%Z by [].
  rewrite E Int.unsigned_repr.
  { by change Int.max_unsigned with 4294967295%Z; lia. }
  rewrite Z.mod_small; first lia.
  rewrite Int.unsigned_repr //; change Int.max_unsigned with 4294967295%Z; lia.
Qed.

(* x << k, for k < 64. *)
Lemma shl_amt x k : (Int64.unsigned k < 64)%Z ->
  Int64.unsigned (Int64.shl' x (Int.modu (Int64.loword k) Int64.iwordsize')) =
  ((Int64.unsigned x * 2 ^ Int64.unsigned k) mod 2 ^ 64)%Z.
Proof.
  move=> Hk; rewrite /Int64.shl' amt_unsigned // Z.shiftl_mul_pow2.
  - have := Int64.unsigned_range k; lia.
  - by rewrite Int64.unsigned_repr_eq.
Qed.

(* f / 32 and f mod 32. *)
Lemma divu32 x :
  Int64.unsigned (Int64.divu x (Int64.repr 32)) = (Int64.unsigned x / 32)%Z.
Proof.
  have Hr := Int64.unsigned_range x.
  have H0 := Z.div_pos (Int64.unsigned x) 32 (proj1 Hr) ltac:(lia).
  have H1 : (Int64.unsigned x / 32 <= Int64.unsigned x)%Z.
  { apply: Z.div_le_upper_bound; lia. }
  rewrite /Int64.divu.
  change (Int64.unsigned (Int64.repr 32)) with 32%Z.
  rewrite Int64.unsigned_repr //.
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

Lemma modu32 x :
  Int64.unsigned (Int64.modu x (Int64.repr 32)) = (Int64.unsigned x mod 32)%Z.
Proof.
  have := Z.mod_pos_bound (Int64.unsigned x) 32 ltac:(lia) => H.
  rewrite /Int64.modu.
  change (Int64.unsigned (Int64.repr 32)) with 32%Z.
  rewrite Int64.unsigned_repr //.
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

End Words.

(* 1 << (f mod 32) is 2^(f mod 32). *)
Lemma shl1_mod32 f :
  Int64.unsigned (Int64.shl' (Int64.repr 1)
    (Int.modu (Int64.loword (Int64.modu f (Int64.repr 32))) Int64.iwordsize'))
  = (2 ^ (Int64.unsigned f mod 32))%Z.
Proof.
  have Hm := Z.mod_pos_bound (Int64.unsigned f) 32 ltac:(lia).
  have Hp : (2 ^ (Int64.unsigned f mod 32) < 2 ^ 32)%Z.
  { apply: Z.pow_lt_mono_r; lia. }
  have Hp0 : (0 < 2 ^ (Int64.unsigned f mod 32))%Z.
  { apply: Z.pow_pos_nonneg; lia. }
  rewrite shl_amt modu32; first lia.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.mul_1_l Z.mod_small //.
  have : (2 ^ 32 <= 2 ^ 64)%Z by apply: Z.pow_le_mono_r; lia.
  lia.
Qed.

(** ** One word in a row of zeros *)

(* Word j of the zeros with w written at q. *)
Lemma setf0E (q : nat) (Hq : (q < NL)%nat) (w : int64) (j : 'I_NL) :
  Int64.unsigned ((setf [ffun=> Int64.zero] q w : numA) j) =
  if nat_of_ord j == q then Int64.unsigned w else 0.
Proof.
  by rewrite (setfP _ _ _ Hq); case: eqP => // _; rewrite ffunE.
Qed.

(* The j low limbs: w at its weight once q is passed. *)
Lemma pval_one (q : nat) (Hq : (q < NL)%nat) (w : int64) k : (k <= NL)%nat ->
  pval (setf [ffun=> Int64.zero] q w : numA) k =
  if (q < k)%nat then limb_base q * Int64.unsigned w else 0.
Proof.
  elim: k => [|k IH] Hk; first by rewrite pval0.
  rewrite (pvalSn _ _ Hk) (IH (ltnW Hk)) setf0E //=.
  case: (ltngtP q k) => [lt|gt|eq].
  - by rewrite ltnS (ltnW lt); ring.
  - by rewrite ltnS leqNgt gt /=; ring.
  - by rewrite -eq ltnS leqnn /=; ring.
Qed.

(* The number: w at the weight of limb q. *)
Lemma valA_one (q : nat) (Hq : (q < NL)%nat) (w : int64) :
  valA (setf [ffun=> Int64.zero] q w : numA) = limb_base q * Int64.unsigned w.
Proof. by rewrite -(pval_all (n := NL)) pval_one // Hq. Qed.

(* Every word is a limb when w is. *)
Lemma limbsA_one (q : nat) (Hq : (q < NL)%nat) (w : int64) :
  limb (Int64.unsigned w) -> limbsA (setf [ffun=> Int64.zero] q w : numA).
Proof. by move=> Hw j; rewrite setf0E //; case: eqP. Qed.

(** ** num_zero *)

(* The loop invariant of body_num_zero: after i rounds, the i low words
   of a are 0. *)
Lemma num_zero_local : num_zero_spec.
Proof.
move=> μ a0 r rl.
start; csteps.
inv I := { [:: a; i] } (fun (a : numA) (i : int64) =>
  (i:N <= NL)%nat /\ forall j : 'I_NL, (j < i:N)%nat -> a j = Int64.zero).
enter_loop I.
{ prove_inv; exsp. }
unfold_inv => - [Hi Ha].
csteps.
case LT: Int64.ltu => /=.
- csteps; rewrite ?setf_map.
  cret; split=> // _; split.
  { solve_loop_conditions. }
  prove_inv; exsp.
  { move: Hi; rewrite /NL; clia i0. }
  move=> j Hj; evalf.
  case: eqP => [_|ne] //.
  apply: Ha; have: (nat_of_ord j) <> (i0:N).
  { by move=> E; apply: ne; apply: val_inj. }
  move: Hi; rewrite /NL; clia i0.
- csteps; cret; split=> //= _; csteps; fin.
  rewrite/envC/=; do 2 f_equal; apply/ffunP => x; rewrite !ffunE.
  have Ei : (i0:N = 6)%nat by move: Hi; rewrite /NL; clia i0.
  congr Vint64; apply: Ha; rewrite Ei; exact: ltn_ord.
Qed.

(** ** num_pow2 *)

Theorem num_pow2_ok : num_pow2_spec.
Proof.
move=> μ a0 f r rl Hf.
have Hf' : 0 <= Int64.unsigned f < 192.
{ have := Int64.unsigned_range f; move: Hf.
  rewrite /ExpModel.num_bits /limb_bits /NL /=; lia. }
have E32 : Int64.eq (Int64.repr 32) Int64.zero = false by [].
start; csteps.
call num_zero_local => /= ->.
csteps; rewrite /divu64 E32 /=; csteps; rewrite /modu64 E32 /=; csteps.
fin; rewrite/envC/=.
eexists; split; first reflexivity.
have Hw : Int64.unsigned (Int64.shl' (Int64.repr 1)
    (Int.modu (Int64.loword (Int64.modu f (Int64.repr 32))) Int64.iwordsize'))
  = 2 ^ (Int64.unsigned f mod 32) by apply: shl1_mod32.
have Hm := Z.mod_pos_bound (Int64.unsigned f) 32 ltac:(lia).
split.
- apply: limbsA_one => //; rewrite Hw /limb /limb_bits; split.
  + apply: Z.pow_nonneg; lia.
  + apply: Z.pow_lt_mono_r; lia.
- rewrite valA_one // Hw /limb_base divu32 Z2Nat.id.
  { by apply: Z.div_pos; lia. }
  rewrite ExpModel.pow2E; first lia.
  have Hd : 0 <= Int64.unsigned f / 32 by apply: Z.div_pos; lia.
  rewrite -Z.pow_add_r /limb_bits; try lia.
  f_equal; have := Z.div_mod (Int64.unsigned f) 32; lia.
Qed.
