(** * A [true] answer of the checker gives the six conditions *)

From Stdlib Require Import ZArith Reals Lia Lra List Bool.
From Flocq Require Import Core.
From ExpTable Require Import ExpCheck ExpParse ExpTaylor ExpArith ExpEncl.

Open Scope R_scope.

(** The parameters leave room for the [2^-m] term of the window. *)
Lemma m_le_lbits : (m <= lbits)%Z.
Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.

(** [N u] is in [[2^xbin, 2^(xbin+1))] when [N] has 53 bits. *)
Lemma x_lo N : (2 ^ 52 <= N)%Z -> bp xbin <= IZR N * u.
Proof.
intros hN; unfold u, uexp, bp.
replace xbin with (52 + (xbin - 52))%Z at 1 by ring.
rewrite bpow_plus; apply Rmult_le_compat_r; [apply bpow_ge_0|].
rewrite <- IZR_Zpower by lia; apply IZR_le; exact hN.
Qed.

Lemma x_hi N : (N < 2 ^ 53)%Z -> IZR N * u < bp (xbin + 1).
Proof.
intros hN; unfold u, uexp, bp.
replace (xbin + 1)%Z with (53 + (xbin - 52))%Z by ring.
rewrite bpow_plus; apply Rmult_lt_compat_r; [apply bpow_gt_0|].
rewrite <- IZR_Zpower by lia; apply IZR_lt; exact hN.
Qed.

Theorem check_lineP M0 n B : check_line M0 n B = true -> line_ok M0 n B.
Proof.
unfold check_line.
destruct (encl M0) as [[[[mL0 fL0] mU0] fU0]|] eqn:h0;
  [|rewrite !andb_false_r; discriminate].
destruct (encl (M0 + n)) as [[[[mL1 fL1] mU1] fU1]|] eqn:h1;
  [|rewrite !andb_false_r; discriminate].
set (e := (Z.log2 mL0 + fL0)%Z).
destruct (coefs mL0 fL0 mU0 fU0 e 0 1 k) as [A|] eqn:hc;
  [|rewrite !andb_false_r; discriminate].
intros h.
apply andb_prop in h as [h hm].
apply andb_prop in hm as [hm hB].
apply andb_prop in hm as [hlt hw].
apply andb_prop in h as [h hlen].
apply andb_prop in h as [h h53].
apply andb_prop in h as [hn h52].
apply Z.leb_le in hn; apply Z.leb_le in h52; apply Z.ltb_lt in h53.
apply Nat.eqb_eq in hlen.
destruct (encl_ok _ _ _ _ _ h0) as [pL0 [pU0 [lo0 up0]]].
destruct (encl_ok _ _ _ _ _ h1) as [pL1 [pU1 [lo1 up1]]].
exists e; cbv zeta.
assert (hx1 : IZR (M0 + n) * u = IZR M0 * u + IZR n * u)
  by (rewrite plus_IZR; ring).
repeat split.
- (* 1. u is constant *)
  exact hn.
- apply x_lo; exact h52.
- apply x_hi; exact h53.
- (* 2. v is constant *)
  apply Rle_trans with (IZR mL0 * bp fL0); [apply log2_le; exact pL0|].
  exact lo0.
- apply Rle_lt_trans with (IZR mU1 * bp fU1); [exact up1|].
  apply lt2_ok; [lia|exact hlt].
- (* 3. (H_A), and the table holds P(0) .. P(k-1) *)
  exists A.
  destruct (coefs_ok _ _ _ _ _ _ _ _ _ _ eq_refl (conj lo0 up0) hc)
    as [hlA hA].
  split; [exact hlA|]; split; [exact hlen|]; split.
  + intros i hi; destruct (hA i hi) as [hA1 hA2]; split; [exact hA1|].
    exact hA2.
  + intros i hi.
    rewrite forallb_forall in hB.
    apply Z.eqb_eq, hB, in_seq; lia.
- (* 4. (H_T) *)
  intros j hj; rewrite hx1.
  apply HT_ok; [apply bpow_gt_0|lia].
- (* 5. (H_E) *)
  apply window_okP with (mU := mU1) (fU := fU1);
    [exact m_le_lbits|exact hn| |exact hw].
  split; [apply Rlt_le, exp_pos|exact up1].
Qed.

Theorem check_tableP t : check_table t = true -> table_ok t.
Proof.
unfold check_table; intros h.
apply andb_prop in h as [h hall].
apply andb_prop in h as [h2E _].
split; [apply Z.ltb_lt; exact h2E|].
intros M0 n B hin.
rewrite forallb_forall in hall.
apply check_lineP; exact (hall _ hin).
Qed.

(** The same on the text of the lines: each one reads as a line that
    satisfies the six conditions. *)
Theorem check_rawP ls : check_raw ls = true ->
  (2 * E < beta_l)%Z /\
  forall s, In s ls -> exists M0 n B,
    parse s = Some (M0, n, B) /\ line_ok M0 n B.
Proof.
unfold check_raw; intros h.
apply andb_prop in h as [h hall].
apply andb_prop in h as [h2E _].
split; [apply Z.ltb_lt; exact h2E|].
intros s hin.
rewrite forallb_forall in hall.
specialize (hall _ hin).
destruct (parse s) as [[[M0 n] B]|]; [|discriminate].
exists M0, n, B; split; [reflexivity|].
apply check_lineP; exact hall.
Qed.

