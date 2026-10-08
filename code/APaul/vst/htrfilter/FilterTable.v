(** * The table check and the C search_filter

    [check_raw] is the check of a table file (code/exptablekl): when it
    answers [true], every line of the file satisfies [line_ok].  On such a
    line, [search_filter] of [htr_filter.c], called with the parameters of
    the line ([k] coefficients of [l] words holding [B], the window
    [err = ERR], [j = 0 .. n-1]) and with [xb0] the bits of the double
    [x0] of the line and [neg] its sign, returns every hard-to-round input
    of the line ([hard] of the table, m = 43) among the first [kept]
    entries of [out], when the candidates of [search] fit in [out].

    As in ../VstTable.v, the statements read off the postcondition of
    [search_filter_spec]: what it says of [out] and of the returned [kept]
    is taken as hypothesis.  It holds of every call of [search_filter]
    proved through [search_filter_spec] ([body_search_filter],
    [htr_filter_funcs_correct]).

    The two filters meet as follows: [search] keeps [j] when the table of
    differences says that [x0 + j u] may be hard (TableCands.cands_line,
    m = 43); exp100's [maybe_hard_bits] answers 0 only on inputs that are
    not hard with m_hard = 42 (ExpSpec.maybe_hard_ok), and hard with
    m = 43 implies hard with m_hard = 42 ([Bits.hard_43_42]); the bits
    given to [maybe_hard_bits] are those of [x0 + j u]
    ([line_bits]). *)

Require Import VST.floyd.proofauto.
From Stdlib Require Import Rdefinitions.
Require Import HF.Spec_filter.
Require HF.Bits.
Require HtrVst.Words HtrVst.Fdiff HtrVst.Common HtrVst.Spec_search.
Require HtrVst.TableCands.
From APaulRocq Require HtrDefs.
From ExpTableKL Require ExpCheck ExpParse ExpProof ExpHard.
Require Exp100.ExpModel Exp100.ExpBits Exp100.ExpSpec.

Local Notation vwords := HtrVst.Common.vwords.
Local Notation coefs := HtrVst.Fdiff.coefs.
Local Notation cands := HtrVst.Spec_search.cands.
Local Notation line_ok := ExpCheck.line_ok.
Local Notation check_raw := ExpParse.check_raw.
Local Notation parse := ExpParse.parse.
Local Notation hard := ExpHard.hard.
Local Notation bp := ExpCheck.bp.
Local Notation uexp := ExpCheck.uexp.
Local Notation ERR := ExpCheck.ERR.
Local Notation xreal := Exp100.ExpBits.xreal.

(** ** The bits of the inputs of a line *)

(** On a line, with [x0] a normal double of bits [xb0] and [neg = 0]
    exactly when [x0 > 0], the bits given to [maybe_hard_bits] for [j]
    are those of [x0 + j u]. *)
Theorem line_bits S0 ex n k l B xb0 neg :
  line_ok S0 ex n k l B ->
  -1022 <= ex <= 1023 -> 0 <= xb0 < 2 ^ 64 ->
  xreal xb0 = (IZR S0 * bp (uexp ex))%R ->
  (neg = 0 <-> 0 < S0) ->
  forall j, 0 <= j < n ->
  xreal (xbj neg xb0 j) = (IZR (S0 + j) * bp (uexp ex))%R.
Proof.
  intros hok He Hxb Hx Hneg j Hj.
  destruct hok as (e & Hdrop & HS0 & HSL & Hsg & _).
  change ExpCheck.drop with 1 in *.
  assert (Hu : bp (uexp ex) = Flocq.Core.Raux.bpow Flocq.Core.Zaux.radix2
                                (ex - 52))
    by (unfold bp, uexp, ExpCheck.prec; f_equal; lia).
  rewrite Hu in *.
  (* S0 + j is between S0 and SL = S0 + n - 1: 53 bits, the sign of S0 *)
  assert (HSj : 2 ^ 52 <= Z.abs (S0 + j) < 2 ^ 53 /\ 0 < S0 * (S0 + j)).
  { destruct (Z.ltb_spec S0 0).
    - assert (S0 + n - 1 < 0) by nia.
      rewrite !Z.abs_neq in * by lia; split; [lia|nia].
    - assert (0 < S0) by (destruct (Z.eq_dec S0 0); [subst; lia|lia]).
      assert (0 < S0 + n - 1) by nia.
      rewrite !Z.abs_eq in * by lia; split; [lia|nia]. }
  destruct HSj as [HSj Hs].
  assert (Hxe : xb0 = HF.Bits.enc S0 ex)
    by (apply HF.Bits.enc_unique; auto).
  rewrite <- HF.Bits.xreal_enc by auto.
  f_equal.
  assert (He0 : 0 <= HF.Bits.enc (S0 + j) ex < 2 ^ 64)
    by (unfold HF.Bits.enc; destruct (S0 + j <? 0); lia).
  rewrite HF.Bits.enc_step in He0 |- * by auto.
  unfold xbj; rewrite Hxe.
  destruct (Z.ltb_spec S0 0); destruct (Z.eqb_spec neg 0);
    try (exfalso; lia); apply Z.mod_small; lia.
Qed.

(** [maybe_hard_bits] answers 0 or 1. *)
Lemma maybe_hard_Z_range xb : 0 <= Exp100.ExpModel.maybe_hard_Z xb <= 1.
Proof.
  unfold Exp100.ExpModel.maybe_hard_Z.
  destruct (Exp100.ExpModel.core_Z xb) as [r|[y hN]]; [lia|].
  unfold Exp100.ExpModel.decide_Z; cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    lia.
Qed.

(** ** On one line *)

Theorem vst_search_filter_line S0 ex n k l B :
  line_ok S0 ex n k l B ->
  forall (xs : list Z) (cap xb0 neg : Z) (os' : list val),
  (* the array holds B, each B_i in l words, the least significant first *)
  coefs xs l (Z.of_nat k) = B ->
  (* x0 = S0 u is a normal double, xb0 its bits, neg = 0 iff x0 > 0 *)
  -1022 <= ex <= 1023 -> 0 <= xb0 < 2 ^ 64 ->
  xreal xb0 = (IZR S0 * bp (uexp ex))%R ->
  (neg = 0 <-> 0 < S0) ->
  (* the postcondition of search_filter_spec, called with the k, l and n
     of the line and err = ERR: kept is what search_filter returns, out'
     is out after the call *)
  let kept := Zlength (kept_list l ERR xs (Z.of_nat k) n cap neg xb0) in
  sublist 0 kept os' =
    vwords (map Z.of_nat (kept_list l ERR xs (Z.of_nat k) n cap neg xb0)) ->
  (* the candidates of search fit in out *)
  Zlength (cands l ERR (coefs xs l (Z.of_nat k)) (Z.to_nat n)) <= cap ->
  (* every hard input j < n is among the first kept entries of out' *)
  forall j, 0 <= j < n ->
  hard (IZR (S0 + j) * bp (uexp ex))%R ->
  In (Vlong (Int64.repr j)) (sublist 0 kept os').
Proof.
  intros hok xs cap xb0 neg os' hB He Hxb Hx Hneg kept hout hcap j hj hhard.
  rewrite hout.
  (* j is a candidate of search *)
  assert (Hc : In (Z.to_nat j) (cands l ERR (coefs xs l (Z.of_nat k))
                                  (Z.to_nat n))).
  { rewrite hB. exact (HtrVst.TableCands.cands_line S0 ex n k l B hok j hj hhard). }
  (* maybe_hard_bits answers 1 on j *)
  assert (Hk : keep neg xb0 (Z.to_nat j) = true).
  { unfold keep; rewrite Z2Nat.id by lia; apply Z.eqb_eq.
    pose proof (maybe_hard_Z_range (xbj neg xb0 j)) as Hr.
    destruct (Z.eq_dec (Exp100.ExpModel.maybe_hard_Z (xbj neg xb0 j)) 0)
      as [H0|H0]; [|lia].
    exfalso.
    assert (Hw : 0 <= xbj neg xb0 j < 2 ^ 64)
      by (unfold xbj; apply Z.mod_pos_bound; lia).
    apply (Exp100.ExpSpec.maybe_hard_ok _ Hw H0).
    rewrite (line_bits S0 ex n k l B xb0 neg hok He Hxb Hx Hneg j hj).
    apply HF.Bits.hard_43_42; exact hhard. }
  (* so j is kept *)
  assert (Hin : In (Z.to_nat j) (kept_list l ERR xs (Z.of_nat k) n cap neg xb0)).
  { unfold kept_list; apply filter_In; split; [|exact Hk].
    rewrite firstn_all2; [exact Hc|].
    rewrite Zlength_correct in hcap; lia. }
  unfold vwords; rewrite !in_map_iff.
  exists (Int64.repr j); split; [reflexivity|].
  apply in_map_iff; exists j; split; [reflexivity|].
  rewrite <- (Z2Nat.id j) by lia; apply in_map; exact Hin.
Qed.

(** ** On a table *)

Theorem vst_search_filter_table ls :
  check_raw ls = true ->
  forall s, In s ls -> exists S0 ex n k l B,
  parse s = Some (S0, ex, n, k, l, B) /\ line_ok S0 ex n k l B /\
  forall (xs : list Z) (cap xb0 neg : Z) (os' : list val),
  (* the array holds B, each B_i in l words, the least significant first *)
  coefs xs l (Z.of_nat k) = B ->
  (* x0 = S0 u is a normal double, xb0 its bits, neg = 0 iff x0 > 0 *)
  -1022 <= ex <= 1023 -> 0 <= xb0 < 2 ^ 64 ->
  xreal xb0 = (IZR S0 * bp (uexp ex))%R ->
  (neg = 0 <-> 0 < S0) ->
  (* the postcondition of search_filter_spec, called with the k, l and n
     of the line and err = ERR *)
  let kept := Zlength (kept_list l ERR xs (Z.of_nat k) n cap neg xb0) in
  sublist 0 kept os' =
    vwords (map Z.of_nat (kept_list l ERR xs (Z.of_nat k) n cap neg xb0)) ->
  (* the candidates of search fit in out *)
  Zlength (cands l ERR (coefs xs l (Z.of_nat k)) (Z.to_nat n)) <= cap ->
  (* every hard input j < n is among the first kept entries of out' *)
  forall j, 0 <= j < n ->
  hard (IZR (S0 + j) * bp (uexp ex))%R ->
  In (Vlong (Int64.repr j)) (sublist 0 kept os').
Proof.
  intros hall s hs.
  destruct (ExpProof.check_rawP ls hall s hs)
    as (S0 & ex & n & k & l & B & hp & hok).
  exists S0, ex, n, k, l, B; split; [exact hp|split; [exact hok|]].
  exact (vst_search_filter_line S0 ex n k l B hok).
Qed.

Print Assumptions vst_search_filter_line.
Print Assumptions vst_search_filter_table.
