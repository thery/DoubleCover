(** * The table check and the C search, through [line_ok]

    [check_raw] is the check of a table file (code/exptablekl): when it
    answers [true], every line of the file satisfies [line_ok]
    ([ExpProof.check_rawP]).  Here, on a line that satisfies [line_ok],
    the C [search] of [htr3.c], called with the parameters of the line
    ([k] coefficients of [l] words holding [B], the window
    [err = ERR = 0x600000], the inputs [j = 0 .. n-1]), returns every
    hard-to-round input of the line among the first [count] entries of
    [out], when [count] fits in [out].  So: [check_raw] -> [line_ok] -> no
    [hard] input is missed.

    The statements read off the postcondition of [search_spec]: what it
    says of [out] and of the returned [count] is taken as hypothesis.
    They hold of every call of [search] proved through [search_spec]
    ([body_search], [htr3_funcs_correct]). *)

Require Import VST.floyd.proofauto.
From Stdlib Require Import Rdefinitions.
Require Import HtrVst.Words HtrVst.Fdiff HtrVst.Common HtrVst.Spec_search.
Require HtrVst.TableCands.
From APaulRocq Require HtrDefs.
From ExpTableKL Require ExpCheck ExpParse ExpProof ExpHard.

Local Notation line_ok := ExpCheck.line_ok.
Local Notation check_raw := ExpParse.check_raw.
Local Notation parse := ExpParse.parse.
Local Notation hard := ExpHard.hard.
Local Notation bp := ExpCheck.bp.
Local Notation uexp := ExpCheck.uexp.
Local Notation ERR := ExpCheck.ERR.

(** [cands] of [Spec_search.v] is a copy of that of [HtrDefs.v]. *)
Lemma cands_HtrDefs l err ds n :
  cands l err ds n = HtrDefs.cands l err ds n.
Proof. reflexivity. Qed.

(** The first [c] entries of [out]: the first [c] candidates, when they
    fit in [out]. *)
Lemma in_out (cs : list nat) (cap : Z) (os' : list val) (j : nat) :
  Zlength cs <= cap ->
  sublist 0 (Z.min (Zlength cs) cap) os' =
    vwords (map Z.of_nat (firstn (Z.to_nat cap) cs)) ->
  In j cs -> In (Vlong (Int64.repr (Z.of_nat j))) (sublist 0 (Zlength cs) os').
Proof.
  intros Hcap Hout Hj.
  rewrite Z.min_l in Hout by lia; rewrite Hout.
  rewrite firstn_all2
    by (rewrite Zlength_correct in Hcap; lia).
  unfold vwords; rewrite !in_map_iff.
  exists (Int64.repr (Z.of_nat j)); split; [reflexivity|].
  apply in_map_iff; exists (Z.of_nat j); split; [reflexivity|].
  apply in_map; exact Hj.
Qed.

(** ** On one line *)

Theorem vst_search_line S0 ex n k l B :
  line_ok S0 ex n k l B ->
  forall (xs : list Z) (cap : Z) (os' : list val),
  (* the array holds B, each B_i in l words, the least significant first *)
  coefs xs l (Z.of_nat k) = B ->
  (* the postcondition of search_spec, called with the k, l and n of the
     line and err = ERR: count is what search returns, out' is out after
     the call *)
  let count := Zlength (cands l ERR (coefs xs l (Z.of_nat k))
                          (Z.to_nat n)) in
  sublist 0 (Z.min count cap) os' =
    vwords (map Z.of_nat
      (firstn (Z.to_nat cap)
        (cands l ERR (coefs xs l (Z.of_nat k)) (Z.to_nat n)))) ->
  (* every hard input j < n is among the first count entries of out' *)
  count <= cap ->
  forall j, 0 <= j < n ->
  hard (IZR (S0 + j) * bp (uexp ex))%R ->
  In (Vlong (Int64.repr j)) (sublist 0 count os').
Proof.
  intros hok xs cap os' hB count hout hcap j hj hhard.
  rewrite <- (Z2Nat.id j) by lia.
  apply (in_out _ cap); auto.
  rewrite hB, cands_HtrDefs.
  apply (TableCands.cands_line S0 ex n k l B hok j hj hhard).
Qed.

(** ** On a table *)

Theorem vst_search_table ls :
  check_raw ls = true ->
  forall s, In s ls -> exists S0 ex n k l B,
  parse s = Some (S0, ex, n, k, l, B) /\ line_ok S0 ex n k l B /\
  forall (xs : list Z) (cap : Z) (os' : list val),
  (* the array holds B, each B_i in l words, the least significant first *)
  coefs xs l (Z.of_nat k) = B ->
  (* the postcondition of search_spec, called with the k, l and n of the
     line and err = ERR *)
  let count := Zlength (cands l ERR (coefs xs l (Z.of_nat k))
                          (Z.to_nat n)) in
  sublist 0 (Z.min count cap) os' =
    vwords (map Z.of_nat
      (firstn (Z.to_nat cap)
        (cands l ERR (coefs xs l (Z.of_nat k)) (Z.to_nat n)))) ->
  (* every hard input j < n is among the first count entries of out' *)
  count <= cap ->
  forall j, 0 <= j < n ->
  hard (IZR (S0 + j) * bp (uexp ex))%R ->
  In (Vlong (Int64.repr j)) (sublist 0 count os').
Proof.
  intros hall s hs.
  destruct (ExpProof.check_rawP ls hall s hs)
    as (S0 & ex & n & k & l & B & hp & hok).
  exists S0, ex, n, k, l, B; split; [exact hp|split; [exact hok|]].
  exact (vst_search_line S0 ex n k l B hok).
Qed.

Print Assumptions vst_search_line.
Print Assumptions vst_search_table.
