(** * The table check and the Capla search_filter

    [check_raw] is the check of a table file (code/exptablekl): when it
    answers [true], every line of the file satisfies [line_ok].  On such a
    line, [search_filter] of ../htr_filter.b, called with the parameters
    of the line ([k] coefficients of [l] words holding [B], the window
    [err = ERR], [j = 0 .. n-1]), with [xb0] the bits of the double [x0]
    of the line and [neg] its sign, returns every
    hard-to-round input of the line ([hard] of the table, m = 43) among
    the first [kept] entries of [out], when the candidates of [search]
    fit in [out].  The Capla version of
    ../../../vst/htrfilter/FilterTable.v.

    The two filters meet as follows: [search] keeps [j] when the table of
    differences says that [x0 + j u] may be hard (TableCands.cands_line,
    m = 43); exp100's [maybe_hard_bits] answers 0 only on inputs that are
    not hard with m_hard = 42 (ExpSpec.maybe_hard_ok), and hard with
    m = 43 implies hard with m_hard = 42 ([Bits.hard_43_42]); the bits
    given to [maybe_hard_bits] are those of [x0 + j u]
    ([Bits.line_bits]).

    The section [Final] proves it from the statement [search_spec] of
    search (Specs.v); the external maybe_hard_bits is used through the
    axiom of ExtAxiom.v. *)

From compcert Require Import CaplaProof.
From Stdlib Require Import Reals.
From APaulRocq Require Import HtrDefs.
From Exp100 Require ExpModel ExpBits ExpHard ExpSpec.
From ExpTableKL Require ExpCheck ExpParse ExpProof ExpHard.
Require Import HtrFilterCapla.htr_filter HtrFilterCapla.HtrWords
  HtrFilterCapla.Specs HtrFilterCapla.FilterProof.
Require HtrFilterCapla.Bits HtrVst.TableCands.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

Local Notation line_ok := ExpCheck.line_ok.
Local Notation check_raw := ExpParse.check_raw.
Local Notation parse := ExpParse.parse.
Local Notation hard := ExpTableKL.ExpHard.hard.
Local Notation bp := ExpCheck.bp.
Local Notation uexp := ExpCheck.uexp.
Local Notation ERR := ExpCheck.ERR.
Local Notation xreal := Exp100.ExpBits.xreal.

(** ** Facts on words and on maybe_hard_Z *)

Lemma xb_range (xb : int64) : (0 <= Int64.unsigned xb < 2 ^ 64)%Z.
Proof.
by have := Int64.unsigned_range xb; change Int64.modulus with (2 ^ 64)%Z.
Qed.

Lemma unsigned_repr_small (z : Z) : (0 <= z < 2 ^ 64)%Z ->
  Int64.unsigned (Int64.repr z) = z.
Proof.
by move=> hz; apply: Int64.unsigned_repr; change Int64.max_unsigned with
  (2 ^ 64 - 1)%Z; lia.
Qed.

(* maybe_hard_bits answers 0 or 1. *)
Lemma maybe_hard_Z_range xb : (0 <= ExpModel.maybe_hard_Z xb <= 1)%Z.
Proof.
rewrite /ExpModel.maybe_hard_Z.
case: (ExpModel.core_Z xb) => [rc|[y hN]]; first lia.
rewrite /ExpModel.decide_Z; cbv zeta.
by repeat match goal with |- context [if ?b then _ else _] => case: b end;
  lia.
Qed.

(* Membership in a list of naturals, the two ways. *)
Lemma In_mem (x : nat) (s : seq.seq nat) : List.In x s -> x \in s.
Proof.
elim: s => [//|y s IH] /= [->|/IH H]; rewrite in_cons ?eqxx //.
by rewrite H orbT.
Qed.

(** ** On one line *)

Section Final.

Hypothesis search_full : search_spec.

Theorem capla_search_filter_line S0 ex n k l B :
  line_ok S0 ex n k l B ->
  forall μ (m cap : int64) (Bw : {ffun 'I_(Z.to_nat (Int64.unsigned m)) -> int64})
    (out : {ffun 'I_(Z.to_nat (Int64.unsigned cap)) -> int64})
    (xb0 neg : int64) r rl,
  (* the array holds B, each B_i in l words, the least significant first *)
  (k * Z.to_nat l <= Z.to_nat (Int64.unsigned m))%nat ->
  coefsA Bw (Z.to_nat l) k = B ->
  (* x0 = S0 u is a normal double, xb0 its bits, neg = 0 iff x0 > 0 *)
  (-1022 <= ex <= 1023)%Z ->
  xreal (Int64.unsigned xb0) = Rmult (IZR S0) (bp (uexp ex)) ->
  (Int64.unsigned neg = 0 <-> 0 < S0)%Z ->
  (* the run of search_filter, with the k, l and n of the line and
     err = ERR *)
  eval_func ge μ f_search_filter
    [:: Bw <:: [u64; Z.to_nat (Int64.unsigned m)]; m <:: u64;
        Int64.repr (Z.of_nat k) <:: u64; Int64.repr l <:: u64;
        Int64.repr n <:: u64; Int64.repr ERR <:: u64;
        out <:: [u64; Z.to_nat (Int64.unsigned cap)]; cap <:: u64;
        xb0 <:: u64; neg <:: u64]
    = Some (r, rl) ->
  exists (Bw' : {ffun 'I_(Z.to_nat (Int64.unsigned m)) -> int64})
    (out' : {ffun 'I_(Z.to_nat (Int64.unsigned cap)) -> int64}) kept,
    rl = [:: Bw' <:: [u64; Z.to_nat (Int64.unsigned m)];
             out' <:: [u64; Z.to_nat (Int64.unsigned cap)]] /\
    r = Vint64 kept /\
    (* when the candidates of search fit in out, every hard input j < n
       is among the first kept entries of out' *)
    ((size (cands l ERR B (Z.to_nat n)) <= Z.to_nat (Int64.unsigned cap))%nat ->
     forall j, (0 <= j < n)%Z ->
     hard (Rmult (IZR (S0 + j)) (bp (uexp ex))) ->
     exists i : 'I_(Z.to_nat (Int64.unsigned cap)),
       (i < Z.to_nat (Int64.unsigned kept))%nat /\ out' i = Int64.repr j).
Proof.
move=> hok μ m cap Bw out xb0 neg r rl hkl hB He Hx Hneg hrun.
have [n1 n53] := TableCands.line_ok_n S0 ex n k l B hok.
have [[k1 k13] [l1 l8]] := TableCands.line_ok_kl S0 ex n k l B hok.
have nk : Z.to_nat (Int64.unsigned (Int64.repr (Z.of_nat k))) = k.
  by rewrite unsigned_repr_small ?Nat2Z.id //; lia.
have nl : Z.to_nat (Int64.unsigned (Int64.repr l)) = Z.to_nat l.
  by rewrite unsigned_repr_small //; lia.
have nn : Z.to_nat (Int64.unsigned (Int64.repr n)) = Z.to_nat n.
  by rewrite unsigned_repr_small //; lia.
have herr : (2 * Int64.unsigned (Int64.repr ERR) <= Int64.max_unsigned)%Z.
  by vm_compute.
have uerr : Int64.unsigned (Int64.repr ERR) = ERR by vm_compute.
have := search_filter_ok search_full μ _ m erefl _ cap
  erefl Bw out (Int64.repr (Z.of_nat k)) (Int64.repr l) (Int64.repr n)
  (Int64.repr ERR) xb0 neg r rl.
rewrite /= nk nl nn.
move=> /(_ ltac:(apply/leP; lia) ltac:(apply/leP; lia) hkl herr hrun).
rewrite uerr hB.
have El : Z.of_nat (Z.to_nat l) = l by lia.
set ks := kept_list _ _ _ _ _ _ _.
move=> [Bw' [out' [-> [-> Hout]]]].
exists Bw', out', (Int64.repr (Z.of_nat (size ks))).
split; first by []; split; first by [].
move=> hcap j hj hhard.
have hj0 : (0 <= j)%Z by lia.
(* j is a candidate of search *)
have Hc : List.In (Z.to_nat j) (cands l ERR B (Z.to_nat n)).
  exact: TableCands.cands_line S0 ex n k l B hok j hj hhard.
(* maybe_hard_bits answers 1 on j *)
have Hk : keep (Int64.unsigned neg) (Int64.unsigned xb0) (Z.to_nat j).
  rewrite /keep (Z2Nat.id _ hj0).
  apply/Z.eqb_eq.
  have Hr := maybe_hard_Z_range
    (xbj (Int64.unsigned neg) (Int64.unsigned xb0) j).
  case: (Z.eq_dec (ExpModel.maybe_hard_Z
    (xbj (Int64.unsigned neg) (Int64.unsigned xb0) j)) 0) => [H0|H0];
    last by lia.
  exfalso.
  have Hw : (0 <= xbj (Int64.unsigned neg) (Int64.unsigned xb0) j < 2 ^ 64)%Z.
    by rewrite /xbj; apply: Z.mod_pos_bound; lia.
  apply: (Exp100.ExpSpec.maybe_hard_ok _ Hw H0).
  rewrite /xbj (Bits.line_bits S0 ex n k l B (Int64.unsigned xb0)
    (Int64.unsigned neg) hok He (xb_range xb0) Hx Hneg j hj).
  exact: Bits.hard_43_42 hhard.
(* so j is kept *)
have Hin : (Z.to_nat j \in ks).
  rewrite /ks /kept_list El mem_filter Hk /= take_oversize //.
  exact: In_mem.
have Hsz : (size ks <= Z.to_nat (Int64.unsigned cap))%nat.
  rewrite /ks /kept_list.
  rewrite size_filter; apply: leq_trans (count_size _ _) _.
  by rewrite size_take_min geq_minl.
have Hi : (seq.index (Z.to_nat j) ks < Z.to_nat (Int64.unsigned cap))%nat.
  by apply: (leq_trans _ Hsz); rewrite index_mem.
have Hu : Int64.unsigned (Int64.repr (Z.of_nat (size ks))) = Z.of_nat (size ks).
  by apply: unsigned_repr_small; have := xb_range cap; lia.
exists (Ordinal Hi); split.
  by rewrite /= Hu Nat2Z.id index_mem.
have Hix : (seq.index (Z.to_nat j) ks < size ks)%nat by rewrite index_mem.
by rewrite (Hout (Ordinal Hi) Hix) /= nth_index // (Z2Nat.id _ hj0).
Qed.

(** ** On a table *)

Theorem capla_search_filter_table ls :
  check_raw ls = true ->
  forall s, List.In s ls -> exists S0 ex n k l B,
  parse s = Some (S0, ex, n, k, l, B) /\ line_ok S0 ex n k l B /\
  forall μ (m cap : int64) (Bw : {ffun 'I_(Z.to_nat (Int64.unsigned m)) -> int64})
    (out : {ffun 'I_(Z.to_nat (Int64.unsigned cap)) -> int64})
    (xb0 neg : int64) r rl,
  (k * Z.to_nat l <= Z.to_nat (Int64.unsigned m))%nat ->
  coefsA Bw (Z.to_nat l) k = B ->
  (-1022 <= ex <= 1023)%Z ->
  xreal (Int64.unsigned xb0) = Rmult (IZR S0) (bp (uexp ex)) ->
  (Int64.unsigned neg = 0 <-> 0 < S0)%Z ->
  eval_func ge μ f_search_filter
    [:: Bw <:: [u64; Z.to_nat (Int64.unsigned m)]; m <:: u64;
        Int64.repr (Z.of_nat k) <:: u64; Int64.repr l <:: u64;
        Int64.repr n <:: u64; Int64.repr ERR <:: u64;
        out <:: [u64; Z.to_nat (Int64.unsigned cap)]; cap <:: u64;
        xb0 <:: u64; neg <:: u64]
    = Some (r, rl) ->
  exists (Bw' : {ffun 'I_(Z.to_nat (Int64.unsigned m)) -> int64})
    (out' : {ffun 'I_(Z.to_nat (Int64.unsigned cap)) -> int64}) kept,
    rl = [:: Bw' <:: [u64; Z.to_nat (Int64.unsigned m)];
             out' <:: [u64; Z.to_nat (Int64.unsigned cap)]] /\
    r = Vint64 kept /\
    ((size (cands l ERR B (Z.to_nat n)) <= Z.to_nat (Int64.unsigned cap))%nat ->
     forall j, (0 <= j < n)%Z ->
     hard (Rmult (IZR (S0 + j)) (bp (uexp ex))) ->
     exists i : 'I_(Z.to_nat (Int64.unsigned cap)),
       (i < Z.to_nat (Int64.unsigned kept))%nat /\ out' i = Int64.repr j).
Proof.
move=> /ExpProof.check_rawP hall s hs.
have [S0 [ex [n [k [l [B [hp hok]]]]]]] := hall s hs.
exists S0, ex, n, k, l, B; split => //; split => //.
exact: capla_search_filter_line.
Qed.

End Final.

Print Assumptions capla_search_filter_line.
Print Assumptions capla_search_filter_table.
