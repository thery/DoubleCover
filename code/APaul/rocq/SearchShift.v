(** * The search driven by Section 5's shifts

    [Search.search63_with] evaluates the degree-7 polynomial by Horner at
    the start of every chunk.  Here the chunk values are produced the way
    Section 5 of [doc/mourad.pdf] produces them: the value at chunk [k] is
    a degree-7 polynomial in [k], so one difference table of eight
    integers, advanced by [Shift.tstep] (seven additions), walks every
    chunk.  Horner runs eight times, once, to fill the first table.

    The main theorem, [search63s_withE], says the two drivers return the
    same list, for any per-chunk post-processing.  So everything proved or
    computed about [search63_with] (the examples of [Check.v]) holds for
    [search63s_with] without running it again. *)

From Stdlib Require Import ZArith.
From APaulRocq Require Import Cheb Search Check.
From mathcomp Require Import all_ssreflect all_algebra ssrZ zify.
From APaulRocq Require Import Shift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** ** Multiplying by an affine function raises the degree by one

    [Shift.is_poly_mulL] does it for a monic factor [c + n]; the chunk
    start is [c + 2^20 n], so we need any slope [a]. *)

Section DegreeAffine.

Variable R : nzRingType.
Implicit Types f : nat -> R.

Lemma diffn_scaler i (a : R) f n :
  diffn i (fun m => f m * a) n = diffn i f n * a.
Proof. by elim: i n => [//|i IH] n; rewrite !diffnS /diff !IH mulrBl. Qed.

Lemma is_poly_scaler d (a : R) f :
  is_poly d f -> is_poly d (fun n => f n * a).
Proof.
by move=> /is_polyP fd; apply/is_polyP => n; rewrite diffn_scaler fd mul0r.
Qed.

Lemma is_poly_ext d f g : (forall m, f m = g m) -> is_poly d f -> is_poly d g.
Proof.
move=> fg /is_polyP fd; apply/is_polyP => n.
by rewrite -(diffn_ext _ _ fg) fd.
Qed.

Lemma diff_mulA (c a : R) f n :
  diff (fun m => f m * (c + a * m%:R)) n
    = diff f n * (c + a + a * n%:R) + f n * a.
Proof.
rewrite /diff -natr1 [a * _]mulrDr mulr1 addrA [c + a + _]addrAC.
set u := c + a * n%:R.
by rewrite mulrBl [f n * (u + a)]mulrDr opprD addrA subrK.
Qed.

Lemma is_poly_mulA d (c a : R) f :
  is_poly d f -> is_poly d.+1 (fun n => f n * (c + a * n%:R)).
Proof.
move=> /is_polyP; elim: d c f => [|d IH] c f fd; apply/is_polyP => n.
  transitivity (diff (fun m => f m * (c + a * m%:R)) n.+1
              - diff (fun m => f m * (c + a * m%:R)) n); first by [].
  rewrite !diff_mulA.
  have f0 : forall m, diff f m = 0 by move=> m; apply: (fd m).
  by rewrite !f0 !mul0r !add0r -mulrBl -/(diff f n) f0 mul0r.
rewrite diffnSr.
have -> : diffn d.+2 (diff (fun m => f m * (c + a * m%:R))) n
        = diffn d.+2 (fun m => diff f m * (c + a + a * m%:R) + f m * a) n.
  by apply: diffn_ext => m; rewrite diff_mulA.
move: n; apply/is_polyP; apply: is_polyD.
  by apply: IH => m; rewrite -diffnSr; apply: (fd m).
by apply: is_poly_scaler; apply/is_polyP.
Qed.

End DegreeAffine.

(** ** The chunk values form a degree-7 polynomial in the chunk index *)

Lemma ZnatrE (n : nat) : (n%:R : Z) = Z.of_nat n.
Proof. by elim: n => [//|n IH]; rewrite -GRing.natr1 IH; lia. Qed.

(** The chunk start [v + k 2^log2N - Cc], written as [c + a k]. *)
Lemma polyV_deg (v : Z) : is_poly 7 (polyV v).
Proof.
pose c : Z := Z.sub v Cc.
pose a : Z := Z.pow 2 log2N.
pose l (k : nat) : Z := c + a * k%:R.
apply: (is_poly_ext (f :=
  (fun k => ((((((A7 * l k + C6) * l k + C5) * l k + C4) * l k + C3)
              * l k + C2) * l k + C1) * l k + C0))).
  move=> k; rewrite /l /c /a ZnatrE /polyV /polyHorner.
  have E : Z.sub (Z.add v (Z.mul (Z.of_nat k) (Z.pow 2 log2N))) Cc
         = (Z.sub v Cc) + (Z.pow 2 log2N) * Z.of_nat k.
    change (Z.sub (Z.add v (Z.mul (Z.of_nat k) (Z.pow 2 log2N))) Cc
          = Z.add (Z.sub v Cc) (Z.mul (Z.pow 2 log2N) (Z.of_nat k))).
    by ring.
  by rewrite E.
have cst e (b : Z) : is_poly e (fun _ : nat => b).
  by apply: (is_polyW (leq0n _)); apply: is_poly_const.
do 7! (apply: is_polyD; last exact: cst; apply: is_poly_mulA).
exact: cst.
Qed.

(** ** The first table, from eight Horner values

    [pdiff] turns the samples [f 0 .. f s] into [diff f 0 .. diff f (s-1)];
    the [i]-th entry of the table is the head of the [i]-th iterate. *)

Definition pdiff (s : seq Z) : seq Z :=
  mkseq (fun m => nth 0 s m.+1 - nth 0 s m) (size s).-1.

Definition tabl (s : seq Z) : seq Z :=
  mkseq (fun i => head 0 (iter i pdiff s)) (size s).

Lemma pdiff_mkseq (f : nat -> Z) s :
  pdiff (mkseq f s) = mkseq (diff f) s.-1.
Proof.
rewrite /pdiff size_mkseq; apply/(@eq_from_nth _ 0).
  by rewrite !size_mkseq.
rewrite size_mkseq => m ms.
have ms1 : (m < s)%N by rewrite (leq_trans ms) // leq_pred.
have ms2 : (m.+1 < s)%N by case: s ms {ms1} => [//|s] /=.
by rewrite !nth_mkseq.
Qed.

Lemma iter_pdiff (f : nat -> Z) s i :
  iter i pdiff (mkseq f s) = mkseq (diffn i f) (s - i).
Proof.
elim: i => [|i IH]; first by rewrite subn0.
by rewrite iterS IH pdiff_mkseq subnS.
Qed.

Lemma tablE (f : nat -> Z) : tabl (mkseq f 8) = dtab 7 f 0.
Proof.
rewrite /tabl size_mkseq /dtab; apply/(@eq_from_nth _ 0).
  by rewrite !size_mkseq.
by rewrite size_mkseq => i i8; rewrite !nth_mkseq // iter_pdiff.
Qed.

(** ** The walk *)

(** What the search does with one chunk, given its value [V]: the scan
    of [Search.search63_with], unchanged. *)
Definition chunk63 (post : list Z -> list Z) (k : nat) (V : Z) : list Z :=
  post (List.map (fun loc => Z.add (Z.mul (Z.of_nat k) (Z.pow 2 log2N)) loc)
            (Lefevre63.scan (seedA63 V) (seedB63 V) (twoE63 V) chunkN)).

(** [n] chunks from chunk [k], the table [t] holding chunk [k]'s. *)
Fixpoint walk (g : nat -> Z -> list Z) (k : nat) (t : seq Z) (n : nat)
  : list Z :=
  if n is n'.+1 then (g k (head 0 t) ++ walk g k.+1 (tstep t) n')%list
  else nil.

(** The first table: eight Horner evaluations. *)
Definition tab0 (v : Z) : seq Z := tabl (mkseq (polyV v) 8).

Definition search63s_with (post : list Z -> list Z) (v : Z) (n : nat)
  : list Z := walk (chunk63 post) 0 (tab0 v) n.

Definition search63s : Z -> nat -> list Z := search63s_with (fun l => l).

Definition hrc63s (v : Z) (n : nat) : list Z :=
  search63s_with (screen v) v n.

(** ** The walk is the search *)

Lemma walkE g f k n : is_poly 7 f ->
  walk g k (dtab 7 f k) n
    = List.concat (List.map (fun j => g j (f j)) (List.seq k n)).
Proof.
move=> fd; elim: n k => [//|n IH] k /=.
by rewrite tstepE // IH.
Qed.

Theorem search63s_withE post v n :
  search63s_with post v n = search63_with post v n.
Proof.
by rewrite /search63s_with /tab0 tablE walkE //; apply: polyV_deg.
Qed.

Corollary search63sE v n : search63s v n = search63 v n.
Proof. exact: search63s_withE. Qed.

Corollary hrc63sE v n : hrc63s v n = hrc63 v n.
Proof. exact: search63s_withE. Qed.

(** ** Examples, carried over from [Check.v] without computing *)

Local Open Scope Z_scope.

Example first_case_chunk_s : hrc63s v_first 1 = [:: 209342].
Proof. by rewrite hrc63sE first_case_chunk. Qed.

Example al_case_rejected_at_35_s : hrc63s v_al 1 = [::].
Proof. by rewrite hrc63sE al_case_rejected_at_35. Qed.
