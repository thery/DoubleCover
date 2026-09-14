(* ---------------------------------------------------------------------------*)
(* Separation predicates on sequences of floats and the list-sum [sumR],      *)
(* split out of the addition development: P-nonoverlapping (Priest, Def. 1), magnitude    *)
(* order [sorted_mag], and the pairwise-ulp separation, with their head/tail  *)
(* manipulation lemmas.  Generic over the precision [p] and minimal exponent  *)
(* the development is generic in [p] (binary64 = [p = 53]).                                   *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Nonoverlap.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.

Let beta := radix2.

Open Scope R_scope.

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Local Notation pow e := (bpow beta e).
Local Notation u := (u p beta).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).

(* [u = 2^-p] (generic form of the roundoff unit [/2 * 2^(1-p)]).             *)
Lemma uE : u = pow (- p).
Proof.
rewrite /u.
have -> : (1 - p = 1 + - p)%Z by lia.
by rewrite bpow_plus bpow_1 /=; lra.
Qed.

(* Sum of a sequence, used to state exactness of the building blocks.         *)
Fixpoint sumR (l : seq R) : R := if l is a :: l' then a + sumR l' else 0.

(* Sum of absolute values, for the VSEB block bound (Theorem 2).              *)
Fixpoint sumRabs (l : seq R) : R :=
  if l is a :: l' then Rabs a + sumRabs l' else 0.

Lemma sumRabs_ge0 l : 0 <= sumRabs l.
Proof. elim: l => /= [|a l IH]; first lra. by have := Rabs_pos a; lra. Qed.

Lemma abs_sumR_le l : Rabs (sumR l) <= sumRabs l.
Proof.
elim: l => /= [|a l IH]; first by rewrite Rabs_R0; lra.
by apply: Rle_trans (Rabs_triang _ _) _; lra.
Qed.

(* P-nonoverlapping (Priest, Definition 1): |x_{i+1}| < ulp (x_i), with a     *)
(* guard letting the successor be ZERO.                                       *)
(*                                                                            *)
(* The guard is FORCED by FLX, where [ulp 0 = 0] (there is no exponent floor).*)
(* Without it, a zero term makes the condition [|x_{i+1}| < 0] unsatisfiable, *)
(* so [[0; 0]] would not be P-nonoverlapping -- yet [[0; 0]] is exactly what  *)
(* [vseb (vecSum [x; -x])] returns, on an input meeting every hypothesis of   *)
(* Theorem 6.  It would also deny [(1, 0, 0)] the status of a TW.             *)
(*                                                                            *)
(* This does NOT weaken the FLT reading: there [ulp 0 = pow emin], and the    *)
(* smallest nonzero format value IS [pow emin], so [|x_{i+1}| < ulp 0] already*)
(* forces [x_{i+1} = 0] on format lists.  The guard merely writes out what the*)
(* [ulp 0 = pow emin] accident was silently doing.  Note it still REJECTS     *)
(* [[0; big]] (the [ulp 0] bound bites when the successor is nonzero), so it  *)
(* is strictly stronger than the zero-FILTERING reading of Definition 3 --    *)
(* which matters, since [isTW] is a PRECONDITION of RoundTW (Thm 5)/3Prod.    *)
Definition Pnonoverlap (l : seq R) : Prop :=
  forall i, (i.+1 < size l)%N ->
    nth 0 l i.+1 = 0 \/ Rabs (nth 0 l i.+1) < ulp (nth 0 l i).

(* Dropping the head of a P-nonoverlapping sequence keeps it P-nonoverlapping.*)
Lemma Pnonoverlap_cons a l : Pnonoverlap (a :: l) -> Pnonoverlap l.
Proof. by move=> alP i iLs; apply: (alP i.+1). Qed.

(* A trailing zero is harmless: the only new constraint has a zero successor, *)
(* which is exactly what the guard covers.  (Under the unguarded reading this *)
(* would need [0 < ulp (last l)], i.e. a nonzero last element -- false in     *)
(* general, and not even true for [l = [:: 0]] under FLX.)                    *)
Lemma Pnonoverlap_rcons0 l : Pnonoverlap l -> Pnonoverlap (rcons l 0).
Proof.
move=> Pl i; rewrite size_rcons ltnS leq_eqVlt => /orP[/eqP Hi|Hi].
  by left; rewrite nth_rcons -Hi ltnn eqxx.
by rewrite !nth_rcons Hi (ltn_trans (ltnSn i) Hi); apply: Pl.
Qed.

(* Eliminator: at a NONZERO successor the guard cannot fire, so Priest's      *)
(* strict bound is recovered.  This is how nearly every consumer uses         *)
(* [Pnonoverlap] -- the guard only ever matters for a zero successor.         *)
Lemma Pnonoverlap_lt l i : Pnonoverlap l -> (i.+1 < size l)%N ->
  nth 0 l i.+1 <> 0 -> Rabs (nth 0 l i.+1) < ulp (nth 0 l i).
Proof. by move=> Pl Hi Hn0; case: (Pl i Hi). Qed.

(* ---- moving a guarded bound to a bigger neighbour ------------------------ *)
(* Under FLX [ulp 0 = 0], so [Pnonoverlap]/[pairwise_ulp] carry a "successor  *)
(* is zero" guard, and every consumer must transport the guard along with     *)
(* the bound.  These three shapes are what the consumers actually need; they  *)
(* keep the guard out of the client proofs.                                   *)

(* [y] stays under the ulp of anything at least as big as [b].                *)
Lemma guarded_ulp_le (y b a : R) :
  (y = 0 \/ Rabs y < ulp b) -> Rabs b <= Rabs a ->
  y = 0 \/ Rabs y < ulp a.
Proof.
move=> [->|Hy] Hba; first by left.
by right; apply: Rlt_le_trans Hy _; apply: (ulp_le beta fexp).
Qed.

(* Same, when [y] is dominated by a value that is itself under [ulp a].       *)
Lemma guarded_ulp_abs_le (y c a : R) :
  Rabs y <= Rabs c -> (c = 0 \/ Rabs c < ulp a) ->
  y = 0 \/ Rabs y < ulp a.
Proof.
move=> Hyc [Hc0|Hc].
  by left; move: Hyc; rewrite Hc0 Rabs_R0; split_Rabs; lra.
by right; apply: Rle_lt_trans Hyc Hc.
Qed.

(* Two guarded steps compose: [uls]-style descent through a format [c].  A    *)
(* zero [c] would force [y] under [ulp 0 = 0], which is what makes the        *)
(* middle guard collapse.                                                     *)
Lemma guarded_ulp_trans (y c a : R) :
  format c -> (y = 0 \/ Rabs y < ulp c) -> (c = 0 \/ Rabs c < ulp a) ->
  y = 0 \/ Rabs y < ulp a.
Proof.
move=> Fc [->|Hy] Hc; first by left.
have cn0 : c <> 0
  by move=> c0; move: Hy; rewrite c0 ulp_FLX_0; split_Rabs; lra.
right; case: Hc => [c0|Hc]; first by case: cn0.
apply: Rlt_trans Hc; apply: Rlt_le_trans Hy _.
by apply: ulp_le_abs.
Qed.

(* The two preconditions of Theorem 6 on the merged sequence.                 *)

(* --- magnitude order -----------------------------------------------------  *)
(* [sorted_mag l]: the sequence is non-increasing in magnitude.               *)
Definition sorted_mag (l : seq R) : Prop :=
  forall i, (i.+1 < size l)%N -> Rabs (nth 0 l i.+1) <= Rabs (nth 0 l i).

(* Peel the head of a [sorted_mag] sequence: the first step plus the tail.    *)
Lemma sorted_mag_cons a1 a2 l :
  sorted_mag [:: a1,  a2 & l] -> Rabs a2 <= Rabs a1 /\ sorted_mag (a2 :: l).
Proof.
move=> a1a2lM; split; first by apply: (a1a2lM 0%N).
by move=> n Hn; apply: (a1a2lM n.+1).
Qed.

(* Cons a larger-magnitude head onto a [sorted_mag] sequence.                 *)
Lemma sorted_mag_cons_inv a1 a2 l :
  Rabs a2 <= Rabs a1 -> sorted_mag (a2 :: l) -> sorted_mag [:: a1,  a2 & l].
Proof. by move=> a2La1 a2lN [//|i Hi]; apply: (a2lN i). Qed.

(* Replace the head by an even larger one (still [sorted_mag]).               *)
Lemma sorted_mag_le a1 a2 l :
  sorted_mag (a1 :: l) -> Rabs a1 <= Rabs a2 -> sorted_mag (a2 :: l).
Proof.
case: l => // a3 l /sorted_mag_cons[a1La3 a3lS] a1La2.
by apply: sorted_mag_cons_inv => //; lra.
Qed.

(* Dropping the LAST entry preserves the magnitude order.                     *)
Lemma sorted_mag_rcons m x : sorted_mag (rcons m x) -> sorted_mag m.
Proof.
move=> H i Hi.
have Hi1 : (i < size m)%N by apply: ltn_trans Hi.
have Hi' : (i.+1 < size (rcons m x))%N by rewrite size_rcons ltnS ltnW.
by have := H i Hi'; rewrite !nth_rcons Hi Hi1.
Qed.

(* --- pairwise ulp separation ---------------------------------------------  *)
(* [pairwise_ulp l]: each term is below ulp of the term two positions before; *)
(* this tolerates a single overlap but never two in a row.  Same zero guard   *)
(* as [Pnonoverlap], forced by [ulp 0 = 0] under FLX: without it a TW with    *)
(* zero limbs is excluded outright, e.g. [Merge (1,0,0) (1,0,0)] gives        *)
(* [[1; 1; 0; 0; 0; 0]], whose [i = 2] instance would demand [0 < ulp 0].     *)
Definition pairwise_ulp (l : seq R) : Prop :=
  forall i, (i.+2 < size l)%N ->
    nth 0 l i.+2 = 0 \/ Rabs (nth 0 l i.+2) < ulp (nth 0 l i).

(* Dropping the LAST entry preserves the pairwise-ulp separation.             *)
Lemma pairwise_ulp_rcons m x : pairwise_ulp (rcons m x) -> pairwise_ulp m.
Proof.
move=> H i Hi.
have Hi1 : (i < size m)%N by apply: ltn_trans Hi; apply: ltnW.
have Hi' : (i.+2 < size (rcons m x))%N by rewrite size_rcons ltnS ltnW.
by have := H i Hi'; rewrite !nth_rcons Hi Hi1.
Qed.

(* Eliminator, as [Pnonoverlap_lt]: a nonzero term two positions on gets the  *)
(* strict bound back.                                                         *)
Lemma pairwise_ulp_lt l i : pairwise_ulp l -> (i.+2 < size l)%N ->
  nth 0 l i.+2 <> 0 -> Rabs (nth 0 l i.+2) < ulp (nth 0 l i).
Proof. by move=> Pl Hi Hn0; case: (Pl i Hi). Qed.

(* Cons a head given its (guarded) bound against the third term.              *)
Lemma pairwise_ulp_cons_inv a1 a2 a3 l :
  (a3 = 0 \/ Rabs a3 < ulp a1) ->
  pairwise_ulp (a2 :: a3 :: l) -> pairwise_ulp [:: a1, a2, a3 & l].
Proof. by move=> a2La1 a2lN [//|i Hi]; apply: (a2lN i). Qed.

(* Cons a head onto any tail: the only new obligation is the third-term bound.*)
Lemma pairwise_ulp_cons1_inv a l :
  pairwise_ulp l  ->
  ((1 < size l)%N -> nth 0 l 1 = 0 \/ Rabs(nth 0 l 1) < ulp a) ->
  pairwise_ulp (a :: l).
Proof.
case: l => // b [|c l] //= bclP /(_ isT) cLua.
by apply: pairwise_ulp_cons_inv.
Qed.



(* P-nonoverlap separation implies magnitude order, zeros included.           *)
(* Depends on:                                                                *)
(*   - [ulp_le_abs] : x <> 0 -> format x -> ulp x <= Rabs x  (Flocq.Core.Ulp) *)
(*     for the x <> 0 case (then Rabs y < ulp x <= Rabs x);                   *)
(*   - [ulp_FLT_0] + [format_lt_ulp_0] above for the x = 0 case (then y = 0). *)
Lemma format_lt_ulp_le x y :
  format x -> format y -> Rabs y < ulp x -> Rabs y <= Rabs x.
Proof.
move=> xF yF yLux.
have x_neq0 : x <> 0.
  by move=> x_eq0; move: yLux; rewrite x_eq0 ulp_FLX_0; split_Rabs; lra.
apply: Rle_trans (Rlt_le _ _ yLux) _.
by apply: ulp_le_abs.
Qed.

(* P-nonoverlap implies pairwise-ulp separation on a single (format) list,    *)
(* zeros included: |x_{i+2}| < ulp x_{i+1} <= ulp x_i, the last step via      *)
(* [ulp_le_abs] (and [format_lt_ulp_0] when x_{i+1} = 0).                     *)
Lemma Pnonoverlap_imp_pairwise_ul l :
  {in l,  forall z : R, format z} -> Pnonoverlap l -> pairwise_ulp l.
Proof.
elim: l => //= a [|b [|c l]] // IH abclF abclP.
apply: pairwise_ulp_cons_inv.
  have /= := abclP 1%N isT => -[c0|cLub]; first by left.
  right.
  (* [b = 0] is impossible here: it would make [ulp b = 0] under FLX, and     *)
  (* [cLub] already puts [Rabs c] strictly below it.                          *)
  have /= := abclP 0%N isT => -[b0|bLua].
    by move: cLub; rewrite b0 ulp_FLX_0; split_Rabs; lra.
  apply: Rle_lt_trans bLua.
  apply: Rle_trans (Rlt_le _ _ cLub) _.
  apply: ulp_le_abs => //.
    by move=> b_eq0; move: cLub; rewrite b_eq0 ulp_FLX_0; split_Rabs; lra.
  by apply: abclF; rewrite !inE eqxx !orbT.
apply: IH.
  by move=> z zIl; apply: abclF; rewrite inE zIl orbT.
by move=> i iLs; apply: (abclP i.+1).
Qed.


Definition ufp (x : R) : R := pow (mag beta x - 1).

Lemma ufp_gt_0 x : 0 < ufp x.
Proof. by apply: bpow_gt_0. Qed.

(* [ufp x <= |x| < 2 * ufp x]: |x| lies in one binade above [ufp x].          *)
Lemma ufp_le_abs x : x <> 0 -> ufp x <= Rabs x.
Proof. exact: bpow_mag_le. Qed.

Lemma abs_lt_2ufp x : Rabs x < 2 * ufp x.
Proof.
rewrite /ufp; set m := mag beta x.
have := bpow_mag_gt beta x; rewrite -/m => H.
suff -> : (2 * bpow beta (m - 1) = bpow beta m)%R by [].
have -> : (2 = IZR beta)%R by rewrite /=; lra.
by rewrite -bpow_plus_1; congr bpow; lia.
Qed.

(* One P-nonoverlap step makes [ufp] shrink by a factor [u]: if [|y| < ulp x] *)
(* (Priest's [Pnonoverlap]) and [x] is not near underflow, then               *)
(* [ufp y <= u * ufp x].  This is the geometric decay behind Theorem 3's tail *)
(* bound [2 u^3 + 4.2 u^4] (each kept term is [u] times finer than the last). *)
Lemma ufp_ulp_step x y : 
  x <> 0 -> y <> 0 -> Rabs y < ulp x -> ufp y <= u * ufp x.
Proof.
move=> xn0 yn0 Hxy.
have Hmagy : (mag beta y <= mag beta x - p)%Z.
  apply: mag_le_bpow => //.
  apply: Rlt_le_trans Hxy _.
  rewrite ulp_neq_0 //.
  by rewrite /cexp /FLX_exp; lra.
by rewrite /ufp uE -bpow_plus; apply: bpow_le; lia.
Qed.

(* Definition 2 (Fabiano): [l] is F-nonoverlapping when each term is at most  *)
(* half the [uls] of its predecessor.  This is Fabiano's separation (more     *)
(* restrictive than Shewchuk's ulp-nonoverlapping); it is the invariant that  *)
(* VecSum establishes (Thm 1) and that VSEB consumes (Thm 2) to yield a       *)
(* P-nonoverlapping output.                                                   *)
(* Zero-free reading (paper Def. 3, "WLOG no zeros"): each NONZERO term is at *)
(* most half the [uls] of the PREVIOUS nonzero term.  Formalised by carrying  *)
(* the last nonzero as [prev] and skipping zeros -- a zero imposes no         *)
(* constraint yet cannot shield a large successor, since the bound is against *)
(* the last nonzero, not the immediate predecessor.  (The old immediate-      *)
(* predecessor guard was too weak: it accepted [1; 0; 1.5].)                  *)
Fixpoint Fnonoverlap_aux (prev : R) (l : seq R) : Prop :=
  if l is x :: l' then
    (x <> 0 -> Rabs x <= / 2 * uls prev) /\
    Fnonoverlap_aux (if Req_EM_T x 0 then prev else x) l'
  else True.

(* Paper Definition 3 (nonoverlapping "wIZ", with interleaving zeros): delete *)
(* the zeros, then require plain F-nonoverlap (Definition 2) on the survivors.*)
(* The first survivor has no predecessor, hence no constraint -- this is what *)
(* [Fnonoverlap_aux] on the zero-free list encodes (it never takes its        *)
(* zero-skipping branch).  Filtering (rather than anchoring [prev] at a       *)
(* possibly-zero head) is what makes leading zeros harmless, matching the     *)
(* paper: VecSum can emit [0; 0; e] by cancelling two equal-magnitude leading *)
(* terms, and the paper drops those zeros before checking nonoverlap.         *)
Definition Fnonoverlap (l : seq R) : Prop :=
  if [seq x <- l | x != 0 :> R] is x :: l' then Fnonoverlap_aux x l' else True.

(* A zero next element is skipped (the vacuous conjunct drops, [prev] stays). *)
Lemma Fnonoverlap_aux_cons0 prev l :
  Fnonoverlap_aux prev (0 :: l) <-> Fnonoverlap_aux prev l.
Proof.
have E0 : (if Req_EM_T (0 : R) 0 then prev else 0) = prev.
  by case: (Req_EM_T 0 0) => [_|H] //; case: (H erefl).
rewrite /= E0; split; first by move=> [_ H].
move=> H; split; last exact: H.
by move=> H0; case: (H0 erefl).
Qed.

(* Prepend a nonzero [x] bounded by [1/2 uls prev].                           *)
Lemma Fnonoverlap_aux_consN prev x l :
  x <> 0 -> Rabs x <= / 2 * uls prev -> Fnonoverlap_aux x l ->
  Fnonoverlap_aux prev (x :: l).
Proof.
move=> xn0 xB Hl.
have Ex : (if Req_EM_T x 0 then prev else x) = x.
  by case: (Req_EM_T x 0) => [xe0|_] //; case: (xn0 xe0).
rewrite /= Ex; split; last exact: Hl.
by move=> _; exact: xB.
Qed.

(* [prev] enters only through [uls prev], monotonically: coarsening [prev]    *)
(* ([uls prev <= uls prev']) preserves [Fnonoverlap_aux].  Used by the VSEB   *)
(* step lemmas, where the running term is replaced by a coarser one.          *)
Lemma Fnonoverlap_aux_prev prev prev' l :
  uls prev <= uls prev' -> Fnonoverlap_aux prev l -> Fnonoverlap_aux prev' l.
Proof.
elim: l prev prev' => [|x l IH] prev prev' Hle //= [Hx Hrec]; split.
  by move=> xn0; apply: Rle_trans (Hx xn0) _; lra.
have [xe0|xne0] := Req_dec x 0.
  have E : forall v : R, (if Req_EM_T x 0 then v else x) = v.
    by move=> v; case: (Req_EM_T x 0) => [_|H] //; case: (H xe0).
  by rewrite !E in Hrec *; apply: IH Hrec.
have E : forall v : R, (if Req_EM_T x 0 then v else x) = x.
  by move=> v; case: (Req_EM_T x 0) => [xe0|_] //; case: (xne0 xe0).
by rewrite !E in Hrec *; apply: (IH x x) Hrec; apply: Rle_refl.
Qed.

(* [Fnonoverlap_aux] never depends on the zeros in its list: it skips them.   *)
(* Hence checking it on the zero-filtered list is the same as on the list --  *)
(* the bridge between the recursive [Fnonoverlap_aux] and the filtering       *)
(* [Fnonoverlap].                                                             *)
Lemma Fnonoverlap_aux_filter prev l :
  Fnonoverlap_aux prev [seq x <- l | x != 0 :> R] <-> Fnonoverlap_aux prev l.
Proof.
elim: l prev => [|x l IH] prev //=.
have [xe0|xne0] := Req_dec x 0.
  rewrite xe0 eqxx /=.
  have E : (if Req_EM_T (0 : R) 0 then prev else 0) = prev by case: Req_EM_T.
  rewrite E; split.
    by move=> /IH H; split; [move=> H0; case: (H0 erefl) | exact: H].
  by move=> [_ /IH].
have xnb : (x != 0 :> R) by apply/eqP.
rewrite xnb /=.
have E : (if Req_EM_T x 0 then prev else x) = x by case: Req_EM_T.
rewrite !E; split; move=> [Hx Hrec]; split; try exact: Hx; by apply/IH.
Qed.

(* Dropping a head keeps [Fnonoverlap] (filtering only shrinks the list).     *)
Lemma Fnonoverlap_cons x l : Fnonoverlap (x :: l) -> Fnonoverlap l.
Proof.
rewrite /Fnonoverlap /=; case: (x =P 0) => [->|/eqP xnb]; first by rewrite /=.
rewrite /=; case E : [seq y <- l | y != 0] => [|y l'] //=.
have yn0 : (y != 0 :> R).
  by move: (mem_head y l'); rewrite -E mem_filter => /andP[].
have -> : (if Req_EM_T y 0 then x else y) = y.
  by case: Req_EM_T => [y0|//]; rewrite y0 eqxx in yn0.
by move=> [_].
Qed.

(* Constructor: a nonzero head [x] with an [Fnonoverlap_aux x l] tail builds  *)
(* [Fnonoverlap (x :: l)] (the nonzero head survives filtering and becomes the*)
(* first, unconstrained, term).                                               *)
Lemma Fnonoverlap_consN x l :
  x <> 0 -> Fnonoverlap_aux x l -> Fnonoverlap (x :: l).
Proof.
move=> xn0 H; rewrite /Fnonoverlap /=.
have -> : (x != 0 :> R) by apply/eqP.
by rewrite /=; apply/Fnonoverlap_aux_filter.
Qed.

(* Eliminator (inverse of [Fnonoverlap_consN]): a nonzero head [x] gives an   *)
(* [Fnonoverlap_aux x l] tail.                                                *)
Lemma Fnonoverlap_consE x l :
  x <> 0 -> Fnonoverlap (x :: l) -> Fnonoverlap_aux x l.
Proof.
move=> xn0; rewrite /Fnonoverlap /=.
have -> : (x != 0 :> R) by apply/eqP.
by rewrite /= => /Fnonoverlap_aux_filter.
Qed.

(* An interior zero after the head is invisible to [Fnonoverlap] (it is       *)
(* filtered out): [Fnonoverlap (x :: 0 :: l) <-> Fnonoverlap (x :: l)].       *)
Lemma Fnonoverlap_drop0 x l :
  Fnonoverlap (x :: 0 :: l) <-> Fnonoverlap (x :: l).
Proof.
rewrite /Fnonoverlap /=.
by have -> : ((0 : R) != 0) = false by rewrite eqxx.
Qed.

(* Head bound: the second element is at most [1/2 uls] of the first, provided *)
(* the first is nonzero (a zero head is dropped by [Fnonoverlap]).            *)
Lemma Fnonoverlap_head2 a b l :
  Fnonoverlap (a :: b :: l) -> a <> 0 -> b <> 0 -> Rabs b <= / 2 * uls a.
Proof.
move=> H an0 bn0; move: H; rewrite /Fnonoverlap /=.
have -> : (a != 0 :> R) by apply/eqP.
have -> : (b != 0 :> R) by apply/eqP.
by move=> /= [H _]; exact: H bn0.
Qed.

(* Drop the [a, b] prefix: the tail keeps [Fnonoverlap_aux] with [prev = b]   *)
(* (when [b <> 0]); [a] may be zero (it is filtered out) with no consequence. *)
Lemma Fnonoverlap_tail a b l :
  Fnonoverlap (a :: b :: l) -> b <> 0 -> Fnonoverlap_aux b l.
Proof.
move=> H bn0; apply/Fnonoverlap_aux_filter.
have bnb : (b != 0 :> R) by apply/eqP.
have Eb : (if Req_EM_T b 0 then a else b) = b by case: Req_EM_T.
move: H; rewrite /Fnonoverlap /=; case: (a =P 0) => [->|/eqP _].
  by rewrite /= bnb /=.
by rewrite /= bnb /= Eb => -[_].
Qed.

Lemma Fnonoverlap_imm l : Fnonoverlap l ->
  forall i, (i.+1 < size l)%N -> nth 0 l i <> 0 ->
    Rabs (nth 0 l i.+1) <= / 2 * uls (nth 0 l i).
Proof.
elim: l => [|x l IH] Fl [|i] //=.
  case: l Fl IH => [|d l'] //= Fl _ _ xn0.
  have [de0|dnb] := Req_dec d 0.
    rewrite de0 Rabs_R0; suff : 0 < uls x by lra.
    exact: uls_gt_0.
  exact: Fnonoverlap_head2 Fl xn0 dnb.
by move=> Hi xn0; apply: (IH (Fnonoverlap_cons Fl) i).
Qed.

(* Converse-of-[imm] bridge: build the recursive [Fnonoverlap_aux prev l]     *)
(* from index-form separation bounds.  [H1] bounds every nonzero element by   *)
(* [1/2 uls prev] (needed only through the leading run of zeros, before the   *)
(* running [prev] first moves); [H2] is the all-pairs separation among the    *)
(* elements of [l].  Reusable: turns a "no overlapping pair" statement into   *)
(* the recursive predicate.                                                   *)
Lemma Fnonoverlap_aux_allpairs prev l :
  (forall j, (j < size l)%N -> nth 0 l j <> 0 ->
     Rabs (nth 0 l j) <= / 2 * uls prev) ->
  (forall i j, (i < j)%N -> (j < size l)%N -> nth 0 l i <> 0 ->
     Rabs (nth 0 l j) <= / 2 * uls (nth 0 l i)) ->
  Fnonoverlap_aux prev l.
Proof.
elim: l prev => [|x l IH] prev //= H1 H2; split.
  by move=> xn0; apply: (H1 0%N).
have [xe0|xne0] := Req_dec x 0.
  have E : (if Req_EM_T x 0 then prev else x) = prev.
    by case: (Req_EM_T x 0) => [_|H]//; case: (H xe0).
  rewrite E; apply: IH.
    by move=> j jL jn0; apply: (H1 j.+1).
  by move=> i j iLj jL in0; apply: (H2 i.+1 j.+1).
have E : (if Req_EM_T x 0 then prev else x) = x.
  by case: (Req_EM_T x 0) => [xe0|_]//; case: (xne0 xe0).
rewrite E; apply: IH.
  by move=> j jL jn0; apply: (H2 0%N j.+1).
by move=> i j iLj jL in0; apply: (H2 i.+1 j.+1).
Qed.

(* All-pairs separation gives [Fnonoverlap l] (paper Def 3): no head          *)
(* condition is needed, since the filtering [Fnonoverlap] drops any leading   *)
(* zeros; the surviving head is unconstrained and each later nonzero is       *)
(* bounded against every earlier nonzero.  The nonzero head [x] of a [cons]   *)
(* supplies the [i = 0] instance feeding [Fnonoverlap_aux_allpairs].          *)
Lemma Fnonoverlap_allpairs l :
  (forall i j, (i < j)%N -> (j < size l)%N -> nth 0 l i <> 0 ->
     Rabs (nth 0 l j) <= / 2 * uls (nth 0 l i)) ->
  Fnonoverlap l.
Proof.
elim: l => [_|x l IH H] //.
have Hl : Fnonoverlap l.
  by apply: IH => i j iLj jLs ni0; apply: (H i.+1 j.+1); rewrite ?ltnS.
rewrite /Fnonoverlap /=; case: (x =P 0) => [->|/eqP xnb].
  by move: Hl; rewrite /Fnonoverlap.
apply/Fnonoverlap_aux_filter; apply: Fnonoverlap_aux_allpairs.
  move=> j jL jn0; apply: (H 0%N j.+1); rewrite ?ltnS //.
  by apply/eqP.
by move=> i j iLj jL in0; apply: (H i.+1 j.+1); rewrite ?ltnS.
Qed.

(* ---- lifted out of the FLT tail below --------------------------------- *)
(* These four are what [TWSum.v] needs and they are already FLX-correct: the *)
(* zero guard is handled via [ulp_FLX_0] ([nth_step_zero] IS the guard's     *)
(* propagation).  They were trapped inside the commented-out FLT block only  *)
(* because [abs_le_ufp_norm] still unfolded [FLT_exp].                       *)

Lemma abs_le_ufp_norm x : format x -> Rabs x <= (2 - 2 * u) * ufp x.
Proof.
move=> Fx.
have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
have Hu1 : u <= 1 by rewrite uE -(pow0E beta); apply: bpow_le; lia.
case: (Req_dec x 0) => [xz|xn0].
  by rewrite xz Rabs_R0; have := ufp_gt_0 0; nra.
have Hsucc : succ beta fexp (Rabs x) <= bpow beta (mag beta x).
  apply: succ_le_lt => //; first exact: generic_format_abs.
    by apply: generic_format_bpow; rewrite /fexp /FLX_exp; lia.
  by apply: bpow_mag_gt.
move: Hsucc; rewrite succ_eq_pos; last exact: Rabs_pos.
rewrite ulp_neq_0; last by move: (Rabs_pos_lt _ xn0); lra.
move=> Hs.
have Hcexp : bpow beta (mag beta x - p) <= bpow beta (cexp (Rabs x)).
  by apply: bpow_le; rewrite /cexp /FLX_exp mag_abs; lia.
have -> : (2 - 2 * u) * ufp x =
  bpow beta (mag beta x) - bpow beta (mag beta x - p).
  rewrite /ufp uE.
  have -> : (2 - 2 * bpow beta (-p)) = bpow beta 1 - bpow beta (1 - p).
    by rewrite (bpow_plus beta 1 (-p)) bpow_1 /=; lra.
  by rewrite Rmult_minus_distr_r -!bpow_plus; congr (bpow _ _ - bpow _ _); lia.
lra.
Qed.

(* A P-nonoverlap list whose head is 0 sums to 0: a zero limb forces its      *)
(* nonzero-float successors below [ulp 0 = 0], hence to 0.                   *)
Lemma small_head_zero l : Pnonoverlap l -> {in l, forall z, format z} ->
  nth 0 l 0 = 0 -> sumR l = 0.
Proof.
elim: l => [//|a l IH] Pl Fl /= a0.
suff Hl0 : sumR l = 0 by rewrite a0 Hl0 Rplus_0_r.
case: l IH Pl Fl => [//|b l'] IH Pl Fl.
apply: IH; first exact: Pnonoverlap_cons Pl.
  by move=> t tin; apply: Fl; rewrite inE tin orbT.
(* The successor is 0 outright, or its [ulp a = ulp 0 = 0] bound is absurd.   *)
have /= := Pl 0%N isT => -[//|Hb].
by move: Hb; rewrite a0 ulp_FLX_0; split_Rabs; lra.
Qed.

(* Key bound: for a P-nonoverlap list of floats, the whole sum is at most     *)
(* twice the [ufp] of the leading term -- the geometric series                *)
(* [(2-2u)(1 + u + u^2 + ...) = 2] collapses in the induction. No nonzero     *)
(* / no-underflow hyp: zero limbs are absorbed by [small_head_zero], and      *)
(* every non-last limb is non-underflowing by [nu_of_lt_ulp].                 *)
Lemma sumR_ufp_bound l : Pnonoverlap l -> {in l, forall z, format z} ->
  Rabs (sumR l) <= 2 * ufp (nth 0 l 0).
Proof.
have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
elim: l => [_ _|a l IH Pl Fl].
  rewrite Rabs_R0.
  by have := ufp_gt_0 (nth 0 (@nil R) 0); lra.
have Fa : format a by apply: Fl; rewrite inE eqxx.
have Hla : Rabs a <= (2 - 2 * u) * ufp a by apply: abs_le_ufp_norm.
have Hua : 0 < ufp a := ufp_gt_0 a.
case: l IH Pl Fl => [|b l] IH Pl Fl.
  have -> : nth 0 [:: a] 0 = a by [].
  have -> : sumR [:: a] = a by rewrite /= Rplus_0_r.
  nra.
have Fb : format b by apply: Fl; rewrite !inE eqxx orbT.
have Hub : 0 < ufp b := ufp_gt_0 b.
have -> : nth 0 (a :: b :: l) 0 = a by [].
have -> : sumR (a :: b :: l) = a + sumR (b :: l) by [].
have IHbl : Rabs (sumR (b :: l)) <= 2 * ufp b.
  apply: IH; first exact: Pnonoverlap_cons Pl.
  by move=> t tin; apply: Fl; rewrite inE tin orbT.
case: (Req_dec b 0) => [b0|bn0].
  have Hs0 : sumR (b :: l) = 0.
    apply: small_head_zero; first exact: Pnonoverlap_cons Pl.
      by move=> t tin; apply: Fl; rewrite inE tin orbT.
    by rewrite /= b0.
  by rewrite Hs0 Rplus_0_r; nra.
(* [b <> 0] here, so the zero guard cannot fire and the strict bound stands.  *)
have Hb : Rabs b < ulp a.
  by have /= := Pl 0%N isT => -[b0|//]; case: bn0.
have Na : a <> 0.
  by move=> a_eq0; move: Hb; rewrite a_eq0 ulp_FLX_0; split_Rabs; lra.
have Hstep : ufp b <= u * ufp a by apply: ufp_ulp_step.
apply: Rle_trans (Rabs_triang _ _) _.
nra.
Qed.

(* A zero limb propagates: its successor is below [ulp 0 = 0], hence 0.      *)
Lemma nth_step_zero l i : Pnonoverlap l -> {in l, forall z, format z} ->
  nth 0 l i = 0 -> nth 0 l i.+1 = 0.
Proof.
move=> Pl Fl Hi.
case: (ltnP i.+1 (size l)) => [Hlt|Hle]; last by rewrite nth_default.
have := Pl i Hlt => -[//|Hb].
by move: Hb; rewrite Hi ulp_FLX_0; split_Rabs; lra.
Qed.


Lemma Fnonoverlap_aux_sumRabs prev l :
  Fnonoverlap_aux prev l -> {in l, forall z, format z} ->
  sumRabs l <= uls prev * (1 - (/ 2) ^ (size l)).
Proof.
elim: l prev => [|x l IH] prev; first by move=> _ _ /=; lra.
move=> Hf xlF.
have xF : format x by apply: xlF; rewrite inE eqxx.
have lF : {in l, forall z, format z}.
  by move=> z zl; apply: xlF; rewrite inE zl orbT.
have Hup : 0 <= uls prev by apply: uls_ge_0.
have Hd0 : 0 < (/ 2) ^ (size l) by apply: pow_lt; lra.
have Hd1 : (/ 2) ^ (size l) <= 1.
  by rewrite -(pow1 (size l)); apply: pow_incr; lra.
have [xe0|xne0] := Req_dec x 0.
  rewrite /= xe0 Rabs_R0 Rplus_0_l.
  have Hrec : Fnonoverlap_aux prev l.
    by move: Hf; rewrite xe0 => /Fnonoverlap_aux_cons0.
  by apply: Rle_trans (IH prev Hrec lF) _; nra.
rewrite /=.
have Hx : Rabs x <= / 2 * uls prev by move: Hf => [/(_ xne0)].
have Ex : (if Req_EM_T x 0 then prev else x) = x.
  by case: (Req_EM_T x 0) => [xe0|_] //; case: (xne0 xe0).
have Hrec : Fnonoverlap_aux x l by move: Hf => [_]; rewrite Ex.
have Hux : uls x <= Rabs x by apply: uls_le_abs.
apply: Rle_trans (_ : Rabs x + uls x * (1 - (/ 2) ^ (size l)) <= _).
  by have := IH x Hrec lF; lra.
by nra.
Qed.

(* A prefix of a P-nonoverlapping sequence is P-nonoverlapping.  Since        *)
(* [vsebK k = take k \o vseb], this is what turns "VSEB is P-nonoverlapping"  *)
(* into "VSEB(k) is P-nonoverlapping".                                        *)
(* Proof: [take k] leaves the [nth]s at indices < k unchanged and only        *)
(* shortens the list, so every instance of the [Pnonoverlap] condition on     *)
(* [take k l] is an instance already available on [l].                        *)
Lemma Pnonoverlap_take k l : Pnonoverlap l -> Pnonoverlap (take k l).
Proof.
elim: l k => //= a [| b l] IH [|[|k]] //=.
move=> ablP [|i] /= iLs; first by apply: (ablP 0%N).
apply: (IH k.+1 _ i) => // z zLs.
by apply: (ablP z.+1).
Qed.

(* ===========================================================================*)
(*  Theorem 1 (VecSum), faithful to paper3 Section 2.1                        *)
(*                                                                            *)
(*  The current [vecSum_Fnonoverlap] below uses the simplified inputs         *)
(*  [sorted_mag]+[pairwise_ulp]; this block states Theorem 1 with the paper's *)
(*  actual [k_i] exponent hypotheses, and the proof steps it goes through.    *)
(* ===========================================================================*)

(* Paper representation: [x = M * 2^(k-p+1)] with [|M| < 2^p], [M] an integer *)
(* and the exponent [k] chosen (not necessarily canonical).  Under FLX every *)
(* such [M * 2^(k-p+1)] with [|M| < 2^p] IS a float, so no side condition on  *)
(* the exponent is needed -- the FLT reading had to require [emin <= k-p+1].  *)





(* [sumR] is additive over concatenation, and P-nonoverlap is stable by drop. *)
Lemma sumR_cat l1 l2 : sumR (l1 ++ l2) = sumR l1 + sumR l2.
Proof. by elim: l1 => [|a l1 IH] /=; rewrite ?IH; ring. Qed.

Lemma Pnonoverlap_drop k l : Pnonoverlap l -> Pnonoverlap (drop k l).
Proof.
move=> H i; rewrite size_drop ltn_subRL => Hi.
by rewrite !nth_drop addnS; apply: H; rewrite -addnS.
Qed.


Lemma sumR_head_drop1 l : sumR l = nth 0 l 0 + sumR (drop 1 l).
Proof. by case: l => [|a l] /=; rewrite ?drop0; lra. Qed.

(* ---- Theorem 3: relative error of truncating a P-nonoverlapping seq ------ *)
(* Paper 2.2, p.4.  Four steps, each about a P-nonoverlapping [l] with        *)
(* [ufp0 := ufp (nth 0 l 0)].  See doc/thm3.md.                               *)

(* Step 1 -- the paper's [ufp(y_k) <= u ufp(y_{k-1}) <= ... <= u^k ufp(y_0)]. *)
Lemma ufp_decay_pow l k :
  Pnonoverlap l -> {in l, forall z, format z} -> nth 0 l k <> 0 ->
  ufp (nth 0 l k) <= u ^ k * ufp (nth 0 l 0).
Proof.
move=> Pl Fl; elim: k => [_|k IH Hkn].
  by rewrite /= Rmult_1_l; apply: Rle_refl.
have Hkn' : nth 0 l k <> 0 by move=> H; apply/Hkn/(nth_step_zero Pl Fl H).
have Hk1 : (k.+1 < size l)%N.
  by rewrite ltnNge; apply/negP => Hge; apply: Hkn; rewrite nth_default.
have Hstep : ufp (nth 0 l k.+1) <= u * ufp (nth 0 l k).
  apply: ufp_ulp_step => //.
  by apply: Pnonoverlap_lt Hk1 Hkn.
have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
have Huk : 0 <= u ^ k by apply: pow_le; lra.
have HU : 0 < ufp (nth 0 l k) := ufp_gt_0 _.
apply: Rle_trans Hstep _.
have Hd := IH Hkn'.
have -> : u ^ k.+1 * ufp (nth 0 l 0) = u * (u ^ k * ufp (nth 0 l 0))
  by rewrite /=; ring.
by apply: Rmult_le_compat_l; lra.
Qed.

(* Step 2 -- tail bound: [sumR_ufp_bound] on the suffix, plus the decay.      *)
Lemma sumR_drop_ufp_bound l k :
  Pnonoverlap l -> {in l, forall z, format z} ->
  Rabs (sumR (drop k l)) <= 2 * u ^ k * ufp (nth 0 l 0).
Proof.
move=> Pl Fl.
have Pdk : Pnonoverlap (drop k l) by apply: Pnonoverlap_drop.
have Fdk : {in drop k l, forall z, format z} by move=> z /mem_drop; apply: Fl.
have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
have Huk : 0 <= u ^ k by apply: pow_le; lra.
have HU0 : 0 < ufp (nth 0 l 0) := ufp_gt_0 _.
have Hbnd := sumR_ufp_bound Pdk Fdk.
rewrite nth_drop addn0 in Hbnd.
case: (Req_dec (nth 0 l k) 0) => [Hzk|Hnzk].
  have -> : sumR (drop k l) = 0.
    apply: small_head_zero Pdk Fdk _.
    by rewrite nth_drop addn0.
  by rewrite Rabs_R0; nra.
have Hdecay := ufp_decay_pow Pl Fl Hnzk.
apply: Rle_trans Hbnd _.
have HUk : 0 < ufp (nth 0 l k) := ufp_gt_0 _.
by nra.
Qed.

(* Step 3 -- lower bound [(1 - 2u) ufp(y_0) <= |sumR l|].                     *)
Lemma sumR_ufp_lower l :
  Pnonoverlap l -> {in l, forall z, format z} -> nth 0 l 0 <> 0 ->
  (1 - 2 * u) * ufp (nth 0 l 0) <= Rabs (sumR l).
Proof.
move=> Pl Fl Hn0.
have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
have HU0 : 0 < ufp (nth 0 l 0) := ufp_gt_0 _.
have Hy0 : ufp (nth 0 l 0) <= Rabs (nth 0 l 0) by apply: ufp_le_abs.
have Htail : Rabs (sumR (drop 1 l)) <= 2 * u ^ 1 * ufp (nth 0 l 0)
  by apply: sumR_drop_ufp_bound.
rewrite /= Rmult_1_r in Htail.
have Htri := Rabs_triang_inv (nth 0 l 0) (- sumR (drop 1 l)).
rewrite Rabs_Ropp in Htri.
have Hsl : nth 0 l 0 - - sumR (drop 1 l) = sumR l
  by rewrite [sumR l]sumR_head_drop1; ring.
rewrite Hsl in Htri.
by move: Htri Htail Hy0; nra.
Qed.

(* Theorem 3 -- the relative truncation error.  [u <= /64] is the [p >= 6]   *)
(* hypothesis, passed explicitly to keep this file generic.                  *)
Lemma Pnonoverlap_truncate_error l k :
  Pnonoverlap l -> {in l, forall z, format z} -> nth 0 l 0 <> 0 -> u <= / 64 ->
  Rabs (sumR (drop k l)) <=
    (2 * u ^ k + 42 / 10 * u ^ k.+1) * Rabs (sumR l).
Proof.
move=> Pl Fl Hn0 Hu64.
have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
have Huk : 0 < u ^ k by apply: pow_lt; lra.
have HU0 : 0 < ufp (nth 0 l 0) := ufp_gt_0 _.
have Htail : Rabs (sumR (drop k l)) <= 2 * u ^ k * ufp (nth 0 l 0)
  by apply: sumR_drop_ufp_bound.
have Hlow := sumR_ufp_lower Pl Fl Hn0.
have Huk1 : u ^ k.+1 = u * u ^ k by rewrite /=; ring.
rewrite Huk1.
have Hs : 2 <= (2 + 42 / 10 * u) * (1 - 2 * u) by nra.
have -> : 2 * u ^ k + 42 / 10 * (u * u ^ k) = (2 + 42 / 10 * u) * u ^ k
  by ring.
apply: Rle_trans Htail _.
have Hpos1 : 0 <= Rabs (sumR l) - (1 - 2 * u) * ufp (nth 0 l 0) by lra.
have Hpos2 : 0 <= u ^ k * ufp (nth 0 l 0) by nra.
have Hc : 0 <= 2 + 42 / 10 * u by lra.
have Ha : 0 <= (2 + 42 / 10 * u) * u ^ k
  by apply: Rmult_le_pos => //; apply: pow_le; lra.
have Hb : 0 <= (2 + 42 / 10 * u) * (1 - 2 * u) - 2 by lra.
have Hstep1 : 0 <= (2 + 42 / 10 * u) * u ^ k *
                   (Rabs (sumR l) - (1 - 2 * u) * ufp (nth 0 l 0))
  by apply: Rmult_le_pos.
have Hstep2 : 0 <= u ^ k * ufp (nth 0 l 0) *
                   ((2 + 42 / 10 * u) * (1 - 2 * u) - 2)
  by apply: Rmult_le_pos.
nra.
Qed.

(* ===========================================================================*)
(*  Error bound: the "Ensure" clause of Algorithm 8 (p >= 6):                 *)
(*    | r - (x + y) | <= (2 u^3 + 4.2 u^4) | x + y |.                         *)
(*                                                                            *)
(*  Sketch (paper, Theorem 3 specialised to k = 3):                           *)
(*   - Merge, VecSum and VSEB are all exact, so the only error comes          *)
(*     from keeping the first three terms of the expansion.                   *)
(*   - The dropped tail of a P-nonoverlapping expansion is bounded by         *)
(*     (2 u^3 + 4.2 u^4) of the total (Theorem 3, k = 3).                     *)
(* ===========================================================================*)

End Nonoverlap.
