(** * Lefevre's lower-bound algorithm

    Algorithm 2 of doc/mourad.pdf (hal-00751446, 4.2); its own source is
    Lefevre's thesis ch. 2.  With [a = A/M], [b = B/M] the search wants a
    lower bound on [inf { b - a*x mod 1 | x < N }].

    Modular arithmetic occurs ONLY in the spec ([dst]).  The loop keeps
    naturals [(p,q,d,u,v)]: [p],[q] the two interval lengths, [u],[v] HOW
    MANY of each, [d] the distance from [b] to its interval's lower end.
    They stay below [M] because [u*p + v*q = M].

    doc/lefevre-these-notes.md  -- what the variables mean.
    doc/alg2-notes.md           -- measurements, dead ends, open holes. *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The specification *)

(** the lattice point [a*x mod 1], scaled by [M]. *)
Definition pt (M A x : nat) := (A * x) %% M.

(** distance from [pt x] up to [b], i.e. [b - a*x mod 1], scaled by [M]. *)
Definition dst (M A B x : nat) := (B + M - pt M A x) %% M.

(** [inf { b - a*x mod 1 | x < n }], scaled by [M].  Sealed with
    [Arguments inf_dst : simpl never]; unfold with [inf_dst0]/[inf_dstS]. *)
Fixpoint inf_dst (M A B n : nat) : nat :=
  if n is n1.+1 then minn (dst M A B n1) (inf_dst M A B n1) else M.

Arguments inf_dst : simpl never.

(** ** Algorithm 2: one turn of the loop. *)
Definition step (p q d u v : nat) : nat * nat * nat * nat * nat :=
  if p < q then
    let k := q %/ p in (p, q - k * p, d %% p, u + k * v, v)
  else
    let k := p %/ q in
    let p' := p - k * q in
    (p', q, (if p' <= d then (d - p') %% q else d), u, v + k * u).

(** The loop.  [fuel] is a structural bound; [fuel_enough] below says [M]
    always suffices, since [p + q] strictly decreases and starts at [M]. *)
Fixpoint run (fuel p q d u v N : nat) : nat :=
  if fuel is fuel1.+1 then
    let: (p', q', d', u', v') := step p q d u v in
    if N <= u' + v' then d' else run fuel1 p' q' d' u' v' N
  else d.

(** [p <- {a}; q <- 1 - {a}; d <- {b}; u <- 1; v <- 1].

    NB the initial [q] is [1 - {a}], not [1]: the invariant
    [u*p + v*q = M] fails otherwise.  (The paper's Algorithm 2 box reads
    [q <- 1]; checked by computation that this is wrong -- with M=32,
    A=5, B=3, N=8 it returns 3 while the true infimum is 0.) *)
Definition lefevre (M A B N : nat) : nat :=
  run M (A %% M) (M - A %% M) (B %% M) 1 1 N.

(** ** Sanity checks (computed, not admitted)

    [a = 17/45] is the example of Figure 4 of the paper. *)

Example lefevre_fig4 : lefevre 45 17 30 5 = 7.
Proof. by vm_compute. Qed.

Example inf_dst_fig4 : inf_dst 45 17 30 5 = 7.
Proof. by vm_compute. Qed.

(** a case where the bound is strict: the algorithm returns 1, the true
    infimum is 2.  So only an inequality can be proved below. *)
Example lefevre_strict : (lefevre 32 23 12 8, inf_dst 32 23 12 8) = (1, 2).
Proof. by vm_compute. Qed.

(** ** The theory *)

Section Theory.

Variable M : nat.
Hypothesis M_gt0 : 0 < M.

Variables A B : nat.
Hypothesis A_lt : A < M.
Hypothesis B_lt : B < M.

(** [pt_neq0] is not an assumption over [nat] but an exact bound on [N]:
    the first index with [Pt n = 0] is [M %/ gcdn A M].  So the section
    assumes only this, and [pt_neq0]/[N_le_Mg] are lemmas. *)
Variable N : nat.
Hypothesis N_gt0 : 0 < N.
Hypothesis N_lt_Mg : N < M %/ gcdn A M.

Local Notation Pt := (pt M A).
Local Notation Dst := (dst M A B).
Local Notation Inf := (inf_dst M A B).

Lemma N_le_Mg : N <= M %/ gcdn A M.
Proof. by apply: ltnW. Qed.

(** [Pt n = 0] iff [M] divides [A * n] iff [M %/ g] divides [n], by Gauss
    after dividing both by [g = gcdn A M].  So the least positive index
    with [Pt n = 0] is [M %/ g], which [N_lt_Mg] puts beyond [N]. *)
Lemma pt_neq0 n : 0 < n <= N -> Pt n != 0.
Proof. Admitted.

(** *** Warm-up: elementary facts about the specification *)

Lemma pt_lt x : Pt x < M.
Proof. by rewrite ltn_mod. Qed.

Lemma pt0 : Pt 0 = 0.
Proof. by rewrite /Pt muln0 mod0n. Qed.

(** the lattice is additive mod M *)
Lemma ptD x y : Pt (x + y) = (Pt x + Pt y) %% M.
Proof. by rewrite modnDm -mulnDr. Qed.

Lemma dst_lt x : Dst x < M.
Proof. by rewrite ltn_mod. Qed.

Lemma dst0 : Dst 0 = B.
Proof. by rewrite /Dst pt0 subn0 modnDr modn_small. Qed.

Lemma dstE x : Dst x = (B + M - Pt x) %% M.
Proof. by []. Qed.

(** moving one lattice step to the right lowers the distance by [Pt y],
    unless it wraps.  The workhorse for [step_d]. *)
Lemma dstD x y : Pt y <= Dst x -> Dst (x + y) = Dst x - Pt y.
Proof.
move=> ptLdx; rewrite dstE ptD.
have F : Pt x + Pt y < M.*2.
  rewrite -addnn; apply: ltn_trans (_ : M + Pt y < _).
    by rewrite ltn_add2r pt_lt.
  by rewrite ltn_add2l pt_lt.
have [xyLM|MLxy]:= ltnP (Pt x + Pt y) M.
  rewrite [(Pt x + _) %% _]modn_small //.
  rewrite subnDA modnB //; last by apply: leq_trans ptLdx (leq_mod _ _).
  rewrite -[(B + M - Pt x) %% M]/(Dst x) ltnNge modn_small; last by apply: pt_lt.
  by rewrite ptLdx add0n.
have -> : (Pt x + Pt y) %% M  = Pt x + Pt y - M.
  by rewrite -[in LHS](subnK MLxy) modnDr modn_small // ltn_subLR // addnn.
rewrite subnCBA // addnCA addnn [Pt x + _]addnC subnDAC.
rewrite modnB ?pt_lt //; last first.
  rewrite leq_subRL.
    by apply: leq_trans (ltnW _) (leq_addl _ _).
  apply: leq_trans (ltnW (pt_lt _)) _.
  apply: leq_trans (leq_addl _ _).
  by rewrite -addnn leq_addr.
rewrite ![Pt _ %% _]modn_small ?pt_lt //.
have -> : (B + M.*2 - Pt x) %% M = Dst x.
  have -> : B + M.*2 = M + B + M by rewrite addnAC addnn addnC.
  rewrite subDnCA; first by rewrite modnDl addnC.
  by rewrite (leq_trans (ltnW (pt_lt _))) // leq_addr.
by rewrite ltnNge ptLdx.
Qed.

(** the only two ways to look inside [Inf]. *)
Lemma inf_dst0 : Inf 0 = M.
Proof. by []. Qed.

Lemma inf_dstS n : Inf n.+1 = minn (Dst n) (Inf n).
Proof. by []. Qed.

(** the infimum is a lower bound on every distance in range *)
Lemma inf_dst_le n x : x < n -> Inf n <= Dst x.
Proof.
elim: n => // n IH; rewrite leq_eqVlt => /orP[/eqP[->]|/IH // nLx].
  by rewrite inf_dstS geq_minl.
apply: leq_trans nLx.
by rewrite inf_dstS geq_minr.
Qed.

(** the minimum is attained -- needed to name a witness for the walk *)
Lemma inf_dst_ex n : 0 < n -> exists2 y, y < n & Inf n = Dst y.
Proof.
elim: n => // [] [_ _|n IH _].
  by exists 0; rewrite // inf_dstS inf_dst0; apply/minn_idPl; rewrite ltnW // dst_lt.
rewrite inf_dstS.
have [y yLn Hy] := IH isT; rewrite Hy.
case: (leqP (Dst n.+1) (Dst y)) => [H|H].
  by exists n.+1 => //; apply/minn_idPl.
by exists y => //; exact: leq_trans yLn (leqnSn _).
Qed.

(** more points can only lower the infimum *)
Lemma inf_dst_mono m n : m <= n -> Inf n <= Inf m.
Proof.
move=> /subnK<-; elim: (_ - _) => // k kmLm.
by rewrite addSn inf_dstS (leq_trans _ kmLm) // geq_minr.
Qed.


(** *** The loop invariant

    [p] is the length of the leftmost interval and [v] the index that
    realises it; [q] is the length of the rightmost interval and [u] the
    index that realises it; [d] is the distance from [b] down to some
    point already placed. *)

Record inv (p q d u v : nat) : Prop := Inv {
  inv_p0  : 0 < p;
  inv_q0  : 0 < q;
  (* slater.v: sum_min_max *)
  inv_bez : u * p + v * q = M;
  (* slater.v: p = `{get_min n * a}, with v = get_min n *)
  inv_pv  : p = Pt v;
  (* slater.v: q = 1 - `{get_max n * a}, with u = get_max n *)
  inv_qu  : q = M - Pt u;
  (* Euclid's invariant.  Measured to hold at every state including the
     initial one.  It is what bounds how long the loop can run: Euclid
     reaches 0 once [u + v] gets to [M / gcd], so the loop must exit
     first, i.e. [N <= M / gcdn A M]. *)
  inv_gcd : gcdn p q = gcdn A M;
  (* [u] and [v] start at 1 and only grow.  NOT derivable from the fields
     above -- u = 0, v = 1, q = M satisfies all of them -- but needed: with
     both positive, [inv_bez] gives [p + q <= M], i.e. the two gaps of the
     three-distance configuration fit inside the circle. *)
  inv_u0  : 0 < u;
  inv_v0  : 0 < v
}.

(** *** The [d] part of the invariant, separately.  The old [inv_d] was
    FALSE; [invd] carries a bound, a congruence and a max instead. *)

Record invd (p q d u v : nat) : Prop := Invd {
  invd_max : d < maxn p q;
  invd_le  : d <= Inf (u + v);
  (* [d] sits on the same residue class mod [p] as the true closest
     distance.  Independent of [invx]: [invx] constrains the CONFIGURATION
     (gaps at least p / q), this constrains [d] RELATIVE to it, and the two
     leaves need both.  Validated: 0 counterexamples over 5152 states, and
     it makes the leaves hold in 121183 of 121183 cases.  See the
     correction note above for why [invx] alone does not suffice. *)
  invd_cong : d = Inf (u + v) %[mod p]
}.

Lemma am_gt0 : 0 < A %% M.
Proof.
have : Pt 1 != 0 by apply: pt_neq0.
by rewrite /Pt muln1; case: (_ %% _).
Qed.

(** *** Initialisation *)

Lemma inv_init : inv (A %% M) (M - A %% M) (B %% M) 1 1.
Proof.
constructor => //.
- by apply: am_gt0.
- by rewrite ltn_subRL addn0 ltn_mod.
- by rewrite !mul1n addnC subnK // ltnW // ltn_mod.
- by rewrite /Pt muln1.
- by rewrite /Pt muln1.
- by rewrite (modn_small A_lt) -{2}(subnKC (ltnW A_lt)) gcdnDl.
Qed.


(** *** One step preserves the invariant

    Split into the four independent obligations so they can be attacked
    separately; [inv_step] just glues them. *)

(* glue -- pure algebra from [inv_bez]. *)
Lemma step_bez p q d u v :
  inv p q d u v ->
  let: (p', q', _, u', v') := step p q d u v in u' * p' + v' * q' = M.
Proof.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0 /=.
rewrite /step; have [pLq|qLp] := ltnP.
  rewrite mulnDl mulnBr addnBA; last by rewrite leq_mul2l leq_divM orbT.
  by rewrite mulnCA mulnA addnAC addnK.
rewrite mulnBr mulnDl addnC addnBA; last by rewrite leq_mul2l leq_divM orbT.
by rewrite mulnCA mulnA addnAC addnK addnC.
Qed.

(** the batched Euclid step: [k] applications of slater's [get_minS] /
    [get_maxS] at once (Property 2 of the paper).  Induction on [k],
    through the two one-step lemmas below. *)

(** one point added on the left: [v] keeps realising the smallest
    positive point, [u] moves to [u + v].  (slater: [get_maxS].) *)
Lemma step_pt_one_lt p q u v :
  inv p q (Dst 0) u v -> p < q ->
  (p = Pt v) /\ (q - p = M - Pt (u + v)).
Proof.
rewrite dst0.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0 /= pLq; split => //.
rewrite ptD modn_small; last by rewrite -ltn_subRL // -pE -qE.
by rewrite subnDA -qE -pE.
Qed.

(** one point added on the right. *)
Lemma step_pt_one_ge p q u v :
  inv p q (Dst 0) u v -> q <= p ->
  (p - q = Pt (v + u)) /\ (q = M - Pt u).
Proof.
rewrite dst0.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0 /= qLp; split => //.
rewrite pE qE ptD subnBA; last by rewrite ltnW // pt_lt.
rewrite [Pt _ + _]addnC.
suff MLuv : M <= Pt u + Pt v.
  rewrite -[in RHS](subnK MLuv) modnDr modn_small // ltn_subLR //.
  rewrite (ltn_trans _ (_ : M + Pt v < _)) //.
    by rewrite ltn_add2r pt_lt.
  by rewrite ltn_add2l pt_lt.
by rewrite -leq_subLR -pE -qE.
Qed.

(* CFrac: the two lemmas above, iterated [k] times. *)
Lemma step_pt p q d u v :
  inv p q d u v ->
  let: (p', q', _, u', v') := step p q d u v in
  0 < p' -> 0 < q' -> (p' = Pt v') /\ (q' = M - Pt u').
Proof.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0.
rewrite /step; have [pLq|qLp] := ltnP; rewrite /= => p'_gt0 q'_gt0.
  rewrite subn_gt0 in q'_gt0.
  suff : forall j, j <= q %/ p -> p = Pt v /\ q -  j * p = M - Pt (u + j * v).
    by move=> /(_ (q %/ p)); apply.
  elim => [|j IH jLq]; first by rewrite subn0 addn0.
  have -> :  q - j.+1 * p = q - j * p - p by rewrite mulSnr subnDA.
  have -> : u + j.+1 * v = u + j * v + v by rewrite mulSnr addnA.
  apply: step_pt_one_lt; last first.
    rewrite ltn_subRL -mulSnr.
    apply: leq_ltn_trans q'_gt0.
    by rewrite leq_mul2r jLq orbT.
  split => //.
  - rewrite subn_gt0 (leq_trans _ (_ :  q %/ p * p <= _)) //.
      by rewrite ltn_mul2r p_gt0.
    by rewrite leq_divM.
  - rewrite mulnDl mulnBr -addnA.
    rewrite mulnCA -mulnA [X in _ + X]addnC subnK //.
    rewrite mulnCA leq_mul2l.
    by rewrite (leq_trans _ (leq_divM q p)) ?orbT // leq_mul2r ltnW ?orbT.
  - by case: IH => //; apply: ltnW.
  have Hjp : j * p <= q.
    by rewrite ltnW // (leq_ltn_trans _ q'_gt0) // leq_mul2r ltnW ?orbT.
  by rewrite -gE -{2}(subnKC Hjp) gcdnMDl.
  by rewrite addn_gt0 u_gt0.
rewrite subn_gt0 in p'_gt0.
suff : forall j, j <= p %/ q -> p - j * q = Pt (v + j * u) /\ q = M - Pt u.
  by move=> /(_ (p %/ q)); apply.
elim => [|j IH jLq]; first by rewrite subn0 addn0.
have -> :  p - j.+1 * q = p - j * q - q by rewrite mulSnr subnDA.
have -> : v + j.+1 * u = v + j * u + u by rewrite mulSnr addnA.
apply: step_pt_one_ge; last first.
  rewrite leq_subRL.
    by rewrite -mulSnr (leq_trans _ (ltnW p'_gt0)) // leq_mul2r jLq orbT.
  by rewrite (leq_trans _ (leq_divM p q)) // leq_mul2r ltnW // orbT.
split => //.
- rewrite subn_gt0 (leq_trans _ (_ :  p %/ q * q <= _)) //.
    by rewrite ltn_mul2r q_gt0.
  by rewrite leq_divM.
- rewrite mulnBr mulnDl.
  rewrite mulnCA -mulnA addnC addnBA.
    by rewrite addnAC addnK addnC.
  rewrite mulnCA leq_mul2l (leq_trans _ (_ :  p %/ q * q <= _)) ?orbT //.
    by rewrite leq_mul2r ltnW // orbT.
  by apply: leq_divM.
- by case: IH => //; apply: ltnW.
have Hjq : j * q <= p.
  by rewrite ltnW // (leq_ltn_trans _ p'_gt0) // leq_mul2r ltnW ?orbT.
  by rewrite -gE gcdnC [in RHS]gcdnC -{2}(subnKC Hjq) gcdnMDl.
by rewrite addn_gt0 v_gt0.
Qed.

(** THE hard one: the [d] update stays a genuine distance. *)

(** ** The [d] obligations, after the redesign. *)

(** the converse of [inf_dst_le]: a pointwise lower bound gives a bound
    on the infimum.  This is what turns [mod_le_dst] (pointwise) into the
    [invd_le] field (about [Inf]). *)
Lemma le_inf_dst e n : e <= M -> (forall x, x < n -> e <= Dst x) -> e <= Inf n.
Proof.
move=> eM; elim: n => [//|n IH H]; rewrite inf_dstS leq_min H // IH // => x xn.
by apply: H (ltnW xn).
Qed.

(** ** The two remaining [d] obligations. *)

Lemma dst_below x : Pt x <= B -> Dst x = B - Pt x.
Proof.
move=> H; rewrite dstE addnC -addnBA // modnDl modn_small //.
apply: leq_ltn_trans (leq_subr _ _) B_lt.
Qed.

Lemma dst_above x : B < Pt x -> Dst x = B + M - Pt x.
Proof.
move=> H; rewrite dstE modn_small //.
rewrite ltn_subLR; last by rewrite (leq_trans (ltnW (pt_lt x))) // leq_addl.
by rewrite ltn_add2r.
Qed.

(** the lattice is linear while it has not wrapped -- needed to turn an
    index bound into a bound on [Pt]. *)
Lemma pt_mul_small k : Pt 1 * k < M -> Pt k = Pt 1 * k.
Proof.
move=> H; have -> : Pt k = (Pt 1 * k) %% M by rewrite /pt muln1 modnMml.
by rewrite modn_small.
Qed.

(** the shape [invd_le] reduces to, in both [invd_first] and [step_invd]:
    a remainder by a gap is below every distance whose index is in range.
    Proof plan: [x <= d %/ g] gives [Dst x = B - Pt x >= B %% g] by
    [dst_below] and [leq_trunc_div]; [x > d %/ g] makes the point wrap, and
    [dst_above] bounds [Dst x] below by [M - Pt x >= B %% g] as long as
    [Pt 1 * x <= B + M], which the index range provides. *)
Lemma mod_le_dst g x : 0 < g -> g = Pt 1 -> Pt 1 * x <= M -> B %% g <= Dst x.
Proof.
move=> g_gt0 gE Hx.
have PtE : Pt x = (g * x) %% M by rewrite gE /pt muln1 modnMml.
have BMg : B %% g <= B by apply: leq_mod.
case: (ltnP (g * x) M) => [gxM|Mgx].
  have Ptx : Pt x = g * x by rewrite PtE modn_small.
  case: (leqP (g * x) B) => [gxB|Bgx].
    rewrite dst_below ?Ptx //.
    have Hd : g * x <= B %/ g * g.
      have Hx1 : x <= B %/ g by rewrite leq_divRL // mulnC.
      by rewrite mulnC leq_mul2r Hx1 orbT.
    have -> : B %% g = B - B %/ g * g by rewrite {2}(divn_eq B g) addnC addnK.
    exact: leq_sub2l Hd.
  rewrite dst_above ?Ptx //.
  apply: leq_trans BMg _.
  rewrite leq_subRL; last by rewrite (leq_trans (ltnW gxM)) // leq_addl.
  by rewrite addnC leq_add2l ltnW.
have gxE : g * x = M by apply/eqP; rewrite eqn_leq Mgx andbT gE.
by rewrite dstE PtE gxE modnn subn0 modnDr (modn_small B_lt).
Qed.

(** after the FIRST step, [d] satisfies [invd]. *)
(** Goals (1) and (3) of the breakdown above -- the [invd_max] field in
    both branches.  Cheap, and now proved. *)
Lemma invd_first_max :
  let: (p', q', d', _, _) := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' < maxn p' q'.
Proof.
have Ha := am_gt0.
have Hq : 0 < M - A %% M by rewrite subn_gt0 ltn_mod.
rewrite /step; case: ltnP => [pLq|qLp]; rewrite /=.
  by rewrite (leq_trans (ltn_pmod _ Ha)) ?leq_maxl.
case: (leqP (A %% M - A %% M %/ (M - A %% M) * (M - A %% M)) (B %% M))
   => [p'Ld|dLp'].
  by rewrite (leq_trans (ltn_pmod _ Hq)) ?leq_maxr.
by rewrite (leq_trans dLp') // leq_maxl.
Qed.

(** Goals (2) and (4): the [invd_le] field.  Goal (2) is [le_inf_dst] plus
    [mod_le_dst]; goal (4) needs the same universal bound as
    [step_invd_le_pt].  Left as one obligation so the two are attacked
    together. *)
(** ** The points added in the [M - A <= A] branch: a descending run. *)
Lemma pt_desc j : j * (M - A) <= A -> Pt (j + 1) = A - j * (M - A).
Proof.
move=> Hj.
have HAM : A <= M by rewrite ltnW.
have HjM : j * M = j * (M - A) + j * A by rewrite -mulnDr subnK.
rewrite /pt.
have -> : A * (j + 1) = A - j * (M - A) + j * M.
  by rewrite HjM addnA subnK // mulnDr muln1 mulnC addnC.
rewrite addnC modnMDl modn_small //.
by rewrite (leq_ltn_trans (leq_subr _ _)).
Qed.

(** The [A < M - A] branch: covered by [mod_le_dst]. *)
(** The [M - A <= A] branch: by [pt_desc] the points descend by [M-A]. *)
(** [modnB] is available but tricky; [pt_sub] shows the pattern. *)
Lemma invd_first_le_ge_then : M - A %% M <= A %% M ->
  A - A %/ (M - A) * (M - A) <= B ->
  forall x, x < (A %/ (M - A)).+2 ->
  (B - (A - A %/ (M - A) * (M - A))) %% (M - A) <= Dst x.
Proof.
move=> qLp0 p'LB x xLk.
have HA : A %% M = A by rewrite modn_small.
have qLp : M - A <= A by move: qLp0; rewrite HA.
have HAM : A <= M by rewrite ltnW.
have Hq : 0 < M - A by rewrite subn_gt0.
have kqA : A %/ (M - A) * (M - A) <= A by rewrite leq_divM.
case: x xLk => [_|j jLk].
  by rewrite dst0 (leq_trans (leq_mod _ _)) // leq_subr.
have jk : j <= A %/ (M - A) by rewrite -ltnS.
have jqk : j * (M - A) <= A %/ (M - A) * (M - A) by rewrite leq_mul2r jk orbT.
have jqA : j * (M - A) <= A by rewrite (leq_trans jqk).
have HPt : Pt j.+1 = A - j * (M - A) by rewrite -addn1 pt_desc.
have HAj : (A - A %/ (M - A) * (M - A)) + (A %/ (M - A) * (M - A) - j * (M - A))
         = A - j * (M - A).
  by rewrite addnBA // subnK.
case: (leqP (A - j * (M - A)) B) => [AjLB|BLAj].
  rewrite dst_below ?HPt //.
  have Hs : A %/ (M - A) * (M - A) - j * (M - A)
          <= B - (A - A %/ (M - A) * (M - A)).
    by rewrite leq_subRL // HAj.
  rewrite -{1}(subnK Hs) -subnDA HAj.
  by rewrite -mulnBl addnC modnMDl leq_mod.
rewrite dst_above ?HPt //.
rewrite (leq_trans (ltnW (ltn_pmod _ Hq))) // leq_subRL; last first.
  by rewrite (leq_trans (leq_subr _ _)) // (leq_trans HAM) // leq_addl.
rewrite (leq_trans (_ : A - j * (M - A) + (M - A) <= M)) ?leq_addl //.
apply: leq_trans (leq_add (leq_subr _ _) (leqnn (M - A))) _.
by rewrite subnKC.
Qed.

Lemma invd_first_le_ge : M - A %% M <= A %% M ->
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' <= Inf (u' + v').
Proof.
move=> qLp0.
have Ha := am_gt0.
have HA : A %% M = A by rewrite modn_small.
have HB : B %% M = B by rewrite modn_small.
have HAM : A <= M by rewrite ltnW.
have Hq : 0 < M - A by rewrite subn_gt0.
have Hthen := invd_first_le_ge_then qLp0.
have qLp : M - A <= A by move: qLp0; rewrite HA.
rewrite /step HA HB.
rewrite ifN /=; last by rewrite -leqNgt.
apply: le_inf_dst.
  case: (leqP (A - A %/ (M - A) * (M - A)) B) => [_|_]; last by rewrite ltnW.
  by rewrite (leq_trans (leq_mod _ _)) // (leq_trans (leq_subr _ _)) // ltnW.
move=> x xLk; rewrite !muln1 !add1n in xLk.
have Hjq : forall j, j <= A %/ (M - A) -> Pt (j + 1) = A - j * (M - A).
  move=> j jLk; apply: pt_desc.
  by rewrite (leq_trans _ (leq_divM A (M - A))) // leq_mul2r jLk orbT.
case: (leqP (A - A %/ (M - A) * (M - A)) B) => [p'LB|BLp']; last first.
  case: x xLk => [_|j jLk]; first by rewrite dst0.
  have jk : j <= A %/ (M - A) by rewrite -ltnS.
  have HPt : Pt j.+1 = A - j * (M - A) by rewrite -addn1 Hjq.
  have HB2 : B < Pt j.+1.
    by rewrite HPt (leq_trans BLp') // leq_sub2l // leq_mul2r jk orbT.
  rewrite dst_above //.
  rewrite leq_subRL; last by rewrite (leq_trans (ltnW (pt_lt _))) // leq_addl.
  rewrite [Pt j.+1 + B]addnC leq_add2l.
  exact: ltnW (pt_lt _).
by apply: Hthen.
Qed.

Lemma invd_first_le :
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' <= Inf (u' + v').
Proof.
have Ha := am_gt0.
have HA : A %% M = A by rewrite modn_small.
have HB : B %% M = B by rewrite modn_small.
have Hp1 : Pt 1 = A by rewrite /pt muln1 HA.
have HAM : A <= M by rewrite ltnW.
have Hk : (M - A) %/ A * A + A <= M.
  by rewrite -{2}(subnK HAM) leq_add2r leq_divM.
have Hge := invd_first_le_ge.
move: Hge; rewrite /step HA HB; case: ltnP => [pLq|qLp] /= Hge; last by apply: Hge.
apply: le_inf_dst; first by rewrite (leq_trans (leq_mod _ _)) // ltnW.
move=> x xLk; rewrite !muln1 !add1n in xLk.
have Hk2 : A * ((M - A) %/ A + 1) <= M by rewrite mulnDr muln1 mulnC.
apply: mod_le_dst.
- by rewrite -HA.
- by rewrite Hp1.
rewrite Hp1 (leq_trans _ Hk2) // leq_mul2l.
by rewrite -ltnS xLk orbT.
Qed.

(** After the FIRST step [d] is EXACTLY the closest distance -- measured,
    0 violations over 3696 cases -- so the congruence there is free once the
    two inequalities are in hand.  ([invd_first_le] is the [<=] half.)
    NB this equality is special to the first step: at later steps it fails
    (150 violations out of 5152), which is why [invd] carries the weaker
    congruence rather than an equation. *)
(** The [A < M - A] branch: the witness is [B %/ A], because
    [Dst (B %/ A) = B %% A] exactly -- the point [A * (B %/ A)] is the
    largest multiple of [A] below [b].  Its index is in range because
    [M = A + (M-A) = A + ((M-A)%/A)*A + (M-A)%%A < ((M-A)%/A + 2) * A]. *)
(** [else] immediate; [then] needs a witness. *)
Lemma invd_first_ge_ge_then : M - A %% M <= A %% M ->
  A - A %/ (M - A) * (M - A) <= B ->
  Inf (1 + (1 + A %/ (M - A) * 1))
    <= (B - (A - A %/ (M - A) * (M - A))) %% (M - A).
Proof.
move=> Hge Hp.
have A_gt0 : 0 < A.
  rewrite (modn_small A_lt) in Hge.
  case: (posnP A) => // A0; move: Hge; rewrite A0 subn0 leqn0 => /eqP MM.
  by move: M_gt0; rewrite MM.
have q_gt0 : 0 < M - A by rewrite subn_gt0.
set q := M - A in Hp q_gt0 *.
set k := A %/ q in Hp *.
set p' := A - k * q in Hp *.
set t := (B - p') %/ q.
have kqA : k * q <= A by rewrite leq_divM.
have p'E : p' = A %% q by rewrite /p' /k {1}(divn_eq A q) addnC addnK.
(* [t <= k] because [B - p' < M - p' = k*q + q] *)
have tk : t <= k.
  rewrite -ltnS /t ltn_divLR // mulSnr.
  have p'A : p' <= A by rewrite leq_subr.
  have Ap' : A - p' = k * q by rewrite /p' subKn.
  have -> : k * q + q = M - p' by rewrite -Ap' addnBAC // /q subnKC // ltnW.
  by rewrite ltn_sub2r // (leq_ltn_trans Hp).
(* the witness: index [(k-t)+1], whose point is [A - (k-t)*q = p' + t*q] *)
have ktq : (k - t) * q <= A.
  by rewrite (leq_trans _ kqA) // leq_mul2r leq_subr orbT.
have PxE : Pt ((k - t) + 1) = A - (k - t) * q by apply: pt_desc.
have tqkq : t * q <= k * q by rewrite leq_mul2r tk orbT.
have PxE2 : A - (k - t) * q = p' + t * q.
  by rewrite mulnBl subnBA // /p' addnBAC.
have tqB : t * q <= B - p' by rewrite leq_divM.
have PxB : Pt ((k - t) + 1) <= B.
  by rewrite PxE PxE2 -{1}(subnKC Hp) leq_add2l.
have DxE : Dst ((k - t) + 1) = (B - p') %% q.
  rewrite dst_below // PxE PxE2 subnDA.
  by rewrite {1}(divn_eq (B - p') q) addnC addnK.
rewrite -DxE; apply: inf_dst_le.
apply: (@leq_ltn_trans (k + 1)); first by rewrite leq_add2r leq_subr.
by rewrite muln1 addnA addnC ltn_add2l.
Qed.

Lemma invd_first_ge_ge : M - A %% M <= A %% M ->
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  Inf (u' + v') <= d'.
Proof.
move=> qLp0.
have Ha := am_gt0.
have HA : A %% M = A by rewrite modn_small.
have HB : B %% M = B by rewrite modn_small.
have Hthen := invd_first_ge_ge_then qLp0.
rewrite /step HA HB; rewrite ifN /=; last by rewrite -leqNgt -HA.
case: (leqP (A - A %/ (M - A) * (M - A)) B) => [p'LB|BLp']; last first.
  by rewrite -[X in _ <= X]dst0; apply: inf_dst_le.
by apply: Hthen.
Qed.

Lemma invd_first_ge :
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  Inf (u' + v') <= d'.
Proof.
have Ha := am_gt0.
have HA : A %% M = A by rewrite modn_small.
have HB : B %% M = B by rewrite modn_small.
have Hp1 : Pt 1 = A by rewrite /pt muln1 HA.
have Hge := invd_first_ge_ge.
move: Hge; rewrite /step HA HB; case: ltnP => [pLq|qLp] /= Hge; last by apply: Hge.
have HzA : A * (B %/ A) <= B by rewrite mulnC leq_divM.
have Hz : Dst (B %/ A) = B %% A.
  rewrite dst_below; last by rewrite pt_mul_small Hp1 // (leq_ltn_trans HzA).
  have HPz : Pt (B %/ A) = A * (B %/ A).
    have H : Pt 1 * (B %/ A) < M by rewrite Hp1 (leq_ltn_trans HzA).
    by rewrite (pt_mul_small H) Hp1.
  by rewrite HPz mulnC {1}(divn_eq B A) addKn.
rewrite -Hz; apply: inf_dst_le.
rewrite muln1 ltn_divLR //.
apply: leq_trans B_lt _.
rewrite !mulnDl mul1n -{1}(subnKC (ltnW A_lt)) {1}(divn_eq (M - A) A).
rewrite addnA leq_add2l.
  by apply: ltnW; rewrite ltn_mod -HA.
by rewrite -HA.
Qed.

Lemma invd_first_cong :
  let: (p', q', d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' = Inf (u' + v') %[mod p'].
Proof.
have Hle := invd_first_le.
have Hge := invd_first_ge.
case E: (step (A %% M) (M - A %% M) (B %% M) 1 1) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hle Hge.
by have -> : d' = Inf (u' + v') by apply/eqP; rewrite eqn_leq Hle Hge.
Qed.

Lemma invd_first :
  let: (p', q', d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  invd p' q' d' u' v'.
Proof.
have Hm := invd_first_max.
have Hl := invd_first_le.
have Hc := invd_first_cong.
case E: (step (A %% M) (M - A %% M) (B %% M) 1 1)
     => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hm Hl Hc.
by split.
Qed.

(** and [invd] is preserved.  THE hardest of the file. *)
Lemma pt_sub x y : y <= x -> Pt y <= Pt x -> Pt (x - y) = Pt x - Pt y.
Proof.
move=> yx Hp; rewrite /pt mulnBr modnB //; last by rewrite leq_mul2l yx orbT.
by rewrite ltnNge Hp /= mul0n add0n.
Qed.

Lemma dstB x y : y <= x -> Pt y <= Pt x -> Dst (x - y) = (Dst x + Pt y) %% M.
Proof.
move=> yx Hp.
have HxM : Pt x <= B + M by rewrite (leq_trans (ltnW (pt_lt x))) // leq_addl.
rewrite dstE pt_sub // subnBA // dstE modnDml.
by rewrite addnBAC.
Qed.

(** holds without [Pt y <= Pt x]. *)
Lemma dstB_gen x y : y <= x -> Dst (x - y) = (Dst x + Pt y) %% M.
Proof.
move=> yx.
have Hpx : Pt x = (Pt (x - y) + Pt y) %% M by rewrite -ptD subnK.
have HP := pt_lt (x - y); have HQ := pt_lt y.
rewrite dstE [in RHS]dstE modnDml Hpx.
case: (ltnP (Pt (x - y) + Pt y) M) => H.
  rewrite (modn_small H) subnDA subnK //.
  by rewrite leq_subRL ?(leq_trans (ltnW HP)) ?leq_addl //
             (leq_trans (ltnW H)) // leq_addl.
have e2 : (Pt (x - y) + Pt y) %% M = Pt (x - y) + Pt y - M.
  rewrite -{1}(subnK H) modnDr modn_small // ltn_subLR //.
  apply: leq_ltn_trans (leq_add (ltnW HP) (leqnn _)) _.
  by rewrite ltn_add2l.
have HPB : Pt (x - y) <= B + M by rewrite (leq_trans (ltnW HP)) // leq_addl.
rewrite e2 subnBA // subnDA subnK.
  by rewrite -[in RHS]addnBAC // modnDr.
rewrite leq_subRL; last by rewrite (leq_trans HPB) // leq_addr.
apply: leq_trans (leq_add (ltnW HP) (ltnW HQ)) _.
by rewrite leq_add2r leq_addl.
Qed.

(** the mirror of [step_d_lt], direction of travel corrected. *)
Lemma step_d_ge p q d u v x j :
  inv p q d u v -> q <= p -> x < u + v -> d = Dst x ->
  j <= d %/ q -> j * u <= x -> Dst (x - j * u) = d - j * q.
Proof.
move=> iv qLp xLuv dE.
have [_ q_gt0 _ _ qE _ _ _] := iv.
have Hpu : Pt u = M - q by rewrite qE subKn // ltnW // pt_lt.
have dM : d < M by rewrite dE dst_lt.
have qM : q <= M by rewrite qE leq_subr.
elim: j => [|j IH jLd juLx]; first by rewrite !mul0n !subn0 dE.
have jLd' : j <= d %/ q by apply: ltnW.
have juLx' : j * u <= x by rewrite (leq_trans _ juLx) // leq_mul2r ltnW ?orbT.
have Hq : j.+1 * q <= d.
  by rewrite (leq_trans _ (leq_divM d q)) // leq_mul2r jLd orbT.
have HqD : q <= d - j * q.
  rewrite leq_subRL; last by rewrite (leq_trans _ Hq) // leq_mul2r leqnSn orbT.
  by rewrite -mulSnr.
have H1 : d - j * q - q <= d by rewrite (leq_trans (leq_subr _ _)) // leq_subr.
have -> : x - j.+1 * u = x - j * u - u by rewrite mulSnr subnDA.
have Hu : u <= x - j * u by rewrite leq_subRL // -mulSnr.
rewrite dstB_gen // IH //.
rewrite Hpu addnBA // -addnBAC // modnDr.
rewrite (modn_small (leq_ltn_trans H1 dM)).
by rewrite mulSnr subnDA.
Qed.

(** [invd] splits into its two fields, which differ sharply in cost.
    The [invd_max] half needs nothing but [ltn_pmod]: [d'] is always a
    remainder by one of the two gaps (or, in the [else] case, is [d] with
    the test itself giving [d < p']). *)
Lemma step_invd_max p q d u v :
  inv p q d u v -> invd p q d u v ->
  let: (p', q', d', _, _) := step p q d u v in d' < maxn p' q'.
Proof.
move=> iv ivd.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
rewrite /step; case: ltnP => [pLq|qLp]; rewrite /=.
  by rewrite (leq_trans (ltn_pmod _ p_gt0)) ?leq_maxl.
case: (leqP (p - p %/ q * q) d) => [p'Ld|dLp'].
  by rewrite (leq_trans (ltn_pmod _ q_gt0)) ?leq_maxr.
by rewrite (leq_trans dLp') // leq_maxl.
Qed.

(** the [invd_le] half: the real content, shared with [invd_first]. *)
(** The missing content, isolated.  [d' <= M] is bundled in because
    [le_inf_dst] needs it for its [n = 0] base case; the second component
    is the universal bound, which is the real work.  Both parts are
    consequences of the validated [d' <= Inf (u' + v')], so this helper is
    a faithful decomposition, not a new conjecture. *) 
(** Only the NEW indices can be hard.  For [x < u + v] the bound is free:
    [d' <= d] (a remainder by a gap, or [d] itself), [d <= Inf (u+v)] by
    [invd_le], and [Inf (u+v) <= Dst x] by [inf_dst_le].  So the whole
    obligation reduces to the indices the step has just added. *)
(** The two branches add points of opposite orientation. *)
(** The two-length structure, reproved natively rather than bridged to
    CFrac/slater.v: the dictionary is in the header, but instantiating
    slater's real-valued development costs more than reproving. *)

(** The proof needs NO completeness statement -- Bezout on the NEW state
    plus [N <= M %/ gcdn A M] is exactly enough.  If [q' = 0] then
    [step_bez] degenerates to [u' * p = M], and [p %| q] forces
    [p = gcdn p q = gcdn A M], so [u' = M %/ gcdn A M >= N], contradicting
    [u' + v' < N].  Symmetrically for [p' = 0].  ([inv_complete], the false
    lemma of round 3, was a wrong turn: it was never needed.) *)
Lemma step_p_gt0 p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', _, u', v') := step p q d u v in
  u' + v' < N -> 0 < p' /\ 0 < q'.
Proof.
move=> iv uvLN.
have [p_gt0 q_gt0 bez pE qE gE _ _] := iv.
have Hb := step_bez iv.
move: Hb; rewrite /step.
have [pLq|qLp] := ltnP => /= Hb Huv; split => //.
  case: (posnP (q - q %/ p * p)) => [q0|] //.
  have qme : q - q %/ p * p = q %% p by rewrite {1}(divn_eq q p) addnC addnK.
  have qmp : q %% p = 0 by rewrite -qme q0.
  have pg : p = gcdn A M by rewrite -gE; apply/esym/gcdn_idPl; rewrite /dvdn qmp.
  move: Hb; rewrite q0 muln0 addn0 => Hb.
  have Hu : u + q %/ p * v = M %/ p by rewrite -Hb mulnK.
  by move: Huv; rewrite Hu pg ltnNge (leq_trans N_le_Mg (leq_addr v _)).
case: (posnP (p - p %/ q * q)) => [p0|] //.
have pme : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
have pmq : p %% q = 0 by rewrite -pme p0.
have qg : q = gcdn A M by rewrite -gE gcdnC; apply/esym/gcdn_idPl; rewrite /dvdn pmq.
move: Hb; rewrite p0 muln0 add0n => Hb.
have Hv : v + p %/ q * u = M %/ q by rewrite -Hb mulnK.
by move: Huv; rewrite Hv qg ltnNge (leq_trans N_le_Mg (leq_addl u _)).
Qed.

(** [q <= M] is free from [inv]. *)
(** [p < q] branch: [x] ranges over the new indices [u+v <= x < u'+v'],
    each written [y + m*v] with [y] old ([new_index_decomp]). *)

Lemma new_index_decomp k u v x :
  0 < v -> u + v <= x -> x < u + k * v + v ->
  exists2 m, 0 < m <= k & (x - m * v < u + v) && (m * v <= x).
Proof.
move=> v_gt0 xge xlt.
set r := x - (u + v).
have Hr : r < k * v by rewrite /r ltn_subLR // addnAC.
have Hmv : r %/ v * v + v <= x.
  apply: leq_trans (leq_add (leq_divM r v) (leqnn v)) _.
  by rewrite -(subnK xge) -/r leq_add2l leq_addl.
exists (r %/ v + 1).
  rewrite addn1 ltn0Sn /= (ltn_divLR _ _ v_gt0) //.
rewrite mulnDl mul1n Hmv andbT.
have -> : x - (r %/ v * v + v) = u + r %% v.
  rewrite -(subnK xge) -/r {1}(divn_eq r v).
  by rewrite subnDA -addnA addKn addnA addnK addnC.
by rewrite ltn_add2l ltn_mod.
Qed.

(** the [p1] shape is exactly "no wrap": [Pt z + p < M]. *)
Lemma pt_addv p v z : p = Pt v -> Pt z + p < M -> Pt (z + v) = Pt z + p.
Proof. by move=> pE H; rewrite ptD -pE modn_small. Qed.

(** batched [pt_addv]. *)
Lemma pt_walkD p v y m :
  p = Pt v -> m * p < M -> Pt y + m * p < M -> Pt (y + m * v) = Pt y + m * p.
Proof.
move=> pE mpM H.
have Hmv : Pt (m * v) = (m * Pt v) %% M by rewrite /pt modnMmr mulnCA.
by rewrite ptD Hmv -pE (modn_small mpM) modn_small.
Qed.


(** the [p2] shape needs no invariant, only [q = M - Pt u]. *)
Lemma pt_subu q u z : q = M - Pt u -> u <= z -> Pt (z - u) = (Pt z + q) %% M.
Proof.
move=> qE uLz.
have Hz : Pt z = (Pt (z - u) + Pt u) %% M by rewrite -ptD subnK.
rewrite qE Hz modnDml -addnA (subnKC (ltnW (pt_lt u))) modnDr.
by rewrite modn_small // pt_lt.
Qed.

Lemma inv_qM p q d u v : inv p q d u v -> q <= M.
Proof. by case=> _ _ _ _ -> _ _ _; apply: leq_subr. Qed.

Record invx (p q u v : nat) : Prop := Invx {
  invx_min : forall m, 0 < m < u + v -> p <= Pt m;
  invx_max : forall m, m < u + v -> Pt m <= M - q;
  (* free wherever [invx] is established, since [inv_qu] gives
     [q = M - Pt u]; carried here so [pt_gap_max] need not take [inv]. *)
  invx_qM  : q <= M;
  (* [b] lies in a gap, and every gap is [p] or [q], so the nearest point
     below it is within [maxn p q].  Needed by [inf_new_lt_le], whose
     witness walks [Inf %/ p] steps and must stay inside the new range.
     Probed: 0 violations / 17608. *)
  invx_inf : Inf (u + v) < maxn p q;
  (* the three-distance content: every distance is the closest one plus
     whole gaps.  Not implied by the fields above. *)
  invx_gap : forall y, y < u + v ->
             exists a b, [/\ a <= u, b <= v &
                             Dst y = Inf (u + v) + a * p + b * q];
  (* three-distance in INDEX form (Lefevre 2.4 / slater get_nextDmin,
     get_nextDmax): [u] gaps of length [p], [v] of length [q]. *)
  invx_p1  : forall z, z < u -> Pt (z + v) = Pt z + p;
  invx_p2  : forall z, u <= z < u + v -> Pt (z - u) = (Pt z + q) %% M
}.

(** the wrapping companion of [pt_sub]: when the order inverts, the
    difference of indices lands on the far side of [M]. *)
(** Here [modnB] IS the right tool -- unlike in [invd_first_le_ge_then],
    where the additive route won.  The hypothesis [Pt x < Pt y] makes
    [modnB]'s boolean term [true] (rather than killing it as in [pt_sub]),
    so the [+ M] it contributes is exactly the wrap. *)
Lemma pt_sub_wrap x y : y <= x -> Pt x < Pt y -> Pt (x - y) = M - (Pt y - Pt x).
Proof.
move=> yx Hp; rewrite /pt mulnBr modnB //; last by rewrite leq_mul2l yx orbT.
move: Hp; rewrite /pt => Hp.
have Hle : (A * x) %% M <= (A * y) %% M by apply: ltnW.
by rewrite Hp mul1n subnBA.
Qed.

(** slater.get_minB: points in index order are at least [p] apart. *)
(** The walk primitive for the partition form of the invariant: [invx_p1]
    iterated.  Stepping the index by [v] raises the point by [p], and the
    guard [z + k*v <= u] keeps every intermediate index below [u], which is
    exactly what [invx_p1] needs at each step. *)
(** the bound that feeds it. *)
Lemma pt_walk_le q y mp : Pt y <= M - q -> q <= M -> mp <= q -> Pt y + mp <= M.
Proof. by move=> H1 qM H2; apply: leq_trans (leq_add H1 H2) _; rewrite subnK. Qed.

Lemma invx_p1_iter p q u v k z :
  invx p q u v -> 0 < v -> z + k * v <= u -> Pt (z + k * v) = Pt z + k * p.
Proof.
move=> ix v_gt0; elim: k z => [z _|k IH z H]; first by rewrite mul0n !addn0.
have -> : z + k.+1 * v = z + v + k * v by rewrite mulSnr addnA addnAC.
have H1 : z + v + k * v <= u by rewrite -addnAC -addnA -mulSnr.
rewrite IH // (invx_p1 ix); last first.
  by rewrite (leq_trans _ H1) // -addnA -[X in X < _]addn0 ltn_add2l addn_gt0 v_gt0.
by rewrite mulSnr addnA addnAC.
Qed.

Lemma pt_gap_min p q u v m1 m2 :
  invx p q u v -> m1 < m2 -> m2 < u + v -> Pt m1 <= Pt m2 ->
  p <= Pt m2 - Pt m1.
Proof.
move=> ix m12 m2n Hp.
rewrite -(pt_sub (ltnW m12) Hp).
apply: (invx_min ix).
by rewrite subn_gt0 m12 (leq_ltn_trans (leq_subr _ _)).
Qed.

(** slater.get_maxB: points whose order INVERTS the index order are at
    least [q] apart. *)
Lemma pt_gap_max p q u v m1 m2 :
  invx p q u v -> m2 < m1 -> m1 < u + v -> Pt m1 < Pt m2 ->
  q <= Pt m2 - Pt m1.
Proof.
move=> ix m21 m1n Hp.
have Hw : Pt (m1 - m2) = M - (Pt m2 - Pt m1) by rewrite (pt_sub_wrap (ltnW m21) Hp).
have Hmax : Pt (m1 - m2) <= M - q.
  by apply: (invx_max ix); rewrite (leq_ltn_trans (leq_subr _ _)).
move: Hmax; rewrite Hw => Hmax.
rewrite -(leq_sub2lE (m := M)) //.
exact: (invx_qM ix).
Qed.

Lemma invx_init : invx (A %% M) (M - A %% M) 1 1.
Proof.
have HA : A %% M = A by apply: modn_small.
have Hp1 : Pt 1 = A by rewrite /pt muln1.
have Inf2 : Inf (1 + 1) = minn (Dst 1) (Dst 0).
  rewrite !inf_dstS inf_dst0.
  by have -> : minn (Dst 0) M = Dst 0 by apply/minn_idPl; rewrite ltnW // dst_lt.
(* the two points are [0] and [A]; [b] sits either above [A] (gap [p]) or
   below it (gap [q]), and that fixes both [Inf] and the decomposition *)
have HI : Inf (1 + 1) = if A <= B then B - A else B.
  case: (leqP A B) => [AB|AB].
    rewrite Inf2 dst0 (_ : Dst 1 = B - A); first by apply/minn_idPl; rewrite leq_subr.
    by rewrite dst_below Hp1.
  rewrite Inf2 dst0 (_ : Dst 1 = B + M - A).
    by apply/minn_idPr; rewrite -addnBA ?leq_addr // ltnW.
  by rewrite dst_above Hp1.
have Hinf : Inf (1 + 1) < maxn (A %% M) (M - A %% M).
  rewrite HI HA; case: (leqP A B) => [AB|AB].
    by rewrite (leq_trans _ (leq_maxr _ _)) // ltn_sub2r.
  by rewrite (leq_trans _ (leq_maxl _ _)).
have Hgap : forall y, y < 1 + 1 ->
    exists a b, [/\ a <= 1, b <= 1 &
                    Dst y = Inf (1 + 1) + a * (A %% M) + b * (M - A %% M)].
  move=> y; move: HI; case: (leqP A B) => [AB|AB] HI.
    have D1 : Dst 1 = B - A by rewrite dst_below Hp1.
    case: y => [|[|y]] //= _.
      by exists 1, 0; split=> //; rewrite dst0 HI HA mul1n mul0n addn0 subnK.
    by exists 0, 0; split=> //; rewrite D1 HI !mul0n !addn0.
  have D1 : Dst 1 = B + M - A by rewrite dst_above Hp1.
  case: y => [|[|y]] //= _.
    by exists 0, 0; split=> //; rewrite dst0 HI !mul0n !addn0.
  by exists 0, 1; split=> //; rewrite D1 HI mul0n addn0 mul1n HA addnBA // ltnW.
have HP1 : forall z, z < 1 -> Pt (z + 1) = Pt z + A %% M.
  by move=> z; case: z => // _; rewrite Hp1 HA pt0.
have HP2 : forall z, 1 <= z < 1 + 1 -> Pt (z - 1) = (Pt z + (M - A %% M)) %% M.
  move=> z; case: z => [|[|z]] //= _.
  by rewrite Hp1 HA pt0 subnKC ?modnn // ltnW.
split => //.
- by move=> m; case: m => [|[|m]] //= _; rewrite Hp1 HA.
- move=> m; case: m => [|[|m]] //= _; first by rewrite pt0.
  by rewrite Hp1 HA subKn // ltnW.
by rewrite leq_subr.
Qed.

(** The one real obligation left: the three-distance step.  Conditioned as
    [inv_step] and [step_p_gt0] are -- only when the loop continues -- since
    at the terminal states ([q = 0], [u + v >= N]) [invx_min] genuinely
    fails: probed 78 violations there, 0 under the guard (376 states). *)
(** [invx_step], one lemma per field per branch: seven fields, two
    branches, [invx_qM] inline.  grep "@INVX_STEP" for status. *)

(** **** the [p < q] branch *)

(** [q < M] strictly: [q = M] would force [Pt u = 0]. *)
Lemma inv_qltM p q d u v : inv p q d u v -> u <= N -> q < M.
Proof.
move=> iv uN.
have [_ _ _ _ qE _ u_gt0 _] := iv.
have qM := inv_qM iv.
rewrite ltn_neqAle qM andbT; apply/eqP => qMe.
have H := subnK (ltnW (pt_lt u)).
move: H; rewrite -qE qMe => H2.
have Hu : Pt u = 0.
  have E0 : M + Pt u == M + 0 by rewrite addn0; apply/eqP.
  by move: E0; rewrite eqn_add2l => /eqP.
have uN' : 0 < u <= N by rewrite u_gt0 uN.
by have := pt_neq0 uN'; rewrite Hu eqxx.
Qed.

(* @INVX_STEP HELPER sharp -- TODO *)
(** [new_index_decomp] sharpened to [j < k].  Witness [j = t %/ v + 1] with
    [t = x - (u+v)]; the three subgoals it leaves are pure arithmetic:
    [t < (k-1)*v], then [ltn_divLR], then the two bounds by [divn_eq]. *)
Lemma new_index_decomp_sharp k u v x :
  0 < v -> u + v <= x -> x < u + k * v ->
  exists2 j, 0 < j < k & (x - j * v < u + v) && (j * v <= x).
Proof. Admitted.

(* @INVX_STEP HELPER lt -- PROVED *)
(** a new index is an old one walked up by [j] copies of [v], adding
    [j*p].  Shared by the five [lt] leaves.  alg2-notes.md 5. *)
Lemma pt_new_lt p q d u v m :
  inv p q d u v -> (forall k, k < u + v -> Pt k <= M - q) ->
  p < q -> u + q %/ p * v + v < N ->
  u + v <= m -> m < u + q %/ p * v + v ->
  exists2 j, 0 < j <= q %/ p &
    (m - j * v < u + v) /\ Pt m = Pt (m - j * v) + j * p.
Proof.
move=> iv Hmax pLq uvN' mnew mLuv'.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have qM : q <= M := inv_qM iv.
have uLN : u <= N.
  by rewrite (leq_trans _ (ltnW uvN')) // (leq_trans (leq_addr (q %/ p * v) u)) // leq_addr.
have qltM : q < M := inv_qltM iv uLN.
have [j jk /andP[ylt jvm]] := new_index_decomp v_gt0 mnew mLuv'.
have /andP[j_gt0 jk2] := jk.
have jpq : j * p <= q by rewrite -leq_divRL.
have m_gt0 : 0 < m by rewrite (leq_trans _ mnew) // addn_gt0 u_gt0.
have mLN : m <= N by rewrite ltnW // (ltn_trans mLuv').
have mN : 0 < m <= N by rewrite m_gt0 mLN.
have HP : Pt (m - j * v) + j * p <= M := pt_walk_le (Hmax _ ylt) qM jpq.
have Hjv : Pt (j * v) = j * p.
  have H1 : Pt (j * v) = (j * Pt v) %% M by rewrite /pt modnMmr mulnCA.
  by rewrite H1 -pE modn_small // (leq_ltn_trans jpq).
have Hne : Pt (m - j * v) + j * p < M.
  rewrite ltn_neqAle HP andbT; apply/eqP => He.
  by have := pt_neq0 mN; rewrite -{1}(subnK jvm) ptD Hjv He modnn eqxx.
exists j => //; split => //.
by rewrite -{1}(subnK jvm) (pt_walkD pE) // (leq_ltn_trans jpq).
Qed.

(* @INVX_STEP lt/min -- PROVED *)
(* needs: inv, invx_min, invx_max, pt_neq0 *)
Lemma invx_step_lt_min p q d u v :
  inv p q d u v -> (forall m, 0 < m < u + v -> p <= Pt m) ->
  (forall m, m < u + v -> Pt m <= M - q) ->
  p < q -> u + q %/ p * v + v < N ->
  forall m, 0 < m < u + q %/ p * v + v -> p <= Pt m.
Proof.
move=> iv Hmin Hmax pLq uvN' m /andP[m_gt0 mLuv'].
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have qM : q <= M := inv_qM iv.
(* the OLD indices are free *)
case: (ltnP m (u + v)) => [mold|mnew].
  by apply: Hmin; rewrite m_gt0.
(* a NEW index is [y + j*v] with [y] old, and the walk adds [j*p >= p] *)
have [j /andP[j_gt0 jk] /andP[ylt jvm]] := new_index_decomp v_gt0 mnew mLuv'.
have jpq : j * p <= q by rewrite -leq_divRL.
have qltM : q < M.
  rewrite ltn_neqAle qM andbT; apply/eqP => qMe.
  have uN : 0 < u <= N.
    rewrite u_gt0 (leq_trans _ (ltnW uvN')) //.
    by rewrite (leq_trans (leq_addr (q %/ p * v) u)) // leq_addr.
  have H := subnK (ltnW (pt_lt u)).
  move: H; rewrite -qE qMe => H2.
  have Hu : Pt u = 0.
    have E0 : M + Pt u == M + 0 by rewrite addn0; apply/eqP.
    by move: E0; rewrite eqn_add2l => /eqP.
  by have := pt_neq0 uN; rewrite Hu eqxx.
have HP : Pt (m - j * v) + j * p <= M := pt_walk_le (Hmax _ ylt) qM jpq.
have Hm : Pt m = Pt (m - j * v) + j * p.
  rewrite -{1}(subnK jvm); apply: pt_walkD pE _ _.
    by rewrite (leq_ltn_trans jpq).
  (* the walk cannot land exactly on [M]: that is [Pt m = 0], and [pt_neq0]
     forbids it below [N] *)
  rewrite ltn_neqAle HP andbT; apply/eqP => He.
  have mN : 0 < m <= N by rewrite m_gt0 (leq_trans (ltnW mLuv')) // ltnW.
  have := pt_neq0 mN.
  rewrite -{1}(subnK jvm) ptD.
  have [_ _ _ pE' _ _ _ _] := iv.
  have Hjv : Pt (j * v) = j * p.
    have H1 : Pt (j * v) = (j * Pt v) %% M by rewrite /pt modnMmr mulnCA.
    by rewrite H1 -pE' modn_small // (leq_ltn_trans jpq).
  by rewrite Hjv He modnn eqxx.
rewrite Hm (leq_trans _ (leq_addl _ _)) //.
by rewrite -{1}[p]mul1n leq_mul2r j_gt0 orbT.
Qed.

(* @INVX_STEP HELPER ge -- PROVED *)
(** mirror: walking by [u] SUBTRACTS [j*q].  alg2-notes.md 5. *)
Lemma pt_new_ge p q d u v m :
  inv p q d u v -> (forall k, 0 < k < u + v -> p <= Pt k) ->
  q <= p -> u + (v + p %/ q * u) < N ->
  u + v <= m -> m < u + (v + p %/ q * u) ->
  exists2 j, 0 < j <= p %/ q &
    [/\ 0 < m - j * u < u + v, j * q <= Pt (m - j * u) &
        Pt m = Pt (m - j * u) - j * q].
Proof.
move=> iv Hmin qLp uvN' mnew mLuv'.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have mnew' : v + u <= m by rewrite addnC.
have mLuv2 : m < v + p %/ q * u + u by rewrite addnC.
have [j jk /andP[ylt jum]] := new_index_decomp u_gt0 mnew' mLuv2.
have /andP[j_gt0 jk2] := jk.
have jqp : j * q <= p by rewrite -leq_divRL.
rewrite addnC in ylt.
have key : forall i, 0 < i <= p %/ q -> 0 < m - i * u -> i * u <= m ->
    m - i * u < u + v ->
    [/\ 0 < m - i * u < u + v, i * q <= Pt (m - i * u) & Pt m = Pt (m - i * u) - i * q].
  move=> i /andP[i_gt0 ik] y_gt0 ium ylt2.
  have iqp : i * q <= p by rewrite -leq_divRL.
  have iqP : i * q <= Pt (m - i * u).
    by rewrite (leq_trans iqp) // Hmin // y_gt0.
  have iqM : i * q < M by rewrite (leq_ltn_trans iqp) // pE pt_lt.
  have PuE : Pt u = M - q by rewrite qE subKn // ltnW // pt_lt.
  have Hiu : Pt (i * u) = M - i * q.
    have H1 : Pt (i * u) = (i * Pt u) %% M by rewrite /pt modnMmr mulnCA.
    rewrite H1 PuE mulnBr.
    have -> : i * M - i * q = (i - 1) * M + (M - i * q).
      rewrite addnBA; last by apply: ltnW.
      by rewrite subn1 -mulSnr prednK.
    by rewrite modnMDl modn_small // ltn_subrL muln_gt0 i_gt0 q_gt0 M_gt0.
  split => //; first by rewrite y_gt0.
  rewrite -{1}(subnK ium) ptD Hiu.
  rewrite addnBA; last exact: ltnW iqM.
  rewrite [Pt (m - i * u) + M]addnC -addnBA // modnDl.
  by rewrite modn_small // (leq_ltn_trans (leq_subr _ _)) // pt_lt.
(* the [Pt 0] corner: if the walk lands on the origin, take one step less *)
case: (posnP (m - j * u)) => [y0|y_gt0]; last by exists j => //; apply: key.
have mE : m = j * u by apply/eqP; rewrite eqn_leq jum andbT -subn_eq0 y0.
have j_gt1 : 1 < j.
  rewrite ltnNge; apply/negP => jL1.
  have j1 : j = 1 by apply/eqP; rewrite eqn_leq jL1 j_gt0.
  move: mnew; rewrite mE j1 mul1n leqNgt => /negP[].
  by rewrite -{1}[u]addn0 ltn_add2l.
have yE : m - j.-1 * u = u.
  by rewrite mE -{1}(prednK j_gt0) mulSnr addnC addnK.
have jpk : 0 < j.-1 <= p %/ q.
  apply/andP; split; first by rewrite -subn1 subn_gt0.
  exact: leq_trans (leq_pred _) jk2.
exists j.-1 => //; apply: key => //.
- by rewrite yE.
- by rewrite (leq_trans _ jum) // leq_mul2r leq_pred orbT.
by rewrite yE -{1}[u]addn0 ltn_add2l.
Qed.

(* @INVX_STEP lt/max -- PROVED *)
(* needs: inv, invx_max *)
Lemma invx_step_lt_max p q d u v :
  inv p q d u v -> (forall k, k < u + v -> Pt k <= M - q) ->
  p < q -> u + q %/ p * v + v < N ->
  forall m, m < u + q %/ p * v + v -> Pt m <= M - (q - q %/ p * p).
Proof.
move=> iv Hmax pLq uvN' m mLuv'.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
have kpq : q %/ p * p <= q by rewrite leq_divM.
case: (ltnP m (u + v)) => [mold|mnew].
  by rewrite (leq_trans (Hmax _ mold)) // leq_sub2l // leq_subr.
have [j /andP[j_gt0 jk] [ylt Hm]] := pt_new_lt iv Hmax pLq uvN' mnew mLuv'.
have jpk : j * p <= q %/ p * p by rewrite leq_mul2r jk orbT.
have -> : M - (q - q %/ p * p) = M - q + q %/ p * p.
  by rewrite subnBA // addnBAC // (inv_qM iv).
by rewrite Hm leq_add // (Hmax _ ylt).
Qed.

(* @INVX_STEP lt/inf -- TODO *)
(* NOT via inf_new_lt: that goes through step_invd_le -> ... ->
   mod_le_restricted, which needs invx.  Circular.  alg2-notes.md 5. *)
Lemma invx_step_lt_inf p q d u v :
  inv p q d u v -> invx p q u v -> p < q -> u + q %/ p * v + v < N ->
  Inf (u + q %/ p * v + v) < maxn p (q - q %/ p * p).
Proof. Admitted.

(* @INVX_STEP lt/gap -- TODO *)
(* the trade [q = q' + (q %/ p)*p] is free (subnK, leq_divM); the content
   is the COUNTS, and it needs lt/inf first (the decomposition is relative
   to the NEW Inf).  alg2-notes.md 5. *)
Lemma invx_step_lt_gap p q d u v :
  inv p q d u v -> invx p q u v -> p < q -> u + q %/ p * v + v < N ->
  forall y, y < u + q %/ p * v + v ->
  exists a b, [/\ a <= u + q %/ p * v, b <= v &
                  Dst y = Inf (u + q %/ p * v + v) + a * p + b * (q - q %/ p * p)].
Proof. Admitted.

(* @INVX_STEP lt/p1 -- TODO *)
(* wants new_index_decomp sharpened to [j < k].  alg2-notes.md 5. *)
Lemma invx_step_lt_p1 p q d u v :
  inv p q d u v -> (forall k, k < u + v -> Pt k <= M - q) ->
  p < q -> u + q %/ p * v + v < N ->
  forall z, z < u + q %/ p * v -> Pt (z + v) = Pt z + p.
Proof. Admitted.

(* @INVX_STEP lt/p2 -- PROVED *)
(* needs: inv only *)
Lemma invx_step_lt_p2 p q d u v :
  inv p q d u v -> p < q -> u + q %/ p * v + v < N ->
  forall z, u + q %/ p * v <= z < u + q %/ p * v + v ->
  Pt (z - (u + q %/ p * v)) = (Pt z + (q - q %/ p * p)) %% M.
(* An instance of [pt_subu], exactly like the [q <= p] one: it needs only
   [q' = M - Pt u'] for the NEW state, which [step_pt] gives once [0 < p']
   and [0 < q'].  Those come from [step_p_gt0] -- which is defined LATER in
   this file, so the proof is blocked by lemma ORDER, not by mathematics.
   [step_p_gt0] is hoisted above the [invx] section for exactly this. *)
Proof.
move=> iv pLq uvN' z /andP[uLz _].
have uvN : u + v < N by rewrite (leq_ltn_trans _ uvN') // leq_add2r leq_addr.
have Hg := step_p_gt0 iv uvN.
have Hpt := step_pt iv.
move: Hg Hpt; rewrite /step pLq /= => Hg Hpt.
have [Hp Hq] := Hg uvN'.
have [_ qE] := Hpt Hp Hq.
by apply: pt_subu.
Qed.

(** **** the [q <= p] branch *)

(* @INVX_STEP ge/min -- PROVED *)
(* needs: inv, invx_min *)
Lemma invx_step_ge_min p q d u v :
  inv p q d u v -> (forall k, 0 < k < u + v -> p <= Pt k) ->
  q <= p -> u + (v + p %/ q * u) < N ->
  forall m, 0 < m < u + (v + p %/ q * u) -> p - p %/ q * q <= Pt m.
Proof.
move=> iv Hmin qLp uvN' m /andP[m_gt0 mLuv'].
case: (ltnP m (u + v)) => [mold|mnew].
  by rewrite (leq_trans (leq_subr _ _)) // Hmin // m_gt0.
have [j /andP[j_gt0 jk] [/andP[y_gt0 ylt] jqP Hm]] :=
  pt_new_ge iv Hmin qLp uvN' mnew mLuv'.
rewrite Hm leq_sub ?Hmin ?y_gt0 //.
by rewrite leq_mul2r jk orbT.
Qed.

(* @INVX_STEP ge/max -- PROVED *)
(* needs: inv, invx_min, invx_max *)
Lemma invx_step_ge_max p q d u v :
  inv p q d u v -> (forall k, 0 < k < u + v -> p <= Pt k) ->
  (forall k, k < u + v -> Pt k <= M - q) ->
  q <= p -> u + (v + p %/ q * u) < N ->
  forall m, m < u + (v + p %/ q * u) -> Pt m <= M - q.
Proof.
move=> iv Hmin Hmax qLp uvN' m mLuv'.
case: (ltnP m (u + v)) => [mold|mnew]; first by apply: Hmax.
have [j /andP[j_gt0 jk] [/andP[y_gt0 ylt] jqP Hm]] :=
  pt_new_ge iv Hmin qLp uvN' mnew mLuv'.
by rewrite Hm (leq_trans (leq_subr _ _)) // Hmax.
Qed.

(* @INVX_STEP ge/inf -- TODO *)
(* no computed counterpart; needs the gap argument.  alg2-notes.md 5. *)
Lemma invx_step_ge_inf p q d u v :
  inv p q d u v -> invx p q u v -> q <= p -> u + (v + p %/ q * u) < N ->
  Inf (u + (v + p %/ q * u)) < maxn (p - p %/ q * q) q.
Proof. Admitted.

(* @INVX_STEP ge/gap -- TODO *)
(* mirror; likewise needs ge/inf first. *)
Lemma invx_step_ge_gap p q d u v :
  inv p q d u v -> invx p q u v -> q <= p -> u + (v + p %/ q * u) < N ->
  forall y, y < u + (v + p %/ q * u) ->
  exists a b, [/\ a <= u, b <= v + p %/ q * u &
                  Dst y = Inf (u + (v + p %/ q * u)) + a * (p - p %/ q * q) + b * q].
Proof. Admitted.

(* @INVX_STEP ge/p1 -- PROVED *)
(* needs: inv, invx_max *)
Lemma invx_step_ge_p1 p q d u v :
  inv p q d u v -> (forall m, m < u + v -> Pt m <= M - q) ->
  q <= p -> u + (v + p %/ q * u) < N ->
  forall z, z < u -> Pt (z + (v + p %/ q * u)) = Pt z + (p - p %/ q * q).
Proof.
move=> iv Hmax qLp uvN' z zLu.
have [_ q_gt0 _ _ _ _ u_gt0 v_gt0] := iv.
have uvN : u + v < N.
  by rewrite (leq_ltn_trans _ uvN') // leq_add2l leq_addr.
have Hg := step_p_gt0 iv uvN.
have Hpt := step_pt iv.
move: Hg Hpt; rewrite /step ifN -?leqNgt // => Hg Hpt.
have [Hp Hq] := Hg uvN'.
have [pE' _] := Hpt Hp Hq.
apply: pt_addv pE' _.
(* no wrap: [Pt z <= M - q] by [invx_max], and [p %% q < q] *)
have pmod : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
have zLuv : z < u + v by rewrite (leq_trans zLu) // leq_addr.
have := Hmax _ zLuv.
rewrite pmod => Hm.
rewrite (leq_ltn_trans (leq_add Hm (leqnn (p %% q)))) //.
by rewrite -{2}(subnK (inv_qM iv)) ltn_add2l ltn_pmod.
Qed.

(* @INVX_STEP ge/p2 -- PROVED *)
(* needs: inv_qu alone *)
Lemma invx_step_ge_p2 p q u v :
  q = M - Pt u ->
  forall z, u <= z < u + (v + p %/ q * u) -> Pt (z - u) = (Pt z + q) %% M.
Proof. by move=> qE z /andP[uLz _]; apply: pt_subu. Qed.

Lemma invx_step p q d u v :
  inv p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', _, u', v') := step p q d u v in
  u' + v' < N -> invx p' q' u' v'.
Proof.
move=> iv ix uvN.
have [_ q_gt0 _ _ _ _ _ _] := iv.
have qM := inv_qM iv.
rewrite /step; case: (ltnP p q) => [pLq|qLp] /= uvN'; split.
- exact: invx_step_lt_min iv (invx_min ix) (invx_max ix) pLq uvN'.
- exact: invx_step_lt_max iv (invx_max ix) pLq uvN'.
- by rewrite (leq_trans _ qM) // leq_subr.
- exact: invx_step_lt_inf iv ix pLq uvN'.
- exact: invx_step_lt_gap iv ix pLq uvN'.
- exact: invx_step_lt_p1 iv (invx_max ix) pLq uvN'.
- exact: invx_step_lt_p2 iv pLq uvN'.
- exact: invx_step_ge_min iv (invx_min ix) qLp uvN'.
- exact: invx_step_ge_max iv (invx_min ix) (invx_max ix) qLp uvN'.
- exact: qM.
- exact: invx_step_ge_inf iv ix qLp uvN'.
- exact: invx_step_ge_gap iv ix qLp uvN'.
- exact: invx_step_ge_p1 iv (invx_max ix) qLp uvN'.
exact: invx_step_ge_p2 (inv_qu iv).
Qed.


(** CORRECTION to PR #108: the claim there was wrong; what follows is the
    corrected version. *)

(** ** Scaffold for the two content leaves: both split on whether the
    walk wraps. *)

(** NB an earlier version of this file had [step_d_lt], which is exactly
    this statement with [d = Dst x] threaded through; several comments above
    still call it "(PROVED)".  It was removed in the round-8 cleanup, so the
    induction is redone here directly on [dstD].  Note [inv] does not mention
    [d] at all, so [inv p q d1 u v -> inv p q d2 u v] -- which is why the
    [Dst y] instance below needs no extra hypothesis. *)
(** two general facts the walk lemmas share: stepping the index by [w]
    lowers the distance by [Pt w] modulo [M], and [Pt] is linear modulo [M]. *)
Lemma dst_add x w : Dst (x + w) = (Dst x + M - Pt w) %% M.
Proof.
have Hd := dstB_gen (x := x + w) (y := w) (leq_addl x w).
rewrite addnK in Hd.
have HD := dst_lt (x + w); have HP := pt_lt w.
rewrite Hd; case: (ltnP (Dst (x + w) + Pt w) M) => H.
  by rewrite (modn_small H) addnAC addnK modnDr modn_small.
have e2 : (Dst (x + w) + Pt w) %% M = Dst (x + w) + Pt w - M.
  rewrite -{1}(subnK H) modnDr modn_small // ltn_subLR //.
  by apply: leq_ltn_trans (leq_add (ltnW HD) (leqnn _)) _; rewrite ltn_add2l.
by rewrite e2 subnK ?addnK ?modn_small // (leq_trans (ltnW HP)) // leq_addl.
Qed.

Lemma pt_muln k x : Pt (k * x) = (k * Pt x) %% M.
Proof. by rewrite /pt modnMmr mulnCA. Qed.

Lemma walk_lt_nowrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> m * p <= Dst y -> Dst (y + m * v) = Dst y - m * p.
Proof.
move=> iv ivd pLq yLuv mk Hmp.
have [p_gt0 _ _ pE _ _ _ _] := iv.
elim: m Hmp {mk} => [|m IH Hmp]; first by rewrite !mul0n addn0 subn0.
have Hm : m * p <= Dst y by rewrite (leq_trans _ Hmp) // leq_mul2r leqnSn orbT.
have -> : y + m.+1 * v = y + m * v + v by rewrite mulSnr addnA.
rewrite dstD; first by rewrite IH // -pE mulSnr subnDA.
by rewrite IH // -pE leq_psubRL // -mulSnr.
Qed.

(** DEAD END, see alg2-notes.md 1. *)
(** split on [m] vs [Dst y %/ p]; the guard is essential (notes 1). *)
Lemma mod_le_restricted p q d u v y :
  inv p q d u v -> invd p q d u v -> invx p q u v -> p < q -> y < u + v ->
  Dst y %/ p <= q %/ p -> d %% p <= Dst y %% p.
Proof.
move=> iv ivd ix pLq yLuv Hg.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
have [_ _ dcong] := ivd.
have [a [b [aLu bLv Hab]]] := invx_gap ix yLuv.
have qdiv : q %/ p * p <= q by rewrite leq_divM.
(* the guard says exactly [Dst y < p + q] *)
have Hlt : Dst y < p + q.
  rewrite {1}(divn_eq (Dst y) p) addnC.
  apply: leq_ltn_trans (_ : Dst y %% p + q %/ p * p < _).
    by rewrite leq_add2l leq_mul2r Hg orbT.
  apply: leq_ltn_trans (leq_add (leqnn (Dst y %% p)) qdiv) _.
  by rewrite ltn_add2r ltn_pmod.
case: b Hab bLv => [|[|b]] Hab bLv.
(* no [q] in the decomposition: the two residues agree outright *)
- by rewrite Hab mul0n addn0 addnC modnMDl dcong.
(* exactly one [q]: then [a = 0] and [Dst y %% p = Inf + q %% p] *)
- have a0 : a = 0.
    case: a Hab aLu => // a Hab aLu; move: Hlt; rewrite Hab mul1n ltnNge => /negP[].
    by rewrite leq_add2r (leq_trans _ (leq_addl _ _)) // mulSnr leq_addl.
  move: Hab; rewrite a0 mul0n addn0 mul1n => Hab.
  have Hd : Dst y %/ p = q %/ p.
    apply/eqP; rewrite eqn_leq Hg /=.
    by rewrite leq_div2r // Hab leq_addl.
  have -> : Dst y %% p = Dst y - Dst y %/ p * p.
    by rewrite {2}(divn_eq (Dst y) p) addKn.
  rewrite Hd Hab dcong modn_small; last first.
    by move: Hlt; rewrite Hab ltn_add2r.
  rewrite leq_subRL; last by rewrite (leq_trans qdiv) // leq_addl.
  by rewrite addnC leq_add2l.
(* two or more [q]s is impossible: [p < q] gives [p + q < 2*q <= Dst y] *)
have Hq2 : p + q < 2 * q by rewrite mul2n -addnn ltn_add2r.
have HD : 2 * q <= Dst y.
  rewrite Hab (leq_trans _ (leq_addl _ _)) // leq_mul2r.
  by apply/orP; right.
by move: Hlt; rewrite ltnNge => /negP[]; exact: leq_trans (ltnW Hq2) HD.
Qed.

Lemma le_lt_nowrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> m * p <= Dst y -> d %% p <= Dst y - m * p.
Proof.
move=> iv ivd ix pLq yLuv /andP[m_gt0 mk] Hmp.
have [p_gt0 _ _ _ _ _ _ _] := iv.
have mdiv : m <= Dst y %/ p by rewrite leq_divRL.
case: (ltnP m (Dst y %/ p)) => [Hlt|Hge].
  apply: leq_trans (_ : p <= _); first by rewrite ltnW // ltn_pmod.
  by rewrite leq_subRL // -mulSnr -leq_divRL.
have mE : m = Dst y %/ p by apply/eqP; rewrite eqn_leq mdiv Hge.
rewrite mE.
have -> : Dst y - Dst y %/ p * p = Dst y %% p.
  by rewrite {1}(divn_eq (Dst y) p) addKn.
by apply: mod_le_restricted iv ivd ix pLq yLuv _; rewrite -mE.
Qed.

(** the WRAP companion of [walk_lt_nowrap]. *)
Lemma walk_lt_wrapeq p q d u v y m :
  inv p q d u v -> invd p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> Dst y < m * p -> Dst (y + m * v) = Dst y + M - m * p.
Proof.
move=> iv ivd pLq yLuv /andP[m_gt0 mk] Hy.
have [p_gt0 _ _ pE qE _ _ _] := iv.
have mpq : m * p <= q by rewrite -leq_divRL.
have mpM : m * p <= M by rewrite (leq_trans mpq) // qE leq_subr.
rewrite dst_add pt_muln -pE.
case: (ltnP (m * p) M) => [Hlt|Hge].
  rewrite (modn_small Hlt) modn_small //.
  rewrite ltn_subLR ?ltn_add2r //.
  by rewrite (leq_trans mpM) // leq_addl.
have mpE : m * p = M by apply/eqP; rewrite eqn_leq mpM Hge.
by rewrite mpE modnn subn0 modnDr modn_small ?dst_lt // addnK.
Qed.

Lemma le_lt_wrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> Dst y < m * p -> d %% p <= Dst (y + m * v).
Proof.
move=> iv ivd pLq yLuv mk Hy.
rewrite (walk_lt_wrapeq iv ivd pLq yLuv mk Hy).
have [p_gt0 q_gt0 bez _ _ _ u_gt0 v_gt0] := iv.
have /andP[m_gt0 mkd] := mk.
have mpq : m * p <= q by rewrite -leq_divRL.
(* the whole point of [inv_u0]/[inv_v0]: [p + q <= M] *)
have pqM : p + q <= M by rewrite -bez leq_add // leq_pmull.
have mpM : m * p <= M by rewrite (leq_trans mpq) // (leq_trans _ pqM) // leq_addl.
apply: leq_trans (_ : p <= _); first by rewrite ltnW // ltn_pmod.
rewrite leq_subRL; last by rewrite (leq_trans mpM) // leq_addl.
apply: leq_trans (_ : M <= _); last by rewrite leq_addl.
by rewrite (leq_trans (leq_add mpq (leqnn p))) // addnC.
Qed.

Lemma step_invd_le_new_lt_at p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  p < q -> y < u + v -> 0 < m <= q %/ p -> d %% p <= Dst (y + m * v).
Proof.
move=> iv ivd ix uvLN pLq yLuv mk.
case: (leqP (m * p) (Dst y)) => [Hmp|Hmp].
  rewrite (walk_lt_nowrap iv ivd pLq yLuv mk Hmp).
  exact: le_lt_nowrap iv ivd ix pLq yLuv mk Hmp.
exact: le_lt_wrap iv ivd pLq yLuv mk Hmp.
Qed.

Lemma step_invd_le_new_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  forall x, u + v <= x < u + (q %/ p) * v + v -> d %% p <= Dst x.
Proof.
move=> iv ivd ix uvLN pLq x /andP[xge xlt].
have v_gt0 : 0 < v.
  case: (posnP v) => // v0.
  have [p_gt0 _ _ pE _ _ _ _] := iv.
  by move: p_gt0; rewrite pE v0 pt0.
have [m mk /andP[ylt myx]] := new_index_decomp v_gt0 xge xlt.
rewrite -{1}(subnK myx).
exact: step_invd_le_new_lt_at iv ivd ix uvLN pLq ylt mk.
Qed.

(** the mirror.  [new_index_decomp] is reused with [u] and [v] SWAPPED:
    its window [u + k*v + v] becomes [v + k*u + u], which is exactly this
    branch's [u + (v + (p %/ q) * u)].  The walk then descends the index
    ([step_d_ge]) instead of ascending. *)
(** the [ge] branch is easier: [d' <= d], and stepping by [u] raises
    [Dst] by [q]. *)
Lemma step_ge_d_le p q d : q <= p ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d) <= d.
Proof.
move=> qLp; case: (leqP (p - p %/ q * q) d) => // dge.
by apply: leq_trans (leq_mod _ _) _; rewrite leq_subr.
Qed.

(** in the [ge] branch [d] IS the closest distance: [d] and [Inf] are
    both below [p] and congruent mod [p]. *)
Lemma ge_d_eq_inf p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> q <= p ->
  d = Inf (u + v).
Proof.
move=> iv ivd ix qLp.
have [dmax _ dcong] := ivd.
have dp : d < p by move: dmax; rewrite /maxn ifN // -leqNgt.
have ip : Inf (u + v) < p by move: (invx_inf ix); rewrite /maxn ifN // -leqNgt.
by rewrite -(modn_small dp) dcong modn_small.
Qed.

Lemma walk_ge_nowrap p q d u v y m :
  inv p q d u v -> q <= p -> y < u + v -> 0 < m <= p %/ q ->
  Dst y + m * q < M -> Dst (y + m * u) = Dst y + m * q.
Proof.
move=> iv qLp yLuv /andP[m_gt0 mk] Hw.
have [p_gt0 q_gt0 _ pE qE _ _ _] := iv.
have PuE : Pt u = M - q by rewrite qE subKn // ltnW // pt_lt.
have mqM : m * q < M by rewrite (leq_ltn_trans (leq_addl (Dst y) _)).
have Hpm : Pt (m * u) = M - m * q.
  rewrite pt_muln PuE mulnBr.
  have -> : m * M - m * q = (m - 1) * M + (M - m * q).
    rewrite addnBA; last by apply: ltnW.
    by rewrite subn1 -mulSnr prednK.
  by rewrite modnMDl modn_small // ltn_subrL muln_gt0 m_gt0 q_gt0 M_gt0.
by rewrite dst_add Hpm (subnBA _ (ltnW mqM)) addnAC addnK modn_small.
Qed.

(** the wrap companion of [walk_ge_nowrap].  [m * q <= p < M] now comes
    from [p + q <= M] ([inv_bez] with [inv_u0]/[inv_v0]), not from the
    no-wrap hypothesis. *)
Lemma walk_ge_wrapeq p q d u v y m :
  inv p q d u v -> q <= p -> y < u + v -> 0 < m <= p %/ q ->
  M <= Dst y + m * q -> Dst (y + m * u) = Dst y + m * q - M.
Proof.
move=> iv qLp yLuv /andP[m_gt0 mk] Hw.
have [p_gt0 q_gt0 bez pE qE _ u_gt0 v_gt0] := iv.
have pqM : p + q <= M by rewrite -bez leq_add // leq_pmull.
have mqp : m * q <= p by rewrite -leq_divRL.
have mqM : m * q < M.
  have pM : p < M by rewrite (leq_trans _ pqM) // -addn1 leq_add2l.
  by rewrite (leq_ltn_trans mqp).
have PuE : Pt u = M - q by rewrite qE subKn // ltnW // pt_lt.
have Hpm : Pt (m * u) = M - m * q.
  rewrite pt_muln PuE mulnBr.
  have -> : m * M - m * q = (m - 1) * M + (M - m * q).
    rewrite addnBA; last by apply: ltnW.
    by rewrite subn1 -mulSnr prednK.
  by rewrite modnMDl modn_small // ltn_subrL muln_gt0 m_gt0 q_gt0 M_gt0.
rewrite dst_add Hpm (subnBA _ (ltnW mqM)) addnAC addnK.
rewrite -{1}(subnK Hw) modnDr modn_small // ltn_subLR //.
by rewrite (leq_ltn_trans (leq_add (ltnW (dst_lt y)) (leqnn _))) // ltn_add2l.
Qed.

(** two halves: [q <= W] is [ge_d_lt_q], [W < q] is [ge_wrap_tight].
    alg2-notes.md 1-2 for what is refuted here. *)

(** the new [d] is below [q] in both branches of its conditional: the
    [then] branch is a remainder mod [q], and the [else] branch has
    [d < p - p %/ q * q = p %% q < q].  This is what makes the
    non-tight half of [le_ge_wrap] trivial. *)
Lemma ge_d_lt_q p q d : 0 < q ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d) < q.
Proof.
move=> q_gt0.
have pmod : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
case: (leqP (p - p %/ q * q) d) => [_|H]; first by rewrite ltn_pmod.
by rewrite (leq_ltn_trans (ltnW H)) // pmod ltn_pmod.
Qed.

(** [ge_wrap_au] was FALSE; see alg2-notes.md 2. *)

(** names no decomposition, so a probe quantifies as it does. *)
Lemma ge_wrap_tight p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> q <= p ->
  y < u + v -> 0 < m <= p %/ q ->
  M <= Dst y + m * q -> Dst y + m * q - M < q ->
  Inf (u + v) <= Dst y + m * q - M \/
  Dst y + m * q - M =
    (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d).
Proof. Admitted.

(** the [q]-side walk, mirror of [invx_p1_iter]; one extra [modnDml]. *)
Lemma invx_p2_iter p q u v k z :
  invx p q u v -> 0 < u -> k * u <= z -> z < u + v ->
  Pt (z - k * u) = (Pt z + k * q) %% M.
Proof. Admitted.

Lemma le_ge_wrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  q <= p -> y < u + v -> 0 < m <= p %/ q -> M <= Dst y + m * q ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    <= Dst (y + m * u).
Proof.
move=> iv ivd ix uvLN qLp yLuv mk Hw.
have [_ q_gt0 _ _ _ _ _ _] := iv.
rewrite (walk_ge_wrapeq iv qLp yLuv mk Hw).
case: (leqP q (Dst y + m * q - M)) => [qW|Wq].
  by apply: leq_trans (ltnW (ge_d_lt_q p d q_gt0)) qW.
case: (ge_wrap_tight iv ivd ix qLp yLuv mk Hw Wq) => [IW|->] //.
apply: leq_trans (step_ge_d_le d qLp) _.
by rewrite (ge_d_eq_inf iv ivd ix qLp).
Qed.

Lemma step_invd_le_new_ge_at p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  q <= p -> y < u + v -> 0 < m <= p %/ q ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    <= Dst (y + m * u).
Proof.
move=> iv ivd ix uvLN qLp yLuv mk.
case: (ltnP (Dst y + m * q) M) => [Hw|Hw]; last first.
  by apply: le_ge_wrap iv ivd ix uvLN qLp yLuv mk Hw.
rewrite (walk_ge_nowrap iv qLp yLuv mk Hw).
apply: leq_trans (step_ge_d_le d qLp) _.
apply: leq_trans (leq_addr _ _).
have [_ dle _] := ivd.
by apply: leq_trans dle _; apply: inf_dst_le.
Qed.

Lemma step_invd_le_new_ge p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> q <= p ->
  forall x, u + v <= x < u + (v + (p %/ q) * u) ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d) <= Dst x.
Proof.
move=> iv ivd ix uvLN qLp x /andP[xge xlt].
(* NOT derivable from [inv] (u = 0, v = 1, q = M is a model of it);
   but when [u = 0] the index range is empty, so [xge]/[xlt] clash. *)
have u_gt0 : 0 < u.
  case: (posnP u) => // u0.
  move: xlt xge; rewrite u0 muln0 addn0 add0n => H1 H2.
  by have := leq_ltn_trans H2 H1; rewrite ltnn.
have xge' : v + u <= x by rewrite addnC.
have xlt' : x < v + p %/ q * u + u by rewrite addnC.
have [m mk /andP[ylt myx]] := new_index_decomp (k := p %/ q) u_gt0
  (x := x) (u := v) (v := u) xge' xlt'.
rewrite -{1}(subnK myx).
rewrite addnC in ylt.
exact: step_invd_le_new_ge_at iv ivd ix uvLN qLp ylt mk.
Qed.

Lemma step_invd_le_new p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in
  forall x, u + v <= x < u' + v' -> d' <= Dst x.
Proof.
move=> iv ivd ix uvLN.
have Hlt := step_invd_le_new_lt iv ivd ix uvLN.
have Hge := step_invd_le_new_ge iv ivd ix uvLN.
rewrite /step; case: ltnP => [pLq|qLp] /=.
  by apply: Hlt.
by apply: Hge.
Qed.

Lemma step_invd_le_pt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in
  d' <= M /\ (forall x, x < u' + v' -> d' <= Dst x).
Proof.
move=> iv ivd ix uvLN.
have [_ dle _] := ivd.
have HdM : d <= M by rewrite (leq_trans dle) // (inf_dst_mono (leq0n (u + v))).
have Hnew := step_invd_le_new iv ivd ix uvLN.
have Hdd : let: (_, _, d', _, _) := step p q d u v in d' <= d.
  rewrite /step; case: ltnP => /= _; first by rewrite leq_mod.
  case: (leqP (p - p %/ q * q) d) => [_|_] //.
  by rewrite (leq_trans (leq_mod _ _)) // leq_subr.
case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hnew Hdd.
split; first by rewrite (leq_trans Hdd).
move=> x xLuv.
case: (ltnP x (u + v)) => [xold|xnew].
  by rewrite (leq_trans Hdd) // (leq_trans dle) // inf_dst_le.
by apply: Hnew; rewrite xnew xLuv.
Qed.

Lemma step_invd_le p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in d' <= Inf (u' + v').
Proof.
move=> iv ivd ix uvLN.
have H := step_invd_le_pt iv ivd ix uvLN.
case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in H.
have [HM Hpt] := H.
by apply: le_inf_dst.
Qed.

(** and preserve it.  The two branches are genuinely different: [p < q]
    keeps the modulus ([p' = p]) so [invd_cong] transports directly, while
    [q <= p] CHANGES it to [p %% q], so its congruence is a different
    statement and gets its own helper. *)
(** stronger than the congruence needed; only [<=] is real content. *)
Lemma inf_new_lt_le p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  Inf (u + (q %/ p) * v + v) <= Inf (u + v) %% p.
Proof.
move=> iv ivd ix uvLN pLq.
have [p_gt0 q_gt0 _ _ _ _ u_gt0 v_gt0] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y yLuv HyE] := inf_dst_ex uv_gt0.
(* [invx_inf] is what puts the walk inside the new range *)
have Iq : Inf (u + v) < q.
  by have := invx_inf ix; rewrite /maxn ifT.
set m := Inf (u + v) %/ p.
have mq : m <= q %/ p by rewrite leq_div2r // ltnW.
have mpI : m * p <= Inf (u + v) by rewrite leq_divM.
case: (posnP m) => [m0|m_gt0].
  have IltP : Inf (u + v) < p by rewrite ltnNge -divn_gt0 // -/m m0.
  rewrite (modn_small IltP).
  by apply: inf_dst_mono; rewrite -addnA leq_add2l leq_addl.
have Hm : 0 < m <= q %/ p by rewrite m_gt0.
have Hmp : m * p <= Dst y by rewrite -HyE.
have Hw := walk_lt_nowrap iv ivd pLq yLuv Hm Hmp.
rewrite -HyE in Hw.
have HwE : Dst (y + m * v) = Inf (u + v) %% p.
  by rewrite Hw /m {1}(divn_eq (Inf (u + v)) p) addKn.
rewrite -HwE; apply: inf_dst_le.
have -> : u + q %/ p * v + v = u + v + q %/ p * v.
  by rewrite -!addnA (addnC v).
by rewrite (leq_ltn_trans (leq_add (leqnn y) (_ : m * v <= q %/ p * v)))
   ?leq_mul2r ?mq ?orbT // ltn_add2r.
Qed.

Lemma inf_new_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  Inf (u + (q %/ p) * v + v) = Inf (u + v) %% p.
Proof.
move=> iv ivd ix uvLN pLq.
have [_ _ dcong] := ivd.
apply/eqP; rewrite eqn_leq (inf_new_lt_le iv ivd ix uvLN pLq) /=.
rewrite -dcong.
have := step_invd_le iv ivd ix uvLN.
by rewrite /step pLq /=.
Qed.

Lemma inf_cong_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  Inf (u + (q %/ p) * v + v) = Inf (u + v) %[mod p].
Proof. by move=> iv ivd ix uvLN pLq; rewrite (inf_new_lt iv ivd ix uvLN pLq) modn_mod. Qed.

Lemma inf_cong_ge p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> q <= p ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    = Inf (u + (v + (p %/ q) * u)) %[mod (p - p %/ q * q)].
Proof. Admitted.

Lemma step_invd_cong p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in
  d' = Inf (u' + v') %[mod p'].
Proof.
move=> iv ivd ix uvLN.
have [_ _ dcong] := ivd.
have Hlt := inf_cong_lt iv ivd ix uvLN.
have Hge := inf_cong_ge iv ivd ix uvLN.
rewrite /step; case: ltnP => [pLq|qLp] /=; last by apply: Hge.
by rewrite modn_mod dcong (Hlt pLq).
Qed.

Lemma step_invd p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in invd p' q' d' u' v'.
Proof.
move=> iv ivd ix uvLN.
have Hm := step_invd_max iv ivd.
have Hl := step_invd_le iv ivd ix uvLN.
have Hc := step_invd_cong iv ivd ix uvLN.
case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hm Hl Hc.
by split.
Qed.

(* CFrac: slater.get_min_NZ / get_max_NZ. *)
(** [inv_complete] was FALSE; these are conditioned on [u'+v' < N]. *)


(* glue -- assemble [step_p_gt0], [step_bez], [step_pt], [step_d] into
   the record.  Mechanical once the four are done; write it last. *)
(** conditioned as [step_p_gt0] is: only needed when the loop continues. *)
Lemma inv_step p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in
  u' + v' < N -> inv p' q' d' u' v'.
Proof.
move=> iv uvLN.
have Hg := step_p_gt0 iv uvLN.
have Hb := step_bez iv.
have Hpt := step_pt iv.
have [_ _ _ _ _ gE u_gt0 v_gt0] := iv.
move: Hg Hb Hpt; rewrite /step.
have [pLq|qLp] := ltnP => /= Hg Hb Hpt Huv.
  have [Hp Hq] := Hg Huv.
  have [Hpv Hqu] := Hpt Hp Hq.
  split => //.
    have -> : q - q %/ p * p = q %% p by rewrite {1}(divn_eq q p) addnC addnK.
    by rewrite gcdn_modr.
  by rewrite addn_gt0 u_gt0.
have [Hp Hq] := Hg Huv.
have [Hpv Hqu] := Hpt Hp Hq.
split => //.
  have -> : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
  by rewrite gcdnC gcdn_modr gcdnC.
by rewrite addn_gt0 v_gt0.
Qed.

(** *** Termination *)

(** [p + q] strictly decreases: each branch subtracts at least the other
    length, which is positive. *)
(* pure -- [q - (q %/ p) * p = q %% p < p <= q] by [ltn_mod] (needs
   [0 < p], from [inv_p0]), so [q] strictly drops in the first branch and
   [p] in the second.  One [modn_def]/[ltn_mod] each; no geometry. *)
Lemma step_measure p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', _, _, _) := step p q d u v in p' + q' < p + q.
Proof.
case => p_gt0 q_gt0 _ _ _ _ _ _ _.
rewrite /step; have [pLq|qLp] := ltnP; rewrite /=.
  have kp_gt0 : 0 < q %/ p * p by rewrite muln_gt0 p_gt0 andbT divn_gt0 // ltnW.
  by rewrite ltn_add2l ltn_subrL kp_gt0 q_gt0.
have kq_gt0 : 0 < p %/ q * q by rewrite muln_gt0 q_gt0 andbT divn_gt0.
by rewrite ltn_add2r ltn_subrL kq_gt0 p_gt0.
Qed.

(** [fuel_enough] was in the skeleton to relate an arbitrary fuel to
    [p + q]; it turned out to be unnecessary and has been removed.
    [run_sound] carries [p + q <= fuel] directly, and [lefevre] runs with
    [fuel = M] while [p + q = A %% M + (M - A %% M) = M], so the
    hypothesis is met exactly.  Nothing else referred to it. *)


(** *** The exit, and the main result *)

(** At the exit [u + v >= N], so the configuration has at least [N]
    points; [d] is a distance in that configuration, hence at most the
    infimum taken over the smaller set [x < N]. *)
(* CFrac: slater.LminDmax -- why [u + v] overshoots [N]. *)
(** At the exit [N <= u + v], so the configuration has at least [N]
    points and its closest-left distance is at most the one over the
    smaller index range; [invd_le] then gives the bound. *)
Lemma exit_bound p q d u v :
  invd p q d u v -> N <= u + v -> d <= Inf N.
Proof.
by case=> _ dLinf _ NLuv; apply: leq_trans dLinf (inf_dst_mono NLuv).
Qed.


(* glue -- induction on [fuel]; at each turn either the loop exits and
   [exit_bound] applies, or [inv_step] re-establishes the invariant. *)
Lemma run_sound fuel p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p + q <= fuel ->
  run fuel p q d u v N <= Inf N.
Proof.
elim: fuel p q d u v => [|fuel IH] p q d u v iv ivd ix uvLN Lf.
  have [p_gt0 _ _ _ _ _ _ _] := iv.
  by move: Lf; rewrite leqn0 addn_eq0 => /andP[/eqP p0 _]; rewrite p0 in p_gt0.
have Hi := inv_step iv uvLN.
have Hx := invx_step iv ix uvLN.
have Hd := step_invd iv ivd ix uvLN.
have Hm := step_measure iv uvLN.
rewrite /=; case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hi Hx Hd Hm.
case: (leqP N (u' + v')) => [NLuv|uvLN'].
  exact: exit_bound Hd NLuv.
apply: IH => //; [exact: Hi uvLN' | exact: Hx uvLN' | ].

by rewrite -ltnS (leq_trans Hm).
Qed.

(** The algorithm returns a lower bound on the infimum. *)
(* glue -- [run_sound] applied to [inv_init], with fuel [M] and
   [A %% M + (M - A %% M) = M] by [subnKC]. *)
Theorem lefevre_sound : 2 < N -> lefevre M A B N <= Inf N.
Proof.
move=> N_gt2; rewrite /lefevre.
have HM : A %% M <= M by rewrite ltnW // ltn_mod.
have Hpq : A %% M + (M - A %% M) = M by rewrite subnKC.
have Hi := inv_step inv_init N_gt2.
have Hx := invx_step inv_init invx_init N_gt2.
have Hd := invd_first.
have Hm := step_measure inv_init N_gt2.
rewrite -{1}(prednK M_gt0) /=.
case E: (step (A %% M) (M - A %% M) (B %% M) 1 1)
     => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hi Hx Hd Hm.
case: (leqP N (u' + v')) => [NLuv|uvLN'].
  exact: exit_bound Hd NLuv.
apply: run_sound => //; [exact: Hi uvLN' | exact: Hx uvLN' |].
by rewrite -ltnS prednK // (leq_trans Hm) // Hpq.
Qed.

(** The form the search actually uses: if the returned bound clears the
    threshold, there is no hard-to-round case in this sub-interval. *)
(* glue -- [lefevre_sound] then [inf_dst_le]; two lines.
   This is the statement the HR-case search consumes, so it is worth
   writing down even while everything above is admitted: it pins the
   interface and lets Search.v/Check.v be re-plumbed against it. *)
Corollary lefevre_test eps :
  2 < N -> eps < lefevre M A B N -> forall x, x < N -> eps < Dst x.
Proof.
move=> N_gt2 epsL x xLN.
apply: leq_trans epsL _.
by apply: leq_trans (lefevre_sound N_gt2) _; apply: inf_dst_le xLN.
Qed.

End Theory.
