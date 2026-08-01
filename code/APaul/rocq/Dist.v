(******************************************************************************)
(*                                                                            *)
(*   Points of the sequence [a*x mod 1] and their distance to [b]             *)
(*                                                                            *)
(*   The vocabulary shared by the lower-bound algorithm and by any search     *)
(*   that scans those points: the points [pt], the distances [dst], the       *)
(*   running minimum [inf], and how far the sequence can run before it        *)
(*   returns to the origin.  Everything is [nat]; modular arithmetic occurs   *)
(*   only in the definitions.                                                 *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*     The specification                                                      *)

(*  The point [a*x mod 1], scaled by [M].                                     *)
Definition pt (M A x : nat) := (A * x) %% M.

(*  The distance from the point [x] up to [b], scaled by [M].                 *)
Definition dst (M A B x : nat) := (B + M - pt M A x) %% M.

(*  The infimum of those distances over the first [n] indices.  Sealed;       *)
(*  unfold with [inf_dst0] and [inf_dstS].                                    *)
Fixpoint inf_dst (M A B n : nat) : nat :=
  if n is n1.+1 then minn (dst M A B n1) (inf_dst M A B n1) else M.

Arguments inf_dst : simpl never.

Section Theory.

(*  The modulus, and the two numerators: the line is [y = a*x - b] with       *)
(*  [a = A/M] and [b = B/M].                                                  *)
Variable M : nat.
Hypothesis M_gt0 : 0 < M.

Variables A B : nat.
Hypothesis ltn_A : A < M.
Hypothesis ltn_B : B < M.

(*  The number of points searched.  It stays below the orbit size, so no      *)
(*  index below it returns to the origin ([pt_neq0]).                         *)
Variable N : nat.
Local Notation g := (gcdn A M).

Hypothesis N_gt0 : 0 < N.
Hypothesis N_lt_Mg : N < M %/ g.

(*  [pt x] is the point, [dst x] its distance to [b], [Inf n] the infimum     *)
(*  of the distances over the first [n] indices.                              *)
Local Notation pt := (pt M A).
Local Notation dst := (dst M A B).
Local Notation inf := (inf_dst M A B).


(*  Elementary facts about the points [pt]                                    *)

(** A point lies below [M]. *)
Lemma ltn_pt x : pt x < M.
Proof. by rewrite ltn_mod. Qed.

(*  The sequence starts at the origin.                                        *)
Lemma pt0 : pt 0 = 0.
Proof. by rewrite /pt muln0 mod0n. Qed.

(*  Points add, modulo [M].                                                   *)
Lemma ptDE x y : pt (x + y) = (pt x + pt y) %% M.
Proof. by rewrite modnDm -mulnDr. Qed.

(*  Subtracting indices subtracts points, when the points are ordered.        *)
Lemma ptB x y : y <= x -> pt y <= pt x -> pt (x - y) = pt x - pt y.
Proof.
move=> yLx pyLpx.
rewrite /pt mulnBr modnB //; last by rewrite leq_mul2l yLx orbT.
by rewrite ltnNge pyLpx /= mul0n add0n.
Qed.

(*  The point [q] below [pt z], as an index difference.                       *)
Lemma ptBu q u z : q = M - pt u -> u <= z -> pt (z - u) = (pt z + q) %% M.
Proof.
move=> qE uLz.
have pzE : pt z = (pt (z - u) + pt u) %% M by rewrite -ptDE subnK.
rewrite qE pzE modnDml -addnA (subnKC (ltnW (ltn_pt u))) modnDr.
by rewrite modn_small // ltn_pt.
Qed.

(*  A multiple of an index multiplies the point, modulo [M].                  *)
Lemma ptM k x : pt (k * x) = (k * pt x) %% M.
Proof. by rewrite /pt modnMmr mulnCA. Qed.

(*  Multiples of a point stay exact while they stay below [M].                *)
Lemma ptM_small k : pt 1 * k < M -> pt k = pt 1 * k.
Proof.
move=> H; have -> : pt k = (pt 1 * k) %% M by rewrite /pt muln1 modnMml.
by rewrite modn_small.
Qed.

(*  In the [M - A <= A] branch the first points descend by [M - A] each.      *)
Lemma ptS j : j * (M - A) <= A -> pt j.+1 = A - j * (M - A).
Proof.
move=> jLA.
have ALM : A <= M by rewrite ltnW.
have jME : j * M = j * (M - A) + j * A by rewrite -mulnDr subnK.
rewrite /pt.
have -> : A * (j.+1) = A - j * (M - A) + j * M.
  by rewrite jME addnA subnK // mulnS mulnC.
rewrite addnC modnMDl modn_small //.
by rewrite (leq_ltn_trans (leq_subr _ _)).
Qed.

(* Stepping the index by [v] raises the point by [pt v], while below [M]      *)
Lemma ptD x y : pt x + pt y < M -> pt (x + y) = pt x + pt y.
Proof. by move=> pzpvLM; rewrite ptDE modn_small. Qed.

(** Iterating the [v]-step adds [j * p], modulo [M].                          *)
Lemma ptWE x y j : pt (x + j * y) = (pt x + j * pt y) %% M.
Proof.
rewrite ptDE.
suff -> : pt (j * y) = (j * pt y) %% M by rewrite modnDmr.
by rewrite ptM /pt modnMmr mulnCA // mulnCA.
Qed.

(** The [y]-walk composes with itself.                                        *)
Lemma ptWD x y m :
  m * pt y < M -> pt x + m * pt y < M -> pt (x + m * y) = pt x + m * pt y.
Proof.
move=> mpyLM pxmpyLm.
have pmyE : pt (m * y) = (m * pt y) %% M by rewrite /pt modnMmr mulnCA.
by rewrite ptDE pmyE (modn_small mpyLM) modn_small.
Qed.

(* The bound that keeps a [x]-walk below [M].                                 *)
Lemma leq_ptW q x mp : pt x <= M - q -> q <= M -> mp <= q -> pt x + mp <= M.
Proof. 
move=> ptxLMq qLM mpLq.
by apply: leq_trans (leq_add ptxLMq mpLq) _; rewrite subnK.
Qed.

(* How far the sequence can run: the orbit of [A] modulo [M]                  *)

(* [N] does not exceed the size of the orbit.                                 *)
Lemma leq_N_Mg : N <= M %/ g.
Proof. by apply: ltnW. Qed.

(* Dividing [A] and [M] by their gcd leaves them coprime.                     *)
Lemma coprime_Mg_Ag : coprime (M %/ g) (A %/ g).
Proof.
have g_gt0 : 0 < g by rewrite gcdn_gt0 M_gt0 orbT.
rewrite /coprime -(eqn_pmul2r g_gt0) mul1n muln_gcdl.
by rewrite !divnK ?dvdn_gcdl ?dvdn_gcdr // gcdnC.
Qed.

(* Only index [0] hits the origin, anywhere in the orbit.                     *)
Lemma pt_neq0M n : 0 < n < M %/ g -> pt n != 0.
Proof.
move=> /andP[n_gt0 nLMg].
have g_gt0 : 0 < g by rewrite gcdn_gt0 M_gt0 orbT.
apply/eqP => /eqP; rewrite /pt -/(_ %| _) => Hdvd.
have HM : M = g * (M %/ g) by rewrite mulnC divnK // dvdn_gcdr.
have HA : A = g * (A %/ g) by rewrite mulnC divnK // dvdn_gcdl.
have Hd : (M %/ g) %| n.
  rewrite -(Gauss_dvdr n coprime_Mg_Ag) -(dvdn_pmul2l g_gt0).
  by rewrite mulnA -HA -HM.
have := dvdn_leq n_gt0 Hd.
by rewrite leqNgt nLMg.
Qed.

(* Only index [0] hits the origin, within the search range.                   *)
Lemma pt_neq0 n : 0 < n <= N -> pt n != 0.
Proof.
by move=> /andP[n_gt0 nN]; apply: pt_neq0M; rewrite n_gt0 (leq_ltn_trans nN).
Qed.


(* Elementary facts about the points [pt] (continued)                         *)

(* The same, under the index bound the loop guarantees.                       *)
Lemma ptD_leq x y :
  0 < x + y <= N -> pt x + pt y <= M -> pt (x + y) = pt x + pt y.
Proof.
move=> xyLN; case: ltngtP => // [pxpyLm|pxpyE] _; first by exact: ptD.
by have := pt_neq0 xyLN; rewrite ptDE pxpyE modnn eqxx.
Qed.

(* The [v]-walk is exact as long as it stays below the [q]-barrier.           *)
Lemma ptWv q x y j :
  pt x <= M - q -> q <= M -> j * pt y <= q -> 0 < x + j * y <= N ->
  pt (x + j * y) = pt x + j * pt y.
Proof.
move=> pxLMq qLM jpyLq xyjLN.
have pxjpyLM : pt x + j * pt y <= M.
  by apply: leq_trans (leq_add pxLMq jpyLq) _; rewrite subnK.
have pxjyE : pt (x + j * y) = (pt x + j * pt y) %% M by apply: ptWE.
rewrite pxjyE modn_small // ltn_neqAle pxjpyLM andbT.
apply/eqP => pxjpyE.
by have := pt_neq0 xyjLN; rewrite pxjyE pxjpyE modnn eqxx.
Qed.


(*  How far the sequence can run: the orbit of [A] modulo [M] (continued)     *)

(* Every point is a multiple of [g].                                          *)
Lemma dvdn_g_pt x : g  %| pt x.
Proof.
by apply/eqP; rewrite /pt (modn_dvdm _ (dvdn_gcdr A M)); apply/eqP;
   apply: dvdn_mulr; exact: dvdn_gcdl.
Qed.


(* Elementary facts about the distances [dst]                                 *)

(* A distance lies below [M].                                                 *)
Lemma ltn_dst x : dst x < M.
Proof. by rewrite ltn_mod. Qed.

(* The distance at index [0] is [B].                                          *)
Lemma dst0 : dst 0 = B.
Proof. by rewrite /dst pt0 subn0 modnDr modn_small. Qed.

(** The distance, unfolded, when the point is below [B].                      *)
Lemma dstE x : dst x = (B + M - pt x) %% M.
Proof. by []. Qed.

(** The distance, unfolded, when the point is above [B].                      *)
Lemma dstD x y : pt y <= dst x -> dst (x + y) = dst x - pt y.
Proof.
move=> ptLdx; rewrite dstE ptDE.
have pxpyLM2 : pt x + pt y < M.*2.
  rewrite -addnn; apply: ltn_trans (_ : M + pt y < _).
    by rewrite ltn_add2r ltn_pt.
  by rewrite ltn_add2l ltn_pt.
have [pxpyLM|MLpxpy]:= ltnP (pt x + pt y) M.
  rewrite [(pt x + _) %% _]modn_small //.
  rewrite subnDA modnB //; last by apply: leq_trans ptLdx (leq_mod _ _).
  rewrite -[_ %% M]/(dst x) ltnNge modn_small; last by apply: ltn_pt.
  by rewrite ptLdx add0n.
have -> : (pt x + pt y) %% M  = pt x + pt y - M.
  by rewrite -[in LHS](subnK MLpxpy) modnDr modn_small // ltn_subLR // addnn.
rewrite subnCBA // addnCA addnn [pt x + _]addnC subnDAC.
rewrite modnB ?ltn_pt //; last first.
  rewrite leq_subRL; first by apply: leq_trans (ltnW _) (leq_addl _ _).
  apply: leq_trans (ltnW (ltn_pt _)) (leq_trans _ (leq_addl _ _)).
  by rewrite -addnn leq_addr.
rewrite ![pt _ %% _]modn_small ?ltn_pt //.
suff -> : (B + M.*2 - pt x) %% M = dst x by rewrite ltnNge ptLdx.
have -> : B + M.*2 = M + B + M by rewrite addnAC addnn addnC.
rewrite subDnCA; first by rewrite modnDl addnC.
by rewrite (leq_trans (ltnW (ltn_pt _))) // leq_addr.
Qed.

(* A point below [B] is at distance [B - pt x].                               *)
Lemma dst_below x : pt x <= B -> dst x = B - pt x.
Proof.
move=> pxLB; rewrite dstE addnC -addnBA // modnDl modn_small //.
apply: leq_ltn_trans (leq_subr _ _) ltn_B.
Qed.

(** A point above [B] is at distance [B + M - pt x].                          *)
Lemma dst_above x : B < pt x -> dst x = B + M - pt x.
Proof.
move=> BLpx; rewrite dstE modn_small //.
rewrite ltn_subLR; last by rewrite (leq_trans (ltnW (ltn_pt x))) // leq_addl.
by rewrite ltn_add2r.
Qed.

(** Shifting the index down by [y] shifts the distance up by [Pt y].          *)
Lemma dstBE x y : y <= x -> dst (x - y) = (dst x + pt y) %% M.
Proof.
move=> yLx.
have pxE : pt x = (pt (x - y) + pt y) %% M by rewrite -ptDE subnK.
have pxyLM := ltn_pt (x - y); have pyLM := ltn_pt y.
rewrite dstE [in RHS]dstE modnDml pxE.
have [pxypyLM|MLpxypy] := ltnP (pt (x - y) + pt y) M.
  rewrite (modn_small pxypyLM) subnDA subnK //.
  by rewrite leq_subRL ?(leq_trans (ltnW pxyLM)) ?leq_addl //
             (leq_trans (ltnW pxypyLM)) // leq_addl.
have pxypyME : (pt (x - y) + pt y) %% M = pt (x - y) + pt y - M.
  rewrite -{1}(subnK MLpxypy) modnDr modn_small // ltn_subLR //.
  apply: leq_ltn_trans (leq_add (ltnW pxyLM) (leqnn _)) _.
  by rewrite ltn_add2l.
have pxyLBM : pt (x - y) <= B + M.
  by rewrite (leq_trans (ltnW pxyLM)) // leq_addl.
rewrite pxypyME subnBA // subnDA subnK.
  by rewrite -[in RHS]addnBAC // modnDr.
rewrite leq_subRL; last by rewrite (leq_trans pxyLBM) // leq_addr.
apply: leq_trans (leq_add (ltnW pxyLM) (ltnW pyLM)) _.
by rewrite leq_add2r leq_addl.
Qed.

(* Shifting the index up by [w] shifts the distance down by [pt w].           *)
Lemma dstDE x y : dst (x + y) = (dst x + M - pt y) %% M.
Proof.
have dxyyE := dstBE (leq_addl x y).
rewrite addnK in dxyyE.
have dxyLM := ltn_dst (x + y); have pyLM := ltn_pt y.
rewrite dxyyE; have [dxypyLM|MLdxypy] := ltnP (dst (x + y) + pt y) M.
  by rewrite (modn_small dxypyLM) addnAC addnK modnDr modn_small.
have dxypyE : (dst (x + y) + pt y) %% M = dst (x + y) + pt y - M.
  rewrite -{1}(subnK MLdxypy) modnDr modn_small // ltn_subLR //.
  apply: leq_ltn_trans (leq_add (ltnW dxyLM) (leqnn _)) _.
  by rewrite ltn_add2l.
by rewrite dxypyE subnK ?addnK ?modn_small.
Qed.

(*  Slater (6): two points are never closer than a gap                        *)
(*  In DISTANCE form (6) splits on whether the index order and the value      *)
(*  order agree: if they do the difference is a plain [Pt], if they do not    *)
(*  the walk round the circle wraps exactly once.                             *)
(*  The distance at [m2] in terms of the distance at [m1] above it.           *)
Lemma dst_diff m1 m2 : m2 <= m1 -> dst m2 = (dst m1 + pt (m1 - m2)) %% M.
Proof. by move=> H; rewrite -{1}(subKn H) dstBE // leq_subr. Qed.

(** Every distance is congruent to [B] modulo [g]].                           *)
Lemma dst_mod_g x : dst x = B %[mod g].
Proof.
have gM : g %| M := dvdn_gcdr A M.
have pxLM : pt x <= M by rewrite ltnW // /pt ltn_mod.
rewrite /dst -addnBA // (modn_dvdm _ gM) -modnDmr.
suff -> : (M - pt x) %% g = 0 by rewrite addn0.
by apply/eqP; apply: dvdn_sub; [exact: gM | exact: dvdn_g_pt].
Qed.

(* A point [t] above another is [t] closer to [B].                            *)
Lemma dst_ofD x y t : pt x = pt y + t -> t <= dst y -> dst x = dst y - t.
Proof.
move=> pxE tLdy.
have BMpxE : B + M - pt x = B + M - pt y - t by rewrite pxE subnDA.
rewrite /dst BMpxE.
move: tLdy; rewrite /dst.
set D := B + M - pt y.
have DLMM : D < M + M.
  by rewrite /D (leq_ltn_trans (leq_subr _ _)) // ltn_add2r.
have [DLM|MLD] := ltnP D M => tLDM.
  rewrite (modn_small DLM) in tLDM *.
  by rewrite modn_small // (leq_ltn_trans (leq_subr _ _)).
have DE : D %% M = D - M.
  by rewrite -{1}(subnK MLD) modnDr modn_small // ltn_subLR.
rewrite DE in tLDM *.
have DtM : M <= D - t.
  by rewrite leq_subRL ?(leq_trans tLDM (leq_subr _ _)) // addnC -leq_subRL.
rewrite -{1}(subnK DtM) modnDr modn_small; first by rewrite subnAC.
by rewrite ltn_subLR // (leq_ltn_trans (leq_subr _ _)).
Qed.

(** A residue below the distance stays below it after reduction.              *)
Lemma leq_mod_dst g x : 0 < g -> g = pt 1 -> pt 1 * x <= M -> B %% g <= dst x.
Proof.
move=> g_gt0 gE Hx.
have pxEM : pt x = (g * x) %% M by rewrite gE /pt muln1 modnMml.
have BgLB : B %% g <= B by apply: leq_mod.
have [gxLM|MLgx] := ltnP (g * x) M; last first.
  have gxE : g * x = M by apply/eqP; rewrite eqn_leq MLgx andbT gE.
  by rewrite dstE pxEM gxE modnn subn0 modnDr (modn_small ltn_B).
have pxE : pt x = g * x by rewrite pxEM modn_small.
have [BgLdx|dxLBg] := leqP (g * x) B.
  rewrite dst_below ?pxE //.
  have gxLBgg : g * x <= B %/ g * g.
    have xLBg : x <= B %/ g by rewrite leq_divRL // mulnC.
    by rewrite mulnC leq_mul2r xLBg orbT.
  have -> : B %% g = B - B %/ g * g by rewrite {2}(divn_eq B g) addnC addnK.
  by apply: leq_sub2l.
rewrite dst_above ?pxE //.
apply: leq_trans BgLB _.
rewrite leq_subRL; last by rewrite (leq_trans (ltnW gxLM)) // leq_addl.
by rewrite addnC leq_add2l ltnW.
Qed.


(* The running minimum [Inf]                                                  *)

(* The empty range has infimum [M].                                           *)
Lemma inf0 : inf 0 = M.
Proof. by []. Qed.

(** One more index takes the minimum with its distance.                       *)
Lemma infSE n : inf n.+1 = minn (dst n) (inf n).
Proof. by []. Qed.

(** The infimum is below every distance in range.                             *)
Lemma leq_inf_dst n x : x < n -> inf n <= dst x.
Proof.
elim: n => // n IH; rewrite leq_eqVlt => /orP[/eqP[->]|/IH // nLx].
  by rewrite infSE geq_minl.
apply: leq_trans nLx.
by rewrite infSE geq_minr.
Qed.

(** The infimum is attained.                                                  *)
Lemma inf_ex n : 0 < n -> exists2 y, y < n & inf n = dst y.
Proof.
elim: n => // [] [_ _|n IH _].
  by exists 0; rewrite // infSE inf0; apply/minn_idPl; rewrite ltnW // ltn_dst.
rewrite infSE.
have [y yLn Hy] := IH isT; rewrite Hy.
have [dSLd|dSLs] := leqP (dst n.+1) (dst y).
  by exists n.+1 => //; apply/minn_idPl.
by exists y => //; exact: leq_trans yLn (leqnSn _).
Qed.

(** The infimum decreases as the range grows.                                 *)
Lemma leq_inf_mono m n : m <= n -> inf n <= inf m.
Proof.
move=> /subnK<-; elim: (_ - _) => // k kmLm.
by rewrite addSn infSE (leq_trans _ kmLm) // geq_minr.
Qed.

(* ThE hard one: the [d] update stays a genuine distance.                     *)
(* A bound below every distance in range is below the infimum.                *)
Lemma leq_inf e n : e <= M -> (forall x, x < n -> e <= dst x) -> e <= inf n.
Proof.
move=> eLM; elim: n => [//|n IH H]; rewrite infSE leq_min H // IH // => x xLn.
by apply: H (ltnW xLn).
Qed.

(* The maximum distance is attained.                                          *)
Lemma dst_max_ex n :
  0 < n -> exists2 y, y < n & forall z, z < n -> dst z <= dst y.
Proof.
elim: n => // [] [_ _|n IH _].
  by exists 0 => // z; rewrite ltnS leqn0 => /eqP->.
have [y yLn Hy] := IH isT.
have [dSLd|dSLs] := leqP (dst n.+1) (dst y).
  exists y; first by rewrite (leq_trans yLn).
  by move=> z; rewrite ltnS leq_eqVlt => /orP[/eqP->|zLn] //; apply: Hy.
exists n.+1 => // z; rewrite ltnS leq_eqVlt => /orP[/eqP->|zLn] //.
by rewrite (leq_trans (Hy _ zLn)) // ltnW.
Qed.


(* Arithmetic used by the loop                                                *)

(* Slater's two equations                                                     *)
(*  Slater 2 (7): at [N+1 = u+v] points the step structure has [u] steps of   *)
(*  length [alpha = p] (index [r |-> r+v], from [r < u]) and [v] of length    *)
(*  [beta = q] ([r |-> r-u]), and none of length [alpha+beta]; (8) is         *)
(*  [u*p + v*q = M], our [inv_bez].  So a walk from [y] up to [z] through     *)
(*  successive points has TWO invariants: the value one [a*p + b*q =          *)
(*  dst y - dst z] and the INDEX one [a*v + y = b*u + z].  The second is      *)
(*    what bounds the two counts.                                             *)
(* Counting step behind [gap_bounds].                                         *)
Lemma gap_count_aux k l w x t :
  0 < k -> k < x -> t < k + l -> x * l <= w * k + t -> l <= w.
Proof.
move=> k_gt0 kx tkl H.
have H1 : l + k * l < w * k + k + l.
  apply: leq_ltn_trans (_ : w * k + t < _); last first.
    by rewrite -addnA ltn_add2l.
  by rewrite (leq_trans _ H) // -mulSn leq_mul2r kx orbT.
rewrite -ltnS -(ltn_pmul2l k_gt0) mulnS mulnC [k * w]mulnC mulnC addnC.
by move: H1; rewrite addnC ltn_add2r.
Qed.

(* The remainder of the Euclidean step lies below the divisor.                *)
Lemma q'_lt_p p q : 0 < p -> q - q %/ p * p < p.
Proof. by move=> p_gt0; rewrite {1}(divn_eq q p) addnC addnK ltn_pmod. Qed.

(* After the step the larger gap is [p].                                      *)
Lemma maxn_new_lt p q : 0 < p -> maxn p (q - q %/ p * p) = p.
Proof. by move=> p_gt0; apply/maxn_idPl; rewrite ltnW // q'_lt_p. Qed.

(* Bound on the offset used by [new_index_decomp_sharp].                      *)
Lemma sharp_t_lt k u v x :
  u + v <= x -> x < u + k * v -> x - (u + v) < (k - 1) * v.
Proof.
move=> xge xlt.
have k_gt0 : 0 < k.
  case: k xlt => // ; rewrite mul0n addn0 => H.
  by have := leq_ltn_trans xge H; rewrite ltnNge leq_addr.
rewrite ltn_subLR // subn1.
move: xlt; rewrite -{1}(prednK k_gt0) mulSnr addnA => xlt.
by rewrite (leq_trans xlt) // addnAC.
Qed.

(* Bound on the multiplier used by [new_index_decomp_sharp].                  *)
Lemma sharp_j_lt_k k v t : 0 < v -> t < (k - 1) * v -> (t %/ v).+1 < k.
Proof.
move=> v_gt0 H.
have H2 : t %/ v < k - 1 by rewrite ltn_divLR.
by move: H2; rewrite ltn_subRL -addn1.
Qed.

(* Lower half of [new_index_decomp_sharp].                                    *)
Lemma sharp_lo u v x : 0 < v -> u + v <= x -> ((x - (u + v)) %/ v).+1 * v <= x.
Proof.
move=> v_gt0 xge.
rewrite mulSnr (leq_trans (leq_add (leq_divM _ _) (leqnn v))) //.
suff -> : x - (u + v) + v = x - u by rewrite leq_subr.
by rewrite subnDA subnK // -(leq_add2l u) subnKC // 
           (leq_trans _ xge) // leq_addr.
Qed.

(* Upper half of [new_index_decomp_sharp].                                    *)
Lemma sharp_hi u v x :
  0 < v -> u + v <= x -> x - ((x - (u + v)) %/ v).+1 * v < u + v.
Proof.
move=> v_gt0 xge.
rewrite ltn_subLR ?sharp_lo // -{1}(subnK xge) ltn_add2r.
by rewrite ltn_ceil.
Qed.

(* [q <= M] is free from [inv].                                               *)
(* A new index is an old one plus a multiple of the step.                     *)
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

(* The same, with the multiplier bounded by the batch.                        *)
Lemma new_index_decomp_sharp k u v x :
  0 < v -> u + v <= x -> x < u + k * v ->
  exists2 j, 0 < j < k & (x - j * v < u + v) && (j * v <= x).
Proof.
move=> v_gt0 xge xlt.
exists ((x - (u + v)) %/ v).+1; last by rewrite sharp_hi // sharp_lo.
by rewrite /= (sharp_j_lt_k v_gt0) // (sharp_t_lt xge).
Qed.

End Theory.
