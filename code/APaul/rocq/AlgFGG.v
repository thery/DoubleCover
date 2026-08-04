(******************************************************************************)
(*                                                                            *)
(*   Lefevre's lower-bound algorithm                                          *)
(*                                                                            *)
(*   Algorithm 2 of doc/mourad.pdf (hal-00751446, 4.2); its own source is     *)
(*    Lefevre's thesis ch. 2.  With [a = A/M], [b = B/M] the search wants a   *)
(*    lower bound on [inf { b - a*x mod 1 | x < N }].                         *)
(*                                                                            *)
(*    Modular arithmetic occurs ONLY in the spec ([dst]).  The loop keeps     *)
(*    naturals [(p,q,d,u,v)]: [p],[q] the two interval lengths, [u],[v] HOW   *)
(*    MANY of each, [d] the distance from [b] to its interval's lower end.    *)
(*    They stay below [M] because [u*p + v*q = M].                            *)
(*                                                                            *)
(*    Companion notes: doc/lefevre-these-notes.md (what the variables mean),  *)
(*    doc/slater-notes.md and doc/mourad-notes.md (the two papers used).      *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From APaulRocq Require Import Dist Config.

(** ** Algorithm 2                                                            *)

(*  The loop, run until the configuration has at least [N] points.  [fuel]    *)
(*  is a structural bound; [M] suffices, as [p + q] decreases from [M].       *)
Fixpoint run (fuel p q d u v N : nat) : nat :=
  if fuel is fuel1.+1 then
    let: (p', q', d', u', v') := step p q d u v in
    if N <= u' + v' then d' else run fuel1 p' q' d' u' v' N
  else d.

(*  The algorithm: start from the two-point configuration and run.  The       *)
(*  initial [q] is [1 - {a}] rather than [1], as [u*p + v*q = M] requires.    *)
Definition lefevre (M A B N : nat) : nat :=
  run M (A %% M) (M - A %% M) (B %% M) 1 1 N.

(*  Sanity checks (computed)                                                  *)
(*                                                                            *)
(*   [a = 17/45] is the example of Figure 4 of the paper.                     *)

Example lefevre_fig4 : lefevre 45 17 30 5 = 7.
Proof. by vm_compute. Qed.

Example inf_dst_fig4 : inf_dst 45 17 30 5 = 7.
Proof. by vm_compute. Qed.

(*  a case where the bound is strict: the algorithm returns 1, the true       *)
(*  infimum is 2.  So only an inequality can be proved below.                 *)
Example lefevre_strict : (lefevre 32 23 12 8, inf_dst 32 23 12 8) = (1, 2).
Proof. by vm_compute. Qed.

(******************************************************************************)
(* The theory                                                                 *)
(******************************************************************************)

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

(*  The vocabulary of Dist.v, with this section's parameters supplied, so     *)
(*  that the lemmas read here exactly as they are stated there.               *)
Local Notation ltn_pt := (ltn_pt M_gt0 A).
Local Notation pt0 := (pt0 M A).
Local Notation ptDE := (ptDE M A).
Local Notation ptS := (ptS ltn_A).
Local Notation dst0 := (dst0 A ltn_B).
Local Notation dst_below := (dst_below ltn_B).
Local Notation dst_above := (dst_above M_gt0).
Local Notation dst_ofD := (dst_ofD ltn_B).
Local Notation leq_mod_dst := (leq_mod_dst M_gt0 ltn_B).
Local Notation leq_inf_dst := (leq_inf_dst M A B).
Local Notation inf_ex := (inf_ex M_gt0 A B).
Local Notation leq_inf_mono := (leq_inf_mono M A B).

(*  and the configuration theory of Config.v, likewise.                       *)
Local Notation inv := (inv M A).
Local Notation invd := (invd M A B).
Local Notation invx := (invx M A B).
Local Notation am_gt0 := (am_gt0 M_gt0 N_gt0 N_lt_Mg).
Local Notation inv_init := (inv_init M_gt0 B ltn_A N_gt0 N_lt_Mg).
Local Notation invx_init := (invx_init M_gt0 ltn_A ltn_B).
Local Notation dst_sub_u := (dst_sub_u M_gt0).
Local Notation pt_add_u := (pt_add_u M_gt0).
Local Notation gap_q_empty := (gap_q_empty M_gt0).
Local Notation gap_p_empty := (gap_p_empty M_gt0).
Local Notation walk_lt_nowrap := (walk_lt_nowrap M_gt0).
Local Notation walk_lt_wrap_ge := (walk_lt_wrap_ge M_gt0).
Local Notation walk_ge_nowrap := (walk_ge_nowrap M_gt0).
Local Notation ge_exit := (ge_exit M_gt0 ltn_B).
Local Notation step_p_gt0 := (@step_p_gt0 M A N N_lt_Mg).
Local Notation inv_step_pos := (@inv_step_pos M M_gt0 A B ltn_B).
Local Notation invx_step := (@invx_step M M_gt0 A B ltn_B N N_lt_Mg).

(* The step preserves [inv].                                                  *)
Lemma inv_step p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in
  u' + v' < N -> inv p' q' d' u' v'.
Proof.
move=> iv uvLN.
have Hg := step_p_gt0 iv uvLN.
have Hi := inv_step_pos iv.
move: Hg Hi; rewrite /step.
have [pLq|qLp] := ltnP => /= Hg Hi Huv.
by have [Hp Hq] := Hg Huv; apply: Hi.
by have [Hp Hq] := Hg Huv; apply: Hi.
Qed.

(* These hold while the loop continues, i.e. under [u' + v' < N].             *)
(* glue -- assemble [step_p_gt0], [step_bez], [step_pt], [step_d] into        *)
(* the record.  Mechanical once the four are done; write it last.             *)
(* [p + q] strictly decreases: each branch subtracts at least the other       *)
(* length, which is positive.                                                 *)
(* [p + q] strictly decreases, so the loop terminates.                        *)
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

(* The invariant [invd] on the recorded distance, and the first step          *)


(** after the FIRST step, [d] satisfies [invd].                               *)
(** The first [d] is below the larger gap.                                    *)
Lemma invd_first_max :
  let: (p', q', d', _, _) := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' < maxn p' q'.
Proof.
have Ha := am_gt0.
have Hq : 0 < M - A %% M by rewrite subn_gt0 ltn_mod.
rewrite /step; case: ltnP => [pLq|qLp]; rewrite /=.
  by rewrite (leq_trans (ltn_pmod _ Ha)) ?leq_maxl.
have [p'Ld|dLp'] := 
    leqP (A %% M - A %% M %/ (M - A %% M) * (M - A %% M)) (B %% M).
  by rewrite (leq_trans (ltn_pmod _ Hq)) ?leq_maxr.
by rewrite (leq_trans dLp') // leq_maxl.
Qed.

(* The [A < M - A] branch: covered by [mod_le_dst].                           *)
(* The [M - A <= A] branch: by [pt_desc] the points descend by [M-A].         *)
(* First step, [A <= M - A], upper case: [d] bounds the distances.            *)
Lemma invd_first_le_ge_then : M - A %% M <= A %% M ->
  A - A %/ (M - A) * (M - A) <= B ->
  forall x, x < (A %/ (M - A)).+2 ->
  (B - (A - A %/ (M - A) * (M - A))) %% (M - A) <= dst x.
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
have HPt : pt j.+1 = A - j * (M - A) by rewrite ptS.
have HAj : (A - A %/ (M - A) * (M - A)) + (A %/ (M - A) * (M - A) - j * (M - A))
         = A - j * (M - A).
  by rewrite addnBA // subnK.
have [AjLB|BLAj] := leqP (A - j * (M - A)) B.
  rewrite dst_below ?HPt //.
  have Hs : A %/ (M - A) * (M - A) - j * (M - A)
          <= B - (A - A %/ (M - A) * (M - A)) by rewrite leq_subRL // HAj.
  rewrite -{1}(subnK Hs) -subnDA HAj.
  by rewrite -mulnBl addnC modnMDl leq_mod.
rewrite dst_above ?HPt //.
rewrite (leq_trans (ltnW (ltn_pmod _ Hq))) // leq_subRL; last first.
  by rewrite (leq_trans (leq_subr _ _)) // (leq_trans HAM) // leq_addl.
rewrite (leq_trans (_ : A - j * (M - A) + (M - A) <= M)) ?leq_addl //.
apply: leq_trans (leq_add (leq_subr _ _) (leqnn (M - A))) _.
by rewrite subnKC.
Qed.

(* First step, [A <= M - A]: [d] bounds the distances.                        *)
Lemma invd_first_le_ge : M - A %% M <= A %% M ->
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' <= inf (u' + v').
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
apply: leq_inf.
  case: (_ <= B); last by rewrite ltnW.
  by rewrite (leq_trans (leq_mod _ _)) // (leq_trans (leq_subr _ _)) // ltnW.
move=> x xLk; rewrite !muln1 !add1n in xLk.
have Hjq : forall j, j <= A %/ (M - A) -> pt j.+1 = A - j * (M - A).
  move=> j jLk; apply: ptS.
  by rewrite (leq_trans _ (leq_divM A (M - A))) // leq_mul2r jLk orbT.
have [p'LB|BLp'] := leqP (A - A %/ (M - A) * (M - A)) B; first by apply: Hthen.
case: x xLk => [_|j jLk]; first by rewrite dst0.
have jk : j <= A %/ (M - A) by rewrite -ltnS.
have HPt : pt j.+1 = A - j * (M - A) by rewrite Hjq.
have HB2 : B < pt j.+1.
  by rewrite HPt (leq_trans BLp') // leq_sub2l // leq_mul2r jk orbT.
rewrite dst_above //.
rewrite leq_subRL; last by rewrite (leq_trans (ltnW (ltn_pt _))) // leq_addl.
rewrite [pt j.+1 + B]addnC leq_add2l.
exact: ltnW (ltn_pt _).
Qed.

(* First step, [A <= M - A]: [d] is below the infimum.                        *)
Lemma invd_first_le :
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' <= inf (u' + v').
Proof.
have Ha := am_gt0.
have AME : A %% M = A by rewrite modn_small.
have BME : B %% M = B by rewrite modn_small.
have p1E : pt 1 = A by rewrite /pt muln1 AME.
have ALM : A <= M by rewrite ltnW.
have kLM : (M - A) %/ A * A + A <= M.
  by rewrite -{2}(subnK ALM) leq_add2r leq_divM.
have Hge := invd_first_le_ge.
move: Hge; rewrite /step AME BME; case: ltnP => [pLq|qLp] /= Hge; last first.
  by apply: Hge.
apply: leq_inf; first by rewrite (leq_trans (leq_mod _ _)) // ltnW.
move=> x xLk; rewrite !muln1 !add1n in xLk.
have Hk2 : A * ((M - A) %/ A + 1) <= M by rewrite mulnDr muln1 mulnC.
apply: leq_mod_dst => //; first by rewrite -AME.
rewrite p1E (leq_trans _ Hk2) // leq_mul2l.
by rewrite -ltnS xLk orbT.
Qed.

(* After the first step [d] is exactly the closest distance, so the           *)
(* congruence is free.  That equality is special to the first step, which     *)
(* is why [invd] carries a congruence rather than an equation.                *)
(* The [A < M - A] branch: the witness is [B %/ A], because                   *)
(* [dst (B %/ A) = B %% A] exactly -- the point [A * (B %/ A)] is the         *)
(* largest multiple of [A] below [b].  Its index is in range because          *)
(* [M = A + (M-A) = A + ((M-A)%/A)*A + (M-A)%%A < ((M-A)%/A + 2) * A].        *)
(* First step, [M - A < A], upper case: [d] bounds the distances.             *)
Lemma invd_first_ge_ge_then : M - A %% M <= A %% M ->
  A - A %/ (M - A) * (M - A) <= B ->
  inf (A %/ (M - A)).+2 <= (B - (A - A %/ (M - A) * (M - A))) %% (M - A).
Proof.
move=> Hge Hp.
have A_gt0 : 0 < A.
  rewrite (modn_small ltn_A) in Hge.
  case: (posnP A) => // A0; move: Hge; rewrite A0 subn0 leqn0 => /eqP MM.
  by move: M_gt0; rewrite MM.
have q_gt0 : 0 < M - A by rewrite subn_gt0.
set q := M - A in Hp q_gt0 *.
set k := A %/ q in Hp *.
set p' := A - k * q in Hp *.
set t := (B - p') %/ q.
have kqA : k * q <= A by rewrite leq_divM.
have p'E : p' = A %% q by rewrite /p' /k {1}(divn_eq A q) addnC addnK.
(* [t <= k] because [B - p' < M - p' = k*q + q]                               *)
have tk : t <= k.
  rewrite -ltnS /t ltn_divLR // mulSnr.
  have p'A : p' <= A by rewrite leq_subr.
  have Ap' : A - p' = k * q by rewrite /p' subKn.
  have -> : k * q + q = M - p' by rewrite -Ap' addnBAC // /q subnKC // ltnW.
  by rewrite ltn_sub2r // (leq_ltn_trans Hp).
(* the witness: index [(k-t)+1], whose point is [A - (k-t)*q = p' + t*q]      *)
have ktq : (k - t) * q <= A.
  by rewrite (leq_trans _ kqA) // leq_mul2r leq_subr orbT.
have pktE : pt (k - t).+1 = A - (k - t) * q by apply: ptS.
have tqkq : t * q <= k * q by rewrite leq_mul2r tk orbT.
have AktqE : A - (k - t) * q = p' + t * q.
  by rewrite mulnBl subnBA // /p' addnBAC.
have tqB : t * q <= B - p' by rewrite leq_divM.
have pktLB : pt (k - t).+1 <= B.
  by rewrite pktE AktqE -{1}(subnKC Hp) leq_add2l.
have dktE : dst (k - t).+1 = (B - p') %% q.
  rewrite dst_below // pktE AktqE subnDA.
  by rewrite {1}(divn_eq (B - p') q) addnC addnK.
rewrite -dktE; apply: leq_inf_dst.
by rewrite !ltnS leq_subr.
Qed.

(* First step, [M - A < A]: [d] bounds the distances.                         *)
Lemma invd_first_ge_ge : M - A %% M <= A %% M ->
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  inf (u' + v') <= d'.
Proof.
move=> qLp0.
have Ha := am_gt0.
have AME : A %% M = A by rewrite modn_small.
have BME : B %% M = B by rewrite modn_small.
have Hthen := invd_first_ge_ge_then qLp0.
rewrite /step AME BME; rewrite ifN /=; last by rewrite -leqNgt -AME.
have [p'LB|BLp'] := leqP (A - A %/ (M - A) * (M - A)) B; last first.
  by rewrite -[X in _ <= X]dst0; apply: leq_inf_dst.
by rewrite muln1; apply: Hthen.
Qed.

(* First step, [M - A < A]: [d] is below the infimum.                         *)
Lemma invd_first_ge :
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  inf (u' + v') <= d'.
Proof.
have Ha := am_gt0.
have AME : A %% M = A by rewrite modn_small.
have BME : B %% M = B by rewrite modn_small.
have p1E : pt 1 = A by rewrite /pt muln1 AME.
have Hge := invd_first_ge_ge.
move: Hge; rewrite /step AME BME.
(have [pLq|qLp] := ltnP) => /= Hge; last by apply: Hge.
have HzA : A * (B %/ A) <= B by rewrite mulnC leq_divM.
have Hz : dst (B %/ A) = B %% A.
  rewrite dst_below; last by rewrite ptM_small p1E // (leq_ltn_trans HzA).
  have HPz : pt (B %/ A) = A * (B %/ A).
    have H : pt 1 * (B %/ A) < M by rewrite p1E (leq_ltn_trans HzA).
    by rewrite (ptM_small H) p1E.
  by rewrite HPz mulnC {1}(divn_eq B A) addKn.
rewrite -Hz; apply: leq_inf_dst.
rewrite muln1 ltn_divLR //; last by rewrite -AME.
apply: leq_trans ltn_B _.
rewrite !mulnDl mul1n -{1}(subnKC (ltnW ltn_A)) {1}(divn_eq (M - A) A).
rewrite addnA leq_add2l.
by apply: ltnW; rewrite ltn_mod -AME.
Qed.

(* The first [d] is congruent to the infimum modulo [p].                      *)
Lemma invd_first_mod :
  let: (p', q', d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' = inf (u' + v') %[mod p'].
Proof.
have Hle := invd_first_le.
have Hge := invd_first_ge.
case E: (step (A %% M) (M - A %% M) (B %% M) 1 1) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hle Hge.
by have -> : d' = inf (u' + v') by apply/eqP; rewrite eqn_leq Hle Hge.
Qed.

(* The state after the first step satisfies [invd].                           *)
Lemma invd_first :
  let: (p', q', d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  invd p' q' d' u' v'.
Proof.
have Hm := invd_first_max.
have Hl := invd_first_le.
have Hc := invd_first_mod.
case E: (step (A %% M) (M - A %% M) (B %% M) 1 1) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hm Hl Hc.
by split.
Qed.

(* The step keeps [d] below the larger gap.                                   *)
Lemma step_invd_max p q d u v :
  inv p q d u v -> invd p q d u v ->
  let: (p', q', d', _, _) := step p q d u v in d' < maxn p' q'.
Proof.
move=> iv ivd.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
rewrite /step; have [pLq|qLp] := ltnP; rewrite /=.
  by rewrite (leq_trans (ltn_pmod _ p_gt0)) ?leq_maxl.
have [p'Ld|dLp'] := leqP (p - p %/ q * q) d.
  by rewrite (leq_trans (ltn_pmod _ q_gt0)) ?leq_maxr.
by rewrite (leq_trans dLp') // leq_maxl.
Qed.

(* The new infimum is below the old one reduced modulo [p].                   *)
Lemma inf_new_lt_le p q d u v :
  inv p q d u v -> invx p q u v -> u + v < N -> p < q ->
  inf (u + (q %/ p) * v + v) <= inf (u + v) %% p.
Proof.
move=> iv ix uvLN pLq.
have [p_gt0 q_gt0 _ _ _ _ u_gt0 v_gt0] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y yLuv HyE] := inf_ex uv_gt0.
(* [invx_inf] is what puts the walk inside the new range                      *)
have Iq : inf (u + v) < q.
  by have := invx_inf ix; rewrite /maxn ifT.
set m := inf (u + v) %/ p.
have mq : m <= q %/ p by rewrite leq_div2r // ltnW.
have mpI : m * p <= inf (u + v) by rewrite leq_divM.
have [m0|m_gt0] := posnP m.
  have IltP : inf (u + v) < p by rewrite ltnNge -divn_gt0 // -/m m0.
  rewrite (modn_small IltP).
  by apply: leq_inf_mono; rewrite -addnA leq_add2l leq_addl.
have Hm : 0 < m <= q %/ p by rewrite m_gt0.
have Hmp : m * p <= dst y by rewrite -HyE.
have Hw := walk_lt_nowrap iv pLq yLuv Hm Hmp.
rewrite -HyE in Hw.
have HwE : dst (y + m * v) = inf (u + v) %% p.
  by rewrite Hw /m {1}(divn_eq (inf (u + v)) p) addKn.
rewrite -HwE; apply: leq_inf_dst.
have -> : u + q %/ p * v + v = u + v + q %/ p * v.
  by rewrite -!addnA (addnC v).
by rewrite (leq_ltn_trans (leq_add (leqnn y) (_ : m * v <= q %/ p * v)))
            ?leq_mul2r ?mq ?orbT // ltn_add2r.
Qed.

(*  NB an earlier version of this file had [step_d_lt], which is exactly      *)
(* this statement with [d = Dst x] threaded through; several comments above   *)
(* still call it "(PROVED)".  It was removed in the round-8 cleanup, so the   *)
(* induction is redone here directly on [dstD].  Note [inv] does not mention  *)
(* [d] at all, so [inv p q d1 u v -> inv p q d2 u v] -- which is why the      *)
(* [Dst y] instance below needs no extra hypothesis.                          *)
(* [d] and a distance compare after reduction, inside the first gaps.         *)
Lemma mod_le_restricted p q d u v y :
  inv p q d u v -> invd p q d u v -> invx p q u v -> p < q -> y < u + v ->
  dst y %/ p <= q %/ p -> d %% p <= dst y %% p.
Proof.
move=> iv ivd ix pLq yLuv Hg.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
have [_ _ dcong] := ivd.
have [a [b [aLu bLv Hab]]] := invx_gap ix yLuv.
have qdiv : q %/ p * p <= q by rewrite leq_divM.
(* the guard says exactly [dst y < p + q]                                     *)
have Hlt : dst y < p + q.
  rewrite {1}(divn_eq (dst y) p) addnC.
  apply: leq_ltn_trans (_ : dst y %% p + q %/ p * p < _).
    by rewrite leq_add2l leq_mul2r Hg orbT.
  apply: leq_ltn_trans (leq_add (leqnn (dst y %% p)) qdiv) _.
  by rewrite ltn_add2r ltn_pmod.
case: b Hab bLv => [|[|b]] Hab bLv.
(* no [q] in the decomposition: the two residues agree outright               *)
- by rewrite Hab mul0n addn0 addnC modnMDl dcong.
(* exactly one [q]: then [a = 0] and [Dst y %% p = Inf + q %% p]              *)
- have a0 : a = 0.
    case: a Hab aLu => // a Hab aLu.
    move: Hlt; rewrite Hab mul1n ltnNge => /negP[].
    by rewrite leq_add2r (leq_trans _ (leq_addl _ _)) // mulSnr leq_addl.
  move: Hab; rewrite a0 mul0n addn0 mul1n => Hab.
  have Hd : dst y %/ p = q %/ p.
    apply/eqP; rewrite eqn_leq Hg /=.
    by rewrite leq_div2r // Hab leq_addl.
  have -> : dst y %% p = dst y - dst y %/ p * p.
    by rewrite {2}(divn_eq (dst y) p) addKn.
  rewrite Hd Hab dcong modn_small; last first.
    by move: Hlt; rewrite Hab ltn_add2r.
  rewrite leq_subRL; last by rewrite (leq_trans qdiv) // leq_addl.
  by rewrite addnC leq_add2l.
(* two or more [q]s is impossible: [p < q] gives [p + q < 2*q <= dst y]       *)
have Hq2 : p + q < 2 * q by rewrite mul2n -addnn ltn_add2r.
have HD : 2 * q <= dst y.
  rewrite Hab (leq_trans _ (leq_addl _ _)) // leq_mul2r.
  by apply/orP; right.
by move: Hlt; rewrite ltnNge => /negP[]; exact: leq_trans (ltnW Hq2) HD.
Qed.

(* [p < q] branch: [d] bounds an unwrapped walk.                              *)
Lemma le_lt_nowrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> m * p <= dst y -> d %% p <= dst y - m * p.
Proof.
move=> iv ivd ix pLq yLuv /andP[m_gt0 mk] Hmp.
have [p_gt0 _ _ _ _ _ _ _] := iv.
have mdiv : m <= dst y %/ p by rewrite leq_divRL.
have [Hlt|Hge] := ltnP m (dst y %/ p).
  apply: leq_trans (_ : p <= _); first by rewrite ltnW // ltn_pmod.
  by rewrite leq_subRL // -mulSnr -leq_divRL.
have mE : m = dst y %/ p by apply/eqP; rewrite eqn_leq mdiv Hge.
rewrite mE.
have -> : dst y - dst y %/ p * p = dst y %% p.
  by rewrite {1}(divn_eq (dst y) p) addKn.
by apply: mod_le_restricted iv ivd ix pLq yLuv _; rewrite -mE.
Qed.

(* [p < q] branch: [d] bounds a wrapped walk.                                 *)
Lemma le_lt_wrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> dst y < m * p -> d %% p <= dst (y + m * v).
Proof.
move=> iv _ pLq yLuv mk Hy.
have [p_gt0 _ _ _ _ _ _ _] := iv.
apply: leq_trans (walk_lt_wrap_ge iv pLq yLuv mk Hy).
exact: ltnW (ltn_pmod _ p_gt0).
Qed.

(* [p < q] branch: [d] bounds the distance at a walked index.                 *)
Lemma step_invd_le_new_lt_at p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  p < q -> y < u + v -> 0 < m <= q %/ p -> d %% p <= dst (y + m * v).
Proof.
move=> iv ivd ix uvLN pLq yLuv mk.
have [Hmp|Hmp] := leqP (m * p) (dst y).
  rewrite (walk_lt_nowrap iv pLq yLuv mk Hmp).
  by apply: le_lt_nowrap iv _ _ _ _ _ Hmp.
by apply: le_lt_wrap iv _ _ _ _ Hmp.
Qed.

(** [p < q] branch: [d] bounds the distances at all new indices.              *)
Lemma step_invd_le_new_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  forall x, u + v <= x < u + (q %/ p) * v + v -> d %% p <= dst x.
Proof.
move=> iv ivd ix uvLN pLq x /andP[xge xlt].
have v_gt0 : 0 < v.
  have [v0|//] := posnP v.
  have [p_gt0 _ _ pE _ _ _ _] := iv.
  by move: p_gt0; rewrite pE v0 pt0.
have [m mk /andP[ylt myx]] := new_index_decomp v_gt0 xge xlt.
rewrite -{1}(subnK myx).
by apply: step_invd_le_new_lt_at iv _ _ _ _ _ mk.
Qed.

(* A new index is an old one lowered by [j] gaps [q].                         *)
Lemma pt_new_ge p q d u v m :
  inv p q d u v -> (forall k, 0 < k < u + v -> p <= pt k) ->
  q <= p ->
  u + v <= m -> m < u + (v + p %/ q * u) ->
  exists2 j, 0 < j <= p %/ q &
    [/\ 0 < m - j * u < u + v, j * q <= pt (m - j * u) &
        pt m = pt (m - j * u) - j * q].
Proof.
move=> iv Hmin qLp mnew mLuv'.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have mnew' : v + u <= m by rewrite addnC.
have mLuv2 : m < v + p %/ q * u + u by rewrite addnC.
have [j jk /andP[ylt jum]] := new_index_decomp u_gt0 mnew' mLuv2.
have /andP[j_gt0 jk2] := jk.
have jqp : j * q <= p by rewrite -leq_divRL.
rewrite addnC in ylt.
have key : forall i, 0 < i <= p %/ q -> 0 < m - i * u -> i * u <= m ->
    m - i * u < u + v ->
    [/\ 0 < m - i * u < u + v, i * q <= pt (m - i * u) & 
        pt m = pt (m - i * u) - i * q].
  move=> i /andP[i_gt0 ik] y_gt0 ium ylt2.
  have iqp : i * q <= p by rewrite -leq_divRL.
  have iqP : i * q <= pt (m - i * u).
    by rewrite (leq_trans iqp) // Hmin // y_gt0.
  have iqM : i * q < M by rewrite (leq_ltn_trans iqp) // pE ltn_pt.
  have PuE : pt u = M - q by rewrite qE subKn // ltnW // ltn_pt.
  have Hiu : pt (i * u) = M - i * q.
    have H1 : pt (i * u) = (i * pt u) %% M by rewrite /pt modnMmr mulnCA.
    rewrite H1 PuE mulnBr.
    have -> : i * M - i * q = (i - 1) * M + (M - i * q).
      rewrite addnBA; last by apply: ltnW.
      by rewrite subn1 -mulSnr prednK.
    by rewrite modnMDl modn_small // ltn_subrL muln_gt0 i_gt0 q_gt0 M_gt0.
  split => //; first by rewrite y_gt0.
  rewrite -{1}(subnK ium) ptDE Hiu.
  rewrite addnBA; last exact: ltnW iqM.
  rewrite [pt (m - i * u) + M]addnC -addnBA // modnDl.
  by rewrite modn_small // (leq_ltn_trans (leq_subr _ _)) // ltn_pt.
(* the [Pt 0] corner: if the walk lands on the origin, take one step less     *)
have [y0|y_gt0] := posnP (m - j * u); last by exists j => //; apply: key.
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

(* [q <= p] branch: [d] is exactly the infimum.                               *)
Lemma ge_d_eq_inf p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> q <= p -> d = inf (u + v).
Proof.
move=> iv ivd ix qLp.
have [dmax _ dcong] := ivd.
have dp : d < p by move: dmax; rewrite /maxn ifN // -leqNgt.
have ip : inf (u + v) < p by move: (invx_inf ix); rewrite /maxn ifN // -leqNgt.
by rewrite -(modn_small dp) dcong modn_small.
Qed.

(*  the mirror.  [new_index_decomp] is reused with [u] and [v] SWAPPED:       *)
(*  its window [u + k*v + v] becomes [v + k*u + u], which is exactly this     *)
(*  branch's [u + (v + (p %/ q) * u)].  The walk then descends the index      *)
(*  ([step_d_ge]) instead of ascending.                                       *)
(*  [q <= p] branch: the step never increases [d].                            *)
Lemma step_ge_d_le p q d : q <= p ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d) <= d.
Proof.
move=> qLp; have [dge|//] := leqP (p - p %/ q * q) d.
by apply: leq_trans (leq_mod _ _) _; rewrite leq_subr.
Qed.


(* The last quotient: [d] bounds a wrapped walk.                              *)
Lemma ge_wrap_exit p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> q <= p ->
  p - p %/ q * q = 0 ->
  y < u + v -> 0 < m <= p %/ q -> M <= dst y + m * q ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    <= dst (y + m * u).
Proof.
move=> iv ivd ix qLp p'0 yLuv mk Hw.
by have [H _] := ge_exit iv ivd ix qLp p'0; apply: H.
Qed.

(* [q <= p] branch: the new configuration keeps the smaller gap.              *)
Lemma invx_step_ge_min p q d u v :
  inv p q d u v -> (forall k, 0 < k < u + v -> p <= pt k) ->
  q <= p ->
  forall m, 0 < m < u + (v + p %/ q * u) -> p - p %/ q * q <= pt m.
Proof.
move=> iv Hmin qLp m /andP[m_gt0 mLuv'].
have [mold|mnew] := ltnP m (u + v).
  by rewrite (leq_trans (leq_subr _ _)) // Hmin // m_gt0.
have [j /andP[j_gt0 jk] [/andP[y_gt0 ylt] jqP Hm]] :=
  pt_new_ge iv Hmin qLp mnew mLuv'.
rewrite Hm leq_sub ?Hmin ?y_gt0 //.
by rewrite leq_mul2r jk orbT.
Qed.

(* [q <= p] branch: the new configuration keeps the larger gap.               *)
Lemma invx_step_ge_max p q d u v :
  inv p q d u v -> (forall k, 0 < k < u + v -> p <= pt k) ->
  (forall k, k < u + v -> pt k <= M - q) ->
  q <= p ->
  forall m, m < u + (v + p %/ q * u) -> pt m <= M - q.
Proof.
move=> iv Hmin Hmax qLp m mLuv'.
case: (ltnP m (u + v)) => [mold|mnew]; first by apply: Hmax.
have [j /andP[j_gt0 jk] [/andP[y_gt0 ylt] jqP Hm]] :=
  pt_new_ge iv Hmin qLp mnew mLuv'.
by rewrite Hm (leq_trans (leq_subr _ _)) // Hmax.
Qed.

(* [q <= p] branch: the new infimum is exactly the new [d], or the old one,   *)
(*  which was below [q].                                                      *)
Lemma ge_inf_alt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> q <= p ->
  0 < p - p %/ q * q ->
  inf (u + (v + p %/ q * u))
    = (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
  \/ (inf (u + (v + p %/ q * u)) = inf (u + v) /\ inf (u + v) < q).
Proof.
move=> iv ivd ix qLp p'_gt0.
have [p_gt0 q_gt0 bez pE qE _ u_gt0 v_gt0] := iv.
have dI : d = inf (u + v) := ge_d_eq_inf iv ivd ix qLp.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Heq] := inf_ex uv_gt0.
have k_gt0 : 0 < p %/ q by rewrite divn_gt0.
have qqM : q + q <= M.
  rewrite -bez (leq_trans (leq_add qLp (leqnn q))) // leq_add //.
    by rewrite leq_pmull.
  by rewrite leq_pmull.
have Hmin' := invx_step_ge_min iv (invx_min ix) qLp.
have Hmax' := invx_step_ge_max iv (invx_min ix) (invx_max ix) qLp.
have iv' : inv (p - p %/ q * q) q
             (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
             u (v + p %/ q * u).
  move: (inv_step_pos iv); rewrite /step.
  case: (ltnP p q) => [pLq|_]; first by rewrite ltnNge qLp in pLq.
  by move=> /= H; apply: H.
have uv'_gt0 : 0 < u + (v + p %/ q * u) by rewrite addn_gt0 u_gt0.
have [zn znL Heqn] := inf_ex uv'_gt0.
have y0L' : y0 < u + (v + p %/ q * u).
  by rewrite (leq_trans y0L) // leq_add2l leq_addr.
have HleI : inf (u + (v + p %/ q * u)) <= inf (u + v).
  by rewrite Heq; apply: leq_inf_dst.
have HgeI : ~ dst zn < dst y0 -> inf (u + (v + p %/ q * u)) = inf (u + v).
  move=> H; apply/eqP.
  rewrite eqn_leq HleI /= Heq Heqn leqNgt; apply/negP => H2.
  by apply: H.
have [y0u|uy0] := ltnP y0 u; last first.
  (* [b] in a [q]-gap: nothing is added there, and [Inf] was already low *)
  right; have qDy : dst y0 < q.
    rewrite ltnNge; apply/negP => qI.
    have Hd := dst_sub_u iv uy0 qI.
    have Hle : inf (u + v) <= dst (y0 - u).
      by apply: leq_inf_dst; rewrite (leq_ltn_trans (leq_subr _ _)).
    by move: Hle; rewrite Hd Heq leqNgt ltn_subrL q_gt0 (leq_trans q_gt0 qI).
  split; last by rewrite Heq.
  apply: HgeI => Hlt.
  suff : dst y0 <= dst zn by rewrite leqNgt Hlt.
  by apply: gap_q_empty iv' _ _ _ _ _ qDy.
have Ip : dst y0 < p.
  rewrite ltnNge; apply/negP => pI.
  have Hsucc : pt (y0 + v) = pt y0 + p by apply: (invx_p1 ix).
  have Hdd := dst_ofD Hsucc pI.
  have Hle : inf (u + v) <= dst (y0 + v).
    by apply: leq_inf_dst; rewrite ltn_add2r.
  by move: Hle; rewrite Hdd Heq leqNgt ltn_subrL p_gt0 (leq_trans p_gt0 pI).
have rq : p - p %/ q * q < q by apply: q'_lt_p.
left; rewrite dI Heq.
have [rI|Ir] := leqP (p - p %/ q * q) (dst y0); last first.
(* [b] in the residual gap at the bottom: [Inf] does not move                 *)
  rewrite -Heq; apply: HgeI => Hlt.
  suff : dst y0 <= dst zn by rewrite leqNgt Hlt.
  by apply: gap_p_empty iv' _ _ (ltnW _) _ _ _.
(* [b] in the [m]-th [q]-gap: [Inf] moves to the point just below it          *)
have rE : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
move: rI Ip; rewrite rE => rI Ip.
set I := dst y0 in rI Ip *.
set k := p %/ q in k_gt0 *.
set m := (I - p %% q) %/ q.
have mk : m < k by rewrite /m ltn_divLR // ltn_subLR // addnC -divn_eq.
set j := k - m.
have j_gt0 : 0 < j by rewrite /j subn_gt0.
have jk : j <= k by rewrite /j leq_subr.
have jqp : j * q <= p.
  by rewrite (leq_trans (leq_mul jk (leqnn q))) // -/k leq_divM.
have pjq : p - j * q = p %% q + m * q.
  have mkq : m * q <= k * q by rewrite leq_mul2r (ltnW mk) orbT.
  have jqE : j * q = k * q - m * q by rewrite /j mulnBl.
  rewrite jqE {1}(divn_eq p q) -/k subnBA //.
  by rewrite -addnA addnC addnK.
have Hsucc : pt (y0 + v) = pt y0 + p by apply: (invx_p1 ix).
have jqPt : j * q <= pt (y0 + v) by rewrite Hsucc (leq_trans jqp) // leq_addl.
have Hpt : pt (y0 + v + j * u) = pt y0 + (p %% q + m * q).
  by rewrite (pt_add_u iv j_gt0 jqp jqPt) Hsucc -pjq addnBA.
have tI : p %% q + m * q <= I.
  by rewrite addnC -(subnK rI) leq_add2r /m leq_divM.
have Hdst : dst (y0 + v + j * u) = I - (p %% q + m * q).
  by rewrite (dst_ofD Hpt tI).
have HE : I - (p %% q + m * q) = (I - p %% q) %% q.
  by rewrite subnDA {1}(divn_eq (I - p %% q) q) -/m addnC addnK.
have x0L : y0 + v + j * u < u + (v + k * u).
  rewrite addnA (leq_ltn_trans (leq_add (leqnn (y0 + v)) (leq_mul jk (leqnn
    u)))) //.
  by rewrite ltn_add2r ltn_add2r.
have ux0 : u <= y0 + v + j * u.
  by rewrite (leq_trans _ (leq_addl (y0 + v) (j * u))) // leq_pmull.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  by rewrite -HE -Hdst; apply: leq_inf_dst.
rewrite Heqn -HE -Hdst.
apply: (gap_q_empty iv' Hmax' qqM ux0 x0L znL).
by rewrite Hdst HE ltn_pmod.
Qed.

(* [q <= p] branch: the new [d] is below every distance in the new range.     *)
Lemma ge_d_leq_inf p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> q <= p ->
  0 < p - p %/ q * q ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    <= inf (u + (v + p %/ q * u)).
Proof.
move=> iv ivd ix qLp p'_gt0.
have [p_gt0 q_gt0 bez pE qE _ u_gt0 v_gt0] := iv.
have dI : d = inf (u + v) := ge_d_eq_inf iv ivd ix qLp.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Heq] := inf_ex uv_gt0.
have k_gt0 : 0 < p %/ q by rewrite divn_gt0.
have qqM : q + q <= M.
  rewrite -bez (leq_trans (leq_add qLp (leqnn q))) // leq_add //.
    by rewrite leq_pmull.
  by rewrite leq_pmull.
have Hmin' := invx_step_ge_min iv (invx_min ix) qLp.
have Hmax' := invx_step_ge_max iv (invx_min ix) (invx_max ix) qLp.
have iv' : inv (p - p %/ q * q) q
             (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
             u (v + p %/ q * u).
  move: (inv_step_pos iv); rewrite /step.
  case: (ltnP p q) => [pLq|_]; first by rewrite ltnNge qLp in pLq.
  by move=> /= H; apply: H.
have uv'_gt0 : 0 < u + (v + p %/ q * u) by rewrite addn_gt0 u_gt0.
have [zn znL Heqn] := inf_ex uv'_gt0.
rewrite Heqn dI Heq.
have y0L' : y0 < u + (v + p %/ q * u).
  by rewrite (leq_trans y0L) // leq_add2l leq_addr.
have Hold : dst y0 <= dst zn -> (if p - p %/ q * q <= dst y0
              then (dst y0 - (p - p %/ q * q)) %% q else dst y0) <= dst zn.
  move=> H; have [rI|//] := leqP (p - p %/ q * q) (dst y0).
  by rewrite (leq_trans _ H) // (leq_trans (leq_mod _ _)) // leq_subr.
have [y0u|uy0] := ltnP y0 u; last first.
(* [b] in a [q]-gap: nothing is added there                                   *)
  apply: Hold.
  have qDy : dst y0 < q.
    rewrite ltnNge; apply/negP => qI.
    have Hd := dst_sub_u iv uy0 qI.
    have Hle : inf (u + v) <= dst (y0 - u).
      by apply: leq_inf_dst; rewrite (leq_ltn_trans (leq_subr _ _)).
    by move: Hle; rewrite Hd Heq leqNgt ltn_subrL q_gt0 (leq_trans q_gt0 qI).
  by apply: gap_q_empty iv' _ _ _ _ _ _.
have Ip : dst y0 < p.
  rewrite ltnNge; apply/negP => pI.
  have Hsucc : pt (y0 + v) = pt y0 + p by apply: (invx_p1 ix).
  have Hdd := dst_ofD Hsucc pI.
  have Hle : inf (u + v) <= dst (y0 + v).
    by apply: leq_inf_dst; rewrite ltn_add2r.
  by move: Hle; rewrite Hdd Heq leqNgt ltn_subrL p_gt0 (leq_trans p_gt0 pI).
have rq : p - p %/ q * q < q by apply: q'_lt_p.
have [rI|Ir] := leqP (p - p %/ q * q) (dst y0); last first.
  (* [b] in the residual gap at the bottom of its [p]-gap *)
  by apply: gap_p_empty iv' _ _ (ltnW _) _ _ _.
(* [b] in the [m]-th [q]-gap: the witness is the point just below it          *)
have rE : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
move: rI Ip; rewrite rE => rI Ip.
set I := dst y0 in rI Ip *.
set k := p %/ q in k_gt0 *.
set m := (I - p %% q) %/ q.
have mk : m < k by rewrite /m ltn_divLR // ltn_subLR // addnC -divn_eq.
set j := k - m.
have j_gt0 : 0 < j by rewrite /j subn_gt0.
have jk : j <= k by rewrite /j leq_subr.
have jqp : j * q <= p.
  by rewrite (leq_trans (leq_mul jk (leqnn q))) // -/k leq_divM.
have pjq : p - j * q = p %% q + m * q.
  have mkq : m * q <= k * q by rewrite leq_mul2r (ltnW mk) orbT.
  have jqE : j * q = k * q - m * q by rewrite /j mulnBl.
  rewrite jqE {1}(divn_eq p q) -/k subnBA //.
  by rewrite -addnA addnC addnK.
have Hsucc : pt (y0 + v) = pt y0 + p by apply: (invx_p1 ix).
have jqPt : j * q <= pt (y0 + v) by rewrite Hsucc (leq_trans jqp) // leq_addl.
have Hpt : pt (y0 + v + j * u) = pt y0 + (p %% q + m * q).
  by rewrite (pt_add_u iv j_gt0 jqp jqPt) Hsucc -pjq addnBA.
have tI : p %% q + m * q <= I.
  by rewrite addnC -(subnK rI) leq_add2r /m leq_divM.
have Hdst : dst (y0 + v + j * u) = I - (p %% q + m * q).
  by rewrite (dst_ofD Hpt tI).
have HE : I - (p %% q + m * q) = (I - p %% q) %% q.
  by rewrite subnDA {1}(divn_eq (I - p %% q) q) -/m addnC addnK.
have x0L : y0 + v + j * u < u + (v + k * u).
  rewrite addnA (leq_ltn_trans (leq_add (leqnn (y0 + v)) 
          (leq_mul jk (leqnn u)))) //.
  by rewrite ltn_add2r ltn_add2r.
have ux0 : u <= y0 + v + j * u.
  by rewrite (leq_trans _ (leq_addl (y0 + v) (j * u))) // leq_pmull.
rewrite -HE -Hdst.
apply: gap_q_empty iv' _ _ _ _ _ _ => //.
by rewrite Hdst HE ltn_pmod.
Qed.

(* [q <= p] branch: [d] bounds a wrapped walk.                                *)
Lemma le_ge_wrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  q <= p -> y < u + v -> 0 < m <= p %/ q -> M <= dst y + m * q ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    <= dst (y + m * u).
Proof.
move=> iv ivd ix uvLN qLp yLuv mk Hw.
have /andP[m_gt0 mk2] := mk.
have [p'0|p'_gt0] := posnP (p - p %/ q * q).
  by apply: ge_wrap_exit iv _ _ _ _ _ _ Hw.
apply: leq_trans (ge_d_leq_inf iv ivd ix qLp p'_gt0) _.
apply: leq_inf_dst; rewrite addnA.
apply: leq_ltn_trans (leq_add (leqnn y) (leq_mul mk2 (leqnn u))) _.
by rewrite ltn_add2r.
Qed.

(* [q <= p] branch: [d] bounds the distance at a walked index.                *)
Lemma step_invd_le_new_ge_at p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  q <= p -> y < u + v -> 0 < m <= p %/ q ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    <= dst (y + m * u).
Proof.
move=> iv ivd ix uvLN qLp yLuv mk.
have [Hw|Hw] := ltnP (dst y + m * q) M; last first.
  by apply: le_ge_wrap iv ivd ix uvLN qLp yLuv mk Hw.
rewrite (walk_ge_nowrap iv qLp yLuv mk Hw).
apply: leq_trans (step_ge_d_le d qLp) _.
apply: leq_trans (leq_addr _ _).
have [_ dle _] := ivd.
by apply: leq_trans dle _; apply: leq_inf_dst.
Qed.

(* [q <= p] branch: [d] bounds the distances at all new indices.              *)
Lemma step_invd_le_new_ge p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> q <= p ->
  forall x, u + v <= x < u + (v + (p %/ q) * u) ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d) <= dst x.
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

(* [d] bounds the distances at all indices the step adds.                     *)
Lemma step_invd_le_new p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in
  forall x, u + v <= x < u' + v' -> d' <= dst x.
Proof.
move=> iv ivd ix uvLN.
have Hlt := step_invd_le_new_lt iv ivd ix uvLN.
have Hge := step_invd_le_new_ge iv ivd ix uvLN.
rewrite /step; case: ltnP => [pLq|qLp] /=.
  by apply: Hlt.
by apply: Hge.
Qed.

(* [d] bounds the distances everywhere in the new range.                      *)
Lemma step_invd_le_pt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in
  d' <= M /\ (forall x, x < u' + v' -> d' <= dst x).
Proof.
move=> iv ivd ix uvLN.
have [_ dle _] := ivd.
have HdM : d <= M by rewrite (leq_trans dle) // (leq_inf_mono (leq0n (u + v))).
have Hnew := step_invd_le_new iv ivd ix uvLN.
have Hdd : let: (_, _, d', _, _) := step p q d u v in d' <= d.
  rewrite /step; case: ltnP => /= _; first by rewrite leq_mod.
  case: (leqP (p - p %/ q * q) d) => [_|_] //.
  by rewrite (leq_trans (leq_mod _ _)) // leq_subr.
case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hnew Hdd.
split; first by rewrite (leq_trans Hdd).
move=> x xLuv.
have [xold|xnew] := ltnP x (u + v).
  by rewrite (leq_trans Hdd) // (leq_trans dle) // leq_inf_dst.
by apply: Hnew; rewrite xnew xLuv.
Qed.

(* The step keeps [d] below the infimum.                                      *)
Lemma step_invd_le p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in d' <= inf (u' + v').
Proof.
move=> iv ivd ix uvLN.
have H := step_invd_le_pt iv ivd ix uvLN.
case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in H.
have [HM Hpt] := H.
by apply: leq_inf.
Qed.

(* [p < q] branch: the new infimum, in closed form.                           *)
Lemma inf_new_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  inf (u + (q %/ p) * v + v) = inf (u + v) %% p.
Proof.
move=> iv ivd ix uvLN pLq.
have [_ _ dcong] := ivd.
apply/eqP; rewrite eqn_leq (inf_new_lt_le iv ix uvLN pLq) /=.
rewrite -dcong.
have := step_invd_le iv ivd ix uvLN.
by rewrite /step pLq /=.
Qed.

(* [p < q] branch: the new [d] is congruent to the new infimum.               *)
Lemma inf_cong_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  inf (u + (q %/ p) * v + v) = inf (u + v) %[mod p].
Proof. 
by move=> iv ivd ix uvLN pLq; rewrite (inf_new_lt iv _ _ _ pLq) // modn_mod.
Qed.

(* [q <= p] branch: the new [d] is congruent to the new infimum.              *)
Lemma inf_cong_ge p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> q <= p ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    = inf (u + (v + (p %/ q) * u)) %[mod (p - p %/ q * q)].
Proof.
move=> iv ivd ix uvLN qLp.
have [p_gt0 q_gt0 _ _ _ _ u_gt0 v_gt0] := iv.
have dI : d = inf (u + v) := ge_d_eq_inf iv ivd ix qLp.
have [p'0|p'_gt0] := posnP (p - p %/ q * q).
  by have [_ H] := ge_exit iv ivd ix qLp p'0.
case: (ge_inf_alt iv ivd ix qLp p'_gt0) => [->|[-> Iq]] //.
rewrite dI; have [rI|//] := leqP (p - p %/ q * q) (inf (u + v)).
have -> : (inf (u + v) - (p - p %/ q * q)) %% q = 
             inf (u + v) - (p - p %/ q * q).
  by rewrite modn_small // (leq_ltn_trans (leq_subr _ _)).
by rewrite -{2}(subnK rI) modnDr.
Qed.

(* The step preserves the congruence between [d] and the infimum.             *)
Lemma step_invd_cong p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in
  d' = inf (u' + v') %[mod p'].
Proof.
move=> iv ivd ix uvLN.
have [_ _ dcong] := ivd.
have Hlt := inf_cong_lt iv ivd ix uvLN.
have Hge := inf_cong_ge iv ivd ix uvLN.
rewrite /step; case: ltnP => [pLq|qLp] /=; last by apply: Hge.
by rewrite modn_mod dcong (Hlt pLq).
Qed.

(* The step preserves [invd].                                                 *)
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


(* Soundness of the loop and of [lefevre]                                     *)
(*                                                                            *)
(* [fuel_enough] was in the skeleton to relate an arbitrary fuel to           *)
(*  [p + q]; it turned out to be unnecessary and has been removed.            *)
(*  [run_sound] carries [p + q <= fuel] directly, and [lefevre] runs with     *)
(*  [fuel = M] while [p + q = A %% M + (M - A %% M) = M], so the              *)
(*  hypothesis is met exactly.  Nothing else referred to it.                  *)
(** At the exit [u + v >= N], so the configuration has at least [N]           *)
(*  points; [d] is a distance in that configuration, hence at most the        *)
(*  infimum taken over the smaller set [x < N].                               *)
(*  CFrac: slater.LminDmax -- why [u + v] overshoots [N].                     *)
(*  On exit, [d] is below the infimum over the whole search range.            *)
Lemma exit_bound p q d u v : invd p q d u v -> N <= u + v -> d <= inf N.
Proof.
by case=> _ dLinf _ NLuv; apply: leq_trans dLinf (leq_inf_mono NLuv).
Qed.

(* The loop returns a lower bound on the infimum.                             *)
Lemma run_sound fuel p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> 
  p + q <= fuel -> run fuel p q d u v N <= inf N.
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
case: (leqP N (u' + v')) => [NLuv|uvLN']; first by apply: exit_bound Hd NLuv.
apply: IH => //; [exact: Hi uvLN' | exact: Hx uvLN' | ].
by rewrite -ltnS (leq_trans Hm).
Qed.

(* The algorithm returns a lower bound on the infimum.                        *)
(* [lefevre] returns a lower bound on the infimum over the search range.      *)
Theorem lefevre_sound : 2 < N -> lefevre M A B N <= inf N.
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

(* The form the search actually uses: if the returned bound clears the        *)
(* threshold, there is no hard-to-round case in this sub-interval.            *)
(* If the returned bound clears the threshold, there is no hard-to-round      *)
(* case here.                                                                 *)
Corollary lefevre_test eps :
  2 < N -> eps < lefevre M A B N -> forall x, x < N -> eps < dst x.
Proof.
move=> N_gt2 epsL x xLN.
apply: leq_trans epsL _.
by apply: leq_trans (lefevre_sound N_gt2) _; apply: leq_inf_dst xLN.
Qed.

End Theory.
