(* =========================================================================  *)
(*  RowCoordOk.v -- hcoset's four numbers move as the twenty cubies do.       *)
(* =========================================================================  *)

(* RowCoord.v carries a position as four numbers moved by tables.  Here: on   *)
(* every position the run can carry, the four numbers of a moved position    *)
(* are the four numbers of the position, moved by the tables.                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Tabi Phase1 Row RowMap RowMemb RowCub RowCubi RowCubInst.
Require Import Lehmer RowLeafFast RowTabL RowCoord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

(* ---- a table built by mkT ------------------------------------------------- *)

Lemma ifold_foldi sz j (f : int -> int) (a : arr) :
  ifold sz j (fun i a => PArray.set a i (f i)) a = ssrint63.foldi sz j (setf f) a.
Proof. by elim: sz j a => [|sz ih] j a //=; rewrite ih. Qed.

Lemma mkT_get sz (f : int -> int) i :
  (sz <= to_nat max_length)%N -> (to_nat i < sz)%N ->
  PArray.get (mkT sz f) i = f i.
Proof.
move=> hsz hi; rewrite /mkT ifold_foldi.
have hml : (to_nat max_length < nwB)%N := to_nat_bounded max_length.
have hszb : (sz < nwB)%N := leq_ltn_trans hsz hml.
apply: get_foldi_in.
- by rewrite to_nat_0 add0n.
- rewrite to_nat_0 add0n length_makeE.
  have -> : (of_nat sz <=? max_length)%uint63 = true.
    by apply/nlebP; rewrite (of_natK _ hszb).
  by rewrite (of_natK _ hszb).
by rewrite to_nat_0 add0n leq0n hi.
Qed.

(* ---- the corners ---------------------------------------------------------- *)

(* the place a moved corner place reads from, below eight                     *)
Definition cmvC : bool :=
  all (fun k => all (fun p => nth 0%N (ymvpn k) p < 8)%N (iota 0 8)) (iota 0 18).
Lemma cmvCE : cmvC. Proof. by vm_compute. Qed.

Lemma cmv_lt k p : (k < 18)%N -> (p < 8)%N -> (nth 0%N (ymvpn k) p < 8)%N.
Proof.
move=> hk hp; have /allP/(_ k) := cmvCE; rewrite mem_iota add0n => /(_ hk).
by move/allP/(_ p); rewrite mem_iota add0n; apply.
Qed.

(* a move reads the corner at place p from the place ymvpn names              *)
Lemma zstep_ycg Y k p : (p < 8)%N ->
  ycg (zstep Y k) p = ycg Y (nth 0%N (ymvpn k) p).
Proof.
move=> hp; have hp20 : (p < 20)%N by apply: ltn_trans hp _.
rewrite /ycg /zstep /ystepm (nth_map 0%N) ?size_iota // nth_iota // add0n hp.
rewrite /ymvpn (nth_map 0%N) ?size_iota // nth_iota // add0n hp.
by rewrite [3 * _]mulnC divnMDl // (@divn_small (_ %% 3) 3) ?addn0 ?ltn_mod.
Qed.

(* every rank below 8! unranks to a permutation that ranks back to it         *)
Definition unrankP (r : int) : bool :=
  [&& Uint63.eqb (lbrank (PArray.get (cunrank r)) 8 8) r,
      all (fun p => to_nat (PArray.get (cunrank r) (of_nat p)) < 8)%N (iota 0 8)
    & uniq [seq to_nat (PArray.get (cunrank r) (of_nat p)) | p <- iota 0 8]].
Definition unrankPC : bool := ifold 40320 0 (fun r b => b && unrankP r) true.
(* the kernel must unfold unrankP before andb: the other way round it runs  *)
(* the unranking symbolically at every Qed that opens the test (measured:    *)
(* a timeout against 26 ms)                                                  *)
Strategy expand [unrankP].
(* stated with the fold written out: using the name alone makes the unifier *)
(* unfold it and run the fold symbolically                                   *)
Lemma unrankPCE : ifold 40320 0 (fun r b => b && unrankP r) true.
Proof. by vm_compute. Qed.

(* what a check written as a fold over the first n ints says of each of them  *)
Lemma ifold_andg n j (P : int -> bool) b :
  (j + n <= nwB)%N ->
  ifold n (advn j 0%uint63) (fun r b => b && P r) b ->
  b /\ forall r, (j <= to_nat r < j + n)%N -> P r.
Proof.
elim: n j b => [|n ih] j b hb /=.
  by move=> hb'; split => // r /andP[h1 h2]; move: (leq_ltn_trans h1 h2); rewrite addn0 ltnn.
have -> : Uint63.add (advn j 0%uint63) 1%uint63 = advn j.+1 0%uint63.
  by rewrite advnS.
move=> /(ih j.+1 _ _) [].
  by rewrite addSnnS.
move=> /andP[hb' hP] hall; split => // r /andP[h1 h2].
have hj : (j < nwB)%N by apply: leq_trans hb; rewrite -[X in (X <= _)%N]addn0 ltn_add2l.
case: (ltngtP j (to_nat r)) => [hlt | hgt | e].
- by apply: hall; rewrite hlt addSnnS.
- by move: h1; rewrite leqNgt hgt.
have -> : r = advn j 0%uint63.
  by apply: to_nat_inj; rewrite to_nat_advn0 // e.
exact: hP.
Qed.

Lemma ifold_andP n (P : int -> bool) :
  (n <= nwB)%N -> ifold n 0%uint63 (fun r b => b && P r) true ->
  forall r, (to_nat r < n)%N -> P r.
Proof.
move=> hb h r hr; have := @ifold_andg n 0 P true; rewrite add0n => /(_ hb h) [_].
by apply; rewrite leq0n hr.
Qed.

(* 8! written out, so the kernel never has to see 8`! and 40320 as one     *)
Lemma fact8E : 8`! = 40320%N. Proof. by []. Qed.

Lemma n40320 : (40320 <= nwB)%N.
Proof. by apply: ltnW; apply: (@lt_nwB _ 16). Qed.

(* a permutation of eight is the unranking of its rank                         *)
Lemma cunrank_rank (f : nat -> nat) :
  {in iota 0 8 &, injective f} -> (forall p, (p < 8)%N -> (f p < 8)%N) ->
  forall p, (p < 8)%N -> to_nat (PArray.get (cunrank (rank8 f)) (of_nat p)) = f p.
Proof.
move=> hinj hf.
have hlr : (lrank 8 f < 8`!)%N := lrank_lt 8 f.
have hr : (to_nat (rank8 f) < 40320)%N.
  by rewrite rank8E (of_natK _ (ltn_trans hlr n8f)) -fact8E.
have hP := @ifold_andP 40320 unrankP n40320 unrankPCE _ hr.
rewrite /unrankP in hP.
have /and3P[hrk0 hrg0 hug] := hP.
have hrk := eqb_correct _ _ hrk0.
have /allP hrg := hrg0.
set a := cunrank (rank8 f) in hrk hrg hug *.
set g := fun p => to_nat (PArray.get a (of_nat p)).
have hgr : forall p, (p < 8)%N -> (g p < 8)%N.
  by move=> p hp; apply: hrg; rewrite mem_iota add0n.
have hpg : perm_eq [seq g p | p <- iota 0 8] (iota 0 8) := perm_of_rng hug hgr.
have huf : uniq [seq f p | p <- iota 0 8] by rewrite map_inj_in_uniq ?iota_uniq.
have hpf : perm_eq [seq f p | p <- iota 0 8] (iota 0 8) := perm_of_rng huf hf.
have hlb : lbrank (PArray.get a) 8 8 = rank8 g.
  apply: lbrank8 => //.
  move=> x z; rewrite !mem_iota !add0n => hx hz; exact: perm_inj hpg x z hx hz.
have hlg : lrank 8 g = lrank 8 f.
  have e : rank8 g = rank8 f := etrans (esym hlb) hrk.
  have e' : to_nat (rank8 g) = to_nat (rank8 f) by rewrite e.
  have hbg : (lrank 8 g < nwB)%N := ltn_trans (lrank_lt 8 g) n8f.
  have hbf : (lrank 8 f < nwB)%N := ltn_trans (lrank_lt 8 f) n8f.
  by move: e'; rewrite !rank8E (of_natK _ hbg) (of_natK _ hbf).
by move=> p hp; apply: (lrank_inj hpg hpf hlg).
Qed.

(* the corner number of a position the run carries is the rank of its corners *)
Lemma corner_rankE y : ypstok y ->
  lbrank (fun p => PArray.get lbcq (PArray.get y p)) 8 8 = rank8 (ycg (a2y y)).
Proof.
move=> hy; have /andP[/andP[hyok htab] _] := hy.
have /allP hyi := yok_yoki hyok.
have hent q : (q < 20)%N -> (to_nat (PArray.get y (of_nat q)) < 24)%N.
  by move=> hq; apply: hyi; rewrite mem_iota add0n.
have /andP[/allP hyc _] := hyok.
apply: lbrank8.
- move=> p hp; have hp20 : (p < 20)%N by apply: ltn_trans hp _.
  case: (lbtabE (hent _ hp20)) => h1 _ _.
  by rewrite /ycg (a2y_nth _ hp20) -h1 to_natK.
- exact: ycg_inj.
by move=> p hp; apply: hyc; rewrite mem_iota add0n.
Qed.

Lemma n725760 : (40320 * 18 <= to_nat max_length)%N.
Proof. by vm_compute. Qed.

(* THE CORNERS STEP: the table moves the corner number as the move moves the  *)
(* corners                                                                    *)
Lemma corner_step y k : (k < 18)%N -> ypstok y ->
  PArray.get ctab
    (Uint63.add (Uint63.mul (lbrank (fun p => PArray.get lbcq (PArray.get y p)) 8 8) 18)
                (of_nat k))
  = lbrank (fun p => PArray.get lbcq (PArray.get (zstepi y (of_nat k)) p)) 8 8.
Proof.
move=> hk hy.
have hy' := ypstok_step hk hy.
rewrite (corner_rankE hy) (corner_rankE hy').
have /andP[/andP[hyok htab] _] := hy.
have /andP[/andP[hyok' htab'] _] := hy'.
set Y := a2y y; set f := ycg Y.
have hfr : forall p, (p < 8)%N -> (f p < 8)%N.
  by have /andP[/allP hyc _] := hyok => p hp; apply: hyc; rewrite mem_iota add0n.
have hfi : {in iota 0 8 &, injective f} := ycg_inj hyok htab.
have hlr : (lrank 8 f < 8`!)%N := lrank_lt 8 f.
have hr : to_nat (rank8 f) = lrank 8 f.
  by rewrite rank8E (of_natK _ (ltn_trans hlr n8f)).
have hk18 : (k < nwB)%N by apply: ltn_trans hk _; apply: ltn_trans n20_small.
have hkk : to_nat (of_nat k) = k := of_natK _ hk18.
have hbig : (lrank 8 f * 18 + k < 40320 * 18)%N.
  have : (lrank 8 f * 18 + k < lrank 8 f * 18 + 18)%N by rewrite ltn_add2l.
  have hlt40 : (lrank 8 f < 40320)%N by rewrite -fact8E.
  by move/leq_trans; apply; rewrite -mulSnr leq_mul2r; apply/orP; right.
have hbnw : (40320 * 18 < nwB)%N.
  by apply: leq_ltn_trans n725760 (to_nat_bounded max_length).
set i := Uint63.add (Uint63.mul (rank8 f) 18) (of_nat k).
have h18 : to_nat 18 = 18%N := erefl.
have hm0 : (lrank 8 f * 18 < nwB)%N.
  by apply: leq_ltn_trans hbnw; apply: leq_trans (ltnW hbig); rewrite leq_addr.
have hm : to_nat (Uint63.mul (rank8 f) 18) = (lrank 8 f * 18)%N.
  have hmb : (to_nat (rank8 f) * to_nat 18 < nwB)%N by rewrite hr h18.
  by rewrite (to_nat_mul _ _ hmb) hr h18.
have hi : to_nat i = (lrank 8 f * 18 + k)%N.
  have ha : (to_nat (Uint63.mul (rank8 f) 18) + to_nat (of_nat k) < nwB)%N.
    by rewrite hm hkk; apply: leq_ltn_trans hbnw; apply: ltnW.
  by rewrite /i (to_nat_add _ _ ha) hm hkk.
rewrite mkT_get; last by rewrite hi.
  2: exact: n725760.
cbv zeta.
have hdiv : Uint63.div i 18 = rank8 f.
  apply: to_nat_inj; rewrite to_nat_div hi hr h18.
  by rewrite divnMDl // divn_small ?addn0.
rewrite hdiv.
have hsub : Uint63.sub i (Uint63.mul (rank8 f) 18) = of_nat k.
  apply: to_nat_inj.
  have hle : (to_nat (Uint63.mul (rank8 f) 18) <= to_nat i)%N.
    by rewrite hm hi leq_addr.
  have hib : (to_nat i < nwB)%N := to_nat_bounded i.
  by rewrite (to_nat_sub _ _ hle hib) hm hi hkk addKn.
rewrite hsub.
have ez := a2y_zstepi hk (yok_yoki hyok).
rewrite ez -/Y; rewrite ez -/Y in hyok' htab'.
apply: lbrank8.
- move=> p hp.
  have hp20 : (p < 20)%N by apply: ltn_trans hp _.
  have hkp : (k * 20 + p < nwB)%N.
    have h360 : (18 * 20 < nwB)%N by apply: (@lt_nwB _ 9).
    apply: (ltn_trans _ h360).
    apply: (@leq_trans (k * 20 + 20)); first by rewrite ltn_add2l.
    by rewrite -mulSnr leq_mul2r hk orbT.
  have hpb : (p < nwB)%N := ltn_trans hp20 n20_small.
  have hpp : to_nat (of_nat p) = p := of_natK _ hpb.
  have h20 : to_nat 20 = 20%N := erefl.
  have hk20 : (k * 20 < nwB)%N by apply: leq_ltn_trans hkp; rewrite leq_addr.
  have hmk : to_nat (Uint63.mul (of_nat k) 20) = (k * 20)%N.
    have hmb : (to_nat (of_nat k) * to_nat 20 < nwB)%N by rewrite hkk h20.
    by rewrite (to_nat_mul _ _ hmb) hkk h20.
  have e : Uint63.add (Uint63.mul (of_nat k) 20) (of_nat p) = of_nat (k * 20 + p).
    apply: to_nat_inj; rewrite (of_natK _ hkp).
    have ha : (to_nat (Uint63.mul (of_nat k) 20) + to_nat (of_nat p) < nwB)%N.
      by rewrite hmk hpp.
    by rewrite (to_nat_add _ _ ha) hmk hpp.
  rewrite e.
  have /and4P[/eqP hp' hpl _ _] := ycubiE hk hp20.
  rewrite hp' cunrank_rank //; last by apply: cmv_lt.
  by rewrite zstep_ycg.
- exact: ycg_inj hyok' htab'.
by have /andP[/allP hyc _] := hyok' => p hp; apply: hyc; rewrite mem_iota add0n.
Qed.
