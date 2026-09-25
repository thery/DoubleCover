(* =========================================================================  *)
(*  RowCoordEdge.v -- the three edge numbers move as the twenty cubies do.    *)
(* =========================================================================  *)

(* RowCoord.v keeps each group of four edges as the four places of its        *)
(* cubies, in base twelve, and moves it by one table.  Here: on every         *)
(* position the run can carry, the table gives the places the cubies of the   *)
(* moved position stand at.                                                   *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Moves Coordfs Phase1 Row RowMap RowFinal RowMembi RowMemb RowCub RowCubi RowCubInst.
Require Import Lehmer RowLeafFast RowTabL RowCoord RowCoordOk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

(* ---- a walk that keeps the last place a test holds at ---------------------- *)

Lemma advn_of j : (j < nwB)%N -> advn j 0%uint63 = of_nat j.
Proof. by move=> hj; apply: to_nat_inj; rewrite to_nat_advn0 // of_natK. Qed.

Lemma ifold_none n j (P : int -> bool) (a : int) :
  (j + n <= nwB)%N ->
  (forall q, (j <= q < j + n)%N -> P (of_nat q) = false) ->
  ifold n (advn j 0%uint63) (fun k r => if P k then k else r) a = a.
Proof.
elim: n j a => [|n ih] j a hb hq //=.
have hb' : (j + n < nwB)%N by rewrite -addnS.
have hj : (j < nwB)%N := leq_ltn_trans (leq_addr n j) hb'.
have -> : Uint63.add (advn j 0%uint63) 1%uint63 = advn j.+1 0%uint63.
  by rewrite advnS.
rewrite (advn_of hj) (hq j); last by rewrite leqnn addnS ltnS leq_addr.
apply: ih; first by rewrite addSnnS.
move=> q /andP[h1 h2]; apply: hq.
by rewrite (ltnW h1) -addSnnS h2.
Qed.

Lemma ifold_last n j (P : int -> bool) (a : int) p :
  (j + n <= nwB)%N -> (j <= p < j + n)%N -> P (of_nat p) ->
  (forall q, (j <= q < j + n)%N -> P (of_nat q) -> q = p) ->
  ifold n (advn j 0%uint63) (fun k r => if P k then k else r) a = of_nat p.
Proof.
elim: n j a => [|n ih] j a hb hp hP hu.
  by move: hp; rewrite addn0 => /andP[h1 h2]; move: (leq_ltn_trans h1 h2);
     rewrite ltnn.
have hb' : (j + n < nwB)%N by rewrite -addnS.
have hj : (j < nwB)%N := leq_ltn_trans (leq_addr n j) hb'.
rewrite /=.
have -> : Uint63.add (advn j 0%uint63) 1%uint63 = advn j.+1 0%uint63.
  by rewrite advnS.
rewrite (advn_of hj).
have [ejp|njp] := eqVneq j p.
  move: hP hu; rewrite -ejp => hP hu.
  rewrite hP ifold_none; first by [].
    by rewrite addSnnS.
  move=> q /andP[h1 h2]; apply/negbTE/negP => hq.
  have e := hu q ltac:(by rewrite (ltnW h1) -addSnnS h2) hq.
  by move: h1; rewrite e ltnn.
have hPj : P (of_nat j) = false.
  apply/negbTE/negP => hq.
  have e := hu j ltac:(by rewrite leqnn addnS ltnS leq_addr) hq.
  by move: njp; rewrite e eqxx.
rewrite hPj; apply: ih.
- by rewrite addSnnS.
- by move: hp => /andP[h1 h2]; rewrite ltn_neqAle njp h1 addSnnS h2.
- exact: hP.
move=> q /andP[h1 h2] hq; apply: hu => //.
by rewrite (ltnW h1) -addSnnS h2.
Qed.

(* ---- the edge cubie at a place, as the run reads it ------------------------ *)

Lemma ypstok_yok y : ypstok y -> yok (a2y y) && tab_ok flast (cub2tab (a2y y)).
Proof. by move=> /andP[]. Qed.

Lemma lbeq_yeg y p : ypstok y -> (p < 12)%N ->
  PArray.get lbeq (PArray.get y (Uint63.add 8 (of_nat p)))
  = of_nat (yeg (a2y y) p).
Proof.
move=> hy hp.
have /andP[hyok _] := ypstok_yok hy.
have /allP hyi := yok_yoki hyok.
have hp20 : (8 + p < 20)%N.
  by rewrite -[20%N]/(8 + 12)%N ltn_add2l.
have e : Uint63.add 8 (of_nat p) = of_nat (8 + p).
  by rewrite plus_ofn //; apply: (@lt_nwB _ 5) => //; apply: ltn_trans hp20 _.
have hv : (to_nat (PArray.get y (of_nat (8 + p))) < 24)%N.
  by apply: hyi; rewrite mem_iota add0n.
rewrite e -[PArray.get y (of_nat (8 + p))]to_natK.
apply: to_nat_inj.
have hy12 : (yeg (a2y y) p < 12)%N.
  by have /andP[_ /allP] := hyok; apply; rewrite mem_iota add0n.
have hyb : (yeg (a2y y) p < nwB)%N.
  by apply: ltn_trans hy12 _; apply: (@lt_nwB _ 5).
rewrite [RHS](of_natK _ hyb).
case: (lbtabE hv) => _ h2 _.
rewrite h2.
by rewrite /yeg (a2y_nth _ hp20).
Qed.

Lemma eqb_ofn (u : nat) (b : int) : (u < nwB)%N ->
  Uint63.eqb (of_nat u) b = (u == to_nat b).
Proof.
move=> hu; apply/idP/idP.
  by move/neqbP; rewrite of_natK // => ->.
by move/eqP => e; apply/neqbP; rewrite of_natK.
Qed.

(* the place of the cubie b: the one place whose cubie it is                  *)
Lemma eplaceE y p b : ypstok y -> (p < 12)%N -> yeg (a2y y) p = to_nat b ->
  eplace y b = of_nat p.
Proof.
move=> hy hp hb.
have /andP[hyok htab] := ypstok_yok hy.
have hinj := yeg_inj hyok htab.
have hl q : (q < 12)%N -> (yeg (a2y y) q < nwB)%N.
  move=> hq; have /andP[_ /allP] := hyok; move/(_ q); rewrite mem_iota add0n.
  by move/(_ hq) => h; apply: ltn_trans h _; apply: (@lt_nwB _ 5).
rewrite /eplace.
apply: (@ifold_last 12 0).
- by apply: ltnW; apply: (@lt_nwB _ 5).
- by rewrite leq0n add0n.
- by rewrite (lbeq_yeg hy hp) eqb_ofn ?hl // hb.
move=> q /andP[_ hq]; rewrite add0n in hq.
rewrite (lbeq_yeg hy hq) eqb_ofn ?hl // -hb => /eqP e.
by apply: hinj; rewrite ?mem_iota ?add0n.
Qed.

(* every edge cubie stands somewhere *)
Lemma yeg_onto y c : ypstok y -> (c < 12)%N ->
  exists2 p, (p < 12)%N & yeg (a2y y) p = c.
Proof.
move=> hy hc.
have /andP[hyok htab] := ypstok_yok hy.
have hinj := yeg_inj hyok htab.
have hr p : (p < 12)%N -> (yeg (a2y y) p < 12)%N.
  by move=> hp; have /andP[_ /allP] := hyok; apply; rewrite mem_iota add0n.
have hu : uniq [seq yeg (a2y y) p | p <- iota 0 12].
  by rewrite map_inj_in_uniq ?iota_uniq.
have hpe := perm_of_rng hu hr.
have : c \in [seq yeg (a2y y) p | p <- iota 0 12].
  by rewrite (perm_mem hpe) mem_iota add0n.
by case/mapP => p; rewrite mem_iota add0n => hp ->; exists p.
Qed.

(* ---- a move ---------------------------------------------------------------- *)

Lemma zstep_yeg Y k q : (q < 12)%N ->
  yeg (zstep Y k) q = yeg Y (nth 0%N (ymvpn k) (8 + q) - 8).
Proof.
move=> hq; have hq20 : (8 + q < 20)%N by rewrite -[20%N]/(8 + 12)%N ltn_add2l.
have hn8 : (8 + q < 8)%N = false by rewrite ltnNge leq_addr.
rewrite /yeg /zstep /ystepm (nth_map 0%N) ?size_iota // nth_iota // add0n hn8.
rewrite /ymvpn (nth_map 0%N) ?size_iota // nth_iota // add0n hn8 addKn.
rewrite [2 * _]mulnC divnMDl // (divn_small (ltn_pmod _ (isT : 0 < 2)%N)) addn0.
by rewrite /yeg.
Qed.

(* where the move sends the edge place x, as the tables read it               *)
Definition ei (k : nat) (x : int) : int :=
  PArray.get einvT (Uint63.add (Uint63.mul (of_nat k) 12) x).

Definition einvC : bool :=
  all (fun k => all (fun x =>
         let e := to_nat (ei k (of_nat x)) in
         (e < 12) && (nth 0 (ymvpn k) (8 + e) == 8 + x))%N
       (iota 0 12)) (iota 0 18).
Lemma einvCE : einvC. Proof. by vm_compute. Qed.

Lemma einvE k x : (k < 18)%N -> (x < 12)%N ->
  (to_nat (ei k (of_nat x)) < 12)%N /\
  nth 0%N (ymvpn k) (8 + to_nat (ei k (of_nat x))) = (8 + x)%N.
Proof.
move=> hk hx; have /allP/(_ k) := einvCE; rewrite mem_iota add0n => /(_ hk).
move/allP/(_ x); rewrite mem_iota add0n => /(_ hx) /andP[h1 /eqP h2].
by split.
Qed.

Lemma allP_iota (P : nat -> bool) n x : all P (iota 0 n) -> (x < n)%N -> P x.
Proof. by move/allP/(_ x); rewrite mem_iota add0n; apply. Qed.

(* the table, entry by entry, over the four places it is read at             *)
Definition etabC : bool :=
  all (fun a => all (fun b => all (fun c => all (fun d => all (fun k =>
    Uint63.eqb
      (PArray.get etab (Uint63.add (Uint63.mul (enc (of_nat a) (of_nat b)
                                                   (of_nat c) (of_nat d)) 18)
                                   (of_nat k)))
      (enc (ei k (of_nat a)) (ei k (of_nat b)) (ei k (of_nat c)) (ei k (of_nat d))))
    (iota 0 18)) (iota 0 12)) (iota 0 12)) (iota 0 12)) (iota 0 12).
Lemma etabCE : etabC. Proof. by vm_compute. Qed.

Lemma etabE a b c d k : (a < 12)%N -> (b < 12)%N -> (c < 12)%N ->
  (d < 12)%N -> (k < 18)%N ->
  PArray.get etab (Uint63.add (Uint63.mul (enc (of_nat a) (of_nat b)
                                              (of_nat c) (of_nat d)) 18)
                              (of_nat k))
  = enc (ei k (of_nat a)) (ei k (of_nat b)) (ei k (of_nat c)) (ei k (of_nat d)).
Proof.
move=> ha hb hc hd hk.
have := etabCE; rewrite /etabC => h.
have {h} := allP_iota h ha.
move=> h; have {h} := allP_iota h hb.
move=> h; have {h} := allP_iota h hc.
move=> h; have {h} := allP_iota h hd.
move=> h; have {h} := allP_iota h hk.
by move=> /eqb_correct.
Qed.

(* one cubie: its place, and its place after the move                         *)
Lemma eplace_step y k bi : (k < 18)%N -> ypstok y -> (to_nat bi < 12)%N ->
  exists p, [/\ (p < 12)%N, eplace y bi = of_nat p &
                eplace (zstepi y (of_nat k)) bi = ei k (of_nat p)].
Proof.
move=> hk hy hb.
have [p hp hpe] := yeg_onto hy hb.
exists p; split => //; first exact: eplaceE.
have [he1 he2] := einvE hk hp.
have hy' := ypstok_step hk hy.
have hyi : yoki y by apply: yok_yoki; have /andP[] := ypstok_yok hy.
rewrite -[ei k (of_nat p)]to_natK.
apply: (eplaceE hy' he1).
rewrite (a2y_zstepi hk hyi) zstep_yeg // he2 addKn.
exact: hpe.
Qed.

(* ---- the three edge numbers ------------------------------------------------ *)

Definition etupn (y : arr) (b : int) : int :=
  enc (eplace y b) (eplace y (Uint63.add b 1)) (eplace y (Uint63.add b 2))
      (eplace y (Uint63.add b 3)).

Lemma cofyE y : cofy y =
  (lbrank (fun p => PArray.get lbcq (PArray.get y p)) 8 8,
   etupn y 0, etupn y 4, etupn y 8).
Proof. by []. Qed.

Lemma etup_step y k b : (k < 18)%N -> ypstok y ->
  (b = 0 \/ b = 4 \/ b = 8)%uint63 ->
  PArray.get etab (Uint63.add (Uint63.mul (etupn y b) 18) (of_nat k))
  = etupn (zstepi y (of_nat k)) b.
Proof.
move=> hk hy hb.
have h0 : (to_nat b < 12)%N by case: hb => [->|[->|->]].
have h1 : (to_nat (Uint63.add b 1) < 12)%N by case: hb => [->|[->|->]].
have h2 : (to_nat (Uint63.add b 2) < 12)%N by case: hb => [->|[->|->]].
have h3 : (to_nat (Uint63.add b 3) < 12)%N by case: hb => [->|[->|->]].
have [p0 [q0 e0 f0]] := eplace_step hk hy h0.
have [p1 [q1 e1 f1]] := eplace_step hk hy h1.
have [p2 [q2 e2 f2]] := eplace_step hk hy h2.
have [p3 [q3 e3 f3]] := eplace_step hk hy h3.
rewrite /etupn e0 e1 e2 e3 f0 f1 f2 f3.
exact: etabE.
Qed.
