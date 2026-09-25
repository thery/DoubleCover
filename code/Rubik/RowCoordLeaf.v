(* =========================================================================  *)
(*  RowCoordLeaf.v -- the member of H read off hcoset's four numbers.         *)
(* =========================================================================  *)

(* RowCoord.v carries a position as four numbers.  At a leaf the run needs    *)
(* the member it names, as three ranks.  Here the ranks are read from two     *)
(* tables, with no ranking at run time, and on every leaf the run can reach   *)
(* they are bitleaf's.                                                        *)

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

Lemma ifold_foldiL sz j (f : int -> int) (a : arr) :
  ifold sz j (fun i a => PArray.set a i (f i)) a = ssrint63.foldi sz j (setf f) a.
Proof. by elim: sz j a => [|sz ih] j a //=; rewrite ih. Qed.

Lemma mkT_getL sz (f : int -> int) i :
  (sz <= to_nat max_length)%N -> (to_nat i < sz)%N ->
  PArray.get (mkT sz f) i = f i.
Proof.
move=> hsz hi; rewrite /mkT ifold_foldiL.
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

(* ---- the leaf ------------------------------------------------------------- *)

(* the cubie at an outer place p, given the places of the cubies 0-3 (u) and  *)
(* 4-7 (v): its index in the eight places                                     *)
Definition l8 (u v : int) : seq int :=
  [:: tp0 u; tp1 u; tp2 u; tp3 u; tp0 v; tp1 v; tp2 v; tp3 v].
Definition ecub (u v p : int) : int := of_nat (index p (l8 u v)).

(* the rank of the outer edges, for the pair of numbers a b of sub8 at        *)
(* 1680 a + b                                                                 *)
Definition e8rT : arr :=
  mkT (1680 * 1680)
    (fun i =>
       let a := Uint63.div i n8t in
       let b := Uint63.sub i (Uint63.mul a n8t) in
       lbrank (ecub (PArray.get tup8 a) (PArray.get tup8 b)) 8 8).

(* the cubie, less eight, at the middle place 8 + p, given the places m of    *)
(* the cubies 8-11                                                            *)
Definition l4 (m : int) : seq int := [:: tp0 m; tp1 m; tp2 m; tp3 m].
Definition mcub (m p : int) : int := of_nat (index (Uint63.add p 8) (l4 m)).

(* the rank of the middle edges                                               *)
Definition e4rT : arr := mkT ntup (fun t => lbrank (mcub t) 4 4).

(* the member: three ranks, two of them read from the tables                  *)
Definition cmemb (x : cpos) : memb :=
  let: (c, u, d, m) := x in
  (c, PArray.get e8rT (Uint63.add (Uint63.mul (PArray.get sub8 u) n8t)
                                   (PArray.get sub8 d)),
   PArray.get e4rT m).

(* ---- the checks ----------------------------------------------------------- *)

(* four places in base twelve read back                                       *)
Definition tpC : bool :=
  all (fun a => all (fun b => all (fun c => all (fun d =>
    let t := enc (of_nat a) (of_nat b) (of_nat c) (of_nat d) in
    [&& tp0 t == of_nat a, tp1 t == of_nat b, tp2 t == of_nat c & tp3 t == of_nat d])
    (iota 0 12)) (iota 0 12)) (iota 0 12)) (iota 0 12).
Lemma tpCE : tpC. Proof. by vm_compute. Qed.

(* four distinct outer places: their number is below 1680 and names them      *)
Definition sub8C : bool :=
  let s := sub8 in let u := tup8 in
  all (fun a => all (fun b => all (fun c => all (fun d =>
    uniq [:: a; b; c; d] ==>
    let t := enc (of_nat a) (of_nat b) (of_nat c) (of_nat d) in
    (PArray.get u (PArray.get s t) == t) && (PArray.get s t <? n8t)%uint63)
    (iota 0 8)) (iota 0 8)) (iota 0 8)) (iota 0 8).
Lemma sub8CE : sub8C. Proof. by vm_compute. Qed.

(* ---- the edges of a position ---------------------------------------------- *)

Lemma yefacts y : ypstok y -> lbguard y ->
  [/\ {in iota 0 12 &, injective (yeg (a2y y))},
      (forall q, q < 12 -> yeg (a2y y) q < 12)%N,
      (forall q, q < 8 -> yeg (a2y y) q < 8)%N,
      (forall p, p < 4 -> 8 <= yeg (a2y y) (8 + p))%N &
      (forall p, p < 12 ->
         to_nat (PArray.get lbeq (PArray.get y (Uint63.add 8 (of_nat p))))
         = yeg (a2y y) p)%N].
Proof.
move=> hy hg.
have /andP[/andP[hyok htab] _] := hy.
set Y := a2y y.
have /allP hyi := yok_yoki hyok.
have hent q : (q < 20)%N -> (to_nat (PArray.get y (of_nat q)) < 24)%N.
  by move=> hq; apply: hyi; rewrite mem_iota add0n.
have /andP[_ /allP hye] := hyok.
have he12 q : (q < 12)%N -> (yeg Y q < 12)%N.
  by move=> hq; apply: hye; rewrite mem_iota add0n.
have hout q : (q < 8)%N -> (yeg Y q < 8)%N.
  move=> hq; have hq20 : (8 + q < 20)%N.
    by rewrite -[20%N]/(8 + 12)%N ltn_add2l; apply: ltn_trans hq _.
  by rewrite /yeg (a2y_nth _ hq20) ltn_divLR // (lbguardP hg hq).
split => //.
- exact: yeg_inj.
- by move=> p hp; apply: middle_ge8.
move=> p hp.
have hp20 : (8 + p < 20)%N by rewrite -[20%N]/(8 + 12)%N ltn_add2l.
have hb : (to_nat 8 + p < nwB)%N.
  by apply: (@lt_nwB _ 5) => //; apply: ltn_trans hp20 _.
rewrite (plus_ofn hb) -[PArray.get y _]to_natK.
have h8 : to_nat 8 = 8%N by [].
rewrite h8.
have [_ h2 _] := lbtabE (hent _ hp20).
rewrite h2.
by rewrite /yeg (a2y_nth _ hp20).
Qed.

Lemma inj_onto12 (f : nat -> nat) :
  {in iota 0 12 &, injective f} -> (forall q, q < 12 -> f q < 12)%N ->
  forall b, (b < 12)%N -> exists2 q, (q < 12)%N & f q = b.
Proof.
move=> hinj hlt b hb.
have hu : uniq (map f (iota 0 12)) by rewrite map_inj_in_uniq ?iota_uniq.
have hs : {subset map f (iota 0 12) <= iota 0 12}.
  by move=> x /mapP[j]; rewrite !mem_iota /= !add0n => hj ->; exact: hlt.
have hsz : (seq.size (iota 0 12) <= seq.size (map f (iota 0 12)))%N.
  by rewrite size_map.
have [_ heq] := uniq_min_size hu hs hsz.
have : b \in map f (iota 0 12) by rewrite heq mem_iota add0n.
case/mapP => k; rewrite mem_iota add0n => /andP[_ hk] hke.
by exists k.
Qed.

(* eplace finds the one place that holds the cubie                            *)
Lemma eplace_fold y b q : ypstok y -> lbguard y -> (b < 12)%N -> (q < 12)%N ->
  yeg (a2y y) q = b ->
  forall n j r, (j + n <= 12)%N ->
  ifold n (advn j 0%uint63)
    (fun p r => if Uint63.eqb (PArray.get lbeq (PArray.get y (Uint63.add 8 p)))
                              (of_nat b)
                then p else r) r
  = if (j <= q < j + n)%N then of_nat q else r.
Proof.
move=> hy hg hb hq hqb.
have [hinj h12 _ _ hlb] := yefacts hy hg.
elim => [|n ih] j r hjn.
  by rewrite /= addn0; case: ifP => // /andP[h1 h2]; move: (leq_ltn_trans h1 h2); rewrite ltnn.
have hj12 : (j < 12)%N by apply: leq_trans hjn; rewrite addnS ltnS leq_addr.
have hjw : (j < nwB)%N by apply: (@lt_nwB _ 5) => //; apply: ltn_trans hj12 _.
have ej : advn j 0%uint63 = of_nat j.
  by apply: to_nat_inj; rewrite to_nat_advn0 // (of_natK _ hjw).
rewrite /=.
have -> : Uint63.add (advn j 0%uint63) 1%uint63 = advn j.+1 0%uint63 by rewrite advnS.
rewrite ih; last by rewrite addSnnS.
rewrite ej.
have hbw : (b < nwB)%N by apply: (@lt_nwB _ 5) => //; apply: ltn_trans hb _.
have ht : Uint63.eqb (PArray.get lbeq (PArray.get y (Uint63.add 8 (of_nat j)))) (of_nat b)
          = (j == q).
  apply/idP/idP.
    move=> /eqb_correct e.
    move: (hlb _ hj12); rewrite e (of_natK _ hbw) -hqb => e'.
    by apply/eqP; apply: hinj; rewrite ?mem_iota ?add0n.
  move=> /eqP ->; apply/eqb_complete; apply: to_nat_inj.
  by rewrite (hlb _ hq) (of_natK _ hbw).
rewrite ht.
have [->|hne] := eqVneq j q.
  by rewrite ltnn /= leqnn /= addnS ltnS leq_addr.
rewrite /= addSn.
have -> : (j < q)%N = (j <= q)%N by rewrite ltn_neqAle hne.
by rewrite addnS.
Qed.

Lemma eplaceE y b q : ypstok y -> lbguard y -> (b < 12)%N -> (q < 12)%N ->
  yeg (a2y y) q = b -> eplace y (of_nat b) = of_nat q.
Proof.
move=> hy hg hb hq hqb.
rewrite /eplace -[X in ifold _ X]/(advn 0 0%uint63).
by rewrite (eplace_fold hy hg hb hq hqb) // add0n hq.
Qed.

(* the place of the edge cubie b                                              *)
Definition winv (Y : seq nat) (b : nat) : nat :=
  index b [seq yeg Y q | q <- iota 0 12].

Lemma winvP y : ypstok y -> lbguard y ->
  [/\ (forall b, b < 12 -> winv (a2y y) b < 12 /\ yeg (a2y y) (winv (a2y y) b) = b),
      (forall p, p < 12 -> winv (a2y y) (yeg (a2y y) p) = p),
      (forall b, b < 8 -> winv (a2y y) b < 8) &
      (forall b, 8 <= b < 12 -> 8 <= winv (a2y y) b)]%N.
Proof.
move=> hy hg.
have [hinj h12 hout hge _] := yefacts hy hg.
set Y := a2y y.
have hmem b : (b < 12)%N -> b \in [seq yeg Y q | q <- iota 0 12].
  move=> hb; have [q hq <-] := inj_onto12 hinj h12 hb.
  by apply/mapP; exists q; rewrite ?mem_iota ?add0n.
have hw b : (b < 12)%N -> (winv Y b < 12)%N /\ yeg Y (winv Y b) = b.
  move=> hb; have hm := hmem _ hb.
  have hi : (winv Y b < 12)%N.
    by rewrite /winv -[12%N](size_iota 0) -(size_map (yeg Y)) index_mem.
  split => //.
  by have := nth_index 0%N hm; rewrite (nth_map 0%N) ?size_iota // nth_iota // add0n.
have hu : uniq [seq yeg Y q | q <- iota 0 12] by rewrite map_inj_in_uniq ?iota_uniq.
split => //.
- move=> p hp; rewrite /winv.
  have -> : yeg Y p = nth 0%N [seq yeg Y q | q <- iota 0 12] p.
    by rewrite (nth_map 0%N) ?size_iota // nth_iota.
  by rewrite index_uniq // size_map size_iota.
- move=> b hb; have hb12 : (b < 12)%N by apply: ltn_trans hb _.
  have [hi he] := hw _ hb12.
  rewrite ltnNge; apply/negP => h8.
  have hp : (winv Y b - 8 < 4)%N by rewrite ltn_subLR.
  have := hge _ hp; rewrite subnKC // he => h.
  by move: (leq_ltn_trans h hb); rewrite ltnn.
move=> b /andP[hb8 hb]; have [hi he] := hw _ hb.
rewrite leqNgt; apply/negP => h8.
by move: (hout _ h8); rewrite he ltnNge hb8.
Qed.

(* ---- the tables, read at a position --------------------------------------- *)

Lemma tpE a b c d : (a < 12)%N -> (b < 12)%N -> (c < 12)%N -> (d < 12)%N ->
  let t := enc (of_nat a) (of_nat b) (of_nat c) (of_nat d) in
  [/\ tp0 t = of_nat a, tp1 t = of_nat b, tp2 t = of_nat c & tp3 t = of_nat d].
Proof.
move=> ha hb hc hd /=.
have := tpCE; rewrite /tpC.
move=> /allP/(_ a); rewrite mem_iota add0n => /(_ ha).
move=> /allP/(_ b); rewrite mem_iota add0n => /(_ hb).
move=> /allP/(_ c); rewrite mem_iota add0n => /(_ hc).
move=> /allP/(_ d); rewrite mem_iota add0n => /(_ hd).
by case/and4P => /eqP -> /eqP -> /eqP -> /eqP ->.
Qed.

Lemma sub8E a b c d : (a < 8)%N -> (b < 8)%N -> (c < 8)%N -> (d < 8)%N ->
  uniq [:: a; b; c; d] ->
  let t := enc (of_nat a) (of_nat b) (of_nat c) (of_nat d) in
  PArray.get tup8 (PArray.get sub8 t) = t /\ (to_nat (PArray.get sub8 t) < 1680)%N.
Proof.
move=> ha hb hc hd hu.
have h := sub8CE; rewrite /sub8C in h; cbv zeta in h.
move: h.
move=> /allP/(_ a); rewrite mem_iota add0n => /(_ ha).
move=> /allP/(_ b); rewrite mem_iota add0n => /(_ hb).
move=> /allP/(_ c); rewrite mem_iota add0n => /(_ hc).
move=> /allP/(_ d); rewrite mem_iota add0n => /(_ hd).
move=> /implyP/(_ hu) /andP[/eqP e /nltbP h].
split; first exact: e.
have e8 : to_nat n8t = 1680%N by [].
exact: (leq_trans h (eq_leq e8)).
Qed.

(* the two tables fit in an array                                             *)
Lemma n8sq_ml : (1680 * 1680 <= to_nat max_length)%N.
Proof. vm_compute. reflexivity. Qed.

Lemma ntup_ml : (ntup <= to_nat max_length)%N.
Proof. vm_compute. reflexivity. Qed.

(* NEVER REWRITE WITH mkT_getL: the rewrite tries every PArray.get of the     *)
(* goal against the table, and one of them is tup8, which it then computes.   *)
Lemma e8rT_get A B : (to_nat A < 1680)%N -> (to_nat B < 1680)%N ->
  PArray.get e8rT (Uint63.add (Uint63.mul A n8t) B)
  = lbrank (ecub (PArray.get tup8 A) (PArray.get tup8 B)) 8 8.
Proof.
move=> hA hB.
have e8 : to_nat n8t = 1680%N by [].
have hml : (1680 * 1680 < nwB)%N := leq_ltn_trans n8sq_ml (to_nat_bounded max_length).
have hlt : (to_nat A * 1680 + to_nat B < 1680 * 1680)%N.
  apply: (@leq_trans (to_nat A * 1680 + 1680)); first by rewrite ltn_add2l.
  by rewrite -mulSnr leq_mul2r hA orbT.
have hAm : (to_nat A * to_nat n8t < nwB)%N.
  rewrite e8; apply: leq_ltn_trans hml; apply: leq_trans (leq_addr (to_nat B) _) _.
  exact: ltnW.
have tA : to_nat (Uint63.mul A n8t) = (to_nat A * 1680)%N by rewrite to_nat_mul // e8.
have hAB : (to_nat (Uint63.mul A n8t) + to_nat B < nwB)%N.
  by rewrite tA; apply: ltn_trans hlt hml.
have ti : to_nat (Uint63.add (Uint63.mul A n8t) B) = (to_nat A * 1680 + to_nat B)%N.
  by rewrite to_nat_add // tA.
have ea : Uint63.div (Uint63.add (Uint63.mul A n8t) B) n8t = A.
  apply: to_nat_inj.
  rewrite to_nat_div ti e8.
  rewrite divnMDl; last by [].
  rewrite divn_small; last exact: hB.
  by rewrite addn0.
have eb : Uint63.sub (Uint63.add (Uint63.mul A n8t) B) (Uint63.mul A n8t) = B.
  apply: to_nat_inj.
  have h1 : (to_nat (Uint63.mul A n8t) <= to_nat (Uint63.add (Uint63.mul A n8t) B))%N.
    by rewrite ti tA leq_addr.
  rewrite (to_nat_sub _ _ h1 (to_nat_bounded _)).
  by rewrite ti tA addKn.
have hi : (to_nat (Uint63.add (Uint63.mul A n8t) B) < 1680 * 1680)%N.
  rewrite ti; exact: hlt.
have := @mkT_getL (1680 * 1680)
  (fun i =>
       let a := Uint63.div i n8t in
       let b := Uint63.sub i (Uint63.mul a n8t) in
       lbrank (ecub (PArray.get tup8 a) (PArray.get tup8 b)) 8 8)
  (Uint63.add (Uint63.mul A n8t) B) n8sq_ml hi.
move=> h; apply: (etrans h); clear h.
cbv zeta.
rewrite ea eb.
reflexivity.
Qed.

Lemma e4rT_get M : (to_nat M < ntup)%N -> PArray.get e4rT M = lbrank (mcub M) 4 4.
Proof.
move=> hM.
have := @mkT_getL ntup (fun t => lbrank (mcub t) 4 4) M ntup_ml hM.
move=> h; exact: h.
Qed.

(* four places in base twelve are below 12 ^ 4                                *)
Definition encC : bool :=
  all (fun a => all (fun b => all (fun c => all (fun d =>
    (enc (of_nat a) (of_nat b) (of_nat c) (of_nat d) <? 20736)%uint63)
    (iota 0 12)) (iota 0 12)) (iota 0 12)) (iota 0 12).
Lemma encCE : encC. Proof. by vm_compute. Qed.

Lemma enc_lt a b c d : (a < 12)%N -> (b < 12)%N -> (c < 12)%N -> (d < 12)%N ->
  (to_nat (enc (of_nat a) (of_nat b) (of_nat c) (of_nat d)) < ntup)%N.
Proof.
move=> ha hb hc hd.
have := encCE; rewrite /encC.
move=> /allP/(_ a); rewrite mem_iota add0n => /(_ ha).
move=> /allP/(_ b); rewrite mem_iota add0n => /(_ hb).
move=> /allP/(_ c); rewrite mem_iota add0n => /(_ hc).
move=> /allP/(_ d); rewrite mem_iota add0n => /(_ hd).
move=> /nltbP h.
have e : to_nat 20736 = ntup by [].
exact: (leq_trans h (eq_leq e)).
Qed.

Lemma ofn_inj12 a b : (a < 12)%N -> (b < 12)%N -> of_nat a = of_nat b -> a = b.
Proof.
move=> ha hb e.
have haw : (a < nwB)%N by apply: (@lt_nwB _ 5) => //; apply: ltn_trans ha _.
have hbw : (b < nwB)%N by apply: (@lt_nwB _ 5) => //; apply: ltn_trans hb _.
by rewrite -(of_natK _ haw) -(of_natK _ hbw) e.
Qed.

(* ecub over any eight distinct places; ws is left abstract, since a rewrite  *)
(* on the real places would compute them                                      *)
Lemma ecub_gen (ws : nat -> nat) p j :
  (forall b, b < 8 -> ws b < 12)%N -> {in iota 0 8 &, injective ws} ->
  (j < 8)%N -> ws j = p ->
  to_nat (ecub (enc (of_nat (ws 0%N)) (of_nat (ws 1%N)) (of_nat (ws 2%N)) (of_nat (ws 3%N)))
               (enc (of_nat (ws 4%N)) (of_nat (ws 5%N)) (of_nat (ws 6%N)) (of_nat (ws 7%N)))
               (of_nat p)) = j.
Proof.
move=> hwl hinj hj hjp.
have [t0 t1 t2 t3] := tpE (hwl 0%N isT) (hwl 1%N isT) (hwl 2%N isT) (hwl 3%N isT).
have [t4 t5 t6 t7] := tpE (hwl 4%N isT) (hwl 5%N isT) (hwl 6%N isT) (hwl 7%N isT).
rewrite /ecub /l8 t0 t1 t2 t3 t4 t5 t6 t7.
set s := [:: _; _; _; _; _; _; _; _].
have hs : s = [seq of_nat (ws b) | b <- iota 0 8] by [].
have hu : uniq s.
  rewrite hs map_inj_in_uniq ?iota_uniq // => b b' hb hb' e.
  have hb8 : (b < 8)%N by move: hb; rewrite mem_iota add0n.
  have hb8' : (b' < 8)%N by move: hb'; rewrite mem_iota add0n.
  by apply: hinj => //; apply: ofn_inj12 (hwl _ hb8) (hwl _ hb8') e.
have hn : of_nat p = nth 0%uint63 s j.
  by rewrite hs (nth_map 0%N) ?size_iota // nth_iota // add0n hjp.
have hi : (j < seq.size s)%N by rewrite hs size_map size_iota.
rewrite hn (index_uniq _ hi hu).
apply: of_natK; apply: (@lt_nwB _ 5) => //; apply: ltn_trans hj _.
by [].
Qed.

(* the same for the four middle places                                        *)
Lemma mcub_gen (ws : nat -> nat) p j :
  (forall b, b < 4 -> ws b < 12)%N -> {in iota 0 4 &, injective ws} ->
  (j < 4)%N -> (p < 4)%N -> ws j = (8 + p)%N ->
  to_nat (mcub (enc (of_nat (ws 0%N)) (of_nat (ws 1%N)) (of_nat (ws 2%N)) (of_nat (ws 3%N)))
               (of_nat p)) = j.
Proof.
move=> hwl hinj hj hp hjp.
have [t0 t1 t2 t3] := tpE (hwl 0%N isT) (hwl 1%N isT) (hwl 2%N isT) (hwl 3%N isT).
rewrite /mcub /l4 t0 t1 t2 t3.
set s := [:: _; _; _; _].
have hs : s = [seq of_nat (ws b) | b <- iota 0 4] by [].
have hu : uniq s.
  rewrite hs map_inj_in_uniq ?iota_uniq // => b b' hb hb' e.
  have hb4 : (b < 4)%N by move: hb; rewrite mem_iota add0n.
  have hb4' : (b' < 4)%N by move: hb'; rewrite mem_iota add0n.
  by apply: hinj => //; apply: ofn_inj12 (hwl _ hb4) (hwl _ hb4') e.
have hpw : (p + 8 < nwB)%N.
  have h12 : (p + 8 < 12)%N by rewrite -[12%N]/(4 + 8)%N ltn_add2r.
  by apply: (@lt_nwB _ 5) => //; apply: ltn_trans h12 _.
have h8 : to_nat 8 = 8%N by [].
have hpw' : (p < nwB)%N by apply: leq_ltn_trans hpw; apply: leq_addr.
have e : Uint63.add (of_nat p) 8 = of_nat (8 + p).
  apply: to_nat_inj; rewrite to_nat_add; last by rewrite h8 (of_natK _ hpw').
  have h8p : (8 + p < nwB)%N by rewrite addnC.
  by rewrite h8 (of_natK _ hpw') (of_natK _ h8p) addnC.
have hn : of_nat (8 + p) = nth 0%uint63 s j.
  by rewrite hs (nth_map 0%N) ?size_iota // nth_iota // add0n hjp.
have hi : (j < seq.size s)%N by rewrite hs size_map size_iota.
rewrite e hn (index_uniq _ hi hu).
apply: of_natK; apply: (@lt_nwB _ 5) => //; apply: ltn_trans hj _.
by [].
Qed.

(* the outer table gives the rank of the outer edges, f being the cubie at    *)
(* each place and ws its place                                                *)
Lemma e8_gen (ws f : nat -> nat) A B :
  (forall b, b < 8 -> ws b < 8)%N -> {in iota 0 8 &, injective ws} ->
  (forall p, p < 8 -> f p < 8 /\ ws (f p) = p)%N ->
  (to_nat A < 1680)%N -> (to_nat B < 1680)%N ->
  PArray.get tup8 A
    = enc (of_nat (ws 0%N)) (of_nat (ws 1%N)) (of_nat (ws 2%N)) (of_nat (ws 3%N)) ->
  PArray.get tup8 B
    = enc (of_nat (ws 4%N)) (of_nat (ws 5%N)) (of_nat (ws 6%N)) (of_nat (ws 7%N)) ->
  PArray.get e8rT (Uint63.add (Uint63.mul A n8t) B) = rank8 f.
Proof.
move=> hw8 hinj hf hA hB tA tB.
rewrite (e8rT_get hA hB) tA tB.
have hw12 b : (b < 8)%N -> (ws b < 12)%N.
  by move=> hb; apply: ltn_trans (hw8 _ hb) _.
apply: lbrank8.
- move=> p hp; have [hfp hwp] := hf _ hp.
  exact: ecub_gen hw12 hinj hfp hwp.
- move=> p p'; rewrite !mem_iota !add0n => hp hp' e.
  have [_ h1] := hf _ hp; have [_ h2] := hf _ hp'.
  by rewrite -h1 -h2 e.
by move=> p hp; case: (hf _ hp).
Qed.

(* and the middle table the rank of the middle edges                          *)
Lemma m4_gen (ws f : nat -> nat) :
  (forall b, b < 4 -> ws b < 12)%N -> {in iota 0 4 &, injective ws} ->
  (forall p, p < 4 -> f p < 4 /\ ws (f p) = 8 + p)%N ->
  PArray.get e4rT
    (enc (of_nat (ws 0%N)) (of_nat (ws 1%N)) (of_nat (ws 2%N)) (of_nat (ws 3%N)))
  = rank4 f.
Proof.
move=> hw12 hinj hf.
rewrite (e4rT_get (enc_lt (hw12 0%N isT) (hw12 1%N isT) (hw12 2%N isT) (hw12 3%N isT))).
apply: lbrank4.
- move=> p hp; have [hfp hwp] := hf _ hp.
  exact: mcub_gen hw12 hinj hfp hp hwp.
- move=> p p'; rewrite !mem_iota !add0n => hp hp' e.
  have [_ h1] := hf _ hp; have [_ h2] := hf _ hp'.
  by apply/eqP; rewrite -(eqn_add2l 8) -h1 -h2 e.
by move=> p hp; case: (hf _ hp).
Qed.

(* ---- the leaf is bitleaf's ------------------------------------------------ *)

(* the four numbers of a position, the edge places written out               *)
Lemma cofyL y : ypstok y -> lbguard y ->
  cofy y =
  (lbrank (fun p => PArray.get lbcq (PArray.get y p)) 8 8,
   enc (of_nat (winv (a2y y) 0%N)) (of_nat (winv (a2y y) 1%N))
       (of_nat (winv (a2y y) 2%N)) (of_nat (winv (a2y y) 3%N)),
   enc (of_nat (winv (a2y y) 4%N)) (of_nat (winv (a2y y) 5%N))
       (of_nat (winv (a2y y) 6%N)) (of_nat (winv (a2y y) 7%N)),
   enc (of_nat (winv (a2y y) 8%N)) (of_nat (winv (a2y y) 9%N))
       (of_nat (winv (a2y y) 10%N)) (of_nat (winv (a2y y) 11%N))).
Proof.
move=> hy hg.
have [hw _ _ _] := winvP hy hg.
have ep b : (b < 12)%N -> eplace y (of_nat b) = of_nat (winv (a2y y) b).
  by move=> hb; have [h1 h2] := hw _ hb; apply: eplaceE.
rewrite /cofy; cbv beta zeta.
rewrite (ep 0%N isT) (ep 1%N isT) (ep 2%N isT) (ep 3%N isT).
rewrite (ep 4%N isT) (ep 5%N isT) (ep 6%N isT) (ep 7%N isT).
rewrite (ep 8%N isT) (ep 9%N isT) (ep 10%N isT) (ep 11%N isT).
reflexivity.
Qed.

(* bitleaf's three ranks, as ranks of the cubies                              *)
Lemma bitleafR y : ypstok y -> lbguard y ->
  bitleaf y = (lbrank (fun p => PArray.get lbcq (PArray.get y p)) 8 8,
               rank8 (yeg (a2y y)),
               rank4 (fun q => (yeg (a2y y) (8 + q) - 8)%N)).
Proof.
move=> hy hg; rewrite /bitleaf hg.
have [hinj h12 hout hge hlb] := yefacts hy hg.
have /andP[/andP[hyok _] _] := hy.
have /allP hyi := yok_yoki hyok.
have hent q : (q < 20)%N -> (to_nat (PArray.get y (of_nat q)) < 24)%N.
  by move=> hq; apply: hyi; rewrite mem_iota add0n.
have hO : lbrank (fun p => PArray.get lbeq (PArray.get y (Uint63.add 8 p))) 8 8
          = rank8 (yeg (a2y y)).
  apply: lbrank8.
  - by move=> p hp; apply: hlb; apply: ltn_trans hp _.
  - move=> p p'; rewrite !mem_iota !add0n => hp hp'; apply: hinj;
    by rewrite mem_iota add0n; apply: ltn_trans (_ : 8 < 12)%N.
  - exact: hout.
have hM : lbrank (fun p => PArray.get lbmq (PArray.get y (Uint63.add 16 p))) 4 4
          = rank4 (fun q => (yeg (a2y y) (8 + q) - 8)%N).
  apply: lbrank4.
  - move=> p hp; have hp20 : (16 + p < 20)%N by rewrite -[20%N]/(16 + 4)%N ltn_add2l.
    have hb : (to_nat 16 + p < nwB)%N.
      by apply: (@lt_nwB _ 5) => //; apply: ltn_trans hp20 _.
    have h16 : to_nat 16 = 16%N by [].
    rewrite (plus_ofn hb) h16 -[PArray.get y (of_nat (16 + p))]to_natK.
    have [_ _ h3] := lbtabE (hent _ hp20).
    by rewrite h3 /yeg -(a2y_nth _ hp20) addnA.
  - move=> x z; rewrite !mem_iota !add0n => hx hz he.
    have h1 := hge _ hx; have h2 := hge _ hz.
    have : (8 + x)%N = (8 + z)%N.
      apply: hinj; rewrite ?mem_iota ?add0n.
      + by rewrite -[12%N]/(8 + 4)%N ltn_add2l.
      + by rewrite -[12%N]/(8 + 4)%N ltn_add2l.
      by rewrite -(subnK h1) -(subnK h2) he.
    by move/eqP; rewrite eqn_add2l => /eqP.
  move=> p hp; rewrite ltn_subLR ?hge //.
  by apply: h12; rewrite -[12%N]/(8 + 4)%N ltn_add2l.
by rewrite hO hM.
Qed.

(* THE LEAF.  The edge places are made an abstract w before the tables come   *)
(* in: a `//' or a rewrite with the tables in the context would compute them. *)
Theorem cmembE y : ypstok y -> lbguard y -> cmemb (cofy y) = bitleaf y.
Proof.
move=> hy hg.
rewrite (bitleafR hy hg) (cofyL hy hg).
have [hinj h12 hout hge _] := yefacts hy hg.
have [hw hwy hw8 hw12] := winvP hy hg.
move: hw hwy hw8 hw12; move: (winv (a2y y)) => w hw hwy hw8 hw12.
have hwinj : {in iota 0 12 &, injective w}.
  move=> b b'; rewrite !mem_iota !add0n => hb hb' e.
  by case: (hw _ hb) => _ <-; case: (hw _ hb') => _ <-; rewrite e.
have hwinj8 : {in iota 0 8 &, injective w}.
  move=> b b'; rewrite !mem_iota !add0n => hb hb'; apply: hwinj;
  by rewrite mem_iota add0n; apply: ltn_trans (_ : 8 < 12)%N.
have hu4 k : (k <= 4)%N -> uniq [:: w k; w k.+1; w k.+2; w k.+3].
  move=> hk.
  have -> : [:: w k; w k.+1; w k.+2; w k.+3] = map w (iota k 4) by [].
  have hk8 : (k + 4 <= 8)%N by rewrite -[8%N]/(4 + 4)%N leq_add2r.
  rewrite map_inj_in_uniq ?iota_uniq // => b b'; rewrite !mem_iota => /andP[_ hb] /andP[_ hb'].
  apply: hwinj8; rewrite mem_iota leq0n /=.
    exact: leq_trans hb hk8.
  exact: leq_trans hb' hk8.
have hf8 p : (p < 8)%N -> (yeg (a2y y) p < 8)%N /\ w (yeg (a2y y) p) = p.
  by move=> hp; split; [apply: hout | apply: hwy; apply: ltn_trans hp _].
have hw12' b : (b < 4)%N -> (w (8 + b) < 12)%N.
  move=> hb; have hb12 : (8 + b < 12)%N by rewrite -[12%N]/(8 + 4)%N ltn_add2l.
  by case: (hw _ hb12).
have hinj4 : {in iota 0 4 &, injective (fun b => w (8 + b))}.
  move=> b b'; rewrite !mem_iota !add0n => /andP[_ hb] /andP[_ hb'] e.
  have hb12 : (8 + b)%N \in iota 0 12.
    by rewrite mem_iota add0n leq0n -[12%N]/(8 + 4)%N ltn_add2l.
  have hb12' : (8 + b')%N \in iota 0 12.
    by rewrite mem_iota add0n leq0n -[12%N]/(8 + 4)%N ltn_add2l.
  have := hwinj _ _ hb12 hb12' e.
  by move/eqP; rewrite eqn_add2l => /eqP.
have hf4 p : (p < 4)%N ->
    ((yeg (a2y y) (8 + p) - 8) < 4)%N /\ w (8 + (yeg (a2y y) (8 + p) - 8)) = (8 + p)%N.
  move=> hp; have h8 := hge _ hp.
  have hp12 : (8 + p < 12)%N by rewrite -[12%N]/(8 + 4)%N ltn_add2l.
  split; first by rewrite ltn_subLR // h12.
  by rewrite subnKC // hwy.
have h3 := @m4_gen (fun b => w (8 + b)) (fun q => (yeg (a2y y) (8 + q) - 8)%N) hw12' hinj4 hf4.
have [tU hU] := sub8E (hw8 0%N isT) (hw8 1%N isT) (hw8 2%N isT) (hw8 3%N isT) (hu4 0%N isT).
have [tD hD] := sub8E (hw8 4%N isT) (hw8 5%N isT) (hw8 6%N isT) (hw8 7%N isT) (hu4 4%N isT).
have h2 := @e8_gen w (yeg (a2y y)) _ _ hw8 hwinj8 hf8 hU hD tU tD.
rewrite -h2 -h3.
reflexivity.
Qed.
