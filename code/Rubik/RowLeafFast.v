(* =========================================================================  *)
(*  RowLeafFast.v -- the leaf ranked straight from the twenty, with a mask.   *)
(* =========================================================================  *)

(* WHY.  The run's leaf turns the twenty cubies back into the forty eight     *)
(* entry table, inverts it and ranks it: 12.0 us a leaf, measured in          *)
(* RowLeafBench.  Ranked straight from the twenty with a bit mask it is 1.16  *)
(* us.  This file proves the two leaves give the same member on every         *)
(* position the leaf test lets through.                                       *)
(*                                                                            *)
(* THE MASK.  A Lehmer digit counts the later values below a value.  When the *)
(* values are 0 .. n-1 that is the value less the EARLIER values below it,    *)
(* and those are a mask of the values already seen: one popcount.            *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Moves Coordfs Lehmer Row RowMap RowFinal RowMembi RowMemb RowCub RowCubi RowCubInst.

Notation arr := (PArray.array int).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ---- a digit, counted from the front ------------------------------------ *)

(* q a permutation of 0 .. n-1: v of its values are below v                  *)
Lemma count_perm_lt n (q : nat -> nat) v :
  {in iota 0 n &, injective q} -> (forall j, j < n -> q j < n) -> v <= n ->
  count (fun j => q j < v) (iota 0 n) = v.
Proof.
move=> hinj hlt hv.
have hu : uniq (map q (iota 0 n)) by rewrite map_inj_in_uniq ?iota_uniq.
have hs : {subset map q (iota 0 n) <= iota 0 n}.
  by move=> x /mapP[j]; rewrite !mem_iota /= !add0n => hj ->; exact: hlt.
have hsz : seq.size (iota 0 n) <= seq.size (map q (iota 0 n)) by rewrite size_map.
have [_ heq] := uniq_min_size hu hs hsz.
have hperm : perm_eq (map q (iota 0 n)) (iota 0 n).
  by apply: uniq_perm => //; exact: iota_uniq.
rewrite -(count_map q (fun x => x < v)) (seq.permP hperm).
rewrite -{1}(subnKC hv) iotaD count_cat add0n.
rewrite (@eq_in_count _ _ predT); last by move=> x; rewrite mem_iota /= add0n => ->.
rewrite count_predT size_iota (@eq_in_count _ _ pred0) ?count_pred0 ?addn0 //.
by move=> x; rewrite mem_iota => /andP[h _]; rewrite /= ltnNge h.
Qed.

(* the digit is the value less the earlier values below it                   *)
Lemma lcode_perm n (q : nat -> nat) i :
  {in iota 0 n &, injective q} -> (forall j, j < n -> q j < n) -> i < n ->
  lcode n q i = q i - count (fun j => q j < q i) (iota 0 i).
Proof.
move=> hinj hlt hi.
have := count_perm_lt hinj hlt (ltnW (hlt _ hi)).
have -> : iota 0 n = iota 0 i ++ i :: iota i.+1 (n - i.+1).
  by rewrite -{1}(subnKC (ltnW hi)) iotaD add0n -(subnSK hi).
rewrite count_cat /= ltnn add0n => h.
by rewrite -[X in X - _]h addKn.
Qed.

(* ---- the mask, on nat --------------------------------------------------- *)

(* bit j of s, and the bits of s among the eight                              *)
Definition bitn (s j : nat) : bool := odd (s %/ 2 ^ j).
Definition popn (s : nat) : nat := count (bitn s) (iota 0 8).

(* ADDING A BIT THAT IS NOT THERE SETS IT AND NOTHING ELSE, and a mask below  *)
(* v keeps the bits below v.  Both on every mask of eight bits, computed.     *)
Definition F1b : bool :=
  all (fun s => all (fun w => ~~ bitn s w ==>
         [&& s + 2 ^ w < 256 &
             all (fun j => bitn (s + 2 ^ w) j == bitn s j || (j == w)) (iota 0 8)])
       (iota 0 8)) (iota 0 256).
Lemma F1bE : F1b. Proof. by vm_compute. Qed.

Definition F2b : bool :=
  all (fun s => all (fun v => all (fun j => bitn (s %% 2 ^ v) j == bitn s j && (j < v))
       (iota 0 8)) (iota 0 9)) (iota 0 256).
Lemma F2bE : F2b. Proof. by vm_compute. Qed.

(* the values seen after i steps, as a mask                                  *)
Definition seenn (q : nat -> nat) (i : nat) : nat := sumn [seq 2 ^ q k | k <- iota 0 i].

Lemma seennS q i : seenn q i.+1 = seenn q i + 2 ^ q i.
Proof.
have -> : i.+1 = i + 1 by rewrite addn1.
by rewrite /seenn iotaD map_cat sumn_cat /= addn0 add0n.
Qed.

(* the mask has a bit exactly for each value seen                            *)
Lemma seenn_bits n (q : nat -> nat) i :
  n <= 8 -> {in iota 0 n &, injective q} -> (forall j, j < n -> q j < n) -> i <= n ->
  seenn q i < 256 /\ forall j, j < 8 -> bitn (seenn q i) j = (j \in map q (iota 0 i)).
Proof.
move=> hn hinj hlt; elim: i => [_ | i ih hi].
  by split=> // j _; rewrite /bitn /seenn /= div0n.
have [hs hb] := ih (ltnW hi).
have hqi : q i < 8 by apply: leq_trans (hlt _ hi) hn.
have hnot : ~~ bitn (seenn q i) (q i).
  rewrite hb //; apply/mapP => -[k]; rewrite mem_iota /= add0n => hk hq.
  have := hinj i k; rewrite !mem_iota /= !add0n => /(_ hi (ltn_trans hk hi) hq) hik.
  by move: hk; rewrite -hik ltnn.
have hs8 : seenn q i \in iota 0 256 by rewrite mem_iota /= add0n.
have hq8 : q i \in iota 0 8 by rewrite mem_iota /= add0n.
have /allP/(_ _ hs8)/allP/(_ _ hq8) := F1bE.
move=> /implyP/(_ hnot)/andP[hs' /allP hb'].
rewrite seennS; split=> // j hj.
have hj8 : j \in iota 0 8 by rewrite mem_iota /= add0n.
have /eqP -> := hb' _ hj8.
have -> : i.+1 = i + 1 by rewrite addn1.
by rewrite hb // iotaD map_cat mem_cat /= mem_seq1 add0n.
Qed.

(* the popcount of the mask below v counts the values seen below v           *)
Lemma popn_seenn n (q : nat -> nat) i v :
  n <= 8 -> {in iota 0 n &, injective q} -> (forall j, j < n -> q j < n) -> i <= n ->
  v <= 8 ->
  popn (seenn q i %% 2 ^ v) = count (fun k => q k < v) (iota 0 i).
Proof.
move=> hn hinj hlt hi hv.
have [hs hb] := seenn_bits hn hinj hlt hi.
have hs8 : seenn q i \in iota 0 256 by rewrite mem_iota /= add0n.
have hv9 : v \in iota 0 9 by rewrite mem_iota /= add0n ltnS.
have /allP/(_ _ hs8)/allP/(_ _ hv9)/allP hF2 := F2bE.
set Q := map q (iota 0 i).
rewrite /popn (@eq_in_count _ _ (predI (fun j => j < v) (mem Q))); last first.
  move=> j hj; have /eqP -> := hF2 _ hj.
  have hj8 : j < 8 by move: hj; rewrite mem_iota /= add0n.
  by rewrite (hb _ hj8) andbC.
have hperm : perm_eq [seq j <- iota 0 8 | j \in Q] Q.
  apply: uniq_perm.
  - by apply: filter_uniq; exact: iota_uniq.
  - rewrite map_inj_in_uniq ?iota_uniq //.
    move=> x y; rewrite !mem_iota /= !add0n => hx hy; apply: hinj;
    by rewrite mem_iota /= add0n; apply: leq_trans hi.
  move=> x; rewrite mem_filter.
  apply/andP/idP => [[] // | hx]; split => //.
  case/mapP: hx => k; rewrite mem_iota add0n => /andP[_ hk] ->.
  by rewrite mem_iota add0n /=; apply: leq_trans (hlt _ (leq_trans hk hi)) hn.
by rewrite -count_filter (seq.permP hperm) count_map.
Qed.

(* ---- the rank with a mask, on nat, is the Lehmer rank -------------------- *)

Definition mrank (n : nat) (q : nat -> nat) : nat :=
  foldl (fun r i => r * (n - i) + (q i - popn (seenn q i %% 2 ^ q i))) 0 (iota 0 n).

Lemma mrankE n (q : nat -> nat) :
  n <= 8 -> {in iota 0 n &, injective q} -> (forall j, j < n -> q j < n) ->
  mrank n q = lrank n q.
Proof.
move=> hn hinj hlt; rewrite /mrank /lrank.
apply: foldl_eq_in => i r; rewrite mem_iota add0n => /andP[_ hi].
have hq8 : q i <= 8 by apply: leq_trans (ltnW (hlt _ hi)) hn.
rewrite (popn_seenn hn hinj hlt (ltnW hi) hq8).
by rewrite -(lcode_perm hinj hlt hi).
Qed.

(* ---- the same rank on int63 --------------------------------------------- *)

(* THE STATE IS ONE int: the rank so far above the mask of eight bits.  The   *)
(* mask and the new bit are ADDED, not or-ed: they are disjoint, so it is the *)
(* same number, and an addition is what the arithmetic below reads.          *)

Local Open Scope uint63_scope.

(* the popcount of every mask of eight bits                                   *)
Definition lbpop : arr := Eval vm_compute in
  ifold 256 0 (fun s a => PArray.set a s (of_nat (popn (to_nat s)))) (PArray.make 256 0).

Definition lbpopC : bool :=
  all (fun s => (to_nat (PArray.get lbpop (of_nat s)) == popn s)%N) (iota 0 256).
Lemma lbpopCE : lbpopC. Proof. by vm_compute. Qed.

Lemma lbpopE s : (s < 256)%N -> to_nat (PArray.get lbpop (of_nat s)) = popn s.
Proof.
move=> hs; have /allP/(_ s) := lbpopCE.
by rewrite mem_iota add0n => /(_ hs)/eqP.
Qed.

(* one step: the digit is the value less the values seen below it            *)
Definition lbstep (ni : int) (v : int -> int) (i st : int) : int :=
  let x := v i in
  let bx := Uint63.lsl 1 x in
  let seen := Uint63.land st 255 in
  let c := Uint63.sub x (PArray.get lbpop (Uint63.land seen (decr bx))) in
  Uint63.add (Uint63.lsl (Uint63.add (Uint63.mul (Uint63.lsr st 8) (Uint63.sub ni i)) c) 8)
             (Uint63.add seen bx).

Definition lbrank (v : int -> int) (nn : nat) (ni : int) : int :=
  Uint63.lsr (ifold nn 0 (lbstep ni v) 0) 8.

Lemma m255 : 255 = decr (Uint63.lsl 1 8). Proof. by vm_compute. Qed.

(* a mask below v has at most v bits, on every mask, computed                 *)
Definition F3b : bool :=
  all (fun s => all (fun v => (popn (s %% 2 ^ v) <= v)%N) (iota 0 9)) (iota 0 256).
Lemma F3bE : F3b. Proof. by vm_compute. Qed.

Lemma popn_le s v : (s < 256)%N -> (v <= 8)%N -> (popn (s %% 2 ^ v) <= v)%N.
Proof.
move=> hs hv; have /allP/(_ s) := F3bE; rewrite mem_iota add0n => /(_ hs)/allP/(_ v).
by rewrite mem_iota add0n ltnS => /(_ hv).
Qed.

(* NEVER LEAVE A BOUND ON nwB TO done: it unfolds 2 ^ 63 in unary.  Go        *)
(* through a power of two instead.                                            *)
Lemma lt_nwB k m : (m <= 63)%N -> (k < 2 ^ m)%N -> (k < nwB)%N.
Proof. by move=> hm hk; apply: (@ltn_nwB m). Qed.

(* one step, read as a nat                                                    *)
Lemma lbstepE ni v i st R S :
  (to_nat ni <= 8)%N -> (to_nat i < to_nat ni)%N -> (to_nat (v i) < 8)%N ->
  to_nat st = (R * 256 + S)%N -> (S < 256)%N -> (R < 2 ^ 24)%N ->
  to_nat (lbstep ni v i st) =
    ((R * (to_nat ni - to_nat i) + (to_nat (v i) - popn (S %% 2 ^ to_nat (v i)))) * 256
     + (S + 2 ^ to_nat (v i)))%N.
Proof.
move=> hn hi hx hst hS hR.
set X := to_nat (v i).
have h8 : (8 <? digits)%uint63 by [].
have hxd : (v i <? digits)%uint63 by apply/nltbP; apply: leq_trans hx _.
have hseen : to_nat (Uint63.land st 255) = S.
  rewrite m255 land_power2 // to_nat_mod to_nat_lsl_one //= hst.
  by rewrite modnMDl modn_small.
have hdiv : to_nat (Uint63.lsr st 8) = R.
  by rewrite to_nat_lsr hst divnMDl // divn_small // addn0.
have hbx : to_nat (Uint63.lsl 1 (v i)) = (2 ^ X)%N.
  by rewrite to_nat_lsl_one //; apply: leq_trans hx _.
have hmask : to_nat (Uint63.land (Uint63.land st 255) (decr (Uint63.lsl 1 (v i))))
             = (S %% 2 ^ X)%N.
  by rewrite land_power2 // to_nat_mod hseen to_nat_lsl_one //; apply: leq_trans hx _.
rewrite /lbstep.
set P := popn (S %% 2 ^ X).
have hX8 : (X <= 8)%N by apply: ltnW.
have hPX : (P <= X)%N by apply: popn_le.
have hmodS : (S %% 2 ^ X < 256)%N by apply: leq_ltn_trans (leq_mod _ _) hS.
have hpop : to_nat (PArray.get lbpop (Uint63.land (Uint63.land st 255)
                                        (decr (Uint63.lsl 1 (v i))))) = P.
  by rewrite -[Uint63.land _ _]to_natK hmask lbpopE.
have hc : to_nat (Uint63.sub (v i) (PArray.get lbpop (Uint63.land (Uint63.land st 255)
                                      (decr (Uint63.lsl 1 (v i)))))) = (X - P)%N.
  rewrite to_nat_sub; first by rewrite hpop.
    by rewrite hpop.
  exact: to_nat_bounded.
have hni : to_nat (Uint63.sub ni i) = (to_nat ni - to_nat i)%N.
  rewrite to_nat_sub //; first exact: ltnW.
  exact: to_nat_bounded.
have hNI : (to_nat ni - to_nat i <= 8)%N by apply: leq_trans (leq_subr _ _) hn.
have hRm : (R * (to_nat ni - to_nat i) < 2 ^ 27)%N.
  apply: leq_ltn_trans (leq_mul (leqnn R) hNI) _.
  have e8 : 8%N = (2 ^ 3)%N by [].
  have e27 : 27%N = (24 + 3)%N by [].
  by rewrite {1}e8 e27 expnD ltn_pmul2r ?expn_gt0.
set A := (R * (to_nat ni - to_nat i) + (X - P))%N.
have hXP : (X - P < 2 ^ 3)%N by apply: leq_ltn_trans (leq_subr _ _) hx.
have hA : (A < 2 ^ 28)%N.
  have e : (2 ^ 28 = 2 ^ 27 + 2 ^ 27)%N by rewrite expnS mul2n addnn.
  rewrite e; apply: leq_trans (_ : R * (to_nat ni - to_nat i) + 2 ^ 3 <= _)%N.
    by rewrite /A ltn_add2l.
  by apply: leq_add; [exact: ltnW | rewrite leq_exp2l].
have e256 : 256%N = (2 ^ 8)%N by [].
have hA8 : (A * 2 ^ 8 < 2 ^ 36)%N.
  have e : 36%N = (28 + 8)%N by [].
  by rewrite e expnD ltn_pmul2r ?expn_gt0.
have hSX : (S + 2 ^ X < 2 ^ 9)%N.
  have e : (2 ^ 9 = 2 ^ 8 + 2 ^ 8)%N by rewrite expnS mul2n addnn.
  rewrite e; apply: leq_trans (_ : S.+1 + 2 ^ X <= _)%N; first by rewrite addSn.
  by apply: leq_add; [rewrite -e256 | rewrite leq_exp2l].
have hmul : to_nat (Uint63.mul (Uint63.lsr st 8) (Uint63.sub ni i))
            = (R * (to_nat ni - to_nat i))%N.
  by rewrite to_nat_mul hdiv hni //; apply: (@lt_nwB _ 27).
have hadd : to_nat (Uint63.add (Uint63.mul (Uint63.lsr st 8) (Uint63.sub ni i))
               (Uint63.sub (v i) (PArray.get lbpop (Uint63.land (Uint63.land st 255)
                                                      (decr (Uint63.lsl 1 (v i))))))) = A.
  rewrite to_nat_add; first by rewrite hmul hc.
  rewrite hmul hc; apply: (@lt_nwB _ 28); [by [] | exact: hA].
have hlsl : to_nat (Uint63.lsl (Uint63.add (Uint63.mul (Uint63.lsr st 8) (Uint63.sub ni i))
               (Uint63.sub (v i) (PArray.get lbpop (Uint63.land (Uint63.land st 255)
                                                      (decr (Uint63.lsl 1 (v i))))))) 8)
            = (A * 256)%N.
  rewrite to_nat_lslW hadd e256 modn_small //.
  apply: (@lt_nwB _ 36); [by [] | exact: hA8].
have hsb : to_nat (Uint63.add (Uint63.land st 255) (Uint63.lsl 1 (v i))) = (S + 2 ^ X)%N.
  rewrite to_nat_add; first by rewrite hseen hbx.
  rewrite hseen hbx; apply: (@lt_nwB _ 9); [by [] | exact: hSX].
rewrite to_nat_add; first by rewrite hlsl hsb.
rewrite hlsl hsb; apply: (@lt_nwB _ 37); first by [].
rewrite e256; have e : (2 ^ 37 = 2 ^ 36 + 2 ^ 36)%N by rewrite expnS mul2n addnn.
rewrite e; apply: leq_trans (_ : (A * 2 ^ 8).+1 + (S + 2 ^ X) <= _)%N; first by rewrite addSn.
apply: leq_add; first exact: hA8.
by apply: leq_trans (ltnW hSX) _; rewrite leq_exp2l.
Qed.

(* the rank after i steps, on nat                                             *)
Definition prk (n : nat) (q : nat -> nat) (i : nat) : nat :=
  foldl (fun r k => r * (n - k) + (q k - popn (seenn q k %% 2 ^ q k)))%N 0%N (iota 0 i).

Lemma prkS n q i : prk n q i.+1 =
  (prk n q i * (n - i) + (q i - popn (seenn q i %% 2 ^ q i)))%N.
Proof.
have -> : i.+1 = (i + 1)%N by rewrite addn1.
by rewrite /prk iotaD foldl_cat.
Qed.

(* THE LOOP INVARIANT: after i steps the state is the rank so far above the  *)
(* mask of the values seen, and the rank is below 8 ^ i                       *)
Lemma lbfoldE n ni (v : int -> int) i :
  to_nat ni = n -> (n <= 8)%N ->
  {in iota 0 n &, injective (fun p => to_nat (v (of_nat p)))} ->
  (forall j, j < n -> to_nat (v (of_nat j)) < n)%N -> (i <= n)%N ->
  let q := fun p => to_nat (v (of_nat p)) in
  to_nat (foldl (fun b k => lbstep ni v (of_nat k) b) 0 (iota 0 i))
    = (prk n q i * 256 + seenn q i)%N /\ (prk n q i < 2 ^ (3 * i))%N.
Proof.
move=> hni hn hinj hlt; elim: i => [_ | i ih hi] q.
  by split.
have [hst hR] := ih (ltnW hi).
have [hS _] := seenn_bits hn hinj hlt (ltnW hi).
have hin : to_nat (of_nat i) = i.
  apply: of_natK; apply: (@lt_nwB _ 8) => //.
  by apply: leq_ltn_trans (ltnW (leq_trans hi hn)) _.
have hq : (q i < 8)%N by apply: leq_trans (hlt _ hi) hn.
have hR24 : (prk n q i < 2 ^ 24)%N.
  apply: leq_trans hR _; rewrite leq_exp2l // (_ : 24 = 3 * 8)%N // leq_mul2l /=.
  exact: leq_trans (ltnW hi) hn.
have e : iota 0 i.+1 = iota 0 i ++ [:: i] by rewrite -addn1 iotaD add0n.
rewrite e foldl_cat /=.
have hvi : (to_nat (v (of_nat i)) < 8)%N by exact: hq.
have h1 : (to_nat ni <= 8)%N by rewrite hni.
have h2 : (to_nat (of_nat i) < to_nat ni)%N by rewrite hin hni.
rewrite (lbstepE h1 h2 hvi hst hS hR24).
rewrite hni.
rewrite hin.
rewrite prkS.
rewrite seennS.
split.
  by [].
have hd : (q i - popn (seenn q i %% 2 ^ q i) < 8)%N.
  by apply: leq_ltn_trans (leq_subr _ _) hq.
have hni8 : (n - i <= 8)%N by apply: leq_trans (leq_subr _ _) hn.
rewrite mulnS expnD (_ : 2 ^ 3 = 8)%N //.
apply: leq_trans (_ : (prk n q i * 8).+1 + 7 <= _)%N.
  rewrite addSn ltnS; apply: leq_add; last by rewrite -ltnS.
  by apply: leq_mul.
rewrite addSnnS -mulSnr mulnC leq_mul2l /=.
exact: hR.
Qed.

(* THE RANK WITH A MASK IS THE LEHMER RANK, on any permutation of 0 .. n-1    *)
Lemma lbrankE n ni (v : int -> int) :
  to_nat ni = n -> (n <= 8)%N ->
  {in iota 0 n &, injective (fun p => to_nat (v (of_nat p)))} ->
  (forall j, j < n -> to_nat (v (of_nat j)) < n)%N ->
  to_nat (lbrank v n ni) = lrank n (fun p => to_nat (v (of_nat p))).
Proof.
move=> hni hn hinj hlt.
have hnw : (n < nwB)%N by apply: (@lt_nwB _ 8) => //; apply: leq_ltn_trans hn _.
rewrite /lbrank (@ifoldE _ n (lbstep ni v) (fun k b => lbstep ni v (of_nat k) b)) //;
  last by move=> k b _; rewrite to_natK.
have [hst _] := lbfoldE hni hn hinj hlt (leqnn n).
have [hS _] := seenn_bits hn hinj hlt (leqnn n).
rewrite to_nat_lsr hst (_ : 2 ^ to_nat 8 = 256)%N // divnMDl // divn_small // addn0.
exact: mrankE.
Qed.

(* ---- the cubies at the eight corner places are eight different cubies --- *)

(* PIGEONHOLE ON THE TABLE.  The three facelets of a place go to the three    *)
(* facelets of the cubie's place, turned.  Two places holding the same cubie  *)
(* would send two different facelets to the same one, and a table is uniq.    *)
Lemma ycg_inj (Y : seq nat) : yok Y -> tab_ok flast (cub2tab Y) ->
  {in iota 0 8 &, injective (ycg Y)}.
Proof.
move=> hy /and3P[/eqP hsz _ hu] p p'; rewrite !mem_iota !add0n /= => hp hp' he.
set t := ytw Y p; set t' := ytw Y p'.
have ht : (t < 3)%N by rewrite /t /ytw ltn_mod.
have ht' : (t' < 3)%N by rewrite /t' /ytw ltn_mod.
set s' := ((t + 3 - t') %% 3)%N.
have hs' : (s' < 3)%N by rewrite /s' ltn_mod.
have hi : (p * 3 < 24)%N by rewrite -[24%N]/(8 * 3)%N ltn_mul2r.
have hi' : (p' * 3 + s' < 24)%N.
  apply: leq_trans (_ : p'.+1 * 3 <= _)%N; first by rewrite mulSn addnC ltn_add2r.
  by rewrite -[24%N]/(8 * 3)%N leq_mul2r hp' orbT.
have /and4P[hf hcf /eqP hpf /eqP hsf] := clayE hi.
have /and4P[hf' hcf' /eqP hpf' /eqP hsf'] := clayE hi'.
rewrite mulnK // modnMl in hpf hsf.
rewrite divnMDl // divn_small // addn0 modnMDl modn_small // in hpf' hsf'.
have e : nth 0%N (cub2tab Y) (nth 0%N cflatp (p * 3))
       = nth 0%N (cub2tab Y) (nth 0%N cflatp (p' * 3 + s')).
  rewrite !cub2tab_nth // hcf hcf' hpf hsf hpf' hsf' -/t -/t' he add0n.
  congr (nth _ _ (_ + _)); apply/eqP; rewrite /s' modnDml subnK ?modnDr //.
  by apply: leq_trans (ltnW ht') (leq_addl _ _).
have hf48 : (nth 0%N cflatp (p * 3) < seq.size (cub2tab Y))%N by rewrite hsz.
have hf48' : (nth 0%N cflatp (p' * 3 + s') < seq.size (cub2tab Y))%N by rewrite hsz.
have := (nth_uniq 0%N hf48 hf48' hu); rewrite e eqxx => /esym/eqP ef.
by rewrite -hpf ef hpf'.
Qed.

(* the same for the twelve edge places                                       *)
Lemma yeg_inj (Y : seq nat) : yok Y -> tab_ok flast (cub2tab Y) ->
  {in iota 0 12 &, injective (yeg Y)}.
Proof.
move=> hy /and3P[/eqP hsz _ hu] p p'; rewrite !mem_iota !add0n /= => hp hp' he.
set t := yfl Y p; set t' := yfl Y p'.
have ht : (t < 2)%N by rewrite /t /yfl ltn_mod.
have ht' : (t' < 2)%N by rewrite /t' /yfl ltn_mod.
set s' := ((t + 2 - t') %% 2)%N.
have hs' : (s' < 2)%N by rewrite /s' ltn_mod.
have hi : (p * 2 < 24)%N by rewrite -[24%N]/(12 * 2)%N ltn_mul2r.
have hi' : (p' * 2 + s' < 24)%N.
  apply: leq_trans (_ : p'.+1 * 2 <= _)%N; first by rewrite mulSn addnC ltn_add2r.
  by rewrite -[24%N]/(12 * 2)%N leq_mul2r hp' orbT.
have /and4P[hf hef /eqP hpf /eqP hsf] := elayE hi.
have /and4P[hf' hef' /eqP hpf' /eqP hsf'] := elayE hi'.
rewrite mulnK // modnMl in hpf hsf.
rewrite divnMDl // divn_small // addn0 modnMDl modn_small // in hpf' hsf'.
have hcf : inC (nth 0%N elay (p * 2)) = false.
  by have /andP[_ /implyP h] := ckindE hf; apply/negbTE; apply: h.
have hcf' : inC (nth 0%N elay (p' * 2 + s')) = false.
  by have /andP[_ /implyP h] := ckindE hf'; apply/negbTE; apply: h.
have e : nth 0%N (cub2tab Y) (nth 0%N elay (p * 2))
       = nth 0%N (cub2tab Y) (nth 0%N elay (p' * 2 + s')).
  rewrite !cub2tab_nth // hcf hcf' hpf hsf hpf' hsf' -/t -/t' he add0n.
  congr (nth _ _ (_ + _)); apply/eqP; rewrite /s' modnDml subnK ?modnDr //.
  by apply: leq_trans (ltnW ht') (leq_addl _ _).
have hf48 : (nth 0%N elay (p * 2) < seq.size (cub2tab Y))%N by rewrite hsz.
have hf48' : (nth 0%N elay (p' * 2 + s') < seq.size (cub2tab Y))%N by rewrite hsz.
have := (nth_uniq 0%N hf48 hf48' hu); rewrite e eqxx => /esym/eqP ef.
by rewrite -hpf ef hpf'.
Qed.

(* ---- what the run's leaf reads at each place ---------------------------- *)

(* a table inverted twice is the table                                       *)
Lemma inv_tabK t : tab_ok flast t -> inv_tab flast (inv_tab flast t) = t.
Proof.
move=> ht; apply: tab_pt_inj => //; first by do 2 apply: tab_ok_inv.
by rewrite -(ptV (tab_ok_inv ht)) -(ptV ht) invgK.
Qed.

(* each primary edge facelet is at its own place, slot nought: computed      *)
Definition eprimPC : bool :=
  all (fun q => (eposn (nth 0%N eprim q) == q) && (eslt (nth 0%N eprim q) == 0%N))
      (iota 0 12).
Lemma eprimPCE : eprimPC. Proof. by vm_compute. Qed.

Lemma eprimP q : (q < 12)%N ->
  eposn (nth 0%N eprim q) = q /\ eslt (nth 0%N eprim q) = 0%N.
Proof.
move=> hq; have /allP/(_ q) := eprimPCE; rewrite mem_iota add0n /= => /(_ hq).
by case/andP => /eqP -> /eqP ->.
Qed.

(* at the primary facelet of corner place p the table holds a facelet of the  *)
(* place of the cubie there                                                  *)
Lemma cposn_prim (Y : seq nat) p : yok Y -> (p < 8)%N ->
  cposn (nth 0%N (cub2tab Y) (nth 0%N cprimp p)) = ycg Y p.
Proof.
move=> hy hp.
have -> : nth 0%N cprimp p = nth 0%N cflatp (p * 3).
  by rewrite /cprimp (nth_map 0%N) ?size_iota // nth_iota // add0n mulnC.
have hi : (p * 3 < 24)%N by rewrite -[24%N]/(8 * 3)%N ltn_mul2r.
have /and4P[hf hcf /eqP hpf /eqP hsf] := clayE hi.
rewrite mulnK // modnMl in hpf hsf.
rewrite cub2tab_nth // hcf hpf hsf add0n.
have /andP[/allP hyc _] := hy.
have hc8 : (ycg Y p < 8)%N by apply: hyc; rewrite mem_iota add0n.
have hj : (ycg Y p * 3 + ytw Y p %% 3 < 24)%N.
  apply: leq_trans (_ : (ycg Y p).+1 * 3 <= _)%N.
    by rewrite mulSn addnC ltn_add2r ltn_mod.
  by rewrite -[24%N]/(8 * 3)%N leq_mul2r hc8 orbT.
have /and4P[_ _ /eqP -> _] := clayE hj.
by rewrite divnMDl // divn_small ?addn0 // ltn_mod.
Qed.

(* and the same for the edge places                                          *)
Lemma eposn_prim (Y : seq nat) q : yok Y -> (q < 12)%N ->
  eposn (nth 0%N (cub2tab Y) (nth 0%N eprim q)) = yeg Y q.
Proof.
move=> hy hq.
have /andP[hf hef] := eprimE hq.
have [hpf hsf] := eprimP hq.
have hcf : inC (nth 0%N eprim q) = false.
  by have /andP[_ /implyP h] := ckindE hf; apply/negbTE; apply: h.
rewrite cub2tab_nth // hcf hpf hsf add0n.
have /andP[_ /allP hye] := hy.
have he12 : (yeg Y q < 12)%N by apply: hye; rewrite mem_iota add0n.
have hj : (yeg Y q * 2 + yfl Y q %% 2 < 24)%N.
  apply: leq_trans (_ : (yeg Y q).+1 * 2 <= _)%N.
    by rewrite mulSn addnC ltn_add2r ltn_mod.
  by rewrite -[24%N]/(12 * 2)%N leq_mul2r he12 orbT.
have /and4P[_ _ /eqP -> _] := elayE hj.
by rewrite divnMDl // divn_small ?addn0 // ltn_mod.
Qed.

(* THE RUN'S LEAF IS THE RANKS OF THE CUBIES AT THE PLACES: whatever the     *)
(* detour through forty eight facelets and the inverse, it reads at place p  *)
(* the cubie the twenty hold there                                           *)
Lemma oldleafE y : ypstok y ->
  tomembi (y2ti y) =
    (rank8 (ycg (a2y y)), rank8 (yeg (a2y y)),
     rank4 (fun q => (yeg (a2y y) (8 + q) - 8)%N)).
Proof.
move=> hy; have ha := ypstok_tabi hy.
have /andP[/andP[hyok htab] _] := hy.
rewrite (tomembiE ha) /tomemb (ti2t_inv Moves.n47_small Moves.n47_len ha) (ypstok_ti hy) /cub2tabR (inv_tabK htab).
congr (_, _, _); rewrite ?rank8E ?rank4E; congr (of_nat _); apply: lrank_eq => p hp.
- exact: cposn_prim.
- by rewrite eposn_prim //; apply: leq_trans hp _.
by rewrite eposn_prim // -[12%N]/(8 + 4)%N ltn_add2l.
Qed.

(* ---- the new leaf -------------------------------------------------------- *)

Local Open Scope uint63_scope.

(* a corner entry is 3 * cubie + twist, an edge entry 2 * cubie + flip, and   *)
(* a middle edge is 8 .. 11: three tables of twenty four make them 0 .. n-1   *)
Definition lbcq : arr := Eval vm_compute in
  ifold 24 0 (fun v a => PArray.set a v (of_nat (to_nat v %/ 3))) (PArray.make 24 0).
Definition lbeq : arr := Eval vm_compute in
  ifold 24 0 (fun v a => PArray.set a v (of_nat (to_nat v %/ 2))) (PArray.make 24 0).
Definition lbmq : arr := Eval vm_compute in
  ifold 24 0 (fun v a => PArray.set a v (of_nat (to_nat v %/ 2 - 8))) (PArray.make 24 0).

Definition lbtabC : bool :=
  all (fun v => [&& to_nat (PArray.get lbcq (of_nat v)) == (v %/ 3)%N,
                    to_nat (PArray.get lbeq (of_nat v)) == (v %/ 2)%N &
                    to_nat (PArray.get lbmq (of_nat v)) == (v %/ 2 - 8)%N])
      (iota 0 24).
Lemma lbtabCE : lbtabC. Proof. by vm_compute. Qed.

Lemma lbtabE v : (v < 24)%N ->
  [/\ to_nat (PArray.get lbcq (of_nat v)) = (v %/ 3)%N,
      to_nat (PArray.get lbeq (of_nat v)) = (v %/ 2)%N &
      to_nat (PArray.get lbmq (of_nat v)) = (v %/ 2 - 8)%N].
Proof.
move=> hv; have /allP/(_ v) := lbtabCE; rewrite mem_iota add0n => /(_ hv).
case/and3P => /eqP h1 /eqP h2 /eqP h3.
by split; [exact: h1 | exact: h2 | exact: h3].
Qed.

(* THE ONE FACT OF H THE LEAF NEEDS, TESTED: the eight outer edge places     *)
(* hold outer edges.  At a real leaf it always holds; if it did not the leaf  *)
(* would fall back on the old one, so nothing about H has to be proved.       *)
Definition lbguard (y : arr) : bool :=
  [&& PArray.get y 8 <? 16, PArray.get y 9 <? 16, PArray.get y 10 <? 16,
      PArray.get y 11 <? 16, PArray.get y 12 <? 16, PArray.get y 13 <? 16,
      PArray.get y 14 <? 16 & PArray.get y 15 <? 16].

Lemma lbguardP y q : lbguard y -> (q < 8)%N ->
  (to_nat (PArray.get y (of_nat (8 + q))) < 16)%N.
Proof.
move=> /andP[h0 /andP[h1 /andP[h2 /andP[h3 /andP[h4 /andP[h5 /andP[h6 h7]]]]]]].
case: q => [_|q]; first exact: (elimT (nltbP _ _) h0).
case: q => [_|q]; first exact: (elimT (nltbP _ _) h1).
case: q => [_|q]; first exact: (elimT (nltbP _ _) h2).
case: q => [_|q]; first exact: (elimT (nltbP _ _) h3).
case: q => [_|q]; first exact: (elimT (nltbP _ _) h4).
case: q => [_|q]; first exact: (elimT (nltbP _ _) h5).
case: q => [_|q]; first exact: (elimT (nltbP _ _) h6).
case: q => [_|q]; first exact: (elimT (nltbP _ _) h7).
by [].
Qed.

Definition bitleaf (y : arr) : Row.memb :=
  if lbguard y then
    (lbrank (fun p => PArray.get lbcq (PArray.get y p)) 8 8,
     lbrank (fun p => PArray.get lbeq (PArray.get y (8 + p))) 8 8,
     lbrank (fun p => PArray.get lbmq (PArray.get y (16 + p))) 4 4)
  else tomembi (y2ti y).

(* ---- and it is the run's leaf ------------------------------------------- *)

Lemma n8f : (8`! < nwB)%N.
Proof. apply: (@lt_nwB _ 16); first by []. by vm_compute. Qed.

Lemma n4f : (4`! < nwB)%N.
Proof. apply: (@lt_nwB _ 16); first by []. by vm_compute. Qed.

(* a mask rank of eight values that are a permutation, as the run ranks them *)
Lemma lbrank8 (v : int -> int) (f : nat -> nat) :
  (forall p, (p < 8)%N -> to_nat (v (of_nat p)) = f p) ->
  {in iota 0 8 &, injective f} -> (forall p, (p < 8)%N -> (f p < 8)%N) ->
  lbrank v 8 8 = rank8 f.
Proof.
move=> hvf hinj hlt; apply: to_nat_inj.
rewrite rank8E of_natK; last by apply: leq_ltn_trans (ltnW (lrank_lt 8 f)) n8f.
have hn : to_nat 8 = 8%N by [].
have hi : {in iota 0 8 &, injective (fun p => to_nat (v (of_nat p)))}.
  move=> x z hx hz /=.
  have hx' : (x < 8)%N by move: hx; rewrite mem_iota add0n.
  have hz' : (z < 8)%N by move: hz; rewrite mem_iota add0n.
  move=> e; apply: (hinj x z hx hz).
  by rewrite -(hvf _ hx') -(hvf _ hz').
have hr : forall j, (j < 8)%N -> (to_nat (v (of_nat j)) < 8)%N.
  by move=> j hj; rewrite (hvf _ hj); exact: hlt.
have hle : (8 <= 8)%N by [].
rewrite (lbrankE hn hle hi hr).
by apply: lrank_eq => p hp; exact: hvf.
Qed.

Lemma lbrank4 (v : int -> int) (f : nat -> nat) :
  (forall p, (p < 4)%N -> to_nat (v (of_nat p)) = f p) ->
  {in iota 0 4 &, injective f} -> (forall p, (p < 4)%N -> (f p < 4)%N) ->
  lbrank v 4 4 = rank4 f.
Proof.
move=> hvf hinj hlt; apply: to_nat_inj.
rewrite rank4E of_natK; last by apply: leq_ltn_trans (ltnW (lrank_lt 4 f)) n4f.
have hn : to_nat 4 = 4%N by [].
have hi : {in iota 0 4 &, injective (fun p => to_nat (v (of_nat p)))}.
  move=> x z hx hz /=.
  have hx' : (x < 4)%N by move: hx; rewrite mem_iota add0n.
  have hz' : (z < 4)%N by move: hz; rewrite mem_iota add0n.
  move=> e; apply: (hinj x z hx hz).
  by rewrite -(hvf _ hx') -(hvf _ hz').
have hr : forall j, (j < 4)%N -> (to_nat (v (of_nat j)) < 4)%N.
  by move=> j hj; rewrite (hvf _ hj); exact: hlt.
have hle : (4 <= 8)%N by [].
rewrite (lbrankE hn hle hi hr).
by apply: lrank_eq => p hp; exact: hvf.
Qed.

(* an index shifted by a constant, as the leaf writes it                     *)
Lemma plus_ofn (k : int) p : (to_nat k + p < nwB)%N ->
  k + of_nat p = of_nat (to_nat k + p).
Proof.
move=> hb; apply: to_nat_inj.
have hp : (p < nwB)%N by apply: leq_ltn_trans hb; apply: leq_addl.
by rewrite to_nat_add (of_natK _ hp) ?(of_natK _ hb).
Qed.

(* THE EIGHT OUTER PLACES TAKE THE EIGHT OUTER EDGES, so the four middle      *)
(* places are left the middle ones: pigeonhole again                         *)
Lemma middle_ge8 (Y : seq nat) p : yok Y -> tab_ok flast (cub2tab Y) ->
  (forall q, (q < 8)%N -> (yeg Y q < 8)%N) -> (p < 4)%N -> (8 <= yeg Y (8 + p))%N.
Proof.
move=> hy ht hout hp; rewrite leqNgt; apply/negP => hlt.
have hinj := yeg_inj hy ht.
have hinj8 : {in iota 0 8 &, injective (yeg Y)}.
  move=> x z; rewrite !mem_iota !add0n => hx hz; apply: hinj;
  by rewrite mem_iota add0n; apply: ltn_trans (_ : 8 < 12)%N.
have hu : uniq (map (yeg Y) (iota 0 8)) by rewrite map_inj_in_uniq ?iota_uniq.
have hs : {subset map (yeg Y) (iota 0 8) <= iota 0 8}.
  by move=> x /mapP[j]; rewrite !mem_iota /= !add0n => hj ->; exact: hout.
have hsz : (seq.size (iota 0 8) <= seq.size (map (yeg Y) (iota 0 8)))%N.
  by rewrite size_map.
have [_ heq] := uniq_min_size hu hs hsz.
have : yeg Y (8 + p) \in map (yeg Y) (iota 0 8) by rewrite heq mem_iota add0n.
case/mapP => k; rewrite mem_iota add0n => /andP[_ hk] hke.
have h12 : (8 + p < 12)%N by rewrite -[12%N]/(8 + 4)%N ltn_add2l.
have hk12 : (k < 12)%N by apply: ltn_trans hk _.
have := hinj (8 + p)%N k; rewrite !mem_iota !add0n => /(_ h12 hk12 hke) e.
by move: hk; rewrite -e ltnNge leq_addr.
Qed.

(* ---- THE THEOREM --------------------------------------------------------- *)

(* On every position the run can carry, the new leaf is the run's leaf.      *)
Theorem bitleafE y : ypstok y -> bitleaf y = tomembi (y2ti y).
Proof.
move=> hy; rewrite /bitleaf; case hg : (lbguard y) => //.
rewrite (oldleafE hy).
have /andP[/andP[hyok htab] _] := hy.
set Y := a2y y.
have /allP hyi := yok_yoki hyok.
have hent q : (q < 20)%N -> (to_nat (PArray.get y (of_nat q)) < 24)%N.
  by move=> hq; apply: hyi; rewrite mem_iota add0n.
have hnth q : (q < 20)%N -> nth 0%N Y q = to_nat (PArray.get y (of_nat q)).
  exact: a2y_nth.
have /andP[/allP hyc /allP hye] := hyok.
have hc8 p : (p < 8)%N -> (ycg Y p < 8)%N.
  by move=> hp; apply: hyc; rewrite mem_iota add0n.
have he12 q : (q < 12)%N -> (yeg Y q < 12)%N.
  by move=> hq; apply: hye; rewrite mem_iota add0n.
(* the corners *)
have hC : lbrank (fun p => PArray.get lbcq (PArray.get y p)) 8 8 = rank8 (ycg Y).
  apply: lbrank8; last by [].
    move=> p hp; have hp20 : (p < 20)%N by apply: ltn_trans hp _.
    have hv := hent _ hp20.
    case: (lbtabE hv) => h1 _ _.
    rewrite /ycg (hnth _ hp20) -h1.
    by rewrite to_natK.
  exact: ycg_inj.
(* the outer edges *)
have hE p : (p < 8)%N ->
    to_nat (PArray.get y (8 + of_nat p)) = nth 0%N Y (8 + p).
  move=> hp; have hp20 : (8 + p < 20)%N by rewrite -[20%N]/(8 + 12)%N ltn_add2l;
    apply: ltn_trans hp _.
  rewrite (hnth _ hp20) plus_ofn //.
  by apply: (@lt_nwB _ 5) => //; apply: ltn_trans hp20 _.
have hout q : (q < 8)%N -> (yeg Y q < 8)%N.
  move=> hq; rewrite /yeg (hnth _ _); last by rewrite -[20%N]/(8 + 12)%N ltn_add2l;
    apply: ltn_trans hq _.
  by rewrite ltn_divLR // (lbguardP hg hq).
have hO : lbrank (fun p => PArray.get lbeq (PArray.get y (8 + p))) 8 8 = rank8 (yeg Y).
  apply: lbrank8 => //.
    move=> p hp; have hp20 : (8 + p < 20)%N by rewrite -[20%N]/(8 + 12)%N ltn_add2l;
      apply: ltn_trans hp _.
    rewrite -[PArray.get y (8 + of_nat p)]to_natK hE //.
    have hv : (nth 0%N Y (8 + p) < 24)%N by rewrite (hnth _ hp20); apply: hent.
    case: (lbtabE hv) => _ h2 _.
    by rewrite h2.
  move=> x z; rewrite !mem_iota !add0n => hx hz; apply: (yeg_inj hyok htab);
  by rewrite mem_iota add0n; apply: ltn_trans (_ : 8 < 12)%N.
(* the middle edges *)
have hge p : (p < 4)%N -> (8 <= yeg Y (8 + p))%N.
  by move=> hp; apply: middle_ge8.
have hM : lbrank (fun p => PArray.get lbmq (PArray.get y (16 + p))) 4 4
          = rank4 (fun q => (yeg Y (8 + q) - 8)%N).
  apply: lbrank4.
  - move=> p hp; have hp20 : (16 + p < 20)%N by rewrite -[20%N]/(16 + 4)%N ltn_add2l.
    have e : of_nat (16 + p) = 16 + of_nat p.
      by rewrite plus_ofn //; apply: (@lt_nwB _ 5) => //; apply: ltn_trans hp20 _.
    rewrite -e -[PArray.get y (of_nat (16 + p))]to_natK.
    have [_ _ ->] := lbtabE (hent _ hp20).
    by rewrite /yeg -(hnth _ hp20) addnA.
  - move=> x z; rewrite !mem_iota !add0n => hx hz he.
    have h1 := hge _ hx; have h2 := hge _ hz.
    have : (8 + x)%N = (8 + z)%N.
      apply: (yeg_inj hyok htab); rewrite ?mem_iota ?add0n.
      + by rewrite -[12%N]/(8 + 4)%N ltn_add2l.
      + by rewrite -[12%N]/(8 + 4)%N ltn_add2l.
      move: he => /= he.
      by rewrite -(subnK h1) -(subnK h2) he.
    by move/eqP; rewrite eqn_add2l => /eqP.
  move=> p hp; rewrite ltn_subLR ?hge //.
  by apply: he12; rewrite -[12%N]/(8 + 4)%N ltn_add2l.
by rewrite hC hO hM.
Qed.
