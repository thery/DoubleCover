(* =========================================================================  *)
(*  Row48.v -- the same row, with two corner permutations to a cell.          *)
(* =========================================================================  *)

(* Row.v gives a cell one corner permutation and its twenty four middle bits, *)
(* so twenty four bits of a sixty four bit word carry anything and the        *)
(* unfolded map is 6.5 GB.  Here the corners are paired as the outer edges    *)
(* already are -- the two that differ by exchanging the cubies 0 and 1 -- so  *)
(* a cell is TWO corner permutations and carries forty eight bits: the low    *)
(* twenty four for the even one of the pair, the high twenty four for the     *)
(* odd one.  Half as many words, 3.25 GB, and one write where there were two. *)
(*                                                                            *)
(* NOTHING NEW IS ASSUMED.  A member is Row's member, what makes a member is  *)
(* Row's membok, and what makes the tables right is Row's e8ok and e4ok --    *)
(* e8ok at the corners as well as at the outer edges, since both are          *)
(* permutations of eight cubies under the same numbering.  So RowTab's e8okC  *)
(* and e4okC carry over as they stand and no walk is checked twice.           *)
(*                                                                            *)
(* THIS IS NOT A SECOND USE OF PARITY.  A row has one parity equation and it  *)
(* is already spent on the outer pair.  Here the cell is coarser, that is     *)
(* all: the corner parity says which of the two corner permutations a bit     *)
(* means, and the outer parity is then what the member's own equation forces. *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

(* ---- the shape of a row, with the corners paired -------------------------- *)

Definition nclsi   : int := 20160%uint63.   (* corner pairs                   *)
Definition nbit48i : int := 48%uint63.      (* parity, then middle perm       *)

(* the row is still named once over: 20160 * 20160 * 48                       *)
Lemma rowsize48E : rowsize = Uint63.mul (Uint63.mul nclsi ngroupi) nbit48i.
Proof. by vm_compute. Qed.

(* a corner pair is counted as a group is, so the range facts are Row's       *)
Lemma nclsiE : nclsi = ngroupi.
Proof. by vm_compute. Qed.

Definition nclsn   : nat := to_nat nclsi.
Definition nbit48n : nat := to_nat nbit48i.

Lemma nclsnE : nclsn = ngroupn.
Proof. by rewrite /nclsn nclsiE. Qed.

Lemma nbitiE : to_nat nbiti = 24%N.
Proof. by vm_compute. Qed.

Lemma nbit48iE : to_nat nbit48i = 48%N.
Proof. by vm_compute. Qed.

(* ---- a number made of a quotient and a remainder -------------------------- *)

(* Row.v does this at two, where a page is two groups.  Here it is needed at  *)
(* twenty four as well, where a cell is two halves, so it is done once for    *)
(* any divisor and used at both.                                              *)

Lemma to_nat_mulD a k b :
  (to_nat a * to_nat k + to_nat b < nwB)%N ->
  to_nat (Uint63.add (Uint63.mul a k) b) = (to_nat a * to_nat k + to_nat b)%N.
Proof.
(* NO SIDE GOAL MAY BE LEFT TO //: what done would evaluate is nwB, which is  *)
(* 2 ^ 63 in unary and does not come back.                                    *)
move=> hb.
have hlt : (to_nat a * to_nat k < nwB)%N.
  by apply: leq_ltn_trans hb; apply: leq_addr.
have hm : to_nat (Uint63.mul a k) = (to_nat a * to_nat k)%N.
  by rewrite (@to_nat_mul _ _ hlt).
have h2 : (to_nat (Uint63.mul a k) + to_nat b < nwB)%N by rewrite hm.
by rewrite (@to_nat_add _ _ h2) hm.
Qed.

Lemma div_mulD a k b :
  (to_nat b < to_nat k)%N -> (to_nat a * to_nat k + to_nat b < nwB)%N ->
  Uint63.div (Uint63.add (Uint63.mul a k) b) k = a.
Proof.
move=> hbk hb; apply: to_nat_inj.
have hk : (0 < to_nat k)%N by apply: leq_ltn_trans hbk.
by rewrite to_nat_div (to_nat_mulD hb) divnMDl // divn_small // addn0.
Qed.

Lemma mod_mulD a k b :
  (to_nat b < to_nat k)%N -> (to_nat a * to_nat k + to_nat b < nwB)%N ->
  Uint63.mod (Uint63.add (Uint63.mul a k) b) k = b.
Proof.
move=> hbk hb; apply: to_nat_inj.
by rewrite to_nat_mod (to_nat_mulD hb) modnMDl modn_small.
Qed.

(* ---- a page number is a pair and a parity -------------------------------- *)

(* The page of RowMap.v is a corner rank; under e8num it is a number n, and   *)
(* n = n / 2 * 2 + odd n.  So a pair and a parity make a page number and take *)
(* it apart again, which is the whole of what the extra bit does.             *)
Lemma pair_page g q : (g <? ngroupi)%uint63 -> (to_nat q < 2)%N ->
  [/\ (Uint63.add (Uint63.mul g 2%uint63) q <? npagei)%uint63,
      Uint63.div (Uint63.add (Uint63.mul g 2%uint63) q) 2%uint63 = g &
      Uint63.mod (Uint63.add (Uint63.mul g 2%uint63) q) 2%uint63 = q].
Proof.
move=> hg hq.
have hgn : (to_nat g < ngroupn)%N by apply: ltn_ngroupi.
have hbd : (to_nat g * to_nat 2%uint63 + to_nat q < nwB)%N.
  rewrite to_nat_two; apply: (@leq_ltn_trans (ngroupn * 2 + 2)).
    by apply: leq_add; [rewrite leq_pmul2r //; apply: ltnW | apply: ltnW].
  by rewrite ngroupnE; apply: (@ltn_nwB 16).
have hq2 : (to_nat q < to_nat 2%uint63)%N by rewrite to_nat_two.
split; last by apply: mod_mulD.
  apply/nltbP; rewrite (to_nat_mulD hbd) to_nat_two -/npagen npage_group.
  apply: (@leq_trans (to_nat g * 2 + 2)); first by rewrite ltn_add2l.
  by rewrite -{2}[2%N]mul1n -mulnDl leq_mul2r addn1 hgn.
by apply: div_mulD.
Qed.

Section Row48.

(* the four tables of Row.v, unchanged, and read at the corners as well       *)
Variable e8num e8inv : arr.
Variable e4bit e4of : arr.
Variable par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

(* ---- where a member stands ----------------------------------------------- *)

(* The page is the corner PAIR, the group is the outer pair as before, and    *)
(* the bit is the corner parity over the middle permutation: bits 0 to 23 for *)
(* the even corner permutation of the pair, 24 to 47 for the odd one.  The    *)
(* halves are whole so that a move exchanges them and nothing else.           *)
Definition place48 (x : memb) : int * int * int :=
  (Uint63.div (PArray.get e8num (mcp x)) 2%uint63,
   Uint63.div (PArray.get e8num (mud x)) 2%uint63,
   Uint63.add (Uint63.mul (PArray.get par8 (mcp x)) nbiti)
              (PArray.get e4bit (mmp x))).

(* and back.  The bit names the corner parity and the middle permutation; the *)
(* corner is then the one of the pair with that parity, and the outer one is  *)
(* the one the member's parity equation asks for.                             *)
Definition unplace48 (pg gr bt : int) : memb :=
  let s := Uint63.div bt nbiti in
  let mp := PArray.get e4of (Uint63.mod bt nbiti) in
  let p := Uint63.lxor s (PArray.get par4 mp) in
  (PArray.get e8inv (Uint63.add (Uint63.mul pg 2%uint63) s),
   PArray.get e8inv (Uint63.add (Uint63.mul gr 2%uint63) p),
   mp).

Definition inrange48 (pg gr bt : int) : bool :=
  [&& (pg <? nclsi)%uint63, (gr <? ngroupi)%uint63 & (bt <? nbit48i)%uint63].

(* ---- the three facts the layout has to have ------------------------------ *)

(* a number below forty eight is a parity and a bit, and nothing wraps        *)
Lemma bit48_bound s b :
  (to_nat s < 2)%N -> (to_nat b < to_nat nbiti)%N ->
  (to_nat s * to_nat nbiti + to_nat b < nwB)%N.
Proof.
rewrite nbitiE => hs hb.
have h1 : (to_nat s * 24 <= 1 * 24)%N by rewrite leq_mul2r; apply/orP; right.
have h2 : (to_nat b <= 23)%N by rewrite -ltnS.
apply: (@leq_ltn_trans 47); last by apply: (@ltn_nwB 6).
by apply: leq_trans (leq_add h1 h2) _.
Qed.

Lemma bit48_lt s b :
  (to_nat s < 2)%N -> (to_nat b < to_nat nbiti)%N ->
  (Uint63.add (Uint63.mul s nbiti) b <? nbit48i)%uint63.
Proof.
move=> hs hb; apply/nltbP.
rewrite (to_nat_mulD (bit48_bound hs hb)) nbit48iE nbitiE.
have h1 : (to_nat s * 24 <= 1 * 24)%N by rewrite leq_mul2r; apply/orP; right.
have h2 : (to_nat b <= 23)%N by rewrite -ltnS -nbitiE.
by apply: leq_ltn_trans (leq_add h1 h2) _.
Qed.

(* a place is in range                                                        *)
Lemma place48_range x pg gr bt :
  membok par8 par4 x -> place48 x = (pg, gr, bt) -> inrange48 pg gr bt.
Proof.
case/and4P => hc hu hm _ [<- <- <-].
case/and5P: (e8at he8 hc) => hnc _ _ _ _.
case/and5P: (e8at he8 hu) => hnu _ _ _ _.
case/and5P: (e4at he4 hm) => hb _ _ _ _.
apply/and3P; split; last by apply: bit48_lt (par8_lt2 he8 hc) (nltbP _ _ hb).
  rewrite nclsiE; apply/nltbP.
  rewrite to_nat_div to_nat_two -/ngroupn ltn_divLR // -npage_group.
  by apply: ltn_npagei.
apply/nltbP.
rewrite to_nat_div to_nat_two -/ngroupn ltn_divLR // -npage_group.
by apply: ltn_npagei.
Qed.

(* reading a place back gives the member that was put there                   *)
Lemma unplace48_place48 x pg gr bt :
  membok par8 par4 x -> place48 x = (pg, gr, bt) -> unplace48 pg gr bt = x.
Proof.
case: x => [[c u] m] /and4P[hc hu hm /eqP hp] [<- <- <-].
case/and5P: (e8at he8 hc) => _ /eqP hmodc /eqP hinvc _ _.
case/and5P: (e8at he8 hu) => _ /eqP hmodu /eqP hinvu _ _.
case/and5P: (e4at he4 hm) => hbi /eqP hofb _ _ _.
have hs2 : (to_nat (PArray.get par8 c) < 2)%N by apply: (par8_lt2 he8).
have hb24 : (to_nat (PArray.get e4bit m) < to_nat nbiti)%N by apply/nltbP.
have h4 : (to_nat (PArray.get par4 m) < 2)%N by apply: (par4_lt2 he4).
have hbd := bit48_bound hs2 hb24.
rewrite /unplace48 (div_mulD hb24 hbd) (mod_mulD hb24 hbd) hofb.
have -> : Uint63.lxor (PArray.get par8 c) (PArray.get par4 m)
        = PArray.get par8 u.
  by rewrite hp (lxorK2 (par8_lt2 he8 hu) h4).
by rewrite -hmodc -hmodu -!int_add_mod hinvc hinvu.
Qed.

(* and every place in range comes from a member                               *)
Lemma place48_unplace48 pg gr bt :
  inrange48 pg gr bt ->
  membok par8 par4 (unplace48 pg gr bt) /\
  place48 (unplace48 pg gr bt) = (pg, gr, bt).
Proof.
case/and3P => hpg hgr hbt.
rewrite /unplace48 /membok /place48 /=.
set s := Uint63.div bt nbiti.
set b := Uint63.mod bt nbiti.
set mp := PArray.get e4of b.
set p := Uint63.lxor s (PArray.get par4 mp).
(* the parity and the bit the place names                                     *)
have h24 : (0 < to_nat nbiti)%N by rewrite nbitiE.
have hs2 : (to_nat s < 2)%N.
  rewrite /s to_nat_div nbitiE ltn_divLR //.
  by apply: leq_trans (nltbP _ _ hbt) _; rewrite nbit48iE.
have hb24 : (to_nat b < to_nat nbiti)%N by rewrite /b to_nat_mod ltn_mod.
have hbi : (b <? nbiti)%uint63 by apply/nltbP.
case/and5P: (e4at he4 hbi) => _ _ hmp /eqP hbit _.
have h4 : (to_nat (PArray.get par4 mp) < 2)%N by apply: (par4_lt2 he4).
have hp2 : (to_nat p < 2)%N by exact: lxor_lt2 hs2 h4.
(* a page number made of a pair and a parity                                  *)
rewrite nclsiE in hpg.
have [hcr hcd hcm] := pair_page hpg hs2.
have [hur hud hum] := pair_page hgr hp2.
case/and5P: (e8at he8 hcr) => _ _ _ hcv /eqP hcn.
case/and5P: (e8at he8 hur) => _ _ _ huv /eqP hun.
(* the two permutations the numbers name, and their parities                  *)
have hparc : PArray.get par8 (PArray.get e8inv
                (Uint63.add (Uint63.mul pg 2%uint63) s)) = s.
  by case/and5P: (e8at he8 hcv) => _ /eqP <- _ _ _; rewrite hcn hcm.
have hparu : PArray.get par8 (PArray.get e8inv
                (Uint63.add (Uint63.mul gr 2%uint63) p)) = p.
  by case/and5P: (e8at he8 huv) => _ /eqP <- _ _ _; rewrite hun hum.
split.
  apply/and4P; split => //; apply/eqP.
  by rewrite hparc hparu /p (lxorK2 hs2 h4).
rewrite hcn hun hcd hud hparc hbit.
by congr (_, _, _); rewrite -int_add_mod.
Qed.

(* so the map has exactly one bit for each member                             *)
Lemma place48_inj x y :
  membok par8 par4 x -> membok par8 par4 y -> place48 x = place48 y -> x = y.
Proof.
move=> hx hy hE.
case E: (place48 y) => [[pg gr] bt].
have Hx := unplace48_place48 hx (etrans hE E).
have Hy := unplace48_place48 hy E.
by rewrite -Hx -Hy.
Qed.

End Row48.
