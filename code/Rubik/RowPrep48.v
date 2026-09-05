(* =========================================================================  *)
(*  RowPrep48.v -- the forty eight bit instance, from the twenty four bit one.*)
(* =========================================================================  *)

(* NOTHING ABOUT THE CUBE IS PROVED TWICE.  A place at forty eight bits and a *)
(* place at twenty four name the SAME member: the page number of RowMap.v is  *)
(* the corner rank, its number under e8num is n, and n = n / 2 * 2 + odd n -- *)
(* so the pair is n / 2 and the parity is odd n, which is where the extra bit *)
(* went.  Read that way,                                                      *)
(*                                                                            *)
(*     unplace48 pg gr bt  =  unplace (e8inv (2 * pg + bt / 24)) gr (bt % 24) *)
(*                                                                            *)
(* and every fact the run asks of the forty eight bit prepass follows from    *)
(* the twenty four bit one it already has.  Two things are new and only two:  *)
(* ONE CHECK, that the class table and the flip really are the page table     *)
(* split that way, and the bit lemma for a cell of two halves.                *)
(*                                                                            *)
(* Both the prepass bridge and the bit lemma are taken as hypotheses of the   *)
(* twenty four bit shape, so this file needs no table and no phase one.       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap Row48 RowMap48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- a bit of a word, and the two halves of a cell ----------------------- *)

Lemma test_bit x b : (b <? digits)%uint63 ->
  ~~ (Uint63.land x (bitof b) =? 0)%uint63 = bit x b.
Proof.
move=> hbd; have hb1 : (1 = one)%uint63 by vm_compute.
apply/idP/idP; last first.
  move=> hx; apply/negP => /neqbP h0.
  have hz : Uint63.land x (bitof b) = 0%uint63 by apply: to_nat_inj.
  have : bit (Uint63.land x (bitof b)) b.
    by rewrite land_spec hx /bitof hb1 bit_onenn // eqxx.
  by rewrite hz bit_0.
apply: contraR => hnb; apply/neqbP.
suff -> : Uint63.land x (bitof b) = 0%uint63 by [].
apply: bit_ext => i; rewrite land_spec bit_0.
have [hid|hid] := boolP (i <? digits)%uint63; last first.
  rewrite bit_M ?andbF //.
  by apply/nlebP; rewrite leqNgt; apply/negP => /nltbP h; case/negP: hid.
rewrite /bitof hb1 bit_onenn //.
by case: eqP => [<-|_]; rewrite ?andbF // (negbTE hnb).
Qed.

Lemma lt_nbiti_digits j : (j <? nbiti)%uint63 -> (j <? digits)%uint63.
Proof.
move=> h; apply/nltbP; apply: leq_trans (_ : to_nat nbiti <= _).
  by apply/nltbP.
by apply/nlebP; vm_compute.
Qed.

Lemma lt_nbit48i_digits j : (j <? nbit48i)%uint63 -> (j <? digits)%uint63.
Proof. exact: lt_digits48. Qed.

Lemma lt_nbiti_nbit48i j : (j <? nbiti)%uint63 -> (j <? nbit48i)%uint63.
Proof.
move=> h; apply/nltbP; apply: leq_trans (_ : to_nat nbiti <= _).
  by apply/nltbP.
by apply/nlebP; vm_compute.
Qed.

(* the low half of a cell is the cell at the places below twenty four         *)
Lemma bit_lo24 v i : (i <? nbiti)%uint63 ->
  bit (Uint63.land v allbits) i = bit v i.
Proof.
move=> hi; rewrite land_spec.
have -> : allbits = decr (Uint63.lsl one nbiti) by vm_compute.
by rewrite bit_decr ?hi ?andbT //; vm_compute.
Qed.

(* and the high half is the cell twenty four places up, masked back           *)
Lemma bit_hi24 v s : (nbiti <=? s)%uint63 -> (s <? nbit48i)%uint63 ->
  bit (Uint63.land (Uint63.lsr v nbiti) allbits) (Uint63.sub s nbiti) = bit v s.
Proof.
move=> hs hs2; have hle : (to_nat nbiti <= to_nat s)%N by apply/nlebP.
rewrite bit_lo24; last first.
  apply/nltbP; rewrite to_nat_sub ?to_nat_bounded //.
  rewrite -(ltn_add2r (to_nat nbiti)) subnK //.
  have -> : (to_nat nbiti + to_nat nbiti = to_nat nbit48i)%N by vm_compute.
  by apply/nltbP.
rewrite bit_lsr.
have he : Uint63.add nbiti (Uint63.sub s nbiti) = s by rewrite laddC subK.
rewrite he ifT //; apply/nlebP.
by rewrite to_nat_sub ?leq_subr ?to_nat_bounded.
Qed.

Section Bits48.

Variable msw mlo mhi cfl : arr.
Variable btmv : int -> int -> int.

(* what the twenty four bit rearrangement already gives                       *)
Hypothesis grpmvP : forall k v bt', (to_nat k < nhn)%N ->
  (bt' <? nbiti)%uint63 ->
  ~~ (Uint63.land (grpmv msw mlo mhi k v) (bitof bt') =? 0)%uint63 ->
  exists2 bt, (bt <? nbiti)%uint63 &
    btmv k bt = bt' /\ ~~ (Uint63.land v (bitof bt) =? 0)%uint63.

Hypothesis hcfl : forall k, (to_nat k < nhn)%N ->
  (to_nat (PArray.get cfl k) < 2)%N.

(* where a bit of a cell goes: its half is exchanged when the move is odd on  *)
(* the corners, and inside the half it moves as it always did                 *)
Definition btmv48 (k bt : int) : int :=
  Uint63.add
    (Uint63.mul (Uint63.lxor (Uint63.div bt nbiti) (PArray.get cfl k)) nbiti)
    (btmv k (Uint63.mod bt nbiti)).

(* one half of a cell, as a word of its own                                   *)
Definition halfw (v h : int) : int :=
  if Uint63.eqb h 0%uint63 then Uint63.land v allbits
  else Uint63.land (Uint63.lsr v nbiti) allbits.

Lemma halfw0 v : halfw v 0%uint63 = Uint63.land v allbits.
Proof. by rewrite /halfw eqb_refl. Qed.

Lemma halfw1 v :
  halfw v 1%uint63 = Uint63.land (Uint63.lsr v nbiti) allbits.
Proof. by rewrite /halfw; have -> : (1 =? 0)%uint63 = false by vm_compute. Qed.

Lemma mul0_nbiti : Uint63.mul 0%uint63 nbiti = 0%uint63.
Proof. by vm_compute. Qed.

Lemma mul1_nbiti : Uint63.mul 1%uint63 nbiti = nbiti.
Proof. by vm_compute. Qed.

(* twenty four places up, as a number                                        *)
Lemma to_nat_add_nbiti bt : (bt <? nbiti)%uint63 ->
  to_nat (Uint63.add nbiti bt) = (24 + to_nat bt)%N.
Proof.
move=> hb; have hbn : (to_nat bt < 24)%N by rewrite -nbitiE; apply/nltbP.
have hs : (to_nat nbiti + to_nat bt < nwB)%N.
  rewrite nbitiE; apply: (@leq_ltn_trans 47); last by apply: (@ltn_nwB 6).
  by rewrite -[47%N]/(24 + 23)%N leq_add2l -ltnS.
by rewrite (@to_nat_add _ _ hs) nbitiE.
Qed.

Lemma bit_half v h bt : (to_nat h < 2)%N -> (bt <? nbiti)%uint63 ->
  bit (halfw v h) bt = bit v (Uint63.add (Uint63.mul h nbiti) bt).
Proof.
move=> hh hb; have hbn : (to_nat bt < 24)%N by rewrite -nbitiE; apply/nltbP.
case: (int_lt2 hh) => ->.
  by rewrite halfw0 mul0_nbiti ladd0n bit_lo24.
rewrite halfw1 mul1_nbiti.
have hle : (nbiti <=? Uint63.add nbiti bt)%uint63.
  by apply/nlebP; rewrite (to_nat_add_nbiti hb) nbitiE leq_addr.
have hlt : (Uint63.add nbiti bt <? nbit48i)%uint63.
  apply/nltbP; rewrite (to_nat_add_nbiti hb) nbit48iE.
  by rewrite -[48%N]/(24 + 24)%N ltn_add2l.
rewrite -(bit_hi24 v hle hlt); congr bit.
apply: to_nat_inj; rewrite to_nat_sub ?to_nat_bounded //.
  by rewrite (to_nat_add_nbiti hb) nbitiE addKn.
by apply/nlebP.
Qed.

(* A BIT OF A MOVED CELL CAME FROM A BIT OF THE CELL.  It is grpmvP one level *)
(* up: the half it is in says which of the two twenty four bit words moved    *)
(* it, and the caller says where that half lands.                             *)
Lemma from_half k v h j bt' : (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  (j <? nbiti)%uint63 ->
  Uint63.add (Uint63.mul (Uint63.lxor h (PArray.get cfl k)) nbiti) j = bt' ->
  ~~ (Uint63.land (grpmv msw mlo mhi k (halfw v h)) (bitof j) =? 0)%uint63 ->
  exists2 bt, (bt <? nbit48i)%uint63 &
    btmv48 k bt = bt' /\ ~~ (Uint63.land v (bitof bt) =? 0)%uint63.
Proof.
move=> hk hh hj hE hset.
have [bt0 hbt0 [hmv hin]] := grpmvP hk hj hset.
have hb0n : (to_nat bt0 < to_nat nbiti)%N by apply/nltbP.
have hbd := bit48_bound hh hb0n.
exists (Uint63.add (Uint63.mul h nbiti) bt0); first by apply: bit48_lt.
split.
  rewrite /btmv48 (div_mulD hb0n hbd) (mod_mulD hb0n hbd) hmv.
  by rewrite -hE.
rewrite test_bit; last first.
  by apply: lt_nbit48i_digits; apply: bit48_lt.
rewrite -bit_half // -test_bit //.
by apply: lt_nbiti_digits.
Qed.

(* a masked half has no bit outside its twenty four places                    *)
Lemma bit_mask24 x j :
  bit (Uint63.land x allbits) j = bit x j && (j <? nbiti)%uint63.
Proof.
rewrite land_spec; congr (_ && _).
have -> : allbits = decr (Uint63.lsl one nbiti) by vm_compute.
by rewrite bit_decr //; vm_compute.
Qed.

(* A CELL IS ITS TWO HALVES AND NOTHING ELSE, once both are masked: a bit of  *)
(* the word is a bit of the low half below twenty four, or a bit of the high  *)
(* half twenty four places up.                                                *)
Lemma split_lor48 a b bt' : (bt' <? nbit48i)%uint63 ->
  bit (Uint63.lor (Uint63.land a allbits)
                  (Uint63.lsl (Uint63.land b allbits) nbiti)) bt' ->
  (bit a bt' /\ (bt' <? nbiti)%uint63) \/
  (bit b (Uint63.sub bt' nbiti) /\ (nbiti <=? bt')%uint63).
Proof.
move=> hbt; rewrite lor_spec bit_lsl bit_mask24.
have hdg : to_nat digits = 63%N by vm_compute.
have hd : ((digits <=? bt')%uint63) = false.
  apply/negbTE; apply/negP => /nlebP; rewrite hdg => h63.
  have h48 : (to_nat bt' < 48)%N by rewrite -nbit48iE; apply/nltbP.
  by have := leq_ltn_trans h63 h48.
have [hlo|hlo] := boolP (bt' <? nbiti)%uint63.
  by rewrite andbT orTb /= orbF => hb; left; split.
rewrite andbF orFb hd /= bit_mask24 => /andP[hb _].
right; split => //.
apply/nlebP; rewrite leqNgt; apply/negP => h.
by case/negP: hlo; apply/nltbP.
Qed.

(* two small facts about the twenty fourth place                             *)
Lemma sub_nbiti_lt bt' : (nbiti <=? bt')%uint63 -> (bt' <? nbit48i)%uint63 ->
  (Uint63.sub bt' nbiti <? nbiti)%uint63.
Proof.
move=> hge hlt; apply/nltbP.
rewrite to_nat_sub ?to_nat_bounded //; last by apply/nlebP.
rewrite nbitiE ltn_subLR; last by rewrite -nbitiE; apply/nlebP.
by rewrite -[(24 + 24)%N]/(48%N) -nbit48iE; apply/nltbP.
Qed.

Lemma add_sub_nbiti bt' :
  Uint63.add (Uint63.mul 1%uint63 nbiti) (Uint63.sub bt' nbiti) = bt'.
Proof. by rewrite mul1_nbiti laddC subK. Qed.

Lemma add_mul0_nbiti x : Uint63.add (Uint63.mul 0%uint63 nbiti) x = x.
Proof. by rewrite mul0_nbiti ladd0n. Qed.

(* A BIT OF A MOVED CELL CAME FROM A BIT OF THE CELL.  Four cases, and they   *)
(* are the two halves against the two values of the flip: which half a bit is *)
(* in says which of the two twenty four bit words moved it, and the flip says *)
(* where that half landed.                                                    *)
Lemma grpmvP48 k v bt' : (to_nat k < nhn)%N -> (bt' <? nbit48i)%uint63 ->
  ~~ (Uint63.land (grpmv48 cfl msw mlo mhi k v) (bitof bt') =? 0)%uint63 ->
  exists2 bt, (bt <? nbit48i)%uint63 &
    btmv48 k bt = bt' /\ ~~ (Uint63.land v (bitof bt) =? 0)%uint63.
Proof.
move=> hk hbt hset.
have hbd : (bt' <? digits)%uint63 := lt_nbit48i_digits hbt.
have hc2 := hcfl hk.
have h0 : (to_nat 0%uint63 < 2)%N by vm_compute.
have h1 : (to_nat 1%uint63 < 2)%N by vm_compute.
have x00 : Uint63.lxor 0%uint63 0%uint63 = 0%uint63 by vm_compute.
have x11 : Uint63.lxor 1%uint63 1%uint63 = 0%uint63 by vm_compute.
have x01 : Uint63.lxor 0%uint63 1%uint63 = 1%uint63 by vm_compute.
have x10 : Uint63.lxor 1%uint63 0%uint63 = 1%uint63 by vm_compute.
rewrite test_bit // /grpmv48 in hset.
have e0 : Uint63.land v allbits = halfw v 0%uint63 by rewrite halfw0.
have e1 : Uint63.land (Uint63.lsr v nbiti) allbits = halfw v 1%uint63.
  by rewrite halfw1.
rewrite e0 e1 in hset.
case: (int_lt2 hc2) => hf; rewrite hf /= in hset.
  (* the move is even on the corners: the halves stay where they are          *)
  case: (split_lor48 hbt hset) => [[hb hlo]|[hb hge]].
    apply: (from_half (h := 0%uint63) (j := bt')) => //.
      by rewrite hf x00 add_mul0_nbiti.
    by rewrite test_bit //; apply: lt_nbiti_digits.
  have hj := sub_nbiti_lt hge hbt.
  apply: (from_half (h := 1%uint63) (j := Uint63.sub bt' nbiti)) => //.
    by rewrite hf x10 add_sub_nbiti.
  by rewrite test_bit //; apply: lt_nbiti_digits.
(* the move is odd on the corners: the two halves change places               *)
case: (split_lor48 hbt hset) => [[hb hlo]|[hb hge]].
  apply: (from_half (h := 1%uint63) (j := bt')) => //.
    by rewrite hf x11 add_mul0_nbiti.
  by rewrite test_bit //; apply: lt_nbiti_digits.
have hj := sub_nbiti_lt hge hbt.
apply: (from_half (h := 0%uint63) (j := Uint63.sub bt' nbiti)) => //.
  by rewrite hf x01 add_sub_nbiti.
by rewrite test_bit //; apply: lt_nbiti_digits.
Qed.

End Bits48.

Section Page48.

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Variable mpg cpg cfl mgr : arr.

(* the flip is a parity                                                       *)
Definition cflok : bool :=
  iter nhn 0%uint63 (fun k => (PArray.get cfl k <? 2)%uint63).

Hypothesis hcflok : cflok.

Lemma hcfl k : (to_nat k < nhn)%N -> (to_nat (PArray.get cfl k) < 2)%N.
Proof.
by move=> hk; have h := iter_at hcflok hk; rewrite -(_ : to_nat 2%uint63 = 2%N);
   [apply/nltbP | vm_compute].
Qed.

(* ---- the corner rank a forty eight bit place names ----------------------- *)

Definition pgof (pg bt : int) : int :=
  PArray.get e8inv (Uint63.add (Uint63.mul pg 2%uint63) (Uint63.div bt nbiti)).

(* the parity of a place is nought or one, and it is the corner parity        *)
Lemma s48_lt2 bt : (bt <? nbit48i)%uint63 -> (to_nat (Uint63.div bt nbiti) < 2)%N.
Proof.
move=> hbt; rewrite to_nat_div nbitiE ltn_divLR //.
by apply: leq_trans (nltbP _ _ hbt) _; rewrite nbit48iE.
Qed.

Lemma b48_lt bt : (Uint63.mod bt nbiti <? nbiti)%uint63.
Proof. by apply/nltbP; rewrite to_nat_mod ltn_mod nbitiE. Qed.

(* the corner rank is a page, and its parity is the place's own               *)
Lemma pgof_page pg bt : (pg <? nclsi)%uint63 -> (bt <? nbit48i)%uint63 ->
  (pgof pg bt <? npagei)%uint63 /\
  PArray.get par8 (pgof pg bt) = Uint63.div bt nbiti.
Proof.
move=> hpg hbt; rewrite nclsiE in hpg.
have [hn hd hm] := pair_page hpg (s48_lt2 hbt).
case/and5P: (e8at he8 hn) => _ _ _ hiv /eqP hnv; split => //.
by case/and5P: (e8at he8 hiv) => _ /eqP <- _ _ _; rewrite hnv.
Qed.

(* ---- AND THE WHOLE OF IT: the two places name the same member ------------ *)

Lemma unplace48E pg gr bt : (pg <? nclsi)%uint63 -> (bt <? nbit48i)%uint63 ->
  unplace48 e8inv e4of par4 pg gr bt
  = unplace e8inv e4of par8 par4 (pgof pg bt) gr (Uint63.mod bt nbiti).
Proof.
move=> hpg hbt; rewrite /unplace48 /unplace /pgof.
by have [_ ->] := pgof_page hpg hbt.
Qed.

Lemma inrange48E pg gr bt : inrange48 pg gr bt ->
  inrange (pgof pg bt) gr (Uint63.mod bt nbiti).
Proof.
case/and3P => hpg hgr hbt; apply/and3P; split => //; last by apply: b48_lt.
by have [h _] := pgof_page hpg hbt.
Qed.

(* ---- the one check: the class table IS the page table, split ------------- *)

(* cpg and cfl are read at a pair and a parity; mpg is read at the corner     *)
(* rank the two name.  This says the two agree -- 20160 by two by ten.        *)
Definition cpgok481 (k : int) : bool :=
  iter nclsn 0%uint63 (fun pg =>
    iter 2 0%uint63 (fun s =>
      (cpgmv cpg k pg <? nclsi)%uint63 &&
      (PArray.get e8inv
         (Uint63.add (Uint63.mul (cpgmv cpg k pg) 2%uint63)
                     (Uint63.lxor s (PArray.get cfl k)))
       =? pgmv mpg k (PArray.get e8inv
                        (Uint63.add (Uint63.mul pg 2%uint63) s)))%uint63)).

Definition cpgok48 : bool := iter nhn 0%uint63 cpgok481.

Hypothesis hcpg : cpgok48.

Lemma cpgok48P k pg s : (to_nat k < nhn)%N -> (pg <? nclsi)%uint63 ->
  (to_nat s < 2)%N ->
  (cpgmv cpg k pg <? nclsi)%uint63 /\
  PArray.get e8inv
    (Uint63.add (Uint63.mul (cpgmv cpg k pg) 2%uint63)
                (Uint63.lxor s (PArray.get cfl k)))
  = pgmv mpg k (PArray.get e8inv (Uint63.add (Uint63.mul pg 2%uint63) s)).
Proof.
move=> hk hpg hs.
have h1 := iter_at hcpg hk.
have h2 := iter_at h1 (nltbP _ _ hpg).
by case/andP: (iter_at h2 hs) => hr /eqP he.
Qed.

(* ---- and the move, which is the twenty four bit move ---------------------- *)

Variable btmv : int -> int -> int.
Variable pos : memb -> {perm facelet}.
Variable hmv : int -> {perm facelet}.

(* what the twenty four bit instance already gives                            *)
Hypothesis prep_move : forall k pg gr bt, (to_nat k < nhn)%N ->
  inrange pg gr bt ->
  inrange (pgmv mpg k pg) (grmv mgr k gr) (btmv k bt) /\
  pos (unplace e8inv e4of par8 par4
         (pgmv mpg k pg) (grmv mgr k gr) (btmv k bt))
  = pos (unplace e8inv e4of par8 par4 pg gr bt) * hmv k.

(* THE SAME MOVE ON THE SAME MEMBER.  The two places name one member, the     *)
(* class table is the page table split, and the flip is where the parity      *)
(* went -- so there is nothing here but reading the twenty four bit fact at   *)
(* the corner rank the place names.                                           *)
Lemma prep_move48 k pg gr bt : (to_nat k < nhn)%N -> inrange48 pg gr bt ->
  inrange48 (cpgmv cpg k pg) (grmv mgr k gr) (btmv48 cfl btmv k bt) /\
  pos (unplace48 e8inv e4of par4 (cpgmv cpg k pg) (grmv mgr k gr)
         (btmv48 cfl btmv k bt))
  = pos (unplace48 e8inv e4of par4 pg gr bt) * hmv k.
Proof.
move=> hk hr; have /and3P[hpg hgr hbt] := hr.
have hs2 : (to_nat (Uint63.div bt nbiti) < 2)%N := s48_lt2 hbt.
have hb : (Uint63.mod bt nbiti <? nbiti)%uint63 := b48_lt bt.
(* the twenty four bit place this one names, and the move on it               *)
have hr24 : inrange (pgof pg bt) gr (Uint63.mod bt nbiti) := inrange48E hr.
have [hr24' hpos] := prep_move hk hr24.
have /and3P[hp' hg' hb'] := hr24'.
have hb'n : (to_nat (btmv k (Uint63.mod bt nbiti)) < to_nat nbiti)%N.
  by apply/nltbP.
(* the parity the move takes it to, and the bit                               *)
have hs' : (to_nat (Uint63.lxor (Uint63.div bt nbiti) (PArray.get cfl k)) < 2)%N.
  by apply: lxor_lt2 => //; apply: hcfl.
have hbd' := bit48_bound hs' hb'n.
have hdiv : Uint63.div (btmv48 cfl btmv k bt) nbiti
          = Uint63.lxor (Uint63.div bt nbiti) (PArray.get cfl k).
  by rewrite /btmv48; apply: (div_mulD hb'n hbd').
have hmod : Uint63.mod (btmv48 cfl btmv k bt) nbiti
          = btmv k (Uint63.mod bt nbiti).
  by rewrite /btmv48; apply: (mod_mulD hb'n hbd').
have hbt48 : (btmv48 cfl btmv k bt <? nbit48i)%uint63.
  by rewrite /btmv48; apply: bit48_lt.
have [hcr hce] := cpgok48P hk hpg hs2.
(* the corner rank of the moved place is the corner rank, moved               *)
have hpgof : pgof (cpgmv cpg k pg) (btmv48 cfl btmv k bt)
           = pgmv mpg k (pgof pg bt).
  by rewrite {1}/pgof hdiv hce.
split; first by apply/and3P; split.
by rewrite (unplace48E gr hpg hbt)
   (unplace48E (grmv mgr k gr) hcr hbt48) hpgof hmod.
Qed.

End Page48.
