(* =========================================================================  *)
(*  RowMap.v -- the map of a row, and the prepass.                            *)
(* =========================================================================  *)

(* A GROUP is twenty four bits and fits in one word, so the map is one word a *)
(* group: 40320 * 20160 words, 6.5 GB.  PArray.max_length is 4 194 303, so it *)
(* is cut into chunks of two million, the shape the folded tables already use.*)
(*                                                                            *)
(* THE PREPASS is one move of H played on the whole map at once.  A page goes *)
(* to a page, a group to a group, and the twenty four bits of a group are     *)
(* rearranged by a table -- six of the ten moves leave the middle four alone  *)
(* and so leave all twenty four bits where they are.  No member is ever taken *)
(* apart, and that is what makes a whole row affordable.                      *)
(*                                                                            *)
(* THE LOOP IS NESTED ON PURPOSE: 812 851 200 as a unary nat does not exist,  *)
(* but 40320 pages of 20160 groups do, and each is the size of nat the        *)
(* existing sweeps already walk.                                              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* The two loop bounds are Row.v's, which are the int63 bounds read over as   *)
(* nats: there is then no numeral anywhere and nothing to bridge when a walk  *)
(* is read at one page and one group.                                         *)

(* walk n consecutive ints, carrying something along                          *)
Fixpoint ifold (A : Type) (n : nat) (x : int) (f : int -> A -> A) (a : A) : A :=
  if n is n1.+1 then ifold n1 (Uint63.add x 1%uint63) f (f x a) else a.

(* what survives such a walk: anything each step keeps                        *)
Lemma ifold_ind (A : Type) (P : A -> Prop) n x f a :
  (forall i b, P b -> P (f i b)) -> P a -> P (ifold n x f a).
Proof.
by move=> hf; elim: n x a => [|n ih] x a //= ha; apply: ih; apply: hf.
Qed.

(* the same, when the step is only good for the numbers the walk reaches --   *)
(* which is how the eighteen moves are read off a walk of eighteen            *)
Lemma ifold_indg (A : Type) (P : A -> Prop) n j f a :
  (j + n <= nwB)%N ->
  (forall k b, (to_nat k < j + n)%N -> P b -> P (f k b)) -> P a ->
  P (ifold n (advn j 0%uint63) f a).
Proof.
elim: n j a => [|n ih] j a hb hf ha //=.
have -> : Uint63.add (advn j 0%uint63) 1%uint63 = advn j.+1 0%uint63.
  by rewrite advnS.
apply: ih.
- by rewrite addSnnS.
- by move=> k b hk hPb; apply: hf => //; rewrite -addSnnS.
apply: hf => //; rewrite to_nat_advn0; first by rewrite addnS ltnS leq_addr.
by apply: leq_trans hb; rewrite addnS ltnS leq_addr.
Qed.

Lemma ifold_indi (A : Type) (P : A -> Prop) n f a :
  (n <= nwB)%N ->
  (forall k b, (to_nat k < n)%N -> P b -> P (f k b)) -> P a ->
  P (ifold n 0%uint63 f a).
Proof. by move=> hb hf ha; apply: (@ifold_indg _ _ n 0). Qed.

(* ---- the map ------------------------------------------------------------- *)

Definition cshft  : int := 21%uint63.          (* two million a chunk         *)
Definition cmskw  : int := 2097151%uint63.
Definition csize  : int := 2097152%uint63.
Definition nchunk : int := 388%uint63.         (* 40320 * 20160 / 2 ^ 21      *)

Definition gget (m : rmap) (g : int) : int :=
  PArray.get (PArray.get m (Uint63.lsr g cshft)) (Uint63.land g cmskw).

Definition gset (m : rmap) (g v : int) : rmap :=
  let c := Uint63.lsr g cshft in
  PArray.set m c (PArray.set (PArray.get m c) (Uint63.land g cmskw) v).

Definition gor (m : rmap) (g v : int) : rmap :=
  gset m g (Uint63.lor (gget m g) v).

(* EVERY CHUNK ITS OWN ARRAY.  `PArray.make nchunk (PArray.make csize 0)'    *)
(* runs the inner make ONCE and hands the same array to all 388 slots, so a   *)
(* write to any chunk chains a difference onto that one array and every other *)
(* chunk then reads through it.  Built chunk by chunk instead, each make is   *)
(* under a lambda and runs afresh.  RowFold has had mkempty for this reason;  *)
(* this file did not, and the row's map paid for it.                          *)
Definition nchunkn : nat := 388.

Definition mkempty (u : unit) : rmap :=
  ifold nchunkn 0%uint63
    (fun c a => PArray.set a c (PArray.make csize 0%uint63))
    (PArray.make nchunk (PArray.make 1%uint63 0%uint63)).

(* NEVER START A RUN FROM THIS ONE: a global is held for ever, so every       *)
(* difference ever made to it stays alive.  This is for reading.              *)
Definition mempty : rmap := mkempty tt.

(* a member's group, and its bit inside it                                    *)
Definition grpof (pg gr : int) : int := Uint63.add (Uint63.mul pg ngroupi) gr.
Definition bitof (bt : int) : int := Uint63.lsl 1%uint63 bt.

Definition mtest (m : rmap) (pg gr bt : int) : bool :=
  negb (Uint63.eqb (Uint63.land (gget m (grpof pg gr)) (bitof bt)) 0%uint63).

Definition mmark (m : rmap) (pg gr bt : int) : rmap :=
  gor m (grpof pg gr) (bitof bt).

(* the map is full when every group has all twenty four bits                  *)
Definition allbits : int := 16777215%uint63.

Definition mfull (m : rmap) : bool :=
  iter npagen 0%uint63
    (fun pg => iter ngroupn 0%uint63
       (fun gr => Uint63.eqb (gget m (grpof pg gr)) allbits)).

(* THE TWO MAPS TOGETHER ARE NEVER BUILT.  Every member has to be in one map *)
(* or the other, and that is asked of the two of them where they stand.  The *)
(* map that was built instead read one of them at every one of its eight     *)
(* hundred million words while writing into it, and a persistent array reads *)
(* an old version by walking back through every write made since -- which is *)
(* what took 53 GB on a machine with 64.                                     *)
Definition mfull2 (m1 m2 : rmap) : bool :=
  iter npagen 0%uint63
    (fun pg => iter ngroupn 0%uint63
       (fun gr =>
          let g := grpof pg gr in
          Uint63.eqb (Uint63.lor (gget m1 g) (gget m2 g)) allbits)).

(* ---- the array axioms, at an array of arrays ----------------------------- *)

(* The axioms are not universe polymorphic, so each type they are used at     *)
(* needs its own instance.  ssrint63 carries the ones at int; these are the   *)
(* same at the map's outer level, where an entry is itself an array.          *)

Lemma get_setA (t : rmap) (i : int) (v : arr) :
  (i <? PArray.length t)%uint63 = true -> PArray.get (PArray.set t i v) i = v.
Proof. exact: (@PArray.get_set_same arr t i v). Qed.

Lemma get_set_otherA (t : rmap) (i j : int) (v : arr) :
  i <> j -> PArray.get (PArray.set t i v) j = PArray.get t j.
Proof. exact: (@PArray.get_set_other arr t i j v). Qed.

Lemma get_makeA (v : arr) (i sz : int) : PArray.get (PArray.make sz v) i = v.
Proof. exact: (@PArray.get_make arr v sz i). Qed.

Lemma get_oobA (t : rmap) (i : int) :
  (i <? PArray.length t)%uint63 = false -> PArray.get t i = PArray.default t.
Proof. exact: (@PArray.get_out_of_bounds arr t i). Qed.

Lemma default_setA (t : rmap) (i : int) (v : arr) :
  PArray.default (PArray.set t i v) = PArray.default t.
Proof. exact: (@PArray.default_set arr t i v). Qed.

Lemma length_setA (t : rmap) (i : int) (v : arr) :
  PArray.length (PArray.set t i v) = PArray.length t.
Proof. exact: (@PArray.length_set arr t i v). Qed.

Lemma get_oobE (t : arr) (i : int) :
  (i <? PArray.length t)%uint63 = false -> PArray.get t i = PArray.default t.
Proof. exact: (@PArray.get_out_of_bounds int t i). Qed.

Lemma default_setE (t : arr) (i v : int) :
  PArray.default (PArray.set t i v) = PArray.default t.
Proof. exact: (@PArray.default_set int t i v). Qed.

Lemma length_setE (t : arr) (i v : int) :
  PArray.length (PArray.set t i v) = PArray.length t.
Proof. exact: (@PArray.length_set int t i v). Qed.

(* ---- the chunking is an ordinary division -------------------------------- *)

(* A group is found by a shift and a mask, which is what makes a read cheap.  *)
(* Those two are the quotient and the remainder by the size of a chunk, and   *)
(* everything below argues with the division and never with the bits.         *)

Lemma cshftE g : Uint63.lsr g cshft = Uint63.div g csize.
Proof.
have -> : csize = Uint63.lsl one cshft by vm_compute.
by apply: div_one_lsl_lsr.
Qed.

Lemma cmskwE g : Uint63.land g cmskw = Uint63.mod g csize.
Proof.
have -> : cmskw = decr (Uint63.lsl one cshft) by vm_compute.
have -> : csize = Uint63.lsl one cshft by vm_compute.
by apply: land_power2.
Qed.

(* so two groups that share a chunk and a place in it are the same group      *)
Lemma grp_eq g g' :
  Uint63.div g csize = Uint63.div g' csize ->
  Uint63.mod g csize = Uint63.mod g' csize -> g = g'.
Proof.
by move=> hd hm; rewrite (int_add_mod g csize) (int_add_mod g' csize) hd hm.
Qed.

(* ---- one write, read anywhere -------------------------------------------- *)

(* THE MAP IS NEVER ASKED TO BE WELL FORMED, and it need not be.  A write     *)
(* outside an array does nothing at all, so a read after a write gives either *)
(* what was written or what was there before -- and that is enough, because   *)
(* everything here is one directional: a bit that is set came from somewhere. *)
(* A map of the wrong shape simply never fills, and the row never finishes.   *)
Lemma gget_gset m g v g' :
  gget (gset m g v) g' = gget m g' \/
  (g = g' /\ gget (gset m g v) g' = v).
Proof.
rewrite /gget /gset !cshftE !cmskwE.
set c := Uint63.div g csize; set c' := Uint63.div g' csize.
set j := Uint63.mod g csize; set j' := Uint63.mod g' csize.
set X := PArray.set (PArray.get m c) j v.
(* another chunk: the write is not seen at all                                *)
have [hc|hc] := eqVneq c c'; last first.
  by left; rewrite get_set_otherA //; apply/eqP.
rewrite -hc.
(* the chunk is not there: a write outside an array does nothing              *)
have [hin|hin] := boolP (c <? PArray.length m)%uint63; last first.
  have hoo : (c <? PArray.length (PArray.set m c X))%uint63 = false.
    by rewrite length_setA; apply: negbTE.
  left; rewrite (@get_oobA _ _ hoo) default_setA.
  by rewrite (@get_oobA _ _ (negbTE hin)).
rewrite (@get_setA _ _ _ hin).
(* another place in the chunk                                                 *)
have [hj|hj] := eqVneq j j'; last first.
  by left; rewrite /X get_set_otherE //; apply/eqP.
rewrite -hj.
(* the place is not there either                                              *)
have [hin2|hin2] := boolP (j <? PArray.length (PArray.get m c))%uint63;
    last first.
  have hoo2 : (j <? PArray.length (PArray.set (PArray.get m c) j v))%uint63
            = false.
    by rewrite length_setE; apply: negbTE.
  by left; rewrite /X (@get_oobE _ _ hoo2) default_setE
                   (@get_oobE _ _ (negbTE hin2)).
by right; split; [apply: grp_eq | rewrite /X (@get_setE _ _ _ hin2)].
Qed.

(* ---- a group number is a page and a group -------------------------------- *)

(* grpof runs the page and the group together into one number, and on the     *)
(* ranges it is one to one -- which is what makes a bit stand for a member.   *)
(* THE BOUND IS SPELT OUT RATHER THAN COMPUTED: forty thousand times twenty   *)
(* thousand does not exist in unary, so it is bounded by powers of two.       *)

(* A BIG NUMBER MUST NOT BE LEFT IN THE CONTEXT.  `done' tries the            *)
(* hypotheses UP TO CONVERSION, so with 2 ^ 31 + 2 ^ 15 < 2 ^ 32 sitting      *)
(* there as a hypothesis, the next `by []' -- on a goal about nothing at all  *)
(* -- went away to build two billion in unary.  The three facts about powers  *)
(* are lemmas of their own for that reason, and none of them is ever a        *)
(* hypothesis.                                                                *)

Lemma ndigits32 : (32 <= ndigits)%N.
Proof. by []. Qed.

Lemma pow_bound : (2 ^ 31 + 2 ^ 15 < 2 ^ 32)%N.
Proof.
have -> : (32 = 31 + 1)%N by [].
by rewrite expnD expn1 muln2 -addnn ltn_add2l ltn_exp2l.
Qed.

Lemma pow_split : (2 ^ 31 = 2 ^ 16 * 2 ^ 15)%N.
Proof. by rewrite -expnD. Qed.

Lemma bound32 a b c :
  (a <= 2 ^ 16)%N -> (b <= 2 ^ 15)%N -> (c <= 2 ^ 15)%N ->
  (a * b + c < nwB)%N.
Proof.
move=> h1 h2 h3.
apply: (@ltn_nwB 32 _ ndigits32).
apply: leq_ltn_trans pow_bound.
by rewrite pow_split; apply: leq_add; [apply: leq_mul | ].
Qed.

Lemma grpof_bound pg gr : (pg <? npagei)%uint63 -> (gr <? ngroupi)%uint63 ->
  (to_nat pg * ngroupn + to_nat gr < nwB)%N.
Proof.
move=> hpg hgr; apply: bound32.
- by apply: leq_trans (ltnW (ltn_npagei hpg)) _; rewrite npagenE.
- by rewrite ngroupnE.
by apply: leq_trans (ltnW (ltn_ngroupi hgr)) _; rewrite ngroupnE.
Qed.

Lemma to_nat_grpof pg gr : (pg <? npagei)%uint63 -> (gr <? ngroupi)%uint63 ->
  to_nat (grpof pg gr) = (to_nat pg * ngroupn + to_nat gr)%N.
Proof.
move=> hpg hgr; have hb := grpof_bound hpg hgr.
have hm : to_nat (Uint63.mul pg ngroupi) = (to_nat pg * ngroupn)%N.
  by apply: to_nat_mul; apply: leq_ltn_trans hb; apply: leq_addr.
have ha : (to_nat (Uint63.mul pg ngroupi) + to_nat gr < nwB)%N by rewrite hm.
by rewrite /grpof (@to_nat_add _ _ ha) hm.
Qed.

Lemma grpof_inj p g pg gr :
  (p <? npagei)%uint63 -> (g <? ngroupi)%uint63 ->
  (pg <? npagei)%uint63 -> (gr <? ngroupi)%uint63 ->
  grpof p g = grpof pg gr -> p = pg /\ g = gr.
Proof.
move=> hp hg hpg hgr he.
have hng : (0 < ngroupn)%N by rewrite ngroupnE.
have hgl : (to_nat g < ngroupn)%N by apply: ltn_ngroupi.
have hgl' : (to_nat gr < ngroupn)%N by apply: ltn_ngroupi.
have heq : (to_nat p * ngroupn + to_nat g = to_nat pg * ngroupn + to_nat gr)%N.
  by rewrite -(to_nat_grpof hp hg) -(to_nat_grpof hpg hgr) he.
split; apply: to_nat_inj.
  have := congr1 (fun k => (k %/ ngroupn)%N) heq.
  by rewrite !divnMDl // !divn_small // !addn0.
have := congr1 (fun k => (k %% ngroupn)%N) heq.
by rewrite !modnMDl // !modn_small.
Qed.

(* ---- the four facts the rest of the development uses --------------------- *)

(* Each is about PArray and the chunking and nothing else -- no cube, no row. *)

(* a bit is nought or one, and the twenty four bits are all in allbits        *)
Lemma land0n x : (0 land x = 0)%uint63.
Proof. by apply: bit_ext => i; rewrite land_spec !bit_0. Qed.

Lemma lt_digits x : (x <? nbiti)%uint63 -> (x <? digits)%uint63.
Proof.
move=> h; apply/nltbP; apply: leq_trans (_ : to_nat nbiti <= _).
  by apply/nltbP.
by apply/nlebP; vm_compute.
Qed.

Lemma allbitsP bt : (bt <? nbiti)%uint63 ->
  (Uint63.land allbits (bitof bt) =? 0)%uint63 = false.
Proof.
move=> hb; have hbd := lt_digits hb.
have hset : bit (Uint63.land allbits (bitof bt)) bt.
  rewrite land_spec.
  have -> : allbits = decr (Uint63.lsl one nbiti) by vm_compute.
  rewrite bit_decr ?hb //.
  rewrite /bitof; have -> : 1%uint63 = one by vm_compute.
  by rewrite bit_onenn // eqxx.
apply/negbTE/negP => /neqbP h0.
have hz : Uint63.land allbits (bitof bt) = 0%uint63 by apply: to_nat_inj.
by move: hset; rewrite hz bit_0.
Qed.

(* a set bit in an or was set in one of the two                               *)
Lemma test_lor a b k :
  ~~ (Uint63.land (Uint63.lor a b) k =? 0)%uint63 ->
  ~~ (Uint63.land a k =? 0)%uint63 || ~~ (Uint63.land b k =? 0)%uint63.
Proof.
rewrite -negb_and; apply: contra => /andP[ha hb].
have ha' : Uint63.land a k = 0%uint63 by apply: to_nat_inj; apply/neqbP.
have hb' : Uint63.land b k = 0%uint63 by apply: to_nat_inj; apply/neqbP.
by rewrite land_lor_distrl ha' hb'.
Qed.

(* two of the twenty four bits meet only when they are the same bit           *)
Lemma bitof_inj b bt : (b <? nbiti)%uint63 -> (bt <? nbiti)%uint63 ->
  ~~ (Uint63.land (bitof b) (bitof bt) =? 0)%uint63 -> b = bt.
Proof.
move=> hb hbt h; have hbd := lt_digits hb; have hbtd := lt_digits hbt.
case: (b =P bt) => // hne; case/negP: h.
have hz : Uint63.land (bitof b) (bitof bt) = 0%uint63.
  apply: bit_ext => i; rewrite land_spec bit_0.
  have [hid|hid] := boolP (i <? digits)%uint63; last first.
    have hd : (digits <=? i)%uint63.
      by apply/nlebP; rewrite leqNgt; apply/negP => /nltbP h1; case/negP: hid.
    by rewrite bit_M ?andbF.
  rewrite /bitof; have -> : 1%uint63 = one by vm_compute.
  rewrite !bit_onenn //.
  case: eqP => [hbi|_] //=; case: eqP => [hti|_] //=.
  by case: hne; rewrite hbi hti.
by rewrite hz; apply/neqbP.
Qed.

(* an empty map has no bit set: every chunk of it is a chunk of noughts       *)
Lemma get_mkempty c :
  PArray.get (mkempty tt) c = PArray.make csize 0%uint63 \/
  PArray.get (mkempty tt) c = PArray.make 1%uint63 0%uint63.
Proof.
have hset : forall (t : rmap) i (v : arr),
    PArray.get (PArray.set t i v) i = v \/
    PArray.get (PArray.set t i v) i = PArray.get t i.
  move=> t i v; have [hin|hin] := boolP (i <? PArray.length t)%uint63.
    by left; rewrite get_setA.
  right; rewrite get_oobA ?default_setA; last by rewrite length_setA;
    apply: negbTE.
  by rewrite (@get_oobA _ _ (negbTE hin)).
rewrite /mkempty.
apply: (@ifold_ind _ (fun a => PArray.get a c = PArray.make csize 0%uint63 \/
                               PArray.get a c = PArray.make 1%uint63 0%uint63));
    last by right; rewrite get_makeA.
move=> i b hb.
have [hic|hic] := eqVneq i c; last first.
  by rewrite get_set_otherA //; apply/eqP.
by rewrite -hic; case: (hset b i (PArray.make csize 0%uint63)) => ->;
   [left | rewrite hic].
Qed.

Lemma mkemptyP pg gr bt : mtest (mkempty tt) pg gr bt = false.
Proof.
rewrite /mtest /gget.
by case: (get_mkempty (Uint63.lsr (grpof pg gr) cshft)) => ->;
   rewrite get_makeE land0n.
Qed.

Lemma memptyP pg gr bt : mtest mempty pg gr bt = false.
Proof. exact: mkemptyP. Qed.

(* a full map has every bit of every place in range                           *)
Lemma mfullP m pg gr bt : mfull m -> inrange pg gr bt -> mtest m pg gr bt.
Proof.
move=> hf /and3P[hpg hgr hbt].
have h1 := iter_at hf (ltn_npagei hpg).
have h2 := iter_at h1 (ltn_ngroupi hgr).
by rewrite /mtest (eqP h2) allbitsP.
Qed.

(* when the two of them are full together, every member is in one of them     *)
Lemma mfull2P m1 m2 pg gr bt : mfull2 m1 m2 -> inrange pg gr bt ->
  mtest m1 pg gr bt || mtest m2 pg gr bt.
Proof.
move=> hf /and3P[hpg hgr hbt].
have h1 := iter_at hf (ltn_npagei hpg).
have h2 := iter_at h1 (ltn_ngroupi hgr).
by apply: test_lor; rewrite (eqP h2) allbitsP.
Qed.

(* a bit an or sets was there already, or is one of the bits it ored in       *)
Lemma mtest_gor (a : rmap) G V P Q B :
  mtest (gor a G V) P Q B ->
  mtest a P Q B \/
  (G = grpof P Q /\ ~~ (Uint63.land V (bitof B) =? 0)%uint63).
Proof.
rewrite /gor /mtest.
case: (gget_gset a G (Uint63.lor (gget a G) V) (grpof P Q)) => [->|[hG ->]].
  by move=> h; left.
by move=> /test_lor/orP[hin|hnew]; [left; rewrite -hG|right].
Qed.

(* a bit set by a mark is the mark, or was there already                      *)
Lemma mmarkP m p g b pg gr bt :
  inrange p g b -> inrange pg gr bt ->
  mtest (mmark m p g b) pg gr bt ->
  [/\ p = pg, g = gr & b = bt] \/ mtest m pg gr bt.
Proof.
case/and3P => hp hg hb; case/and3P => hpg hgr hbt.
rewrite /mmark /gor /mtest.
case: (gget_gset m (grpof p g)
        (Uint63.lor (gget m (grpof p g)) (bitof b)) (grpof pg gr))
    => [->|[hgg ->]]; first by move=> hh; right.
move=> /test_lor/orP[hin|hnew]; first by right; rewrite -hgg.
left; have [-> ->] := grpof_inj hp hg hpg hgr hgg.
by split => //; apply: bitof_inj hnew.
Qed.

Section Pre.

(* ---- the ten moves of H, on pages, on groups and on bits ----------------- *)

(* mpg and mgr are permutations of the pages and of the groups; msw says      *)
(* whether a move exchanges the two halves of a group, and mlo, mhi rearrange *)
(* the twelve bits of each half.  Six of the ten leave the bits alone, and    *)
(* for those mlo and mhi are the identity.                                    *)
Variable mpg : arr.                 (* 40320 * 10                             *)
Variable mgr : arr.                 (* 20160 * 10                             *)
Variable msw : arr.                 (* 10                                     *)
Variable mlo mhi : arr.             (* 10 * 4096                              *)

Definition nhi : int := 10%uint63.
Definition nhn : nat := 10.

Definition pgmv (k pg : int) : int :=
  PArray.get mpg (Uint63.add (Uint63.mul pg nhi) k).
Definition grmv (k gr : int) : int :=
  PArray.get mgr (Uint63.add (Uint63.mul gr nhi) k).

Definition lomv (k v : int) : int :=
  PArray.get mlo (Uint63.add (Uint63.lsl k 12%uint63) v).
Definition himv (k v : int) : int :=
  PArray.get mhi (Uint63.add (Uint63.lsl k 12%uint63) v).

Definition lo12 : int := 4095%uint63.

(* one group, moved                                                           *)
(* THE HIGH HALF IS MASKED TOO.  Without it a word with a bit above the       *)
(* twenty fourth indexes mhi inside ANOTHER move's block of four thousand and *)
(* gives back that move's rearrangement -- and no check on the tables can     *)
(* repair it, since those entries are the other move's real data.  The        *)
(* prototype never meets it because it keeps the two halves in two arrays;    *)
(* packing them into one word is this side's own doing, so the mask is too.   *)
Definition grpmv (k v : int) : int :=
  let l := lomv k (Uint63.land v lo12) in
  let h := himv k (Uint63.land (Uint63.lsr v 12%uint63) lo12) in
  if Uint63.eqb (PArray.get msw k) 0%uint63
  then Uint63.lor l (Uint63.lsl h 12%uint63)
  else Uint63.lor h (Uint63.lsl l 12%uint63).

(* ---- one move over the whole map ----------------------------------------- *)

(* The source is read and the destination written, which is why there are two *)
(* maps: playing a move on what a move has just reached would count a member  *)
(* a level too soon.                                                          *)
Definition prepmv (k : int) (src : rmap) (dst : rmap) : rmap :=
  ifold npagen 0%uint63
    (fun pg d =>
       let pg' := pgmv k pg in
       ifold ngroupn 0%uint63
         (fun gr d' =>
            let v := gget src (grpof pg gr) in
            if Uint63.eqb v 0%uint63 then d'
            else gor d' (grpof pg' (grmv k gr)) (grpmv k v))
         d)
    dst.

(* THE CARRY IS A FRESH MAP, not the source itself.  All ten moves read the   *)
(* source, so if the writes were stacked on top of it every read would walk   *)
(* back over them.  The source is copied into a map of its own first and then *)
(* stays a plain array that is only read.  The copy is one sweep against the  *)
(* ten the moves already make.                                                *)
Definition mcopy (src : rmap) : rmap :=
  ifold npagen 0%uint63
    (fun pg a =>
       ifold ngroupn 0%uint63
         (fun gr a' => let g := grpof pg gr in gset a' g (gget src g))
         a)
    (mkempty tt).

(* and the copy claims nothing of its own *)
Lemma mcopyP src pg gr bt : mtest (mcopy src) pg gr bt -> mtest src pg gr bt.
Proof.
have hstep : forall (g : int) (a : rmap),
    (forall p q c, mtest a p q c -> mtest src p q c) ->
    forall p q c,
    mtest (gset a g (gget src g)) p q c -> mtest src p q c.
  move=> g a ha p q c.
  case: (gget_gset a g (gget src g) (grpof p q)).
    by rewrite /mtest => ->; apply: ha.
  by case=> hg; rewrite /mtest => ->; rewrite hg.
suff h : forall p q c, mtest (mcopy src) p q c -> mtest src p q c by apply: h.
rewrite /mcopy.
apply: (@ifold_ind _ (fun m => forall p q c, mtest m p q c -> mtest src p q c));
    last by move=> p q c; rewrite mkemptyP.
move=> i a ha.
apply: (@ifold_ind _ (fun m => forall p q c, mtest m p q c -> mtest src p q c))
    => // k b hb.
by apply: hstep.
Qed.

(* THE CARRY IS THE SOURCE ITSELF.  Copying it into a map of its own was      *)
(* tried and is far worse: it allocates a fresh 6.5 GB map and writes 812     *)
(* million words into it at every level.                                      *)
Definition prepass (src : rmap) : rmap :=
  ifold nhn 0%uint63 (fun k d => prepmv k src d) src.

End Pre.
