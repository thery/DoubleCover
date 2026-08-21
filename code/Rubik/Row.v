(* =========================================================================  *)
(*  Row.v -- one row of the upper bound: its members, and each as a bit.      *)
(* =========================================================================  *)

(* A row is the set of positions whose summary is solved after a fixed        *)
(* position p is played first: every w with p * w in H, where H is generated  *)
(* by U, D and the four half turns.  It has 8! * 8! * 4! / 2 members, and     *)
(* the whole cube splits into 2 217 093 120 rows.                             *)
(*                                                                            *)
(* The upper bound for a row is that every member is within twenty moves, and *)
(* it is proved by marking a bit for each member the search or the prepass    *)
(* reaches and finding no bit left clear.  This file says which bit a member  *)
(* is, and it is the only place where that correspondence is settled.         *)
(*                                                                            *)
(* THE LAYOUT IS hcoset's, because it is what makes the prepass fast.  A page *)
(* is one corner permutation.  Inside a page a GROUP of twenty four bits is a *)
(* PAIR of outer edge permutations -- the two that differ by exchanging the   *)
(* cubies 0 and 1 -- and the twenty four bits are the twenty four middle      *)
(* permutations, the twelve even ones low and the twelve odd ones high.       *)
(* Which member of the pair a bit means is settled by parity and so costs     *)
(* nothing, which is what makes the pair a group and the group a machine word.*)
(*                                                                            *)
(* Everything is a Variable: this file compiles with no table at all.  The    *)
(* four small tables are what ocaml/rubik_row.ml already builds.              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the shape of a row -------------------------------------------------- *)

Definition npagei  : int := 40320%uint63.   (* corner permutations            *)
Definition ngroupi : int := 20160%uint63.   (* pairs of outer edge perms      *)
Definition nbiti   : int := 24%uint63.      (* middle permutations            *)
Definition nhalfi  : int := 12%uint63.      (* of one parity                  *)

Definition rowsize : int := 19508428800%uint63.

(* SIZES ARE int63 AND NEVER nat: 19 508 428 800 in unary does not exist.     *)
Lemma rowsizeE : rowsize = Uint63.mul (Uint63.mul npagei ngroupi) nbiti.
Proof. by vm_compute. Qed.

(* ---- walking a range of int63 -------------------------------------------- *)

(* The walk HSweep.v uses, and for the same reason: a bool at each of n       *)
(* consecutive ints, with advn saying where the walk stands after k steps.    *)
(* Reading a step off it then costs no arithmetic, and the checks below are   *)
(* all of this shape.                                                         *)

Fixpoint iter (n : nat) (x : int) (f : int -> bool) : bool :=
  if n is n1.+1 then f x && iter n1 (Uint63.add x 1%uint63) f else true.

Fixpoint advn (n : nat) (x : int) : int :=
  if n is n1.+1 then advn n1 (Uint63.add x 1%uint63) else x.

Lemma iterP n x f k : (k < n)%N -> iter n x f -> f (advn k x).
Proof.
elim: n x k => [|n ih] x [|k] //= kn /andP[fx it] //.
by apply: ih.
Qed.

Lemma to_nat_advn n x : to_nat (advn n x) = (to_nat x + n) %% nwB.
Proof.
elim: n x => [x|n ih x] /=.
  by rewrite addn0 modn_small // to_nat_bounded.
by rewrite ih to_nat_addW to_nat_1 modnDml addn1 addSn addnS.
Qed.

Lemma advn0K x : advn (to_nat x) 0%uint63 = x.
Proof.
apply: to_nat_inj; rewrite to_nat_advn to_nat_0 add0n.
by rewrite modn_small // to_nat_bounded.
Qed.

(* one step of the walk, from either end                                      *)
Lemma advnS j x :
  Uint63.add (advn j x) 1%uint63 = advn j (Uint63.add x 1%uint63).
Proof. by elim: j x => [|j ih] x //=; rewrite ih. Qed.

(* where the walk stands after i steps, as a number                           *)
Lemma to_nat_advn0 i : (i < nwB)%N -> to_nat (advn i 0%uint63) = i.
Proof. by move=> h; rewrite to_nat_advn to_nat_0 add0n modn_small. Qed.

(* the form the checks are used in: a walk from nought settles every int the  *)
(* walk is long enough to reach                                               *)
Lemma iter_at n f x : iter n 0%uint63 f -> (to_nat x < n)%N -> f x.
Proof. by move=> hi hx; have := iterP hx hi; rewrite advn0K. Qed.

(* ---- two int63 facts about small numbers --------------------------------- *)

(* A parity is nought or one, and that is all that is ever needed of it: the  *)
(* four cases of an exclusive or are then a computation.                      *)
Lemma int_lt2 a : (to_nat a < 2)%N -> a = 0%uint63 \/ a = 1%uint63.
Proof.
move=> aL; case: (to_nat a =P 0) => [h0|h0].
  by left; apply: to_nat_inj; rewrite h0 to_nat_0.
right; apply: to_nat_inj; rewrite to_nat_1.
by case: (to_nat a) h0 aL => [|[|]].
Qed.

Lemma lxor_lt2 a b : (to_nat a < 2)%N -> (to_nat b < 2)%N ->
  (to_nat (Uint63.lxor a b) < 2)%N.
Proof.
by case/int_lt2 => ->; case/int_lt2 => ->; vm_compute.
Qed.

Lemma lxorK2 a b : (to_nat a < 2)%N -> (to_nat b < 2)%N ->
  Uint63.lxor (Uint63.lxor a b) b = a.
Proof.
by case/int_lt2 => ->; case/int_lt2 => ->; vm_compute.
Qed.

Lemma to_nat_two : to_nat 2%uint63 = 2%N.
Proof. by vm_compute. Qed.

(* n = 2 g + p, with p nought or one: the number that a group and a parity    *)
(* make between them, and its size.  Everything below takes it apart again    *)
(* with the ordinary division, never with bits.                               *)
Lemma to_nat_mul2D a b :
  (to_nat a * 2 + to_nat b < nwB)%N ->
  to_nat (Uint63.add (Uint63.mul a 2%uint63) b) = (to_nat a * 2 + to_nat b)%N.
Proof.
(* NEITHER SIDE GOAL MAY BE LEFT TO //: what done would evaluate here is      *)
(* nwB, which is 2 ^ 63 in unary and does not come back.                      *)
move=> hb.
have hlt : (to_nat a * to_nat 2%uint63 < nwB)%N.
  by rewrite to_nat_two; apply: leq_ltn_trans hb; apply: leq_addr.
have hm : to_nat (Uint63.mul a 2%uint63) = (to_nat a * 2)%N.
  by rewrite (@to_nat_mul _ _ hlt) to_nat_two.
have h2 : (to_nat (Uint63.mul a 2%uint63) + to_nat b < nwB)%N by rewrite hm.
by rewrite (@to_nat_add _ _ h2) hm.
Qed.

Section Row.

(* ---- the four small tables ----------------------------------------------  *)

(* An outer edge permutation is numbered so that the pair {q, q with the two  *)
(* cubies 0 and 1 exchanged} is {2k, 2k+1}, and so that the low bit is the    *)
(* PARITY.  Two things follow and the prepass needs both: a move sends a pair *)
(* to a pair, because exchanging two cubies before a move is the same as      *)
(* exchanging them after it; and the parity says which member of a pair a bit *)
(* means, so the pair is one group and nothing is lost.                       *)
Variable e8num e8inv : arr.         (* rank <-> number, 40320 each            *)

(* A middle permutation gets a bit, the even ones taking 0..11 and the odd    *)
(* ones 12..23, an odd one sitting where the even one it comes from by F2 is. *)
(* That makes F2 the exchange of the two halves and nothing else.             *)
Variable e4bit e4of : arr.          (* rank <-> bit, 24 each                  *)

(* the parity of a permutation, by rank                                       *)
Variable par8 : arr.
Variable par4 : arr.

(* ---- a member, as a place ------------------------------------------------ *)

(* A member of a row is three permutations: the eight corners, the eight      *)
(* edges outside the middle layer, and the four inside it.  They are given    *)
(* here by their ranks.                                                       *)
Definition memb := (int * int * int)%type.

Definition mcp (x : memb) : int := let: (c, _, _) := x in c.
Definition mud (x : memb) : int := let: (_, u, _) := x in u.
Definition mmp (x : memb) : int := let: (_, _, m) := x in m.

(* The three ranks are in range, and they agree on parity -- which is why a   *)
(* row has 8! * 8! * 4! / 2 members and not more.                             *)
Definition membok (x : memb) : bool :=
  [&& (mcp x <? npagei)%uint63, (mud x <? npagei)%uint63,
      (mmp x <? nbiti)%uint63 &
      (PArray.get par8 (mcp x) =?
         Uint63.lxor (PArray.get par8 (mud x))
                     (PArray.get par4 (mmp x)))%uint63].

(* where a member stands: its page, its group, and its bit.  Halving the      *)
(* number is what puts the two of a pair in one group.                        *)
Definition place (x : memb) : int * int * int :=
  (mcp x,
   Uint63.div (PArray.get e8num (mud x)) 2%uint63,
   PArray.get e4bit (mmp x)).

(* and back.  The bit names the middle permutation and the group names a pair *)
(* of outer ones; which of the pair is meant is settled by parity, and the    *)
(* numbering carries the parity in its last place.                            *)
Definition unplace (pg gr bt : int) : memb :=
  let mp := PArray.get e4of bt in
  let p := Uint63.lxor (PArray.get par8 pg) (PArray.get par4 mp) in
  (pg, PArray.get e8inv (Uint63.add (Uint63.mul gr 2%uint63) p), mp).

(* ---- what the four tables have to satisfy -------------------------------- *)

(* The layout is a bijection only if the tables are the right ones, and what  *)
(* they have to be is a COMPUTATION, one walk over each: forty thousand       *)
(* entries and twenty four.  Nothing here is about the cube -- these are      *)
(* facts about six little arrays.                                             *)

(* The bounds as nats are the bounds themselves, read over.  There is then    *)
(* nothing to bridge when a check is used and no numeral in sight, which is   *)
(* what keeps a forty thousand entry walk out of unary arithmetic.            *)
Definition npagen : nat := to_nat npagei.
Definition ngroupn : nat := to_nat ngroupi.
Definition nbitn : nat := to_nat nbiti.

(* the numbering of the outer edge permutations: it lands in range, its last  *)
(* place is the parity, and it undoes and is undone by e8inv                  *)
Definition e8ok : bool :=
  iter npagen 0%uint63 (fun u =>
    [&& (PArray.get e8num u <? npagei)%uint63,
        (Uint63.mod (PArray.get e8num u) 2 =? PArray.get par8 u)%uint63,
        (PArray.get e8inv (PArray.get e8num u) =? u)%uint63,
        (PArray.get e8inv u <? npagei)%uint63 &
        (PArray.get e8num (PArray.get e8inv u) =? u)%uint63]).

(* the same for the twenty four middle permutations and their bits            *)
Definition e4ok : bool :=
  iter nbitn 0%uint63 (fun m =>
    [&& (PArray.get e4bit m <? nbiti)%uint63,
        (PArray.get e4of (PArray.get e4bit m) =? m)%uint63,
        (PArray.get e4of m <? nbiti)%uint63,
        (PArray.get e4bit (PArray.get e4of m) =? m)%uint63 &
        (PArray.get par4 m <? 2)%uint63]).

Hypothesis he8 : e8ok.
Hypothesis he4 : e4ok.

(* ---- what has to be true of all this ------------------------------------- *)

(* These three are the whole content of the layout, and nothing else in the   *)
(* development may look inside place or unplace.                              *)

Definition inrange (pg gr bt : int) : bool :=
  [&& (pg <? npagei)%uint63, (gr <? ngroupi)%uint63 & (bt <? nbiti)%uint63].

(* A numeral is looked at exactly here, and by going through of_nat rather    *)
(* than by computing a unary number: a page is two groups, which is all the   *)
(* arithmetic the layout needs, and a page number fits in a word.             *)
Lemma npagenE : npagen = 40320%N.
Proof.
have h : (40320 < nwB)%N by apply: (@ltn_nwB 16).
rewrite /npagen.
have -> : npagei = Uint63.of_nat 40320 by vm_compute.
by rewrite (@of_natK 40320 h).
Qed.

Lemma ngroupnE : ngroupn = 20160%N.
Proof.
have h : (20160 < nwB)%N by apply: (@ltn_nwB 15).
rewrite /ngroupn.
have -> : ngroupi = Uint63.of_nat 20160 by vm_compute.
by rewrite (@of_natK 20160 h).
Qed.

Lemma npage_group : npagen = (ngroupn * 2)%N.
Proof. by rewrite npagenE ngroupnE. Qed.

Lemma npagen_nwB : (npagen < nwB)%N.
Proof. by rewrite npagenE; apply: (@ltn_nwB 16). Qed.

Lemma ltn_npagei x : (x <? npagei)%uint63 -> (to_nat x < npagen)%N.
Proof. by move=> h; apply/nltbP. Qed.

Lemma ltn_ngroupi x : (x <? ngroupi)%uint63 -> (to_nat x < ngroupn)%N.
Proof. by move=> h; apply/nltbP. Qed.

Lemma ltn_nbiti x : (x <? nbiti)%uint63 -> (to_nat x < nbitn)%N.
Proof. by move=> h; apply/nltbP. Qed.

(* the two checks, at one entry                                               *)
Lemma e8at u : (u <? npagei)%uint63 ->
  [&& (PArray.get e8num u <? npagei)%uint63,
      (Uint63.mod (PArray.get e8num u) 2 =? PArray.get par8 u)%uint63,
      (PArray.get e8inv (PArray.get e8num u) =? u)%uint63,
      (PArray.get e8inv u <? npagei)%uint63 &
      (PArray.get e8num (PArray.get e8inv u) =? u)%uint63].
Proof. by move=> h; apply: iter_at he8 (ltn_npagei h). Qed.

Lemma e4at m : (m <? nbiti)%uint63 ->
  [&& (PArray.get e4bit m <? nbiti)%uint63,
      (PArray.get e4of (PArray.get e4bit m) =? m)%uint63,
      (PArray.get e4of m <? nbiti)%uint63,
      (PArray.get e4bit (PArray.get e4of m) =? m)%uint63 &
      (PArray.get par4 m <? 2)%uint63].
Proof. by move=> h; apply: iter_at he4 (ltn_nbiti h). Qed.

(* a parity, from either table, is nought or one -- the outer one because it  *)
(* is the last place of the number                                            *)
Lemma par8_lt2 u : (u <? npagei)%uint63 -> (to_nat (PArray.get par8 u) < 2)%N.
Proof.
move=> h; case/and5P: (e8at h) => _ /eqP <- _ _ _.
by rewrite to_nat_mod to_nat_two ltn_mod.
Qed.

Lemma par4_lt2 m : (m <? nbiti)%uint63 -> (to_nat (PArray.get par4 m) < 2)%N.
Proof.
by move=> h; case/and5P: (e4at h) => _ _ _ _ /nltbP; rewrite to_nat_two.
Qed.

(* a place is in range                                                        *)
Lemma place_range x pg gr bt :
  membok x -> place x = (pg, gr, bt) -> inrange pg gr bt.
Proof.
case/and4P => hc hu hm _ [<- <- <-].
case/and5P: (e8at hu) => hn _ _ _ _.
case/and5P: (e4at hm) => hb _ _ _ _.
apply/and3P; split => //.
apply/nltbP; rewrite to_nat_div to_nat_two -/ngroupn ltn_divLR // -npage_group.
by apply: ltn_npagei.
Qed.

(* reading a place back gives the member that was put there                   *)
Lemma unplace_place x pg gr bt :
  membok x -> place x = (pg, gr, bt) -> unplace pg gr bt = x.
Proof.
case: x => [[c u] m] /and4P[hc hu hm /eqP hp] [<- <- <-].
case/and5P: (e8at hu) => _ /eqP hmod /eqP hinv _ _.
case/and5P: (e4at hm) => _ /eqP hof _ _ _.
have h8 : (to_nat (PArray.get par8 u) < 2)%N by apply: par8_lt2.
have h4 : (to_nat (PArray.get par4 m) < 2)%N by apply: par4_lt2.
rewrite /unplace /= hof.
have -> : Uint63.lxor (PArray.get par8 c) (PArray.get par4 m)
        = PArray.get par8 u.
  by rewrite hp (lxorK2 h8 h4).
by rewrite -hmod -int_add_mod hinv.
Qed.

(* and every place in range comes from a member                               *)
Lemma place_unplace pg gr bt :
  inrange pg gr bt ->
  membok (unplace pg gr bt) /\ place (unplace pg gr bt) = (pg, gr, bt).
Proof.
case/and3P => hpg hgr hbt.
rewrite /unplace /membok /place /=.
set mp := PArray.get e4of bt.
set p := Uint63.lxor (PArray.get par8 pg) (PArray.get par4 mp).
set n := Uint63.add (Uint63.mul gr 2%uint63) p.
case/and5P: (e4at hbt) => _ _ hof /eqP hbit _.
have hp2 : (to_nat p < 2)%N.
  by apply: lxor_lt2; [apply: par8_lt2 | apply: par4_lt2].
have hgrn : (to_nat gr < ngroupn)%N by apply: ltn_ngroupi.
(* the number a group and a parity make, and it is a page number              *)
have hnn : to_nat n = (to_nat gr * 2 + to_nat p)%N.
  apply: to_nat_mul2D.
  apply: (@leq_ltn_trans (ngroupn * 2 + 2)).
    apply: leq_add; last by apply: ltnW.
    by rewrite leq_pmul2r //; apply: ltnW.
  by rewrite ngroupnE; apply: (@ltn_nwB 16).
have hnp : (n <? npagei)%uint63.
  apply/nltbP; rewrite hnn -/npagen npage_group.
  apply: (@leq_trans (to_nat gr * 2 + 2)); first by rewrite ltn_add2l.
  by rewrite -{2}[2%N]mul1n -mulnDl leq_mul2r addn1 hgrn.
(* and taking it apart again gives the group back, and the parity             *)
have hnd : Uint63.div n 2%uint63 = gr.
  apply: to_nat_inj; rewrite to_nat_div to_nat_two hnn.
  by rewrite divnMDl // divn_small // addn0.
have hnm : Uint63.mod n 2%uint63 = p.
  apply: to_nat_inj; rewrite to_nat_mod to_nat_two hnn.
  by rewrite modnMDl modn_small.
case/and5P: (e8at hnp) => _ _ _ hiv /eqP hnv.
(* the outer permutation the number names, and its parity                     *)
have hpu : PArray.get par8 (PArray.get e8inv n) = p.
  by case/and5P: (e8at hiv) => _ /eqP <- _ _ _; rewrite hnv.
split; last by rewrite hnv hnd hbit.
apply/and4P; split => //.
have h8 : (to_nat (PArray.get par8 pg) < 2)%N by apply: par8_lt2.
have h4 : (to_nat (PArray.get par4 mp) < 2)%N by apply: par4_lt2.
by apply/eqP; rewrite hpu /p (lxorK2 h8 h4).
Qed.

(* so the map has exactly one bit for each member.  This one is not a new     *)
(* fact: reading a place back is what makes it one to one.                    *)
Lemma place_inj x y : membok x -> membok y -> place x = place y -> x = y.
Proof.
move=> hx hy hE.
case E: (place y) => [[pg gr] bt].
have Hx := unplace_place hx (etrans hE E).
have Hy := unplace_place hy E.
by rewrite -Hx -Hy.
Qed.

End Row.
