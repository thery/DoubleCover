(* =========================================================================  *)
(*  Phase1.v -- the phase 1 heuristic, its table, and its certificate.        *)
(*                                                                            *)
(*  The flip x slice table Far.v ships today is 2 ^ 24 entries and caps the    *)
(*  heuristic at 9.  Phase 1 -- twist x flip x slice -- caps at 12, which is   *)
(*  what a depth 19 search needs.  The raw space is                           *)
(*                                                                            *)
(*     2187 twist  x  2048 flip  x  495 slice  =  2 217 093 120 states        *)
(*                                                                            *)
(*  The point of this file is to MIMIC ocaml/rubik_par.ml, whose depth 19     *)
(*  run is the computational content of Diameter.v's superflip_far:           *)
(*  104 561 988 516 nodes, 24.0 CPU-hours.                                    *)
(*                                                                            *)
(*  FOLDED by the sixteen symmetries that fix the U/D axis.  They act on the  *)
(*  flip x slice coordinate, so one row per orbit of ranks is enough: the     *)
(*  1 013 760 ranks fall into 64 430 orbits, and a state is read by mapping   *)
(*  its rank to its orbit and its twist through the symmetry that takes the   *)
(*  rank to the orbit representative.  Only 16 of the 48 symmetries act on    *)
(*  the coordinate at all -- a u that moves the UD slice does not -- so the   *)
(*  orbit of a rank is not defined for the other 32.                          *)
(*                                                                            *)
(*     64 430 orbits x 2187 twist  =  140 908 410 entries                     *)
(*     4 bits each, 15 per int63   =    9 393 894 words  =  75 MB             *)
(*     PArray.max_length           =    4 194 303 words                       *)
(*                                                                            *)
(*  so the table is a PArray of 5 PArrays, split on the word index at a       *)
(*  power of two (w >> cwlog), which stays definitional -- the trick Fspar.v's *)
(*  cbits uses.                                                               *)
(*                                                                            *)
(*  THE FOLD ASSUMES NOTHING OF THE THREE TABLES IT READS.  The orbit of a    *)
(*  rank, the symmetry that reaches the representative, and the action on     *)
(*  twists are parameters here, with no property attached: p1checkStep        *)
(*  checks exactly the expression the search reads, so a wrong orbit table    *)
(*  makes the check fail rather than the heuristic unsound.  Fold.v is the    *)
(*  other half, where the check is run at the representatives only and the    *)
(*  symmetries do have to act.                                                *)
(*                                                                            *)
(*  CLAMP.  Entries hold the true distance, capped ABOVE at p1cap + 1 by       *)
(*  stopping the BFS -- never an offset clamped from below.  Storing d - base  *)
(*  and clamping the underflow to 0 reports base for a state that is really    *)
(*  nearer, which OVERstates the distance and can prune a real solution.       *)
(*                                                                            *)
(*  THE TABLE IS GENERATED AND VALIDATED.  bench/p1gen.ml builds it in the     *)
(*  Rocq coordinate in ~2 min and agrees with rubik_par at every BFS level     *)
(*  (4, 50, 592, 7156, 87236, 1043817, 12070278, 124946368, 821605960) and     *)
(*  node for node in the search (2102, 25598, 340658 at depths 12, 13, 14).    *)
(*  Two programs on two different cube models.                                *)
(*                                                                            *)
(*  It is never asked to be CORRECT: p1check0 and p1checkStep make it a local  *)
(*  certificate, so the generator is not in the trusted base.                  *)
(*                                                                            *)
(*  THIS FILE IS ADMIT-FREE.  Print Assumptions on anything in it lists only  *)
(*  the Uint63 and PArray primitives.  srank and the twist move table are     *)
(*  real data, from P1Small.v; what is still missing is the phase 1 table     *)
(*  itself -- 5 chunks, see section 7 -- and the wiring of the search to      *)
(*  carry a twist.                                                            *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
(* Far.v's chain minus Fsmain, so this does not drag in the sixteen
   certificate files *)
Require Import Table Tabi Rubik333 Coordfs Coordfsi Fstab Moves P1Small P1Ts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* =========================================================================  *)
(*  1.  The corner data                                                       *)
(*                                                                            *)
(*  DERIVED from the move tables, not read off a picture of a cube.  A facelet *)
(*  is a corner facelet iff f mod 8 is in {0,2,5,7} (each face is a row major  *)
(*  3x3 with the centre dropped, which is what Coordfs.eprim's {1,3,4,6}       *)
(*  confirms).  Two corner facelets sit on the same cubie iff exactly the same *)
(*  face turns fix them -- a corner lies on 3 of the 6 faces and distinct      *)
(*  corners have distinct face triples, so the eight triples fall out of the   *)
(*  fixed sets.                                                               *)
(*                                                                            *)
(*  THE U/D AXIS IS NOT A FREE CHOICE.  It must be the axis the flip x slice   *)
(*  coordinate already uses, namely the two faces whose quarter turn leaves    *)
(*  the slice alone.  An earlier version put it elsewhere; twist and           *)
(*  flip x slice were then quotients along different axes, their product was   *)
(*  not Kociemba's phase 1 coordinate, and every BFS level came out too large  *)
(*  (6, 71, 810, ... against the correct 4, 50, 592, ...).  Caught by the      *)
(*  generator, whose depth histogram must agree with ocaml/rubik_par.ml's.     *)
(*                                                                            *)
(*  NB two numberings that are easy to confuse: the MOVE GROUP k / 3 and the   *)
(*  FACELET BLOCK f / 8 do not agree.  Move group 3 spins block 5.  The U/D    *)
(*  groups are 0 and 3; the U/D blocks are 0 and 5, and it is the blocks that  *)
(*  carry the stickers below.                                                 *)
(* =========================================================================  *)

(* 3 ^ 7 -- the eighth orientation is forced, the sum being 0 mod 3 *)
Definition ntwist := 2187.

(* the U/D sticker of each corner, one per cubie *)
Definition cprim : seq nat := [:: 0; 2; 5; 7; 40; 42; 45; 47]%N.

(* the three stickers of each corner, U/D one first.  The cyclic order of the
   other two is NOT free.  All 2 ^ 8 choices give the same 2187 value quotient,
   which is what an earlier comment here claimed, but the DIGIT ALGEBRA needs
   a coherent order: corner orientation is an action only when the 3-cycle
   rotating every corner in place commutes with every move, i.e. when cubcP
   holds.  Exactly 2 of the 256 qualify -- the two chiralities -- and this is
   the smaller mask.  Measured by bench/p1gen.ml, which now derives it rather
   than sorting.  The AXIS is not free either -- see the warning above. *)
Definition ctrip : seq (nat * nat * nat) :=
  [:: ( 0,  8, 34); ( 2, 32, 26); ( 5, 16, 10); ( 7, 24, 18);
      (40, 15, 21); (42, 23, 29); (45, 39, 13); (47, 31, 37)]%N.

(* NB: qualified Uint63 functions throughout rather than the << and >> and
   .[ ] notations -- fingroup owns << _ >> for the generated subgroup, so the
   shift notation does not survive an all_fingroup import. *)
Definition cmask : int := Eval vm_compute in
  foldr (fun f a => Uint63.lor a (Uint63.lsl 1%uint63 (of_nat f))) 0%uint63
        cprim.

(* is facelet x a U/D sticker?  the bitmask form, as Coordfs's bit pmask *)
Definition bitc (x : int) : bool :=
  negb (Uint63.eqb (Uint63.land cmask (Uint63.lsl 1%uint63 x)) 0%uint63).

(* Three levels, exactly as Coordfs / Coordfsi do it for flip x slice:
   arrays (what the search runs), lists (the intermediate), permutations (what
   the proofs talk about).  The bridges are ectwistiE and ctwisttE below,
   mirroring Coordfsi.ecoordiE and Coordfsi.coordtE.

   In all three, u is the INVERSE, so u at slot s is the facelet occupying s. *)

Definition corienti (u : arr) (t : nat * nat * nat) : nat :=
  let: (c0, c1, c2) := t in
  if bitc (PArray.get u (of_nat c0)) then 0%N
  else if bitc (PArray.get u (of_nat c1)) then 1%N else 2%N.

Definition corientt (u : seq nat) (t : nat * nat * nat) : nat :=
  let: (c0, c1, c2) := t in
  if nth 0%N u c0 \in cprim then 0%N
  else if nth 0%N u c1 \in cprim then 1%N else 2%N.

(* base 3 over the first seven corners; the eighth is forced *)
Definition ectwisti (u : arr) : int :=
  foldr (fun t x => Uint63.add (Uint63.mul x 3%uint63) (of_nat (corienti u t)))
        0%uint63 (take 7 ctrip).

Definition ectwistt (u : seq nat) : int :=
  foldr (fun t x => Uint63.add (Uint63.mul x 3%uint63) (of_nat (corientt u t)))
        0%uint63 (take 7 ctrip).

Definition ctwisti (a : arr) : int := ectwisti (inv_tabi 47 a).
Definition ctwistt (t : seq nat) : int := ectwistt (inv_tab 47 t).

(* acttw is COMPUTED from the move, exactly as Coordfs.actfs is, and NOT a
   generated table.  That is the whole point: coordfs (g * m) = actfs (coordfs
   g) m needs no data, and the twist must be able to say the same.  A table
   would make coordtw_step a statement about emitted numbers.

   The corner analogue of Coordfs's epos / eprimf / src / xbit: a corner
   facelet belongs to a cubie (cpos) and sits in one of its three slots
   (cslot), the U/D slot being slot 0.  A move sends the U/D slot of corner p
   to some slot of some corner, and that pair IS the action on the digit. *)

(* the 24 corner facelets, grouped by cubie, U/D sticker first *)
Definition cflat : seq nat :=
  flatten [seq [:: t.1.1; t.1.2; t.2] | t <- ctrip].

Definition cpos  (f : facelet) : nat := (index (f : nat) cflat) %/ 3.
Definition cslot (f : facelet) : nat := (index (f : nat) cflat) %% 3.

(* the U/D slot of corner position p *)
Definition cprimf (p : nat) : facelet := inord (nth 0%N cprim p).

(* which corner arrives at p, and how far it is rotated when it gets there *)
Definition csrc   (m : {perm facelet}) (p : nat) : nat := cpos  (m^-1 (cprimf p)).
Definition cdelta (m : {perm facelet}) (p : nat) : nat := cslot (m^-1 (cprimf p)).

(* =========================================================================  *)
(*  Base 3 digits -- the analogue of Coordfs's packn / nbit                    *)
(*                                                                            *)
(*  Everything here is on nat.  The values are below 3 ^ 7 = 2187, nowhere    *)
(*  near overflow, so the int63 side is reached once at the end rather than   *)
(*  carried through every lemma.                                             *)
(* =========================================================================  *)

Fixpoint pack3n (k : nat) (f : nat -> nat) : nat :=
  if k is k1.+1 then pack3n k1 f + (f k1 %% 3) * 3 ^ k1 else 0.

Definition dig3n (x j : nat) : nat := (x %/ 3 ^ j) %% 3.

Lemma pack3n_lt k f : (pack3n k f < 3 ^ k)%N.
Proof.
elim: k => [|k IH]; first by rewrite expn0.
have h3 : (f k %% 3 < 3)%N by rewrite ltn_mod.
apply: leq_ltn_trans (_ : pack3n k f + 2 * 3 ^ k < _)%N.
  by rewrite leq_add2l leq_mul2r -ltnS h3 orbT.
have h : (3 ^ k.+1 = 3 ^ k + 2 * 3 ^ k)%N.
  by rewrite expnS (_ : 3 = 1 + 2)%N // mulnDl mul1n.
by rewrite h ltn_add2r.
Qed.

Lemma dig3n_pack3n k f j : (j < k)%N -> dig3n (pack3n k f) j = f j %% 3.
Proof.
elim: k j => [//|k IH] j; rewrite ltnS leq_eqVlt => /orP[/eqP->|jL].
  rewrite /dig3n /= addnC divnMDl ?expn_gt0 //.
  by rewrite divn_small ?pack3n_lt // addn0 modn_mod.
have HH : (j <= k)%N := ltnW jL.
rewrite /dig3n /= divnDr; last by apply: dvdn_mull; apply: dvdn_exp2l.
(* the third k is the exponent; the first two are pack3n k f and f k *)
rewrite -{3}(subnK HH) expnD mulnA mulnK ?expn_gt0 //.
have h3 : (3 %| (f k %% 3) * 3 ^ (k - j))%N.
  by apply: dvdn_mull; rewrite -{1}(expn1 3) dvdn_exp2l // subn_gt0.
rewrite -modnDmr (eqP h3) addn0.
by move: (IH _ jL); rewrite /dig3n => ->.
Qed.

(* pack3n only reads f below k, so agreeing there is enough.  This is all the
   assembly needs -- injectivity of pack3n never comes up, because both sides
   of coordtwM are packed and the proof compares the digit functions. *)
Lemma pack3n_ext k f g :
  (forall j, (j < k)%N -> f j = g j) -> pack3n k f = pack3n k g.
Proof.
elim: k => [//|k IH] h /=.
rewrite IH; last by move=> j jL; apply: h; apply: ltnW.
by rewrite (h k (ltnSn k)).
Qed.

(* Every int63 step below needs a `_ < nwB` side condition, and leaving one to
   // is the unary trap -- 2 ^ 63 in successors.  Proved once here, against a
   bound vm_compute can actually check, and used by name thereafter. *)
Lemma small_nwB n : (n < 2 ^ 20)%N -> (n < nwB)%N.
Proof.
move=> nL; apply: leq_trans nL _.
by rewrite nwB_pow leq_exp2l.
Qed.

(* the foldr that coordtw and acttw are written with, read as pack3n.  The
   accumulator has to be generalised: iota 0 n.+1 peels its LAST element, so
   the induction step changes acc rather than n's contribution.  The bound is
   exactly preserved -- it is the same number on both sides. *)
Lemma foldr3E f n (acc : int) :
  (forall p, (f p < 3)%N) ->
  (to_nat acc * 3 ^ n + pack3n n f < 2 ^ 20)%N ->
  to_nat (foldr (fun p x => Uint63.add (Uint63.mul x 3%uint63) (of_nat (f p)))
                acc (iota 0 n))
  = (to_nat acc * 3 ^ n + pack3n n f)%N.
Proof.
move=> f3; elim: n acc => [acc _|n IH acc hb].
  by rewrite /= expn0 muln1 addn0.
have fn3 : (f n %% 3 = f n)%N by apply/modn_small/f3.
have hstep : (to_nat acc * 3 + f n <= to_nat acc * 3 ^ n.+1 + pack3n n.+1 f)%N.
  apply: leq_add.
    by rewrite leq_mul2l expnS leq_pmulr ?expn_gt0 ?orbT.
  rewrite /= fn3; apply: leq_trans (leq_addl _ _).
  by apply: leq_pmulr; rewrite expn_gt0.
have hb' : (to_nat acc * 3 + f n < nwB)%N.
  by apply: small_nwB; apply: leq_ltn_trans hstep hb.
have h3i : to_nat 3%uint63 = 3%N by vm_compute.
have hmb : (to_nat acc * to_nat 3%uint63 < nwB)%N.
  rewrite h3i; apply: small_nwB.
  by apply: leq_ltn_trans hb; apply: leq_trans hstep; rewrite leq_addr.
have hm : to_nat (Uint63.mul acc 3%uint63) = (to_nat acc * 3)%N.
  by rewrite to_nat_mul // h3i.
have hfnw : (f n < nwB)%N by apply: small_nwB; apply: leq_trans (f3 n) _.
have hacc : to_nat (Uint63.add (Uint63.mul acc 3%uint63) (of_nat (f n)))
          = (to_nat acc * 3 + f n)%N.
  rewrite to_nat_add; last by rewrite hm of_natK.
  by rewrite hm of_natK.
(* the same algebra serves the IH's bound and the final step *)
have heq : ((to_nat acc * 3 + f n) * 3 ^ n + pack3n n f
            = to_nat acc * 3 ^ n.+1 + pack3n n.+1 f)%N.
  rewrite mulnDl -mulnA -expnS /= fn3.
  by rewrite -addnA [(f n * 3 ^ n + _)%N]addnC addnA.
have -> : iota 0 n.+1 = iota 0 n ++ [:: n].
  by rewrite -addn1 iotaD add0n.
rewrite foldr_cat.
(* acc must be given EXPLICITLY: IH's bound mentions it too, so rewrite
   cannot pin it from the left-hand side alone. *)
set acc' := foldr _ acc [:: n].
have haccE : acc' = Uint63.add (Uint63.mul acc 3%uint63) (of_nat (f n)) by [].
rewrite (IH acc'); last by rewrite haccE hacc heq.
by rewrite haccE hacc heq.
Qed.

(* THE PROOF SIDE.  Computed from the move, so coordtwM is a theorem about the
   moves and not about emitted numbers. *)
(* the eighth orientation is not stored: the eight sum to 0 mod 3 *)
Definition dig8 (x : int) : nat :=
  (3 - (foldr (fun q a => a + dig3n (to_nat x) q) 0 (iota 0 7)) %% 3) %% 3.

Definition dign (x : int) (p : nat) : nat :=
  if p == 7 then dig8 x else dig3n (to_nat x) p.

(* digit p of the moved coordinate: the corner that arrives at p, rotated *)
(* cdelta is SUBTRACTED: corientg counts how far one must turn to REACH the
   U/D sticker, so it runs opposite to cslot.  Measured, not guessed --
   corientg g p = (3 - cslot (g^-1 (cprimf p))) %% 3, 0 mismatches in 800 008,
   and this law 0 in 1 400 007. *)
Definition acttwd (x : int) (m : {perm facelet}) (p : nat) : nat :=
  (dign x (csrc m p) + 3 - cdelta m p) %% 3.

Definition acttw (x : int) (m : {perm facelet}) : int :=
  foldr (fun p a => Uint63.add (Uint63.mul a 3%uint63) (of_nat (acttwd x m p)))
        0%uint63 (iota 0 7).

Lemma acttwE x m : to_nat (acttw x m) = pack3n 7 (acttwd x m).
Proof.
rewrite /acttw foldr3E ?to_nat_0 ?mul0n ?add0n //.
  by move=> p; rewrite /acttwd ltn_mod.
by apply: leq_trans (pack3n_lt 7 _) _.
Qed.

(* THE TABLE LEVEL.  acttw mentions m^-1 on a {perm facelet}, which no compute
   tactic can touch, so acttwiE cannot be checked against it directly -- the
   same wall moves_cubcP hit.  acttwt says the same thing about a move TABLE,
   where everything is nat and int63, and acttwtE bridges the two. *)

Definition cposn (f : nat) : nat := (index f cflat %/ 3)%N.
Definition cslotn (f : nat) : nat := (index f cflat %% 3)%N.

Definition csrct (mt : seq nat) (p : nat) : nat :=
  cposn (nth 0%N (inv_tab 47 mt) (nth 0%N cprim p)).
Definition cdeltat (mt : seq nat) (p : nat) : nat :=
  cslotn (nth 0%N (inv_tab 47 mt) (nth 0%N cprim p)).

Definition acttwdt (x : int) (mt : seq nat) (p : nat) : nat :=
  (dign x (csrct mt p) + 3 - cdeltat mt p) %% 3.

Definition acttwt (x : int) (mt : seq nat) : int :=
  foldr (fun p a => Uint63.add (Uint63.mul a 3%uint63) (of_nat (acttwdt x mt p)))
        0%uint63 (iota 0 7).

Lemma acttwtE x mt : tab_ok 47 mt -> acttw x (pt 47 mt) = acttwt x mt.
Proof.
move=> mok; have iok := tab_ok_inv mok.
have hfold (F G : nat -> int -> int) l :
    (forall p y, F p y = G p y) -> foldr F 0%uint63 l = foldr G 0%uint63 l.
  by move=> h; elim: l => //= q l ->; rewrite h.
rewrite /acttw /acttwt; apply: hfold => p y.
(* suff, not congr and not f_equal2: both have to unify against the int63
   addition and neither returns.  suff never touches it. *)
suff -> : acttwd x (pt 47 mt) p = acttwdt x mt p by [].
rewrite /acttwd /acttwdt /csrc /cdelta /csrct /cdeltat /cprimf.
have hcpl : (nth 0%N cprim p < 48)%N.
  have hall : all (fun q => (nth 0%N cprim q < 48)%N) (iota 0 8) by vm_compute.
  have [pL|pL] := ltnP p 8.
    by have := allP hall p; rewrite mem_iota /= pL => /(_ isT).
  by rewrite nth_default // (_ : seq.size cprim = 8).
rewrite (ptV mok) ptE; last exact: iok.
rewrite (inordK hcpl).
have hX : (nth 0%N (inv_tab 47 mt) (nth 0%N cprim p) < 48)%N.
  have /and3P[/eqP sz /allP hall _] := iok.
  by apply: hall; rewrite mem_nth // sz.
by rewrite /cpos /cslot /cposn /cslotn (inordK hX).
Qed.

(* THE COMPUTATION SIDE.  {perm facelet} is a 48-element finfun that neither
   vm_compute nor native_compute can touch, so the check cannot run acttw.
   It runs this instead -- a 2187 x 18 table, tiny next to the phase 1 table --
   and acttwiE ties the two together by a finite check over 39 366 entries.
   Exactly Fstab's actd / actf / actfE split, one level up. *)

(* the length as an int63 LITERAL: of_nat (ntwist * 18) is 39 366 successors,
   built every time the array is forced.  Same reason nfsi is a literal. *)
Definition ntwmovei : int := 39366%uint63.     (* ntwist * 18                *)

(* P1Small.v's 39 366 numbers become an array here, and nowhere else.  Same
   fold as FsTable.mkarr, with the length and the default given: the entries
   are twist coordinates, so the default 0 is a twist coordinate too. *)
Definition mkarr (n d : int) (l : seq int) : arr :=
  (fix go (a : arr) (i : int) (l : seq int) {struct l} : arr :=
     if l is x :: l' then go (PArray.set a i x) (i + 1)%uint63 l' else a)
    (PArray.make n d) 0%uint63 l.

Definition twmove : arr := mkarr ntwmovei 0%uint63 twmove_data. (* GENERATED *)

(* THE MOVE INDEX AS AN int63.  acttwi takes a nat, so every call runs
   of_nat on it, and p1stepFr's inner loop calls it eighteen times for every
   checked packed value.  MEASURED vm, 100 000 iterations: the eighteen move
   loop costs 15.7 us with of_nat against 1.18 us with the indices already
   int63 -- 13.3x, and actfsr converts a second time on top.

   acttwi is DEFINED FROM acttwii rather than repeating its body: with two
   copies the two sides of acttwiiE are only convertible after delta, and the
   `by []' closing it then evaluates twmove -- 39 366 entries -- which is
   where a whole Phase1.v build went.  Factored, the lemma is one delta. *)
Definition acttwii (x k : int) : int :=
  PArray.get twmove (Uint63.add (Uint63.mul x 18%uint63) k).

Definition acttwi (x : int) (k : nat) : int := acttwii x (of_nat k).

(* /acttwi, not `by []': nothing is left to done, which on these tables
   reaches for the arrays and does not come back *)
Lemma acttwiiE x k : acttwii x (of_nat k) = acttwi x k.
Proof. by rewrite /acttwi. Qed.

(* THE FINITE CHECK.  2187 twists x 18 moves, both sides computable: acttwi
   reads the emitted array, acttwt runs the digit formula on the move TABLE.
   Measured in OCaml before it was proved: 0 mismatches out of 39 366
   (bench/p1gen.ml, mode `acttwi'). *)

(* BOTH LOOP INVARIANTS ARE HOISTED, and the check does not run without it:
   acttwt as written rebuilds inv_tab 47 mt for each of the seven digits and
   again for each of the 2187 twists, and dign runs a division on a UNARY nat.
   Straight `vm_compute' on the unhoisted check ran 667 s.  Same trick, and
   the same reason, as p1mdata in section 5. *)

(* the move's contribution: which corner arrives at p, and how far it is
   turned -- seven pairs per move, computed once for all twists *)
Definition acttwm (mt : seq nat) : seq (nat * nat) :=
  [seq (csrct mt p, cdeltat mt p) | p <- iota 0 7].

Definition acttwms : seq (seq (nat * nat)) := [seq acttwm mt | mt <- mtabs].

(* the nine digits of x -- eight corners and the slot 8 that cposn returns for
   a facelet that is not a corner facelet at all -- computed once for all
   moves.  NINE, not eight, because csrct is an index divided by three and the
   index of a missing facelet is the size of the list. *)
Definition twdigs (x : int) : seq nat := [seq dign x p | p <- iota 0 9].

Definition acttwtd (d : seq nat) (l : seq (nat * nat)) : int :=
  foldr (fun q a => Uint63.add (Uint63.mul a 3%uint63)
                               (of_nat ((nth 0%N d q.1 + 3 - q.2) %% 3)))
        0%uint63 l.

(* foldr over a map, so the hoisted form and acttwt are the same fold *)
Lemma foldr_map_seq (T R : Type) (F : T -> R -> R) (g : nat -> T)
    (z : R) (l : seq nat) :
  foldr F z [seq g p | p <- l] = foldr (fun p a => F (g p) a) z l.
Proof. by elim: l => //= p l ->. Qed.

(* cposn is an index divided by three, and index returns the size when the
   facelet is absent, so 24 %/ 3 = 8 is the largest value it can take *)
Lemma csrct_lt mt p : (csrct mt p < 9)%N.
Proof.
rewrite /csrct /cposn.
have hsz : seq.size cflat = 24%N by vm_compute.
apply: leq_ltn_trans (_ : (24 %/ 3 < 9)%N) => //.
by rewrite -hsz leq_div2r // index_size.
Qed.

Lemma twdigsE x j : (j < 9)%N -> nth 0%N (twdigs x) j = dign x j.
Proof. by move=> jL; rewrite /twdigs (nth_map_iota _ _ jL). Qed.

Lemma acttwtdE x mt : acttwtd (twdigs x) (acttwm mt) = acttwt x mt.
Proof.
rewrite /acttwtd /acttwm /acttwt foldr_map_seq.
elim: (iota 0 7) => //= p l ->; congr Uint63.add.
by rewrite /acttwdt twdigsE // csrct_lt.
Qed.

(* the three functions the loop runs, split so that the two hoisted arguments
   are evaluated once per twist and not once per (twist, move) *)
Definition acttwiCk (x : int) (d : seq nat) (k : nat) : bool :=
  acttwi x k == acttwtd d (nth [::] acttwms k).

(* AN EQUATION, NOT A DELTA STEP, and this one is worth 168 s.  `rewrite
   /acttwiCk in hk' at the instance x := of_nat (to_nat x) does not return
   inside five minutes, while the same step through this lemma is 0.001 s.
   The conversion itself is free -- `by []' proves this at that very instance
   in 0.003 s -- so what is slow is ssreflect's UNIFICATION of the two forms,
   not the kernel.  Same lesson, and same fix, as p1checkTwE below. *)
Lemma acttwiCkE x d k :
  acttwiCk x d k = (acttwi x k == acttwtd d (nth [::] acttwms k)).
Proof. by []. Qed.

Definition acttwiCx (n : nat) : bool :=
  all (acttwiCk (of_nat n) (twdigs (of_nat n))) (iota 0 18).

Definition acttwiC : bool := all acttwiCx (iota 0 ntwist).

(* EQUATIONS, so that allP never has to unfold a definition against `all' *)
Lemma acttwiCxE n :
  acttwiCx n = all (acttwiCk (of_nat n) (twdigs (of_nat n))) (iota 0 18).
Proof. by []. Qed.

Lemma acttwiCE : acttwiC = all acttwiCx (iota 0 ntwist).
Proof. by []. Qed.

Lemma acttwiCP : acttwiC.
Proof. by vm_compute. Qed.

(* The twist coordinate is seven base 3 digits, so x >= ntwist is not a twist
   coordinate at all and the array has no entry for it -- acttwi would read the
   default.  Hence the bound, which every caller has: it is Dp1_step_of_check's
   twL. *)
Lemma acttwiE x k : (to_nat x < ntwist)%N -> (k < 18)%N ->
  acttwi x k = acttw x (pt 47 (nth [::] mtabs k)).
Proof.
move=> xL kL.
have hmt : seq.size mtabs = 18%N by vm_compute.
have mok : tab_ok 47 (nth [::] mtabs k).
  by apply: (allP mtabs_ok); rewrite mem_nth // hmt.
(* NO `/=' ANYWHERE BELOW.  simpl on a goal mentioning all _ (iota 0 2187)
   unfolds the fixpoint into 2187 conjuncts and does not return; that is why
   the memberships are discharged by add0n / leq0n instead. *)
have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have xM : to_nat x \in iota 0 ntwist by rewrite mem_iota add0n leq0n xL.
have hnth : nth [::] acttwms k = acttwm (nth [::] mtabs k).
  by rewrite /acttwms (nth_map [::]) // hmt.
have hall : all acttwiCx (iota 0 ntwist) by rewrite -acttwiCE; exact: acttwiCP.
have hx := allP hall _ xM; rewrite acttwiCxE in hx.
have hk := allP hx _ kM.
rewrite acttwiCkE to_natK hnth acttwtdE in hk.
by rewrite (eqP hk) (acttwtE _ mok).
Qed.

(* the structured counterpart, for the proofs -- mirrors Coordfs.coordfs, which
   is likewise stated with g^-1 applied to the slot's primary facelet *)
Definition udcol (f : facelet) : bool := (f : nat) \in cprim.

Definition corientg (g : {perm facelet}) (p : nat) : nat :=
  let: (c0, c1, c2) := nth (0, 0, 0)%N ctrip p in
  if udcol (g^-1 (inord c0)) then 0%N
  else if udcol (g^-1 (inord c1)) then 1%N else 2%N.

Definition coordtw (g : {perm facelet}) : int :=
  foldr (fun p x => Uint63.add (Uint63.mul x 3%uint63) (of_nat (corientg g p)))
        0%uint63 (iota 0 7).

(* corientg returns one of 0, 1, 2 by construction *)
Lemma corientg_lt g p : (corientg g p < 3)%N.
Proof.
rewrite /corientg; case: (nth (0, 0, 0)%N ctrip p) => [[c0 c1] c2].
by case: ifP => _ //; case: ifP.
Qed.

(* the coordinate, read as a base 3 packing.  3 ^ 7 = 2187 is far below
   2 ^ 20, so foldr3E's bound is immediate. *)
Lemma coordtwE g : to_nat (coordtw g) = pack3n 7 (fun p => corientg g p).
Proof.
rewrite /coordtw foldr3E ?to_nat_0 ?mul0n ?add0n //.
  exact: corientg_lt.
by apply: leq_trans (pack3n_lt 7 _) _.
Qed.

(* reading a digit back out: what acttw's digi has to agree with *)
Lemma dig_coordtw g q : (q < 7)%N -> dig3n (to_nat (coordtw g)) q = corientg g q.
Proof.
move=> qL; rewrite coordtwE dig3n_pack3n //.
by apply/modn_small/corientg_lt.
Qed.

(* =========================================================================  *)
(*  2.  Re-indexing flip x slice into 1 013 760 consecutive slots             *)
(*                                                                            *)
(*  Coordfs packs flip into bits 0..11 and slice into bits 12..23, so the      *)
(*  packed coordinate ranges over 2 ^ 24 while only 2048 x 495 values occur.   *)
(*  Indexing the class table by the packed value would need 16.7 M words and   *)
(*  therefore chunking; ranking the slice mask instead gives 1 013 760 and one *)
(*  array.  srank is 4096 words, the rank of each 12 bit mask among those with *)
(*  four bits set, or 495 for the ones that cannot occur.                      *)
(* =========================================================================  *)

Definition nflip  := 2048.
(* the number of 12 bit masks with four bits set.  NOT Coordfs.nslice,
   which is 4, the number of slice edges. *)
Definition nsrank := 495.
Definition nfs    := 1013760.   (* nflip * nsrank *)
Definition nmask  := 4096.      (* 2 ^ nedge, the masks srank is indexed by  *)

(* nsrank as an int63 literal, for the same reason ntwmovei is one *)
Definition nsranki : int := 495%uint63.                      (* nsrank      *)
Definition nmaski  : int := 4096%uint63.                     (* 2 ^ 12      *)

(* the rank of each twelve bit mask among those with four bits set, or 495 for
   a mask that cannot occur -- which is also the default, so an index past the
   end reads the same "impossible" value rather than the rank of slice 0. *)
(* `Eval vm_compute in': without it the body of this table IS the cons
   list, and one delta step puts a 67 584 cell TERM in front of any
   tactic that unfolds a lookup -- it does not return.  See fsdtab in
   Farp1.v for the measurement. *)
Definition srank : arr :=                                     (* GENERATED *)
  Eval vm_compute in mkarr nmaski nsranki srank_data.

(* the flip is masked with 2047, not 4095: bit 11 is the parity of the other
   eleven for a real cube, so only 2048 of the 4096 masks occur.  nsranki is
   the int63 literal, not of_nat nsrank, which would walk a unary nat. *)
Definition fsidx (x : int) : int :=
  Uint63.add
    (Uint63.mul (Uint63.land x 2047%uint63) nsranki)
    (PArray.get srank (Uint63.lsr x 12%uint63)).

(* and the guard: `fsidx x <? nfsi' does NOT say that x is a summary, and
   fsok does -- it admits exactly nflip * nsrank = nfs values.  See
   doc/rubik333-notes.md.  The definitions are here because p1stepF below
   needs them; the lemmas about them are in Fsparity.v. *)

(* the parity of the twelve flip bits *)
Definition fpar (x : int) : bool := odd (count (nbit x) (iota 0 nedge)).

Definition nfmaski : int := 4095%uint63.               (* the twelve bits *)

(* the same parity as a table, since fpar reads only those twelve bits *)
Definition fpartab : arr := Eval vm_compute in
  mkarr nmaski 0%uint63
        [seq (if fpar (of_nat m) then 1 else 0)%uint63 | m <- iota 0 nmask].

Definition fparr (x : int) : bool :=
  (PArray.get fpartab (Uint63.land nfmaski x) =? 1)%uint63.

Lemma bit_nfmaski k : (k < nedge)%N -> bit nfmaski (of_nat k).
Proof. by do 12![case: k => [|k]; first by vm_compute]. Qed.

Lemma fpar_mask x : fpar (Uint63.land nfmaski x) = fpar x.
Proof.
rewrite /fpar; congr odd; apply: eq_in_count => k.
rewrite mem_iota => /andP[_ kL].
by rewrite /nbit land_spec bit_nfmaski ?andTb.
Qed.

Definition fparC : bool :=
  all (fun m => (PArray.get fpartab (of_nat m) =? 1)%uint63 == fpar (of_nat m))
      (iota 0 nmask).

Lemma fparCP : fparC. Proof. by vm_compute. Qed.

(* the equation, so that allP does not have to unfold fparC *)
Lemma fparCE : fparC =
  all (fun m => (PArray.get fpartab (of_nat m) =? 1)%uint63 == fpar (of_nat m))
      (iota 0 nmask).
Proof. by []. Qed.

Lemma fparrE x : fparr x = fpar x.
Proof.
rewrite /fparr -fpar_mask.
set m := (Uint63.land nfmaski x).
have mL : (to_nat m < nmask)%N.
  by apply: (@to_nat_land_bound _ _ 12); vm_compute.
have hmem : to_nat m \in iota 0 nmask by rewrite mem_iota /=.
have hall : all (fun k => (PArray.get fpartab (of_nat k) =? 1)%uint63
                          == fpar (of_nat k)) (iota 0 nmask).
  by rewrite -fparCE; exact: fparCP.
by have := eqP (allP hall _ hmem); rewrite to_natK.
Qed.

(* the slice mask really is one of the 495 with four bits set *)
Definition sok (x : int) : bool :=
  (PArray.get srank (Uint63.lsr x 12%uint63) <? nsranki)%uint63.

(* an if and not `&&', which is a function and evaluates both sides *)
Definition fsok (x : int) : bool := if sok x then ~~ fparr x else false.

Lemma fsokE x : fsok x = sok x && ~~ fpar x.
Proof. by rewrite /fsok fparrE; case: sok. Qed.

(* =========================================================================  *)
(*  3.  The index, folded: one row of twists per orbit of ranks.              *)
(*      The 16 symmetry fold is discussed in doc/rubik333-notes.md.           *)
(* =========================================================================  *)

(* nfs and ntwist as int63 LITERALS, not as of_nat applied to the nat.
   of_nat is O(n) on a unary nat, so of_nat nfs is a million reduction steps --
   fine once, ruinous inside a loop the kernel runs 4 * 10 ^ 10 times, and it
   is also what makes `case: ifP` on the guard below diverge. *)
Definition nfsi    : int := 1013760%uint63.
Definition ntwisti : int := 2187%uint63.

(* NB `to_nat nfsi = nfs` as stated is not worth proving: nfs as a unary nat
   is a million successors.  But the FACTORED form is, and cheaply -- see
   nfsiE, to_nat nfsi = nflip * nsrank, where neither side is ever evaluated.
   Everything else below stays on the int63 side. *)

(* the orbits the sixteen symmetries cut the ranks into.  It is the ROW
   COUNT of the folded table; nfsi stays the bound on a rank. *)
Definition norb := 64430.

(* the table is orbit major: one block of ntwist entries per orbit, so the
   index is the orbit times ntwisti plus the twist.  Fold.foldi is the same
   index, and cannot be used here -- Fold.v is built on top of this file. *)
Definition p1foldi (rep tw : int) : int :=
  Uint63.add (Uint63.mul rep ntwisti) tw.

(* =========================================================================  *)
(*  3bis.  Twist x slice, rubik_par's second pruning table                    *)
(*                                                                            *)
(*  rubik_par reads THREE lower bounds per view and takes the max: flip x     *)
(*  slice, twist x slice, and phase 1.  Rocq had the first (fstab) and the    *)
(*  third; this is the second.  2187 x 495 = 1 082 565 states, all of them    *)
(*  reached by depth 9, so nothing is unreachable and four bits suffice.      *)
(*                                                                            *)
(*  INDEXED BY MASK, not by rank.  rubik_par uses t * 495 + slice rank.  The  *)
(*  RANK does not move on its own -- recovering it needs unranking -- but the *)
(*  MASK does: actfs's high half reads only high bits of x, so the slice mask *)
(*  of a moved coordinate depends on the slice mask alone.  FsTable.v already *)
(*  made exactly this trade for the flip x slice table, and for exactly this  *)
(*  reason: "the waste costs memory and nothing else".  Same values, same     *)
(*  node counts, 8.2x the slots.  A mask that cannot occur holds 0, which     *)
(*  makes the step condition trivially true there.                            *)
(* =========================================================================  *)

Definition nmask3    := 4096.        (* 2 ^ nedge, the masks it is indexed by *)
Definition ntsentries := 8957952.    (* ntwist * nmask3                       *)
Definition ntswordsi : int := 597197%uint63.   (* ceil (ntsentries / 15)      *)
Definition nmaski3   : int := 4096%uint63.

(* `Eval vm_compute in': without it the body of this table IS the cons
   list, and one delta step puts a 67 584 cell TERM in front of any
   tactic that unfolds a lookup -- it does not return.  See fsdtab in
   Farp1.v for the measurement. *)
Definition tstab : arr :=                                     (* GENERATED *)
  Eval vm_compute in mkarr ntswordsi 0%uint63 ts_data.

Definition tsget (i : int) : int :=
  let w := Uint63.div i 15%uint63 in
  let r := Uint63.sub i (Uint63.mul w 15%uint63) in
  Uint63.land (Uint63.lsr (PArray.get tstab w) (Uint63.mul r 4%uint63))
              15%uint63.

(* INDEXED BY RANK, t * 495 + s, exactly as rubik_par indexes it: the search
   carries ranks, so this is the direct read. *)
Definition Dtsi (tw s : int) : int :=
  tsget (Uint63.add (Uint63.mul tw nsranki) s).

Definition Dts (tw m : int) : nat := to_nat (Dtsi tw m).

(* the slice mask of a packed summary is its top twelve bits *)
Definition smaski (x : int) : int := Uint63.lsr x 12%uint63.

(* the mask action, emitted alongside: 4096 x 18 *)
(* the slice action by RANK, 495 x 18 *)
Definition slmtab : arr := mkarr 8910%uint63 0%uint63 slmove_data.

Definition actslri (s : int) (k : nat) : int :=
  PArray.get slmtab (Uint63.add (Uint63.mul s 18%uint63) (of_nat k)).

(* -- the two checks, exactly Fstab's pair ---------------------------------- *)

Definition slrank (f : int) : int :=
  Uint63.sub f (Uint63.mul (Uint63.div f nsranki) nsranki).

Definition ts_check0 : bool :=
  (Dtsi (ctwistt (id_tab 47)) (slrank (fsidx (coordt (id_tab 47)))) =? 0)%uint63.

Definition tsstepF (tw s : int) : bool :=
  all (fun k => (Dtsi tw s <=? incr (Dtsi (acttwi tw k) (actslri s k)))%uint63)
      (iota 0 18).

(* the mask loop is an all_pow over twelve bits, so it never leaves int63;
   only the twist loop pays of_nat, once per twist rather than per state.
   MEASURED: 200 twists in 25.8 s under vm_compute, so all 2187 is about
   4.7 minutes -- which is why the proof lives in its own file and goes
   through native_cast_no_check, as Far_00.v does. *)
(* all_pow 9 covers 512 ranks, so the 17 past 495 are guarded out rather than
   read into the next twist's block. *)
Definition ts_checkStep : bool :=
  all (fun t => all_pow 9 0%uint63
                  (fun s => (nsranki <=? s)%uint63 || tsstepF (of_nat t) s))
      (iota 0 ntwist).

Lemma ts_check0P : ts_check0.
Proof. by vm_compute. Qed.

(* =========================================================================  *)
(*  4.  The table itself: four bits per entry, fifteen per word               *)
(*                                                                            *)
(*  FOUR bits, holding the true distance capped at p1cap + 1 -- never an       *)
(*  offset clamped from below.  Storing d - base and clamping the underflow    *)
(*  to zero reports base for a state that is really nearer, which OVERstates   *)
(*  the distance and is not an admissible heuristic; it can prune away a real  *)
(*  solution.  Clamping from ABOVE is the safe direction, and that is exactly  *)
(*  what stopping the BFS at p1cap does.                                      *)
(* =========================================================================  *)

Definition p1cap     := 9.            (* the BFS stops here, as rubik_par does *)
(* int63, not nat.  Nothing computes with these two -- they record the shape
   of the table -- but a nat that size is a stack overflow waiting for the
   first `vm_compute' that reaches it, and Rocq warns about the literal. *)
Definition p1entriesi : int := 140908410%uint63.   (* norb * ntwist          *)
Definition p1wordsi   : int := 9393894%uint63.     (* ceil (p1entries / 15)  *)

(* p1words > PArray.max_length = 4 194 303, so the table is a PArray of
   PArrays.  The split is on the WORD index at a power of two, w >> cwlog,
   which stays definitional -- the same trick Fspar.v's cbits uses. *)
Definition cwlog  := 21.
Definition nchunk := 5.

(* THE TABLE IS A PARAMETER, exactly as Fstab.v takes it and FsTable.v        *)
(* supplies it.  Nothing below assumes ANYTHING about it -- no length, no     *)
(* default, no contents -- because the two checks are what make the heuristic *)
(* admissible, whatever the array holds.  So the theory can be developed, and *)
(* the search wired up, against a table that has not been emitted yet.        *)
(* THE THREE FOLD TABLES ARE PARAMETERS ON THE SAME TERMS: no property of     *)
(* them is assumed either, because the check reads through them exactly as    *)
(* the search does.                                                           *)
(* WHERE THE FOLDING TABLES LIVE.  They ride in the same array as the        *)
(* distance chunks, in the three slots after them, so a folded read still    *)
(* takes one table and no definition below grows an argument.                *)
Definition frepslot  : int := 5%uint63.   (* a rank's orbit               *)
Definition fsymslot  : int := 6%uint63.   (* the symmetry that folds it   *)
Definition twsymslot : int := 7%uint63.   (* the twist under a symmetry   *)

Section P1Tab.

Variable p1ftabs : PArray.array arr.

(* three twenty bit values to a word, and fifteen four bit ones *)
Definition get20i (a : arr) (i : int) : int :=
  let w := Uint63.div i 3%uint63 in
  let j := Uint63.sub i (Uint63.mul w 3%uint63) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j 20%uint63))
              1048575%uint63.

Definition get4i (a : arr) (i : int) : int :=
  let w := Uint63.div i 15%uint63 in
  let j := Uint63.sub i (Uint63.mul w 15%uint63) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j 4%uint63))
              15%uint63.

Definition frep (r : int) : int := get20i (PArray.get p1ftabs frepslot) r.

Definition fsym (r : int) : int := get4i (PArray.get p1ftabs fsymslot) r.

Definition twsym (tw s : int) : int :=
  get20i (PArray.get p1ftabs twsymslot)
         (Uint63.add (Uint63.mul tw 16%uint63) s).

(* THE SHIFT IS AN int63 LITERAL, not of_nat of a nat.  cwlog is a nat, and
   of_nat walks it: MEASURED at 1.53 us for of_nat 21, against 0.04 us for
   the array read it is supposed to index.  p1get did it twice per read, so
   p1get cost 2.99 us where the read costs 0.13.  cwlogi is the same number
   -- cwlogiE checks it -- so every value below is unchanged. *)
Definition cwlogi : int := 21%uint63.       (* = of_nat cwlog, see cwlogiE *)

Lemma cwlogiE : of_nat cwlog = cwlogi.
Proof. by vm_compute. Qed.

(* the offset mask as a literal: it was rebuilt with a shift and a
   subtraction on every lookup, and there are nineteen a value *)
Definition cwmaski : int := Eval vm_compute in
  Uint63.sub (Uint63.lsl 1%uint63 cwlogi) 1%uint63.

Definition p1get (i : int) : int :=
  let w := Uint63.div i 15%uint63 in
  let r := Uint63.sub i (Uint63.mul w 15%uint63) in
  let c := Uint63.lsr w cwlogi in
  let o := Uint63.land w cwmaski in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get p1ftabs c) o) (Uint63.mul r 4%uint63))
    15%uint63.

(* the heuristic: the stored value, which IS the distance up to the cap.
   BY RANK, because the fold is by rank and the search carries the rank. *)
Definition Dp1ri (tw r : int) : int :=
  p1get (p1foldi (frep r) (twsym tw (fsym r))).

Definition Dp1i (tw x : int) : int := Dp1ri tw (fsidx x).
Definition Dp1 (tw x : int) : nat := to_nat (Dp1i tw x).

(* the bridge to the ranked read, an EQUATION so that nothing has to unfold
   Dp1i to get at it *)
Lemma Dp1iE tw x : Dp1i tw x = Dp1ri tw (fsidx x).
Proof. by []. Qed.

(* =========================================================================  *)
(*  5.  What has to be proved                                                 *)
(*                                                                            *)
(*  Exactly the shape Coordfs already uses: the table is never asked to be     *)
(*  CORRECT, only to be a local certificate.  Fsmain.v discharges the flip x   *)
(*  slice version in sixteen generated slices glued by all_pow_glue16, and     *)
(*  the same mkfs.sh machinery applies here -- the check is a forall over      *)
(*  independent entries, so it parallelises with no new proof technique.       *)
(*  Budget: about 70 CPU hours, roughly 4 hours wall at -j18, once.            *)
(* =========================================================================  *)

(* -- the twist is a genuine quotient coordinate -------------------------- *)

(* the identity leaves every corner's U/D sticker on its own slot, so every
   base 3 digit is 0.  perm1 kills the permutation and inordK the ordinal, and
   then each test is a membership in cprim that computes.  NB neither
   vm_compute nor native_compute can do this directly -- they time out on the
   48 element finfun behind (1 : {perm facelet}). *)
Lemma coordtw_id : coordtw 1 = 0%uint63.
Proof. by rewrite /coordtw /corientg invg1 /= !perm1 /udcol !inordK. Qed.

(* the bitmask really is membership in cprim -- 48 cases, so it computes *)
Lemma bit_cmask x : (x < 48)%N -> bitc (of_nat x) = (x \in cprim).
Proof.
move=> xL.
have H : all (fun k => bitc (of_nat k) == (k \in cprim)) (iota 0 48).
  by vm_compute.
by move/allP: H => /(_ x); rewrite mem_iota /= xL => /(_ isT)/eqP.
Qed.

Lemma of_pos_of_nat n : of_pos n = of_nat (BinPos.Pos.to_nat n).
  by rewrite Znat.positive_nat_Z.
  Qed.

(* array -> list, mirroring Coordfsi.ecoordiE.

   STUCK -- the proof below gets to one step from the end and then loops.
   After

     rewrite !bE.

   there are 15 goals: the first is literally X = X and closes with by [],
   and the other 14 are  to_nat (get u (of_pos k)) < 48  for the fourteen
   facelets of the seven triples.  blt discharges exactly those, but

     apply: blt

   diverges, and so does a trailing //.  The reason looks like the numerals:
   the /= that unfolds foldr over the concrete seven element take 7 ctrip
   also normalises of_nat 37 into of_pos 37%AC, so closing the side goal asks
   unification to solve  of_nat ?c == of_pos 37%AC,  i.e. to invert of_nat,
   and it unfolds forever.  Coordfsi.ecoordiE does not hit this because it
   goes through eq_packn and never simplifies a numeral.

   Two ways out I can see, both of which I would rather you picked between:
   lock of_nat across the /=, or restate ectwist* as a fold over iota 0 7
   with nth into ctrip so the side condition is c < 7 rather than a numeral.

Proof.
move=> uok.
have bE (y : int) : (to_nat y < 48)%N -> bitc y = (to_nat y \in cprim).
  by move=> yL; rewrite -bit_cmask ?to_natK.
have blt c : (c < 48)%N -> (to_nat (PArray.get u (of_nat c)) < 48)%N.
  by move=> cL; apply: tabi_lt.
rewrite /ectwisti /ectwistt /=.
rewrite !bE.                      (* 15 goals; goal 1 is X = X *)
(* ... and here apply: blt loops on every one of the fourteen *)
Qed. *)
Lemma ectwistiE u : tabi_ok 47 u -> ectwisti u = ectwistt (ti2t 47 u).
Proof.
move=> uok.
have bE y : (to_nat y < 48)%N -> bitc y = (to_nat y \in cprim).
  by move=> yL; rewrite -bit_cmask ?to_natK.
have blt c : (c < 48)%N -> (to_nat (PArray.get u (of_nat c)) < 48)%N.
  by move=> cL; apply: tabi_lt.
rewrite /ectwisti /ectwistt /=.
have of_posE n : of_pos n = of_nat (BinPos.Pos.to_nat n).
  by rewrite Znat.positive_nat_Z.
by rewrite !of_posE -[(get u 0)]/(get u (of_nat 0)) !bE //; apply: blt.
Qed.

(* Coordfsi.coordiE, one level up *)
Lemma ctwistiE a : tabi_ok 47 a -> ctwisti a = ctwistt (ti2t 47 a).
Proof.
move=> aok; rewrite /ctwisti /ctwistt ectwistiE.
  by rewrite (ti2t_inv n47_small n47_len aok).
by rewrite /tabi_ok (ti2t_inv n47_small n47_len aok); apply: tab_ok_inv.
Qed.

(* list -> permutation, mirroring Coordfsi.coordtE *)
(* Coordfsi.coordtE, one level up *)
Lemma ctwisttE t : tab_ok 47 t -> coordtw (pt 47 t) = ctwistt t.
Proof.
move=> tok; have iok := tab_ok_inv tok.
have ilt c : (c < 48)%N -> (nth 0%N (inv_tab 47 t) c < 48)%N.
  move=> cL; have /and3P[/eqP sz /allP hall _] := iok.
  by apply: hall; rewrite mem_nth // sz.
have hval c : (c < 48)%N ->
    udcol ((pt 47 t)^-1 (inord c)) = (nth 0%N (inv_tab 47 t) c \in cprim).
  move=> cL; rewrite (ptV tok) ptE; last exact: iok.
  by rewrite /udcol (inordK cL) (inordK (ilt _ cL)).
(* the entries of ctrip are facelets *)
have hb : all (fun tr => ((tr.1.1 < 48) && (tr.1.2 < 48) && (tr.2 < 48))%N) ctrip.
  by vm_compute.
have hfold (F G : nat -> int -> int) l :
    (forall p x, F p x = G p x) -> foldr F 0%uint63 l = foldr G 0%uint63 l.
  by move=> h; elim: l => //= p l ->; rewrite h.
have hlist : take 7 ctrip = [seq nth (0, 0, 0)%N ctrip p | p <- iota 0 7] by [].
rewrite /coordtw /ctwistt /ectwistt hlist foldr_map.
(* hfold quantifies over every p, including p >= 8 where nth gives the
   default -- whose entries are 0, so the bound holds there too *)
move/(all_nthP (0, 0, 0)%N): hb => hb'.
have hsz : seq.size ctrip = 8 by [].
have hbp q : (((nth (0, 0, 0)%N ctrip q).1.1 < 48) &&
              ((nth (0, 0, 0)%N ctrip q).1.2 < 48))%N.
  have [qL|qL] := ltnP q 8.
    have qs : (q < seq.size ctrip)%N by rewrite hsz.
    by have /andP[/andP[-> ->] _] := hb' q qs.
  by rewrite nth_default ?hsz.
apply: hfold => p x; congr (Uint63.add _ _); congr (of_nat _).
rewrite /corientg /corientt.
have /andP[h0 h1] := hbp p.
case: (nth (0, 0, 0)%N ctrip p) h0 h1 => [[c0 c1] c2] h0 h1.
by rewrite (hval _ h0) (hval _ h1).
Qed.

(* the corner analogue of Coordfs's epair: where an edge's two stickers are
   swapped by an involution, a corner's three are rotated by a 3-cycle.  A
   permutation "moves cubies rigidly" exactly when it commutes with it, and
   that is the guard coordtwM needs -- Coordfs.cubP one level up. *)
(* AS A TABLE, not as a product of cycles.  pt 47 gives a permutation whose
   application computes through ptE, which is what the corner facts below
   need; \prod_(l <- Ccyc) cyc l does not compute. *)
Definition ccyct : seq nat :=
  [seq (let i := index f cflat in
        if (i < 24)%N then nth 0%N cflat (i - i %% 3 + (i %% 3).+1 %% 3) else f)
   | f <- iota 0 48].

Definition ccyc : {perm facelet} := pt 47 ccyct.

Lemma ccyct_ok : tab_ok 47 ccyct.
Proof. by vm_compute. Qed.

(* The two facts about the concrete corner data, stated on nat so they
   compute: the U/D stickers are exactly the slot 0 ones, and ccyct advances
   the slot by one.  Both are an `all` over the 24 corner facelets. *)
Lemma cslot_facts :
  all (fun i => [&& (i \in cprim) == (index i cflat %% 3 == 0)%N,
                 index (nth 0%N ccyct i) cflat %% 3 ==
                   ((index i cflat %% 3).+1 %% 3)%N,
                 nth 0%N ccyct i \in cflat &
                 (nth 0%N ccyct i < 48)%N]) cflat.
Proof. by vm_compute. Qed.

Definition cubcP (g : {perm facelet}) : bool :=
  [forall f : facelet, ccyc (g f) == g (ccyc f)].

(* Coordfs.coordfsM transposed.  With acttw computed rather than tabled this
   is a theorem about the moves, not about emitted numbers. *)
(* ccyc applied, through ptE *)
Lemma ccycE (f : facelet) : ccyc f = inord (nth 0%N ccyct f).
Proof. by rewrite /ccyc ptE ?ccyct_ok. Qed.

(* ccyc moves exactly the corner facelets -- so cornerhood is definable from
   ccyc alone, and cubcP therefore preserves it *)
Lemma ccyc_moves : all (fun i => (nth 0%N ccyct i != i) == (i \in cflat))
                       (iota 0 48).
Proof. by vm_compute. Qed.

(* cubcP passes to the inverse *)
Lemma cubcPV g : cubcP g -> forall f, g^-1 (ccyc f) = ccyc (g^-1 f).
Proof.
move=> /forallP cg f.
have := eqP (cg (g^-1 f)); rewrite permKV => ->.
by rewrite permK.
Qed.

(* corientg counts how far one must turn to REACH the U/D sticker, so it runs
   OPPOSITE to cslot, which says where the sticker sitting there came from.
   Measured: 0 mismatches in 800 008.  cubcP is needed -- the second branch
   asks about a different slot of the same cubie POSITION, and only a rigid
   motion ties that to the first. *)
(* everything concrete about ctrip that the proof needs, in one vm_compute *)
Lemma ctrip_facts :
  all (fun p => let t := nth (0, 0, 0)%N ctrip p in
       [&& nth 0%N cprim p == t.1.1, nth 0%N ccyct t.1.1 == t.1.2,
           (t.1.1 < 48)%N, (t.1.2 < 48)%N & t.1.1 != t.1.2]) (iota 0 8).
Proof. by vm_compute. Qed.

Lemma corientgE g p : cubcP g -> (p < 8)%N ->
  corientg g p = ((3 - cslot (g^-1 (cprimf p))) %% 3)%N.
Proof.
move=> cg pL.
have := allP ctrip_facts p; rewrite mem_iota /= pL => /(_ isT).
rewrite /corientg /cprimf.
case: (nth (0, 0, 0)%N ctrip p) => [[c0 c1] c2].
case/and5P => /eqP hcp /eqP hcc h0L h1L hne.
rewrite hcp.
(* the sticker at slot c1 is ccyc of the one at slot c0 *)
have hcy : inord c1 = ccyc (inord c0) :> facelet.
  by rewrite ccycE inordK // hcc.
have h1 : g^-1 (inord c1) = ccyc (g^-1 (inord c0)).
  by rewrite hcy (cubcPV cg).
(* so ccyc moves that sticker, hence it IS a corner facelet *)
have hmv : ccyc (g^-1 (inord c0)) != g^-1 (inord c0).
  rewrite -h1; apply/eqP => /perm_inj /(congr1 (@nat_of_ord 48)).
  by rewrite !inordK // => e; move: hne; rewrite e eqxx.
have hcorner : ((g^-1 (inord c0) : nat) \in cflat).
  have hi := allP ccyc_moves (g^-1 (inord c0) : nat).
  rewrite mem_iota /= ltn_ord in hi.
  rewrite -(eqP (hi isT)); apply: contra hmv => /eqP e.
  by apply/eqP; rewrite ccycE e inord_val.
have /and4P[/eqP hud /eqP hsl hin hlt] := allP cslot_facts _ hcorner.
have /and4P[/eqP hudc _ _ _] := allP cslot_facts _ hin.
rewrite /udcol /cslot h1 ccycE inordK // hud hudc.
(* LOCK the other index first.  Two index _ cflat %% 3 subterms are in the
   goal and hsl matches only one; it is the FAILED matches against the other
   that do not return, not the successful one. *)
rewrite [index (g^-1 (inord c0) : nat) cflat]lock hsl -lock.
have hs3 : (index (g^-1 (inord c0) : nat) cflat %% 3 < 3)%N by rewrite ltn_mod.
by move: hs3; case: (index _ _ %% 3) => [|[|[|?]]].
Qed.

(* cubcP is closed under composition, so g * m is covered by corientgE *)
Lemma cubcPM g m : cubcP g -> cubcP m -> cubcP (g * m).
Proof.
move=> /forallP cg /forallP cm; apply/forallP => f.
by rewrite !permM (eqP (cm _)) (eqP (cg _)).
Qed.

(* cubcP passes to the inverse as a predicate, not just as the equation *)
Lemma cubcPI g : cubcP g -> cubcP g^-1.
Proof. by move=> cg; apply/forallP => f; rewrite (cubcPV cg). Qed.

(* cornerhood is definable from ccyc -- ccyc moves exactly the corner
   facelets -- so anything commuting with ccyc preserves it *)
Lemma cubcP_corner g f :
  cubcP g -> (((g f : nat) \in cflat) = ((f : nat) \in cflat)).
Proof.
move=> /forallP cg.
have hmv h : ((ccyc h != h) = ((h : nat) \in cflat)).
  have hi := allP ccyc_moves (h : nat).
  rewrite mem_iota /= ltn_ord in hi.
  rewrite -(eqP (hi isT)); apply/idP/idP; apply: contra.
    by move=> /eqP e; apply/eqP; rewrite ccycE e inord_val.
  move=> /eqP e; apply/eqP.
  have hlt : (nth 0%N ccyct (h : nat) < 48)%N.
    have /and3P[/eqP sz /allP hall _] := ccyct_ok.
    by apply: hall; rewrite mem_nth // sz ltn_ord.
  by move: e; rewrite ccycE => /(congr1 (@nat_of_ord 48)); rewrite inordK.
by rewrite -!hmv (eqP (cg f)) (inj_eq perm_inj).
Qed.

(* THE TOTAL TWIST.  cubcP says the corners turn rigidly; it does NOT say the
   eight orientations sum to 0 mod 3.  But the coordinate stores only seven
   digits and recovers the eighth from that sum, so dign at 7 is right only
   when it holds.  It is a property of the cube group, not of rigidity, and
   so it has to be carried. *)
Definition twsum (g : {perm facelet}) : nat :=
  (foldr (fun p a => a + corientg g p) 0 (iota 0 8)) %% 3.

(* where each corner sticker sits relative to its cubie's U/D sticker *)
(* every corner sticker is its cubie's U/D sticker turned cslot times *)
Lemma cflat_reach :
  all (fun i => let c := (index i cflat %/ 3)%N in
       [&& i == iter (index i cflat %% 3) (nth 0%N ccyct) (nth 0%N cprim c),
           (nth 0%N cprim c \in cflat) & (c < 8)%N]) cflat.
Proof. by vm_compute. Qed.

Lemma cprim_facts :
  all (fun p => (nth 0%N cprim p \in cflat) && (nth 0%N cprim p < 48)%N)
      (iota 0 8).
Proof. by vm_compute. Qed.

(* every entry of ccyct is a facelet *)
Lemma ccyct_lt j : (j < 48)%N -> (nth 0%N ccyct j < 48)%N.
Proof.
move=> jL; have /and3P[/eqP sz /allP hall _] := ccyct_ok.
by apply: hall; rewrite mem_nth // sz.
Qed.

(* cflat is closed under the step, so iterating stays in range *)
Lemma cflat_lt j : (j \in cflat) -> (j < 48)%N.
Proof.
have h : all (fun i => (i < 48)%N) cflat by vm_compute.
by move=> hj; apply: (allP h).
Qed.

Lemma iter_ccycE j s : (j < 48)%N ->
  inord (iter s (nth 0%N ccyct) j) = iter s ccyc (inord j) :> facelet.
Proof.
elim: s j => [//|s IH] j jL.
have hlt : (iter s (nth 0%N ccyct) j < 48)%N.
  by elim: s {IH} => [//|k IH]; apply: ccyct_lt.
by rewrite !iterS -IH // ccycE inordK.
Qed.

(* one step, as its own lemma: inside cslot_iter the goal carries two cslot
   occurrences and rewriting hsl there has the same trouble corientgE had *)
Lemma cslot_ccyc (y : facelet) : ((y : nat) \in cflat) ->
  cslot (ccyc y) = ((cslot y).+1 %% 3)%N.
Proof.
move=> hy.
have /andP[_ /andP[/eqP hsl /andP[_ hlt]]] := allP cslot_facts (y : nat) hy.
by rewrite /cslot ccycE inordK.
Qed.

Lemma cflat_ccyc (y : facelet) : ((y : nat) \in cflat) ->
  ((ccyc y : nat) \in cflat).
Proof.
move=> hy.
have /andP[_ /andP[_ /andP[hin hlt]]] := allP cslot_facts (y : nat) hy.
by rewrite ccycE inordK.
Qed.

Lemma cslot_iter (x : facelet) s : ((x : nat) \in cflat) ->
  cslot (iter s ccyc x) = ((cslot x + s) %% 3)%N.
Proof.
move=> hx; elim: s => [|s IH]; first by rewrite addn0 modn_small ?ltn_mod.
have hin : ((iter s ccyc x : nat) \in cflat).
  by elim: s {IH} => [//|k IH]; rewrite iterS; apply: cflat_ccyc.
by rewrite iterS cslot_ccyc // IH addnS -addn1 modnDml addn1.
Qed.

Lemma ccyc_iter_inv g (x : facelet) s : cubcP g ->
  g^-1 (iter s ccyc x) = iter s ccyc (g^-1 x).
Proof. by move=> cg; elim: s => [//|s IH]; rewrite !iterS -IH (cubcPV cg). Qed.

(* an accumulator in an additive foldr just comes out in front *)
Lemma foldr_addE (h : nat -> nat) l acc :
  foldr (fun q a => a + h q) acc l = (acc + foldr (fun q a => a + h q) 0 l)%N.
Proof.
by elim: l acc => [|x l IH] acc /=; rewrite ?addn0 // IH addnA.
Qed.

(* reading ANY of the eight digits, including the forced one.  For q < 7 this
   is dig_coordtw; for q = 7 it is exactly what twsum g = 0 buys. *)
Lemma dignE g q : cubcP g -> twsum g = 0%N -> (q < 8)%N ->
  dign (coordtw g) q = corientg g q.
Proof.
move=> cg ts qL; rewrite /dign.
have [->|qn7] := eqVneq q 7; last first.
  by rewrite dig_coordtw // ltn_neqAle qn7 -ltnS.
(* the list is concrete, so unfold it rather than induct: seven rewrites *)
have hf : foldr (fun q a => a + dig3n (to_nat (coordtw g)) q) 0 (iota 0 7)
        = foldr (fun q a => a + corientg g q) 0 (iota 0 7).
  by rewrite [iota 0 7]/= /= !dig_coordtw.
rewrite /dig8 hf.
move: ts; rewrite /twsum -addn1 iotaD add0n foldr_cat.
rewrite [foldr _ _ [:: 7]]/= add0n foldr_addE.
have h7 : (corientg g 7 < 3)%N by apply: corientg_lt.
set S := foldr _ 0 _; rewrite -modnDml.
(* S occurs bare in the hypothesis, so bring it under %% 3 first; then both
   sides are opaque terms below 3 and the nine cases compute. *)
rewrite -modnDmr.
have hs : (S %% 3 < 3)%N by rewrite ltn_mod.
by move: h7 hs; case: (corientg g 7) => [|[|[|?]]] //;
   case: (S %% 3) => [|[|[|?]]].
Qed.

(* THE CORNER FACT, and the only genuinely new content left.  A move sends
   the U/D slot of corner p to slot cdelta m p of corner csrc m p; since a
   cubcP permutation turns each cubie rigidly, the orientation there is the
   orientation of that corner under g, advanced by cdelta. *)
Lemma corientgM g m p : cubcP g -> cubcP m -> twsum g = 0%N -> (p < 7)%N ->
  corientg (g * m) p = acttwd (coordtw g) m p.
Proof.
move=> cg cm ts pL.
have p8 : (p < 8)%N by apply: ltnW.
rewrite (corientgE (cubcPM cg cm) p8) invMg permM /acttwd /csrc /cdelta.
(* the sticker arriving at p's U/D slot *)
have hcpl : (nth 0%N cprim p \in cflat) && (nth 0%N cprim p < 48)%N.
  by apply: (allP cprim_facts); rewrite mem_iota.
have /andP[hcpin hcplt] := hcpl.
have hcp : ((cprimf p : nat) \in cflat) by rewrite /cprimf inordK.
have hf : ((m^-1 (cprimf p) : nat) \in cflat).
  by rewrite cubcP_corner ?cubcPI.
have /and3P[/eqP hre hcin hc8] := allP cflat_reach _ hf.
(* it is its cubie's U/D sticker turned cslot times *)
set c := (index _ cflat %/ 3)%N in hre hcin hc8.
have hcl : (nth 0%N cprim c < 48)%N.
  have hm : (c \in iota 0 8) by rewrite mem_iota /= hc8.
  by have /andP[_ hh] := allP cprim_facts c hm; exact: hh.
have hreach : m^-1 (cprimf p) = iter (cslot (m^-1 (cprimf p))) ccyc (cprimf c).
  by rewrite /cprimf -iter_ccycE // -hre inord_val.
have hgc : ((g^-1 (cprimf c) : nat) \in cflat).
  by rewrite cubcP_corner ?cubcPI // /cprimf inordK.
(* {1}: hreach's RHS contains its own LHS, so an unrestricted rewrite
   re-matches forever.  Only the occurrence under g^-1 is wanted. *)
rewrite {1}hreach.
(* side conditions SUPPLIED, not left to //: cubcP g is a [forall f : facelet]
   and done tries to evaluate it. *)
rewrite (ccyc_iter_inv _ _ cg) (cslot_iter _ hgc).
rewrite (dignE cg ts hc8) (corientgE cg hc8).
set a := cslot (g^-1 (cprimf c)); set s := cslot (m^-1 (cprimf p)).
have ha : (a < 3)%N by rewrite /a /cslot ltn_mod.
have hs : (s < 3)%N by rewrite /s /cslot ltn_mod.
by move: ha hs; case: a => [|[|[|?]]] //; case: s => [|[|[|?]]].
Qed.

(* THE SAME FACT WITHOUT THE COORDINATE, and so without twsum: corientgM
   reads the source digit out of coordtw g, which is only the orientation
   when the eighth digit is the forced one.  Read it off corientg directly
   and the hypothesis is not needed -- and the range widens to all eight
   corners, which is what the total twist has to sum over. *)
Lemma corientgM0 g m p : cubcP g -> cubcP m -> (p < 8)%N ->
  corientg (g * m) p = (corientg g (csrc m p) + 3 - cdelta m p) %% 3.
Proof.
move=> cg cm p8.
rewrite (corientgE (cubcPM cg cm) p8) invMg permM /csrc /cdelta.
have hcpl : (nth 0%N cprim p \in cflat) && (nth 0%N cprim p < 48)%N.
  by apply: (allP cprim_facts); rewrite mem_iota.
have /andP[hcpin hcplt] := hcpl.
have hcp : ((cprimf p : nat) \in cflat) by rewrite /cprimf inordK.
have hf : ((m^-1 (cprimf p) : nat) \in cflat).
  by rewrite cubcP_corner ?cubcPI.
have /and3P[/eqP hre hcin hc8] := allP cflat_reach _ hf.
set c := (index _ cflat %/ 3)%N in hre hcin hc8.
have hcl : (nth 0%N cprim c < 48)%N.
  have hm : (c \in iota 0 8) by rewrite mem_iota /= hc8.
  by have /andP[_ hh] := allP cprim_facts c hm; exact: hh.
have hreach : m^-1 (cprimf p) = iter (cslot (m^-1 (cprimf p))) ccyc (cprimf c).
  by rewrite /cprimf -iter_ccycE // -hre inord_val.
have hgc : ((g^-1 (cprimf c) : nat) \in cflat).
  by rewrite cubcP_corner ?cubcPI // /cprimf inordK.
rewrite {1}hreach.
rewrite (ccyc_iter_inv _ _ cg) (cslot_iter _ hgc).
rewrite (corientgE cg hc8).
set a := cslot (g^-1 (cprimf c)); set s := cslot (m^-1 (cprimf p)).
have ha : (a < 3)%N by rewrite /a /cslot ltn_mod.
have hs : (s < 3)%N by rewrite /s /cslot ltn_mod.
by move: ha hs; case: a => [|[|[|?]]] //; case: s => [|[|[|?]]].
Qed.

(* and coordtwM is then just the packing *)
Lemma coordtwM g m :
  cubcP g -> cubcP m -> twsum g = 0%N ->
  coordtw (g * m) = acttw (coordtw g) m.
Proof.
move=> cg cm ts; apply: to_nat_inj.
rewrite coordtwE acttwE; apply: pack3n_ext => p pL.
exact: corientgM.
Qed.

(* the form the search uses *)
(* the moves turn corners rigidly -- a table fact, so it computes *)
Lemma moves_cubcP_tab :
  all (fun mt => all (fun f => nth 0%N ccyct (nth 0%N mt f) ==
                               nth 0%N mt (nth 0%N ccyct f)) (iota 0 48)) mtabs.
Proof. by vm_compute. Qed.

Lemma moves_cubcP k : (k < 18)%N -> cubcP (pt 47 (nth [::] mtabs k)).
Proof.
move=> kL; set mt := nth [::] mtabs k.
have hsz : seq.size mtabs = 18 by [].
have hmt : tab_ok 47 mt.
  by apply: (allP mtabs_ok); apply: mem_nth; rewrite hsz.
have hlt j : (j < 48)%N -> (nth 0%N mt j < 48)%N.
  move=> jL; have /and3P[/eqP sz /allP hall _] := hmt.
  by apply: hall; rewrite mem_nth // sz.
have htab : all (fun f => nth 0%N ccyct (nth 0%N mt f) ==
                          nth 0%N mt (nth 0%N ccyct f)) (iota 0 48).
  by apply: (allP moves_cubcP_tab); rewrite mem_nth // hsz.
apply/forallP => f; apply/eqP.
rewrite ccycE ptE // ccycE.
rewrite (inordK (hlt _ (ltn_ord f))) ptE //.
rewrite (inordK (ccyct_lt (ltn_ord f))).
congr (inord _); apply/eqP.
by have := allP htab (f : nat); rewrite mem_iota /= ltn_ord => /(_ isT).
Qed.

Lemma coordtw_step (g : {perm facelet}) (k : nat) : (k < 18)%N ->
  cubcP g -> twsum g = 0%N ->
  coordtw (g * pt 47 (nth [::] mtabs k)) =
  acttw (coordtw g) (pt 47 (nth [::] mtabs k)).
Proof. by move=> kL cg ts; apply: coordtwM => //; apply: moves_cubcP. Qed.

(* =========================================================================  *)
(*  5bis.  The total twist is invariant, so twsum = 0 is not a hypothesis     *)
(*                                                                            *)
(*  coordtwM and coordtw_step both carry `twsum g = 0' and nothing discharged *)
(*  it.  It is discharged here, as an INVARIANT rather than a fact about a    *)
(*  single g: the identity has total twist 0, and no move changes it.         *)
(*                                                                            *)
(*  WHY IT IS TRUE.  A move sends the U/D slot of corner p to slot            *)
(*  cdelta m p of corner csrc m p, so summing corientg (g * m) over the eight *)
(*  corners re-sums corientg g over a PERMUTATION of them, shifted by the     *)
(*  total of the deltas.  The permutation leaves the sum alone, and the total *)
(*  delta of every move is 0 mod 3 -- a quarter turn of a face on the U/D     *)
(*  axis twists nothing, and any other quarter turn twists its four corners   *)
(*  by 1, 2, 1, 2.  Both are table facts and both are checked below.          *)
(*                                                                            *)
(*  This is what makes the phase 1 coordinate an action of the cube GROUP     *)
(*  rather than of the rigid-corner monoid: cubcP is not enough, and the      *)
(*  eighth digit is exactly where the difference shows.                       *)
(* =========================================================================  *)

(* -- sums over a list, all four generic ------------------------------------ *)

Lemma foldr_sum_split (h1 h2 : nat -> nat) l :
  foldr (fun p a => a + (h1 p + h2 p)) 0%N l
  = (foldr (fun p a => a + h1 p) 0%N l + foldr (fun p a => a + h2 p) 0%N l)%N.
Proof. by elim: l => //= x l ->; rewrite addnACA. Qed.

Lemma foldr_sum_big (h : nat -> nat) l :
  foldr (fun q a => a + h q) 0%N l = (\sum_(q <- l) h q)%N.
Proof. by elim: l => [|x l IH]; rewrite ?big_nil //= big_cons IH addnC. Qed.

(* the reindexing, and the only reason bigop appears in this file *)
Lemma foldr_sum_perm (h : nat -> nat) l1 l2 : perm_eq l1 l2 ->
  foldr (fun q a => a + h q) 0%N l1 = foldr (fun q a => a + h q) 0%N l2.
Proof. by move=> hp; rewrite !foldr_sum_big; apply: perm_big. Qed.

Lemma foldr_sum_eq_in (h1 h2 : nat -> nat) l : {in l, h1 =1 h2} ->
  foldr (fun p a => a + h1 p) 0%N l = foldr (fun p a => a + h2 p) 0%N l.
Proof.
elim: l => [//|x l IH] hc /=.
rewrite IH; last by move=> p pl; apply: hc; rewrite inE pl orbT.
by rewrite hc ?inE ?eqxx.
Qed.

Lemma foldr_sum_cong (h1 h2 : nat -> nat) l :
  {in l, forall p, h1 p %% 3 = h2 p %% 3} ->
  (foldr (fun p a => a + h1 p) 0%N l) %% 3
  = (foldr (fun p a => a + h2 p) 0%N l) %% 3.
Proof.
elim: l => [//|x l IH] hc /=.
have hx : h1 x %% 3 = h2 x %% 3 by apply: hc; rewrite inE eqxx.
have hl : (foldr (fun p a => a + h1 p) 0%N l) %% 3
        = (foldr (fun p a => a + h2 p) 0%N l) %% 3.
  by apply: IH => p pl; apply: hc; rewrite inE pl orbT.
by rewrite -modnDml hl modnDml -modnDmr hx modnDmr.
Qed.

(* -- the invariance, for any m that behaves like a move -------------------- *)

Lemma twsumM g m : cubcP g -> cubcP m ->
  perm_eq [seq csrc m p | p <- iota 0 8] (iota 0 8) ->
  (foldr (fun p a => a + (3 - cdelta m p)) 0%N (iota 0 8)) %% 3 = 0%N ->
  twsum (g * m) = twsum g.
Proof.
move=> cg cm hperm hd; rewrite /twsum.
rewrite (foldr_sum_cong
           (h2 := fun p => corientg g (csrc m p) + (3 - cdelta m p)));
  last first.
  move=> p; rewrite mem_iota add0n => /andP[_ p8].
  rewrite (corientgM0 cg cm p8) modn_mod addnBA //.
  by apply: ltnW; rewrite /cdelta /cslot ltn_mod.
rewrite foldr_sum_split -modnDmr hd addn0.
(* the map form has to be named: the eta-contracted `addn^~' in the goal does
   not match foldr_map_seq's right hand side *)
have hmap : foldr (fun p a => (a + corientg g (csrc m p))%N) 0%N (iota 0 8)
          = foldr (fun q a => (a + corientg g q)%N) 0%N
                  [seq csrc m p | p <- iota 0 8].
  by rewrite foldr_map_seq.
by rewrite hmap (foldr_sum_perm _ hperm).
Qed.

(* -- the two hypotheses, at the table level -------------------------------- *)

(* the same {perm facelet} wall as everywhere else: csrc and cdelta mention
   m^-1, so the checks run on the move TABLES and these bridge them *)
Lemma cprimf_ptV mt p : tab_ok 47 mt ->
  (((pt 47 mt)^-1 (cprimf p)) : nat)
  = nth 0%N (inv_tab 47 mt) (nth 0%N cprim p).
Proof.
move=> mok; have iok := tab_ok_inv mok.
have hcpl : (nth 0%N cprim p < 48)%N.
  have hall : all (fun q => (nth 0%N cprim q < 48)%N) (iota 0 8) by vm_compute.
  have [pL|pL] := ltnP p 8.
    by have := allP hall p; rewrite mem_iota /= pL => /(_ isT).
  by rewrite nth_default // (_ : seq.size cprim = 8).
rewrite /cprimf (ptV mok) ptE; last exact: iok.
rewrite (inordK hcpl).
have hX : (nth 0%N (inv_tab 47 mt) (nth 0%N cprim p) < 48)%N.
  have /and3P[/eqP sz /allP hall _] := iok.
  by apply: hall; rewrite mem_nth // sz.
by rewrite (inordK hX).
Qed.

Lemma csrcE mt p : tab_ok 47 mt -> csrc (pt 47 mt) p = csrct mt p.
Proof. by move=> mok; rewrite /csrc /csrct /cpos /cposn cprimf_ptV. Qed.

Lemma cdeltaE mt p : tab_ok 47 mt -> cdelta (pt 47 mt) p = cdeltat mt p.
Proof. by move=> mok; rewrite /cdelta /cdeltat /cslot /cslotn cprimf_ptV. Qed.

(* the corners a move brings to the eight slots are the eight corners *)
Lemma csrct_perm_moves :
  all (fun mt => perm_eq [seq csrct mt p | p <- iota 0 8] (iota 0 8)) mtabs.
Proof. by vm_compute. Qed.

(* THE TOTAL DELTA OF A MOVE IS 0 MOD 3.  Stated on 3 - cdelta, the quantity
   the sum actually needs, so that no nat subtraction has to be pushed
   through a sum afterwards. *)
Definition cdsumt (mt : seq nat) : nat :=
  (foldr (fun p a => a + (3 - cdeltat mt p)) 0%N (iota 0 8)) %% 3.

Lemma cdsumt_moves : all (fun mt => cdsumt mt == 0)%N mtabs.
Proof. by vm_compute. Qed.

(* -- and the invariant ----------------------------------------------------- *)

Lemma twsum_step g k : (k < 18)%N -> cubcP g ->
  twsum (g * pt 47 (nth [::] mtabs k)) = twsum g.
Proof.
move=> kL cg; set mt := nth [::] mtabs k.
have hsz : seq.size mtabs = 18%N by vm_compute.
have hmem : mt \in mtabs by rewrite /mt mem_nth // hsz.
have mok : tab_ok 47 mt by apply: (allP mtabs_ok).
apply: twsumM => //; first exact: moves_cubcP.
  have -> : [seq csrc (pt 47 mt) p | p <- iota 0 8]
          = [seq csrct mt p | p <- iota 0 8].
    by apply: eq_map => p; exact: csrcE.
  exact: (allP csrct_perm_moves _ hmem).
rewrite (foldr_sum_eq_in (h2 := fun p => 3 - cdeltat mt p)); last first.
  by move=> p _; rewrite cdeltaE.
exact: (eqP (allP cdsumt_moves _ hmem)).
Qed.

(* the solved cube has every corner already showing its U/D sticker *)
Lemma twsum1 : twsum 1 = 0%N.
Proof.
have hb : all (fun tr => (tr.1.1 \in cprim) && (tr.1.1 < 48)%N) ctrip.
  by vm_compute.
have h0 : {in iota 0 8, corientg 1 =1 fun _ => 0%N}.
  move=> p; rewrite mem_iota add0n => /andP[_ p8].
  rewrite /corientg.
  have hm : nth (0, 0, 0)%N ctrip p \in ctrip.
    by rewrite mem_nth // (_ : seq.size ctrip = 8%N).
  have /andP[hin hlt] := allP hb _ hm.
  case E : (nth (0, 0, 0)%N ctrip p) => [[c0 c1] c2].
  rewrite E in hin hlt.
  by rewrite invg1 perm1 /udcol (inordK hlt) hin.
by rewrite /twsum (foldr_sum_eq_in h0).
Qed.

Lemma cubcP1 : cubcP 1.
Proof. by apply/forallP => f; rewrite !perm1. Qed.

(* THE PACKAGED FORM, in exactly the shape Coordfs.v's section wants of an
   invariant: true at 1, closed under the moves.  Whatever threads the search
   carries this and coordtw_step's hypotheses come for free. *)
Definition twP (g : {perm facelet}) : bool := cubcP g && (twsum g == 0%N).

Lemma twP1 : twP 1.
Proof. by rewrite /twP cubcP1 twsum1 eqxx. Qed.

Lemma twPM g k : (k < 18)%N -> twP g -> twP (g * pt 47 (nth [::] mtabs k)).
Proof.
move=> kL /andP[cg ts]; rewrite /twP.
by rewrite (cubcPM cg (moves_cubcP kL)) (twsum_step kL cg) ts.
Qed.

(* the form the search will actually use: no twsum in sight *)
Lemma coordtw_stepP (g : {perm facelet}) (k : nat) : (k < 18)%N -> twP g ->
  coordtw (g * pt 47 (nth [::] mtabs k)) =
  acttw (coordtw g) (pt 47 (nth [::] mtabs k)).
Proof. by move=> kL /andP[cg /eqP ts]; apply: coordtw_step. Qed.

(* =========================================================================  *)
(*  6.  THE CHECK                                                             *)
(*                                                                            *)
(*  The table is never asked to be CORRECT, only to be a local certificate:    *)
(*  zero at the identity, and never dropping by more than one across a move.   *)
(*  Those two facts alone make the heuristic admissible, and both are decided  *)
(*  by a closed boolean the kernel evaluates.  Exactly Fstab.v's check0 /      *)
(*  checkStep, one level up.                                                  *)
(*                                                                            *)
(*  WHY THE LOOP IS OVER RANKS.  Only 1 013 760 of the 2 ^ 24 packed flip x    *)
(*  slice values occur -- 6 % -- so iterating over packed values would do      *)
(*  sixteen times the work.  unranki turns a rank back into a packed value,    *)
(*  and p1checkUnrank is what makes that legitimate.                          *)
(*                                                                            *)
(*  WHY p1mdata IS HOISTED.  Fstab.v measured this: with the move data built   *)
(*  inside the lambda it is rebuilt per state, 26 ms against 79 us -- ninety   *)
(*  days against seven hours.  Here the loop is 132 times longer still.       *)
(* =========================================================================  *)

Definition p1mdata : seq (nat * mdatf) :=
  [seq (k, mdatf_of_tab (nth [::] mtabs k)) | k <- iota 0 18].

(* THE LOOP RUNS OVER PACKED VALUES, NOT OVER RANKS, and that is deliberate.
   Ranking first would be 16x fewer iterations, but then the checked instance
   is at unranki (fsidx x) rather than at x, and closing the gap needs fsidx
   to be injective on the summaries -- a real obligation, and one Coordfs does
   not currently provide.  Over packed values, all_powP hands back the
   instance at x itself and the proof is Fstab.DfsStep_of_check verbatim.
   Measured cost of the choice: the extra sweep is ~5 % on top of the move
   checks, which dominate either way.

   The fsidx guard is NOT cosmetic: without it every one of the 2 ^ 24 packed
   values would run the eighteen move checks instead of the 6 % that are
   summaries, which is sixteen times the work. *)
(* fsok, NOT `fsidx x <? nfsi' -- see the note where fsok is defined.  The
   old guard let through values that are not summaries at all, which made
   this check assert a distance inequality about table slots that no state
   occupies, and made it 8.3x larger than it needs to be. *)
(* Dp1i tw x does not depend on km, so it is read once and not eighteen
   times.  The let is inside the else: outside it, it would run on every
   value rather than on the ones the guard admits. *)
Definition p1stepF (tw : int) : int -> bool :=
  let md := p1mdata in
  fun x =>
    if ~~ fsok x then true
    else let d := Dp1i tw x in
         all (fun km => (d <=?
                incr (Dp1i (acttwi tw km.1) (actf x km.2)))%uint63) md.

Definition p1checkTw (tw : int) : bool := all_pow ncoord 0%uint63 (p1stepF tw).

Definition p1checkStep : bool :=
  all (fun t => p1checkTw (of_nat t)) (iota 0 ntwist).

(* An EQUATION, not a delta step.  Any conversion that has to see through
   p1checkTw lets the kernel unfold the all_pow fixpoint at ncoord = 24, i.e.
   2 ^ 24 conjuncts: applying all_powP to p1checkTw tw directly loops in the
   tactic, `rewrite /p1checkTw in htw` loops at Qed, and even a definitional
   coercion loops in elaboration.  Rewriting with this lemma is an eq_ind with
   a small motive and does not. *)
Lemma p1checkTwE tw : p1checkTw tw = all_pow ncoord 0%uint63 (p1stepF tw).
Proof. by rewrite /p1checkTw. Qed.

Definition p1check0 : bool :=
  (Dp1i (ctwistt (id_tab 47)) (coordt (id_tab 47)) =? 0)%uint63.

(* -- the split for parallel checking --------------------------------------- *)

(* The outer loop is an all over iota, not an all_pow, so splitting it is
   cat_take_drop and all_cat -- no all_pow_glue16 needed.  That is the one
   place this is EASIER than the flip x slice certificate: 2187 twists cut
   into as many slices as there are cores, each its own file. *)
Lemma p1checkStep_split n :
  all (fun t => p1checkTw (of_nat t)) (take n (iota 0 ntwist)) ->
  all (fun t => p1checkTw (of_nat t)) (drop n (iota 0 ntwist)) ->
  p1checkStep.
Proof.
by rewrite /p1checkStep -{3}(cat_take_drop n (iota 0 ntwist)) all_cat => -> ->.
Qed.

Lemma p1checkStep_of_slices (s : seq nat) :
  s = iota 0 ntwist ->
  all (fun t => p1checkTw (of_nat t)) s -> p1checkStep.
Proof. by move=> ->. Qed.

(* -- what the two checks buy ---------------------------------------------- *)

(* These are the point of the file.  A table passing them is a valid
   heuristic, whatever it actually contains. *)

(* coordtw 1 does not compute, being about a permutation; the identity table
   is its computable form, by pt1 and ctwisttE -- exactly Fstab's coordfs1E *)
Lemma coordtw1E : coordtw 1 = ctwistt (id_tab 47).
Proof. by rewrite -(ctwisttE (tab_ok_id 47)) pt1. Qed.

Lemma Dp1_0_of_check : p1check0 -> Dp1 (coordtw 1) (coordfs 1) = 0%N.
Proof.
rewrite /p1check0 /Dp1 /Dp1i coordtw1E coordfs1E.
by move=> /eqb_correct ->; rewrite to_nat_0.
Qed.

(* NO Dp1_oob ANALOGUE, and the reason matters.  Fstab gets Dfs_oob because a
   coordinate past 2 ^ ncoord indexes past the table.  Here the index is
   frep (fsidx x) * ntwist + twsym tw (fsym (fsidx x)), and rows are
   contiguous: an orbit at or past norb, or a twist at or past ntwist, does
   NOT leave the table -- it lands in a neighbouring row and reads a
   perfectly good entry for a different state.  Folding adds a second
   indirection with exactly the same hazard.  So the fsidx guard in p1stepF
   is not free: it has to be discharged, not absorbed.

   NOTHING MORE IS NEEDED HERE, though, and that is worth being precise
   about: p1checkStep checks the composite read at the very x the search
   reads it at, so no range fact about frep, fsym or twsym enters.  Fold.v
   is where the ranges do have to be assumed, because there the check runs
   at the orbit representatives and has to be carried back.

   That is what fsidx_lt is for.  It is a fact about the summaries, not about
   the table: the flip half is eleven bits and the slice half is a mask with
   exactly four bits set, so fsidx lands below 2048 * 495.  It belongs in
   Coordfs, which owns both halves; it is stated here until it moves. *)
(* -- the slice half has exactly four bits set ------------------------------ *)

(* ALL FOUR OF THESE BELONG IN Coordfs.v, which owns eprim, esec and epair;
   they are here only so that closing fsidx_lt does not rebuild the sixteen
   certificate files.  Move them when the file settles.

   Note the cubP hypothesis, which is not decoration: for an arbitrary
   permutation the count is anything at all, and fsidx_lt is then FALSE.  It
   is the same hypothesis coordfs_flip and coordfs_slice carry. *)

(* a slice edge is one whose position is among the last four -- read off the
   24 edge facelets, since scol and epos are both functions of the nat *)
Lemma scol_epos (f : facelet) : (f : nat) \in eprim ++ esec ->
  scol f = (nedge - nslice <= epos f)%N.
Proof.
move=> fE; apply/eqP.
have hall : all (fun m => ((m \in drop 8 eprim ++ drop 8 esec)
                  == (nedge - nslice <= index m (eprim ++ esec) %% nedge)%N))
                (eprim ++ esec).
  by vm_compute.
exact: (allP hall _ fE).
Qed.

(* a primary facelet is never the partner of a primary facelet: eprim and the
   image of eprim under the pairing are disjoint *)
Lemma eprimf_epair_neq p q : (p < nedge)%N -> (q < nedge)%N ->
  eprimf q != epair (eprimf p).
Proof.
move=> pL qL; apply/eqP => e.
have hsz : seq.size eprim = nedge by vm_compute.
have hb : (epairn (eprimf p : nat) < nfacelet)%N := epairn_lt (eprimf_edge pL).
have e' : nth 0%N eprim q = epairn (nth 0%N eprim p).
  by rewrite -(eprimfK pL) -(eprimfK qL) e epairE (inordK hb).
have hall : all (fun m => epairn m \notin eprim) eprim by vm_compute.
have hpm : nth 0%N eprim p \in eprim by apply: mem_nth; rewrite hsz.
have hqm : nth 0%N eprim q \in eprim by apply: mem_nth; rewrite hsz.
by have := allP hall _ hpm; rewrite -e' hqm.
Qed.

(* the position the edge at p came from is injective in p.  Two positions with
   the same source hold the two facelets of one edge -- edge_case -- and the
   secondary case is exactly what eprimf_epair_neq rules out. *)
Lemma eprimg_inj g p q : cubP g -> (p < nedge)%N -> (q < nedge)%N ->
  epos (g^-1 (eprimf p)) = epos (g^-1 (eprimf q)) -> p = q.
Proof.
move=> cg pL qL e.
have key : g^-1 (eprimf p) = g^-1 (eprimf q) -> p = q.
  move=> /(@perm_inj _ g^-1) ee.
  by move: (f_equal epos ee); rewrite (epos_prim pL) (epos_prim qL).
have aE : ((g^-1 (eprimf p)) : nat) \in eprim ++ esec.
  by rewrite (cubP_edge _ (cubPV cg)) eprimf_edge.
have bE : ((g^-1 (eprimf q)) : nat) \in eprim ++ esec.
  by rewrite (cubP_edge _ (cubPV cg)) eprimf_edge.
case: (edge_case aE) => [aP|aS]; case: (edge_case bE) => [bP|bS].
- by apply: key; rewrite {1}aP e -bP.
- have : eprimf q = epair (eprimf p).
    apply: (@perm_inj _ g^-1).
    by rewrite (cubP_epairV _ cg) {1}bS -e -aP.
  by move=> /eqP; rewrite (negbTE (@eprimf_epair_neq p q pL qL)).
- have : eprimf p = epair (eprimf q).
    apply: (@perm_inj _ g^-1).
    by rewrite (cubP_epairV _ cg) {1}aS e -bP.
  by move=> /eqP; rewrite (negbTE (@eprimf_epair_neq q p qL pL)).
- by apply: key; rewrite {1}aS e -bS.
Qed.

(* THE FACT.  p |-> epos (g^-1 (eprimf p)) is injective on twelve positions
   with twelve values, hence a permutation of them, so the four positions it
   sends into the last four are counted exactly once each.  Stated and proved
   on SEQS -- perm_eq of the map with iota -- rather than through finset. *)
Lemma count_sliceb g : cubP g -> count (sliceb g) (iota 0 nedge) = nslice.
Proof.
move=> cg.
have hedge p : (p < nedge)%N -> ((g^-1 (eprimf p)) : nat) \in eprim ++ esec.
  by move=> pL; rewrite (cubP_edge _ (cubPV cg)) eprimf_edge.
have hE : {in iota 0 nedge, sliceb g =1
            (fun p => (nedge - nslice <= epos (g^-1 (eprimf p)))%N)}.
  move=> p; rewrite mem_iota add0n => /andP[_ pL].
  by rewrite /sliceb (scol_epos (hedge p pL)).
rewrite (eq_in_count hE).
have hsub : {subset [seq epos (g^-1 (eprimf p)) | p <- iota 0 nedge]
                    <= iota 0 nedge}.
  move=> r /mapP[p _ ->]; rewrite mem_iota add0n leq0n /=.
  exact: epos_lt.
have huniq : uniq [seq epos (g^-1 (eprimf p)) | p <- iota 0 nedge].
  (* the side condition SUPPLIED: `rewrite map_inj_in_uniq ?iota_uniq //'
     does not return *)
  have hinj : {in iota 0 nedge &,
                injective (fun p => epos (g^-1 (eprimf p)))}.
    move=> p q; rewrite !mem_iota !add0n => /andP[_ pL] /andP[_ qL].
    exact: eprimg_inj cg pL qL.
  by rewrite (map_inj_in_uniq hinj) iota_uniq.
have hsz : (seq.size (iota 0 nedge) <=
            seq.size [seq epos (g^-1 (eprimf p)) | p <- iota 0 nedge])%N.
  by rewrite size_map.
have hperm : perm_eq [seq epos (g^-1 (eprimf p)) | p <- iota 0 nedge]
                     (iota 0 nedge).
  apply: uniq_perm; [exact: huniq | exact: iota_uniq | ].
  by have [_ hi] := uniq_min_size huniq hsub hsz; exact: hi.
have -> : count (fun p => (nedge - nslice <= epos (g^-1 (eprimf p)))%N)
                (iota 0 nedge)
        = count (fun r => (nedge - nslice <= r)%N)
                [seq epos (g^-1 (eprimf p)) | p <- iota 0 nedge].
  by rewrite count_map.
(* seq.permP, NOT permP: all_fingroup shadows it with the {perm _} one *)
by rewrite (seq.permP hperm); vm_compute.
Qed.

(* -- from the count to the array read -------------------------------------- *)

(* THE PRODUCT IS NEVER NORMALISED, and that is the whole trick.  Section 3
   says to_nat nfsi = nfs "cannot be proved at all", and that is true of the
   LITERAL: nfs as a unary nat is a million successors.  But nfsi = 2048 * 495
   holds in int63 by machine arithmetic, to_nat is a morphism for the product,
   and 2048 and 495 are small.  So the bound travels to nat without either
   side ever being evaluated -- 0.56 s.  (thery's suggestion.) *)
Lemma nfsiE : to_nat nfsi = (nflip * nsrank)%N.
Proof.
have h2048 : to_nat 2048%uint63 = nflip by vm_compute.
have h495 : to_nat 495%uint63 = nsrank by vm_compute.
have hb : (to_nat 2048%uint63 * to_nat 495%uint63 < nwB)%N.
  rewrite h2048 h495.
  apply: leq_ltn_trans (_ : (2 ^ 20)%N < _); first by vm_compute.
  by rewrite nwB_pow ltn_exp2l.
rewrite (_ : nfsi = (2048 * 495)%uint63); last by vm_compute.
by rewrite (to_nat_mul _ _ hb) h2048 h495.
Qed.

(* the arithmetic half, with the srank bound as a hypothesis: the flip is
   eleven bits and the rank is below 495, so the index is below 2048 * 495 *)
Lemma fsidx_ltB x :
  (to_nat (PArray.get srank (Uint63.lsr x 12%uint63)) < nsrank)%N ->
  (fsidx x <? nfsi)%uint63.
Proof.
move=> hs; apply/nltbP; rewrite nfsiE /fsidx.
set f := to_nat (Uint63.land x 2047%uint63).
set s := to_nat (PArray.get srank (Uint63.lsr x 12%uint63)).
have hnw : (nflip * nsrank < nwB)%N.
  apply: leq_ltn_trans (_ : (2 ^ 20)%N < _); first by vm_compute.
  by rewrite nwB_pow ltn_exp2l.
have hf : (f < nflip)%N.
  rewrite /f landC -(_ : (2 ^ 11 = nflip)%N); last by vm_compute.
  by apply: to_nat_land_bound; vm_compute.
have hns : to_nat (of_nat nsrank) = nsrank.
  by apply: of_natK; apply: leq_ltn_trans hnw; vm_compute.
have hmulb : (f * to_nat (of_nat nsrank) < nwB)%N.
  rewrite hns; apply: leq_ltn_trans hnw.
  by rewrite leq_mul2r; apply/orP; right; exact: ltnW hf.
have hmul : to_nat (Uint63.mul (Uint63.land x 2047%uint63) (of_nat nsrank))
          = (f * nsrank)%N.
  by rewrite (to_nat_mul _ _ hmulb) hns.
have haddb : (to_nat (Uint63.mul (Uint63.land x 2047%uint63) (of_nat nsrank))
              + s < nwB)%N.
  rewrite hmul; apply: leq_ltn_trans hnw.
  apply: leq_trans (_ : (f.+1 * nsrank <= nflip * nsrank)%N).
    (* mulSnr, NOT mulSn + addnC: addnC has two additions to choose from here
       and the rewrite does not return *)
    by rewrite mulSnr leq_add2l; exact: ltnW hs.
  by rewrite leq_mul2r hf orbT.
rewrite (to_nat_add _ _ haddb) hmul -/s.
apply: leq_trans (_ : (f.+1 * nsrank <= nflip * nsrank)%N).
  by rewrite mulSnr ltn_add2l; exact: hs.
by rewrite leq_mul2r hf orbT.
Qed.

(* the shift, on bits: srank is indexed by the top twelve bits *)
Lemma nbit_lsr_nedge x j : (j < nedge)%N ->
  nbit (Uint63.lsr x 12%uint63) j = nbit x (nedge + j).
Proof.
move=> jL.
have hjw : (j < nwB)%N.
  by apply: small_nwB; apply: leq_trans jL _; vm_compute.
have hsw : (nedge + j < nwB)%N.
  apply: small_nwB; apply: leq_ltn_trans (_ : (nedge + nedge < 2 ^ 20)%N).
    by rewrite leq_add2l ltnW.
  by vm_compute.
have hsum : (12%uint63 + of_nat j)%uint63 = of_nat (nedge + j).
  rewrite (_ : 12%uint63 = of_nat nedge); last by vm_compute.
  exact: Fstab.of_nat_addE hsw.
have hcond : (of_nat j <=? 12%uint63 + of_nat j)%uint63.
  by apply/nlebP; rewrite hsum !of_natK // leq_addl.
by rewrite /nbit bit_lsr (ifT _ _ hcond) hsum.
Qed.

(* the mask is twelve bits, because the coordinate is twenty four *)
Lemma smask_lt g : (to_nat (Uint63.lsr (coordfs g) 12%uint63) < nmask)%N.
Proof.
have h12 : to_nat 12%uint63 = nedge by vm_compute.
rewrite to_nat_lsr h12 ltn_divLR ?expn_gt0 //.
rewrite (_ : (nmask = 2 ^ 12)%N); last by vm_compute.
by rewrite -expnD; exact: coordfs_lt.
Qed.

Lemma nbit_smask g j : (j < nedge)%N ->
  nbit (Uint63.lsr (coordfs g) 12%uint63) j = sliceb g j.
Proof.
move=> jL; rewrite nbit_lsr_nedge // /coordfs nbit_packn.
- by rewrite ltnNge leq_addr /= addKn.
- by rewrite /ncoord ltn_add2l.
- exact: ncoord_dig.
Qed.

(* THE TABLE FACT: a mask with four bits set has a rank, and it is below 495.
   4096 masks, so the check is instant.  The emitted table satisfies it
   exactly -- the 495 masks with four bits set get distinct ranks 0 .. 494 and
   every other mask gets 495. *)
Definition srankC : bool :=
  all (fun m => (count (nbit (of_nat m)) (iota 0 nedge) == nslice)
                ==> (to_nat (PArray.get srank (of_nat m)) < nsrank)%N)
      (iota 0 nmask).

Lemma srankCP : srankC.
Proof. by vm_compute. Qed.

(* the equation again, and again worth it: `allP srankCP' unfolds srankC by
   unification and costs 14.5 s at Qed, against 0.2 s through this *)
Lemma srankCE : srankC =
  all (fun m => (count (nbit (of_nat m)) (iota 0 nedge) == nslice)
                ==> (to_nat (PArray.get srank (of_nat m)) < nsrank)%N)
      (iota 0 nmask).
Proof. by []. Qed.

(* -- and the guard itself -------------------------------------------------- *)

(* THE cubP HYPOTHESIS IS NECESSARY: for an arbitrary permutation the slice
   mask is arbitrary, srank hands back its 495, and fsidx reaches exactly
   nfs.  It is the hypothesis coordfs_flip and coordfs_slice already carry. *)
Lemma fsidx_lt g : cubP g -> (fsidx (coordfs g) <? nfsi)%uint63.
Proof.
move=> cg; apply: fsidx_ltB.
have hmem : to_nat (Uint63.lsr (coordfs g) 12%uint63) \in iota 0 nmask.
  by rewrite mem_iota add0n leq0n smask_lt.
have hcount : count (nbit (of_nat (to_nat (Uint63.lsr (coordfs g) 12%uint63))))
                    (iota 0 nedge) == nslice.
  rewrite to_natK; apply/eqP; rewrite -(count_sliceb cg).
  apply: eq_in_count => j.
  by rewrite mem_iota add0n => /andP[_ jL]; exact: nbit_smask jL.
have hall : all (fun m => (count (nbit (of_nat m)) (iota 0 nedge) == nslice)
                ==> (to_nat (PArray.get srank (of_nat m)) < nsrank)%N)
      (iota 0 nmask).
  by rewrite -srankCE; exact: srankCP.
by have := implyP (allP hall _ hmem) hcount; rewrite to_natK.
Qed.

(* the entries are four bits, so the successor on the int side is the
   successor on the nat side -- no wrap.  Fstab.Dfsi_small verbatim. *)
Lemma Dp1i_small tw x : (to_nat (Dp1i tw x) < nwB.-1)%N.
Proof.
rewrite /Dp1i /Dp1ri /p1get.
set v := (X in (X land _)%uint63); rewrite landC.
apply: ltn_trans (_ : 2 ^ 4 < _); last first.
  rewrite -ltnS prednK; last by apply: ltn_trans ndigitsLwB.
  by apply: ltn_trans ndigitsLwB.
by apply: to_nat_land_bound.
Qed.

(* nfs < nwB, needed to move of_nat across the fsidx guard.  Proved the way
   ssrint63.ndigitsLwB is -- bound by a power of two, then nwB_pow -- because
   `by []` on a `_ < nwB` goal is the unary trap: 2 ^ 63 in successors. *)
Lemma nfsB : (nfs < nwB)%N.
Proof.
apply: leq_ltn_trans (_ : (2 ^ 20)%N < _); first by vm_compute.
by rewrite nwB_pow ltn_exp2l.
Qed.

(* STATED ON COORDINATES, not on g -- exactly Fstab.DfsStep_of_check.  The
   guard cubP that coordfs's coordM needs never appears here, and the step to
   g is taken later, where coordtw_step and coordM are applied together. *)
(* -- small facts about the move tables, hoisted so each gets its own Qed --- *)

Lemma mtabs_size : seq.size mtabs = 18.
Proof. by []. Qed.

Lemma nth_mtabs_ok k : (k < 18)%N -> tab_ok 47 (nth [::] mtabs k).
Proof.
by move=> kL; apply: (allP mtabs_ok); apply: mem_nth; rewrite mtabs_size.
Qed.

Lemma nth_moves_pt k : (k < 18)%N -> nth 1%g moves k = pt 47 (nth [::] mtabs k).
Proof. by move=> kL; rewrite mtabsE (nth_map [::]) ?mtabs_size. Qed.

(* the move as a permutation and the move as packed data agree *)
Lemma actfs_actfE x k : (k < 18)%N ->
  actfs x (nth 1%g moves k) = actf x (mdatf_of_tab (nth [::] mtabs k)).
Proof.
move=> kL; rewrite nth_moves_pt // actfE.
by apply: actdE; apply: nth_mtabs_ok.
Qed.

(* split in two so the Qeds are separate: getting the checked instance out of
   the loop, and then reading the k-th move out of it *)
Lemma p1stepF_of_check tw x :
  p1checkStep -> (to_nat tw < ntwist)%N -> (to_nat x < 2 ^ ncoord)%N ->
  p1stepF tw x.
Proof.
rewrite /p1checkStep => hcheck twL xL.
have htw : p1checkTw tw.
  move/allP: hcheck => /(_ (to_nat tw)).
  by rewrite mem_iota /= twL to_natK; apply.
rewrite p1checkTwE in htw.
exact: (all_powP ncoord_dig htw xL).
Qed.

Lemma p1checkStep_inst tw x k :
  p1stepF tw x -> fsok x -> (k < 18)%N ->
  (Dp1i tw x <=?
   incr (Dp1i (acttwi tw k) (actf x (mdatf_of_tab (nth [::] mtabs k)))))%uint63.
Proof.
move=> hall hs kL.
(* the guard, settled on its own and entirely in int63 *)
have hcond : ~~ fsok x = false by rewrite hs.
move: hall; rewrite /p1stepF hcond => hstep.
move: hstep => /(all_nthP (0%N, mdatf_of_tab [::])).
rewrite size_map size_iota => /(_ k kL).
(* nth_map_iota, not nth_map + nth_iota: with the length a literal the
   latter pair makes the iota compute and unfolds the whole list. *)
by rewrite (nth_map_iota _ _ kL).
Qed.

Lemma Dp1_step_of_check :
  p1checkStep ->
  forall tw x k, (to_nat tw < ntwist)%N -> (to_nat x < 2 ^ ncoord)%N ->
  fsok x -> (k < 18)%N ->
  (Dp1 tw x <=
   (Dp1 (acttwi tw k) (actfs x (nth 1%g moves k))).+1)%N.
Proof.
move=> hcheck tw x k twL xL fsL kL.
have F := p1checkStep_inst (p1stepF_of_check hcheck twL xL) fsL kL.
by rewrite (actfs_actfE _ kL) /Dp1; apply: leb_incr_le; last exact: Dp1i_small.
Qed.

(* Notes kept from the attempt: three causes found and fixed getting here,
   each worth a day if rediscovered.

     - htw must be UNFOLDED (rewrite /p1checkTw in htw) before all_powP, or
       unification expands all_pow ncoord into 2 ^ 24 conjuncts;
     - nfs must appear as the int63 literal nfsi, never as of_nat nfs.
       of_nat is O(n) on a unary nat, so of_nat nfs is a million reduction
       steps -- and the kernel would pay it inside a 4 * 10 ^ 10 loop;
     - to_nat nfsi = nfs cannot be proved at all: it materialises the unary
       nat and overflows the stack.  Hence the fsidx bound is stated in
       int63, as fsidx x <? nfsi.

   And the guard itself, which is what actually blocked: from
   fsL : (fsidx x <? nfsi) show (nfsi <=? fsidx x) = false.  case: ifP on the
   unfolded p1stepF and case E : on the bare condition both fail to return;
   apply/idP/negP to put both inequalities in the context, then nlebP/nltbP
   to move to nat and leqNgt to close, is thery's route and is instant.   *)

(* =========================================================================  *)
(*  6bis.  The heuristic at a permutation                                     *)
(*                                                                            *)
(*  What Searchr.v asks of a heuristic is exactly two things -- h 1 = 0 and   *)
(*  h g <= (h (g * m)).+1 for every move -- and those are what p1check0 and   *)
(*  p1checkStep buy.  This section turns the one into the other.              *)
(*                                                                            *)
(*  IT CANNOT GO THROUGH Coordfs.hcoordg, and the reason is worth recording:  *)
(*  that section wants `Dstep' for EVERY x, and Dp1 does not have it.  Fstab  *)
(*  does, because a coordinate past 2 ^ ncoord indexes past the table and     *)
(*  reads 0, which is below everything.  Here the rows are contiguous, so an  *)
(*  out of range rank lands in a neighbouring row and reads a perfectly good  *)
(*  entry for a different state.  So the guard is discharged by hand, from    *)
(*  the invariant, and fsidx_lt is what makes it possible.                    *)
(* =========================================================================  *)

(* the twist coordinate is seven base 3 digits, hence below 3 ^ 7 *)
Lemma coordtw_lt g : (to_nat (coordtw g) < ntwist)%N.
Proof.
rewrite coordtwE.
apply: leq_trans (pack3n_lt 7 _) _.
by rewrite (_ : (3 ^ 7 = ntwist)%N) //; vm_compute.
Qed.

Lemma size_moves18 : seq.size moves = 18%N.
Proof. by rewrite mtabsE size_map; vm_compute. Qed.

(* a move is the k-th move table for some k, which is how the abstract
   `m \in Sset' meets acttwi's numbered interface *)
Lemma Sset_move m : m \in Sset ->
  exists2 k, (k < 18)%N & m = pt 47 (nth [::] mtabs k).
Proof.
rewrite inE => /(nthP 1%g)[k kL kE].
have kL18 : (k < 18)%N by move: kL; rewrite size_moves18.
by exists k => //; rewrite -kE mtabsE (nth_map [::]).
Qed.

Lemma hmovesE k : (k < 18)%N -> nth 1%g moves k = pt 47 (nth [::] mtabs k).
Proof. by move=> kL; rewrite mtabsE (nth_map [::]). Qed.

(* HOISTED ABOVE Section P1Heur, and it has to be: inside it the context
   holds hchkS : p1checkStep, and every `done' -- including the sixteen that
   close odd_count_addb's four case splits -- then tries `assumption'
   against it and unfolds an all_pow at ncoord = 24.  None of these lemmas
   mentions the table.  The same trap as everywhere else in this file. *)

(* ---- the flip parity, the edge analogue of twsum ------------------------- *)

(* odd (count _) is a sum in F2, so a pointwise xor splits *)
Lemma odd_count_addb (T : Type) (f g : T -> bool) (s : seq T) :
  odd (count (fun k => f k (+) g k) s) = odd (count f s) (+) odd (count g s).
Proof.
elim: s => [|a s IH] //=; rewrite !oddD IH.
by case: (f a); case: (g a); case: (odd (count f s)); case: (odd (count g s)).
Qed.

(* THE TWO FACTS ABOUT THE MOVES it rests on: each permutes the twelve edges,
   and flips an EVEN number of them.  Both finite, so both checked. *)
Definition mtabs_fpar : bool :=
  all (fun mt => perm_eq (msrc mt) (iota 0 nedge)
                 && ~~ odd (count id (mxbit mt))) mtabs.

Lemma mtabs_fparP : mtabs_fpar.
Proof. by vm_compute. Qed.

(* the flip half of actd is the flip half of x permuted, then xored with the
   move's own xbit vector, so the PARITY picks up only the second -- and that
   is a constant of the move, not of x *)
Lemma fpar_actd x d :
  perm_eq d.1 (iota 0 nedge) -> seq.size d.2 = nedge ->
  fpar (actd x d) = fpar x (+) odd (count id d.2).
Proof.
move=> hp hs; rewrite /fpar.
have hnb j : j \in iota 0 nedge ->
    nbit (actd x d) j = nbit x (nth 0%N d.1 j) (+) nth false d.2 j.
  rewrite mem_iota add0n => /andP[_ jL].
  rewrite /actd (nbit_packn _ (j := j)) //; first by rewrite jL.
  by apply: leq_trans jL (leq_addr _ _).
rewrite (eq_in_count hnb) odd_count_addb; congr (_ (+) _).
  rewrite -(seq.permP hp (nbit x)) -count_map.
  have hsz : seq.size d.1 = nedge by rewrite (perm_size hp) size_iota.
  by rewrite -hsz -/(mkseq _ _) mkseq_nth.
by rewrite -(count_map (nth false d.2) id) -hs -/(mkseq _ _) mkseq_nth.
Qed.

(* THE INVARIANT: a move does not change the flip parity *)
Lemma fpar_actfsS x m : m \in Sset -> fpar (actfs x m) = fpar x.
Proof.
move=> mS; have [k kL mE] := Sset_move mS.
have hsz : seq.size mtabs = 18%N by vm_compute.
have hmt : nth [::] mtabs k \in mtabs by rewrite mem_nth // hsz.
have mok : tab_ok 47 (nth [::] mtabs k) by apply: (allP mtabs_ok).
have /andP[hp hx] := allP mtabs_fparP _ hmt.
(* @: Unset Strict Implicit makes d implicit, and hp's type only fixes
   d.1 through a projection, which unification will not invert *)
rewrite mE (actdE _ mok)
        (@fpar_actd x (mdat_of_tab (nth [::] mtabs k)) hp).
  by move: hx; rewrite mdat_snd; case: odd => //=; rewrite addbF.
by rewrite mdat_snd /mxbit size_map size_iota.
Qed.

(* the slice half of the guard, at a real cube.  The first half of fsidx_lt,
   which runs the two together. *)
Lemma sok_coordfs g : cubP g -> sok (coordfs g).
Proof.
move=> cg; rewrite /sok; apply/nltbP.
rewrite (_ : to_nat nsranki = nsrank); last by vm_compute.
have hmem : to_nat (Uint63.lsr (coordfs g) 12%uint63) \in iota 0 nmask.
  by rewrite mem_iota add0n leq0n smask_lt.
have hcount : count (nbit (of_nat (to_nat (Uint63.lsr (coordfs g) 12%uint63))))
                    (iota 0 nedge) == nslice.
  rewrite to_natK; apply/eqP; rewrite -(count_sliceb cg).
  apply: eq_in_count => j.
  by rewrite mem_iota add0n => /andP[_ jL]; exact: nbit_smask jL.
have hall : all (fun m => (count (nbit (of_nat m)) (iota 0 nedge) == nslice)
                ==> (to_nat (PArray.get srank (of_nat m)) < nsrank)%N)
      (iota 0 nmask).
  by rewrite -srankCE; exact: srankCP.
by have := implyP (allP hall _ hmem) hcount; rewrite to_natK.
Qed.

Section P1Heur.

Hypothesis hchk0 : p1check0.
Hypothesis hchkS : p1checkStep.

(* the invariant: cubP for the flip x slice half, twP for the twist half *)
(* CARRIED, like twsum g = 0 and for the same reason: a single flipped edge is
   a rigid cubie permutation, so cubP does not give it.  With it, twcP g is
   exactly what p1stepF's guard asks of coordfs g. *)
Definition twcP (g : {perm facelet}) : bool :=
  [&& cubP g, twP g & ~~ fpar (coordfs g)].

Lemma twcP1 : twcP 1.
Proof.
(* !andTb, NOT /=: see the note in Farp1.hv1E -- simpl here unfolds twP *)
rewrite /twcP cubP1 twP1 !andTb.
by rewrite coordfs1E; vm_compute.
Qed.

Lemma twcPM g m : twcP g -> m \in Sset -> twcP (g * m).
Proof.
move=> /and3P[cg tg fg] mS; rewrite /twcP (cubP_step cg mS) /=.
rewrite (coordfsMS cg mS) (fpar_actfsS _ mS) fg andbT.
by have [k kL ->] := Sset_move mS; exact: twPM.
Qed.

(* and so the guard holds at every state the search reaches *)
Lemma fsok_twcP g : twcP g -> fsok (coordfs g).
Proof. by move=> /and3P[cg _ fg]; rewrite fsokE (sok_coordfs cg). Qed.

(* 0 off the invariant, which is what makes both obligations unconditional --
   Coordfs.hcoordg's trick, done by hand for the reason above *)
Definition hp1 (g : {perm facelet}) : nat :=
  if twcP g then Dp1 (coordtw g) (coordfs g) else 0%N.

(* EQUATIONS, because `case: ifP' and `case E :' on this guard are the trap
   the notes below record: one of them returned once and timed out the next
   time on the same goal. *)
Lemma hp1E g : twcP g -> hp1 g = Dp1 (coordtw g) (coordfs g).
Proof. by rewrite /hp1 => ->. Qed.

Lemma hp1N g : ~~ twcP g -> hp1 g = 0%N.
Proof. by rewrite /hp1 => /negbTE ->. Qed.

Lemma hp10 : hp1 1 = 0%N.
Proof. by rewrite /hp1 twcP1 (Dp1_0_of_check hchk0). Qed.

Lemma hp1S g m : m \in Sset -> hp1 g <= (hp1 (g * m)).+1.
Proof.
move=> mS; have [Pg|nPg] := boolP (twcP g); last by rewrite (hp1N nPg).
rewrite (hp1E Pg) (hp1E (twcPM Pg mS)).
have /and3P[cg /andP[cc /eqP ts] _] := Pg.
have [k kL mE] := Sset_move mS.
rewrite mE (coordfsMS cg _); last by rewrite -mE.
rewrite (coordtw_step kL cc ts) -(acttwiE (coordtw_lt g) kL) -(hmovesE kL).
exact: (Dp1_step_of_check hchkS (coordtw_lt g) (coordfs_lt _)
                          (fsok_twcP Pg) kL).
Qed.

End P1Heur.

End P1Tab.

(* =========================================================================  *)
(*  7.  The dummy table                                                       *)
(*                                                                            *)
(*  Every entry zero, so Dp1 is 0 everywhere: an admissible heuristic that    *)
(*  prunes nothing.  It exists so that everything downstream -- the search    *)
(*  carrying twists, h5 as a max of Dp1 -- can be built and RUN before the    *)
(*  five chunks of literals are emitted.  Swapping the real table in later    *)
(*  only makes the search faster; it cannot make it wrong, and it cannot      *)
(*  make it right either -- that is what p1check0 and p1checkStep are for,    *)
(*  and the dummy passes both BY PROOF rather than by evaluation, which the   *)
(*  real table cannot do.                                                     *)
(*                                                                            *)
(*  The three fold tables get dummies too: the identity symmetry everywhere   *)
(*  and one orbit, which is the fold of a table that is constant anyway.      *)
(*                                                                            *)
(*  With the dummy, `max (h5 ...) (Dp1 ...)' is exactly today's h5, so the    *)
(*  depth 12-14 runs stay comparable while the wiring is developed.           *)
(* =========================================================================  *)

Definition p1dummy : PArray.array arr :=
  PArray.make (of_nat nchunk) (PArray.make 1%uint63 0%uint63).

(* every rank in orbit 0, reached by the symmetry 0, which leaves the twist *)

(* PArray.get on a `make' is the fill value at EVERY index -- in range or not,
   since the fill value is also the default.  So the two nested reads give 0
   and the shift and mask leave it there.

   THE PATTERNS ARE NOT OPTIONAL: a bare `rewrite PArray.get_make' fails on
   both reads ("does not match any subterm"), because the two are at different
   types -- array (array int) and array int -- and the implicit A is what
   unification gets wrong.  Naming the redex fixes it, and this is the same
   "arguments explicit" rule the conjugation rewrites in Sym.v needed. *)
Lemma p1get_dummy i : p1get p1dummy i = 0%uint63.
Proof.
rewrite /p1get /p1dummy.
rewrite [PArray.get (PArray.make (of_nat nchunk)
                       (PArray.make 1%uint63 0%uint63)) _]PArray.get_make.
rewrite [PArray.get (PArray.make 1%uint63 0%uint63) _]PArray.get_make.
by rewrite lsr0 land0.
Qed.

Lemma Dp1i_dummy tw x :
  Dp1i p1dummy tw x = 0%uint63.
Proof. exact: p1get_dummy. Qed.

Lemma Dp1_dummy tw x : Dp1 p1dummy tw x = 0%N.
Proof. by rewrite /Dp1 Dp1i_dummy to_nat_0. Qed.

Lemma p1check0_dummy : p1check0 p1dummy.
Proof. by rewrite /p1check0 Dp1i_dummy. Qed.

(* `apply/allP' does NOT work on this goal -- the view leaves an evar for the
   list and reports "no assumption" -- and neither `/Dp1i' nor a bang does.
   Rewriting the predicate to xpredT, then naming each redex, is instant. *)
Lemma p1stepF_dummy tw x :
  p1stepF p1dummy tw x.
Proof.
(* the guard branch closed by isT, NOT by //: done on the other branch has
   the whole p1mdata all in front of it and reaches for the tables *)
rewrite /p1stepF; case: ifP => [_|_]; first exact: isT.
rewrite (eq_all (a2 := xpredT)) ?all_predT // => km.
by rewrite [Dp1i p1dummy tw x]p1get_dummy
           [Dp1i p1dummy (acttwi tw km.1) (actf x km.2)]p1get_dummy.
Qed.

(* BY PROOF, NOT BY EVALUATION, and that is the whole point of the dummy:
   all_pow_all takes a predicate that is true everywhere and never unfolds the
   2 ^ 24 loop.  The real table has to be checked by the kernel instead. *)
Lemma p1checkStep_dummy : p1checkStep p1dummy.
Proof.
apply/allP => t _; rewrite p1checkTwE.
by apply: Fstab.all_pow_all => x; exact: p1stepF_dummy.
Qed.

(* so the two things the search needs hold, unconditionally *)
Lemma Dp1_0_dummy :
  Dp1 p1dummy (coordtw 1) (coordfs 1) = 0%N.
Proof. exact/Dp1_0_of_check/p1check0_dummy. Qed.

Lemma Dp1_step_dummy :
  forall tw x k, (to_nat tw < ntwist)%N -> (to_nat x < 2 ^ ncoord)%N ->
  fsok x -> (k < 18)%N ->
  (Dp1 p1dummy tw x <=
   (Dp1 p1dummy (acttwi tw k)
        (actfs x (nth 1%g moves k))).+1)%N.
Proof. exact: (Dp1_step_of_check p1checkStep_dummy). Qed.

(* =========================================================================  *)
(*  8.  Still to build (code, not proof)                                      *)
(*                                                                            *)
(*  - the emission of the real table: 5 chunks of literals, plus the orbit,   *)
(*    symmetry and twist tables the fold reads.  bench/p1gen.ml `emit', and   *)
(*    it runs on roquableu, not here                                          *)
(*  - Far.v's searchz5 carries five flip x slice coordinates; it must carry   *)
(*    five twists as well, and h5 becomes a max of five Dp1.  THIS CAN BE     *)
(*    DONE NOW, against p1dummy, and swapping the real table in afterwards    *)
(*    changes no proof                                                        *)
(* =========================================================================  *)
