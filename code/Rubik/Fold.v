(* =========================================================================  *)
(*  Fold.v -- the fold: the table and the folding functions as variables,   *)
(*            and the seventeen facts assumed of them.                      *)
(*                                                                          *)
(*  See fold.md for the design, the pitfalls and the numbers.               *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts Phase1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* =========================================================================  *)
(*  1.  The folded index and the folded read                                  *)
(* =========================================================================  *)

Definition nsym    := 16.      (* the symmetries that fix the U/D axis      *)
Definition norblog := 17.      (* 2 ^ 17 covers the orbit indices           *)

(* the orbits of ranks under those sixteen, as an int63 LITERAL: of_nat
   walks a unary nat, and this number is read once per node *)
Definition norbi : int := 64430%uint63.

(* the folded table is orbit major: one block of ntwist entries per orbit *)
Definition foldi (rep tw : int) : int :=
  Uint63.add (Uint63.mul rep ntwisti) tw.

(* the folded read: the orbit of r, and the twist carried through the
   symmetry that takes r to that orbit's representative *)
Definition Dfoldi (F : PArray.array arr) (frep fsym : int -> int)
    (twsym : int -> int -> int) (tw r : int) : int :=
  p1get F (foldi (frep r) (twsym tw (fsym r))).

Definition Dfold (F : PArray.array arr) (frep fsym : int -> int)
    (twsym : int -> int -> int) (tw r : int) : nat :=
  to_nat (Dfoldi F frep fsym twsym tw r).

(* four bits per entry, so the successor on the int side is the successor on
   the nat side.  Phase1.Dp1i_small verbatim, and it needs no hypothesis. *)
Lemma Dfoldi_small F frep fsym twsym tw r :
  (to_nat (Dfoldi F frep fsym twsym tw r) < nwB.-1)%N.
Proof.
rewrite /Dfoldi /p1get.
set v := (X in (X land _)%uint63); rewrite landC.
apply: ltn_trans (_ : 2 ^ 4 < _); last first.
  rewrite -ltnS prednK; last by apply: ltn_trans ndigitsLwB.
  by apply: ltn_trans ndigitsLwB.
by apply: to_nat_land_bound.
Qed.

(* the orbit index fits the loop below *)
Lemma norbi_dig : (to_nat norbi < 2 ^ norblog)%N.
Proof. by vm_compute. Qed.

Lemma norblog_dig : norblog <= ndigits.
Proof. by vm_compute. Qed.

(* an orbit index below norbi passes the loop guard.  Stated on int63 and
   proved through nltbP and nlebP: the nat value of norbi is not needed, and
   the nat form of the guard is what makes `case: ifP' diverge. *)
Lemma norbi_guard i : (i <? norbi)%uint63 -> (norbi <=? i)%uint63 = false.
Proof.
move/nltbP => iL; apply/negbTE/negP => /nlebP h.
by move: iL; rewrite ltnNge h.
Qed.

(* ---- the widths the generator packs with -------------------------------- *)

Definition nsymi   : int := 16%uint63.                 (* nsym            *)
Definition nrbits  := 20.                (* 2 ^ 20 covers the ranks       *)
Definition nwide   : int := 3%uint63.       (* twenty bit values a word    *)
Definition wbits   : int := 20%uint63.
Definition wmaski  : int := 1048575%uint63.            (* 2 ^ 20 - 1      *)
Definition nnarrow : int := 15%uint63.        (* four bit values a word    *)
Definition nbits   : int := 4%uint63.
Definition nmask4  : int := 15%uint63.

(* a twenty bit value out of a flat array, three to a word *)
Definition get20 (a : arr) (i : int) : int :=
  let w := Uint63.div i nwide in
  let j := Uint63.sub i (Uint63.mul w nwide) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j wbits)) wmaski.

(* a four bit value out of a flat array, fifteen to a word *)
Definition get4 (a : arr) (i : int) : int :=
  let w := Uint63.div i nnarrow in
  let j := Uint63.sub i (Uint63.mul w nnarrow) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j nbits)) nmask4.

(* =========================================================================  *)
(*  2.  The data the fold needs, and what is assumed of it                    *)
(*                                                                            *)
(*  F        the folded table, orbit major, four bits per entry               *)
(*  frep r   the orbit of the rank r, an index below norbi                    *)
(*  fsym r   a symmetry taking r to its orbit representative                  *)
(*  rrep r   the RANK of that representative                                  *)
(*  reps i   the rank of the representative of the orbit i                    *)
(*  twsym    a symmetry acting on twists                                      *)
(*  ract     a symmetry acting on ranks                                       *)
(*  smul     the composition of two symmetries                                *)
(*  actr     a move acting on ranks                                           *)
(*  msym k s the move a symmetry s turns the move k into                      *)
(* =========================================================================  *)

Section Fold.

Variable F : PArray.array arr.
Variables frep fsym rrep reps : int -> int.
Variables twsym ract smul : int -> int -> int.
Variable actr : int -> nat -> int.
Variable msym : nat -> int -> nat.

Local Notation D := (Dfoldi F frep fsym twsym).

(* -- everything below is about RANKS, so r <? nfsi throughout -------------- *)

(* THE RANK GUARD IS NOT DECORATION.  The four rank tables have nfs entries,
   so at r past nfs they answer with their default and none of the equations
   below can hold there.  It is Phase1's fsok guard again, and a caller
   discharges it the same way, by Phase1.fsidx_lt. *)

(* fsym r really does carry r to the representative of its orbit *)
Hypothesis fsymE : forall r, (r <? nfsi)%uint63 -> ract r (fsym r) = rrep r.
Hypothesis fsymL : forall r, (r <? nfsi)%uint63 -> (to_nat (fsym r) < nsym)%N.

(* the orbit and its representative do not move inside the orbit *)
Hypothesis frepS : forall r s, (r <? nfsi)%uint63 -> (to_nat s < nsym)%N ->
  frep (ract r s) = frep r.
Hypothesis rrepS : forall r s, (r <? nfsi)%uint63 -> (to_nat s < nsym)%N ->
  rrep (ract r s) = rrep r.

(* the orbit table and the representative table name the same rank *)
Hypothesis repsE : forall r, (r <? nfsi)%uint63 -> reps (frep r) = rrep r.

(* THE RANGE OBLIGATIONS.  Rows are contiguous, so an orbit index at or past
   norbi, or a twist at or past ntwist, does not read a default: it reads a
   good entry belonging to another state.  Both are what let the check at the
   representatives be read back at r. *)
Hypothesis frepL : forall r, (r <? nfsi)%uint63 -> (frep r <? norbi)%uint63.
Hypothesis twsymL : forall tw s, (to_nat tw < ntwist)%N ->
  (to_nat s < nsym)%N -> (to_nat (twsym tw s) < ntwist)%N.

(* a symmetry and a move both take a rank to a rank *)
Hypothesis ractL : forall r s, (r <? nfsi)%uint63 -> (to_nat s < nsym)%N ->
  (ract r s <? nfsi)%uint63.
Hypothesis actrL : forall r k, (r <? nfsi)%uint63 -> (k < 18)%N ->
  (actr r k <? nfsi)%uint63.

(* -- the symmetries act --------------------------------------------------- *)

(* THE TWIST BOUND IS NOT DECORATION, here as in stabE: past ntwist the
   twist table has no entry and answers with its default, so neither of the
   two equations below can hold there.  Every caller has the bound. *)
Hypothesis twsymA : forall tw s t, (to_nat tw < ntwist)%N ->
  (to_nat s < nsym)%N -> (to_nat t < nsym)%N ->
  twsym (twsym tw s) t = twsym tw (smul s t).
Hypothesis ractA : forall r s t, (r <? nfsi)%uint63 -> (to_nat s < nsym)%N ->
  (to_nat t < nsym)%N -> ract (ract r s) t = ract r (smul s t).
Hypothesis smulL : forall s t, (to_nat s < nsym)%N -> (to_nat t < nsym)%N ->
  (to_nat (smul s t) < nsym)%N.

(* THE ONE OBLIGATION THAT IS NOT BOOKKEEPING.  A rank whose orbit is shorter
   than sixteen is taken to its representative by several symmetries, and
   those symmetries send the twist to different places.  So the folded row of
   such an orbit must give the same entry for all of them, and no shape
   argument supplies that -- it is a property of the emitted table.  On a
   table built from a genuine distance it holds, because a symmetry fixing
   the rank relates two states at the same distance. *)
Hypothesis stabE : forall tw r u, (to_nat tw < ntwist)%N ->
  (r <? nfsi)%uint63 -> (to_nat u < nsym)%N ->
  ract r u = rrep r -> p1get F (foldi (frep r) (twsym tw u)) = D tw r.

(* a move keeps the twist a twist, which the check below needs twice *)
Hypothesis acttwiL : forall tw k, (to_nat tw < ntwist)%N -> (k < 18)%N ->
  (to_nat (acttwi tw k) < ntwist)%N.

(* -- the symmetries permute the moves -------------------------------------- *)

Hypothesis msymL : forall k s, (k < 18)%N -> (to_nat s < nsym)%N ->
  (msym k s < 18)%N.
Hypothesis msymT : forall tw k s, (to_nat tw < ntwist)%N -> (k < 18)%N ->
  (to_nat s < nsym)%N ->
  acttwi (twsym tw s) (msym k s) = twsym (acttwi tw k) s.
Hypothesis msymR : forall r k s, (r <? nfsi)%uint63 -> (k < 18)%N ->
  (to_nat s < nsym)%N -> actr (ract r s) (msym k s) = ract (actr r k) s.

(* -- the rank action is the packed action, ranked -------------------------- *)

(* the search carries ranks, so the emitted move table is by rank; actf is
   the same move on the packed summary *)
Hypothesis actrE : forall x k, (k < 18)%N ->
  fsidx (actf x (mdatf_of_tab (nth [::] mtabs k))) = actr (fsidx x) k.

(* =========================================================================  *)
(*  3.  The folded read is the same at every point of an orbit                *)
(*                                                                            *)
(*  This is what the fold means, and it is the only place the stabiliser      *)
(*  hypothesis is used.                                                       *)
(* =========================================================================  *)

Lemma DfoldiS tw r s : (to_nat tw < ntwist)%N -> (r <? nfsi)%uint63 ->
  (to_nat s < nsym)%N -> D (twsym tw s) (ract r s) = D tw r.
Proof.
move=> twL rL sL; have qL := ractL rL sL; have tL := fsymL qL.
rewrite -[RHS](stabE twL rL (smulL sL tL) _); last first.
  by rewrite -(ractA rL sL tL) (fsymE qL) (rrepS rL sL).
by rewrite /Dfoldi (frepS rL sL) (twsymA twL sL tL).
Qed.

(* =========================================================================  *)
(*  4.  The two checks, at the orbit representatives only                     *)
(*                                                                            *)
(*  Phase1.p1checkStep sweeps every rank; this one sweeps the orbits, which   *)
(*  is where the fold pays.  The loop is an all_pow over 2 ^ 17 orbit indices *)
(*  with the ones past norbi guarded out, and an all over the twists so that  *)
(*  of_nat is paid once per twist rather than once per state.                 *)
(* =========================================================================  *)

Definition foldstepF (tw i : int) : bool :=
  let r := reps i in
  all (fun k => (D tw r <=? incr (D (acttwi tw k) (actr r k)))%uint63)
      (iota 0 18).

Definition foldcheckOrb (tw : int) : bool :=
  all_pow norblog 0%uint63
    (fun i => (norbi <=? i)%uint63 || foldstepF tw i).

Definition foldcheckStep : bool :=
  all (fun t => foldcheckOrb (of_nat t)) (iota 0 ntwist).

(* An EQUATION, not a delta step: any conversion that sees through
   foldcheckOrb unfolds the all_pow into 2 ^ 17 conjuncts. *)
Lemma foldcheckOrbE tw :
  foldcheckOrb tw =
  all_pow norblog 0%uint63
    (fun i => (norbi <=? i)%uint63 || foldstepF tw i).
Proof. by rewrite /foldcheckOrb. Qed.

Definition foldcheck0 : bool :=
  (D (ctwistt (id_tab 47)) (fsidx (coordt (id_tab 47))) =? 0)%uint63.

(* the two loops cut into slices, as Phase1.p1checkStep_split does *)
Lemma foldcheckStep_split n :
  all (fun t => foldcheckOrb (of_nat t)) (take n (iota 0 ntwist)) ->
  all (fun t => foldcheckOrb (of_nat t)) (drop n (iota 0 ntwist)) ->
  foldcheckStep.
Proof.
rewrite /foldcheckStep -{3}(cat_take_drop n (iota 0 ntwist)) all_cat.
by move=> -> ->.
Qed.

(* =========================================================================  *)
(*  5.  What the checks buy                                                   *)
(* =========================================================================  *)

(* getting the checked instance out of the two loops *)
Lemma foldstepF_of_check tw i :
  foldcheckStep -> (to_nat tw < ntwist)%N -> (i <? norbi)%uint63 ->
  foldstepF tw i.
Proof.
rewrite /foldcheckStep => hcheck twL iL.
have htw : foldcheckOrb tw.
  move/allP: hcheck => /(_ (to_nat tw)).
  by rewrite mem_iota add0n leq0n twL to_natK; apply.
rewrite foldcheckOrbE in htw.
have hi : (to_nat i < 2 ^ norblog)%N.
  by apply: leq_trans (ltnW norbi_dig); apply/nltbP.
by have := all_powP norblog_dig htw hi; rewrite (norbi_guard iL) orFb.
Qed.

(* and the k-th move out of the instance *)
Lemma foldstepF_inst tw i k : foldstepF tw i -> (k < 18)%N ->
  (D tw (reps i) <=? incr (D (acttwi tw k) (actr (reps i) k)))%uint63.
Proof.
move=> /allP hall kL; apply: hall.
by rewrite mem_iota add0n leq0n kL.
Qed.

(* THE POINT OF THE FILE: checked at the representatives, true at every
   rank.  The symmetry moves the state to the representative, the check
   fires there, and DfoldiS moves the moved state back. *)
Lemma Dfoldi_step_of_check :
  foldcheckStep ->
  forall tw r k, (to_nat tw < ntwist)%N -> (r <? nfsi)%uint63 -> (k < 18)%N ->
  (D tw r <=? incr (D (acttwi tw k) (actr r k)))%uint63.
Proof.
move=> hcheck tw r k twL rL kL; have sL := fsymL rL.
have hs : foldstepF (twsym tw (fsym r)) (frep r).
  by apply: foldstepF_of_check;
     [exact: hcheck | exact: (twsymL twL sL) | exact: (frepL rL)].
have := foldstepF_inst hs (msymL kL sL).
rewrite (repsE rL) -(fsymE rL) (msymT twL kL sL) (msymR rL kL sL).
by rewrite (DfoldiS twL rL sL) (DfoldiS (acttwiL twL kL) (actrL rL kL) sL).
Qed.

(* the same in nat, which is the form Searchr.v asks for *)
Lemma Dfold_step_of_check :
  foldcheckStep ->
  forall tw r k, (to_nat tw < ntwist)%N -> (r <? nfsi)%uint63 -> (k < 18)%N ->
  (Dfold F frep fsym twsym tw r <=
   (Dfold F frep fsym twsym (acttwi tw k) (actr r k)).+1)%N.
Proof.
move=> hcheck tw r k twL rL kL; rewrite /Dfold.
apply: leb_incr_le; last exact: Dfoldi_small.
exact: (Dfoldi_step_of_check hcheck twL rL kL).
Qed.

(* the step at a packed summary, which is the shape Phase1.Dp1_step_of_check
   has; the rank guard is what Phase1.fsidx_lt discharges *)
Lemma Dfoldx_step_of_check :
  foldcheckStep ->
  forall tw x k, (to_nat tw < ntwist)%N -> (fsidx x <? nfsi)%uint63 ->
  (k < 18)%N ->
  (Dfold F frep fsym twsym tw (fsidx x) <=
   (Dfold F frep fsym twsym (acttwi tw k)
      (fsidx (actfs x (nth 1%g moves k)))).+1)%N.
Proof.
move=> hcheck tw x k twL rL kL.
rewrite (actfs_actfE _ kL) (actrE _ kL).
exact: (Dfold_step_of_check hcheck twL rL kL).
Qed.

Lemma Dfold_0_of_check :
  foldcheck0 -> Dfold F frep fsym twsym (coordtw 1) (fsidx (coordfs 1)) = 0%N.
Proof.
rewrite /foldcheck0 /Dfold coordtw1E coordfs1E.
by move=> /eqb_correct ->; rewrite to_nat_0.
Qed.

End Fold.
