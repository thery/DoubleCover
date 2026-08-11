(* =========================================================================  *)
(*  FoldChecks.v -- The twelve checks as hypotheses, and the fact each one  *)
(*     buys.                                                                *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts Phase1 Far
        Fold Sym16.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Definition ntwbits := 12.               (* 2 ^ 12 covers the 2187 twists   *)

(* =========================================================================  *)
(*  1.  Reading a checked loop back at a point                                *)
(* =========================================================================  *)

(* The sixteen symmetries as int63 values.  A loop over `iota 0 16' would
   read them as `of_nat s', and the instance at an int s could then only be
   recovered by unifying `f (of_nat s)' -- not a pattern, so not solvable.
   Over this list the loop is `all f sym16i' and f is read off directly. *)
Definition sym16i : seq int :=
  Eval vm_compute in [seq of_nat i | i <- iota 0 16].

(* The four loop shapes as functions.  As NOTATIONS they would have had to
   capture their index, and a notation argument is read in the ambient scope,
   where that index does not exist. *)
Definition allrank (f : int -> bool) : bool :=
  all_powi nrbits 0%uint63 (Uint63.lsl 1 (of_nat nrbits))
           (fun r => if (nfsi <=? r)%uint63 then true else f r).

Definition alltw (f : int -> bool) : bool :=
  all_powi ntwbits 0%uint63 (Uint63.lsl 1 (of_nat ntwbits))
           (fun tw => if (ntwisti <=? tw)%uint63 then true else f tw).

Definition allsym (f : int -> bool) : bool := all f sym16i.

Definition allmv (f : nat -> bool) : bool := all f (iota 0 18).

(* and the eighteen moves as int63 values, for the same reason: a loop that
   reads them as `of_nat k' cannot be instantiated at an int k. *)
Definition mv18i : seq int :=
  Eval vm_compute in [seq of_nat i | i <- iota 0 18].

Definition allmvi (f : int -> bool) : bool := all f mv18i.

(* the rank loop: 2 ^ 20 values with the ones past nfsi guarded out.  This is
   FoldTables.frepL's proof, said once. *)
Lemma rank_of_check (f : int -> bool) :
  allrank f -> forall r, (r <? nfsi)%uint63 -> f r.
Proof.
rewrite /allrank => hchk r hr.
have h1 : (to_nat r < to_nat nfsi)%N by apply/nltbP.
have hlt : (to_nat r < 2 ^ nrbits)%N by apply: leq_trans h1 _; vm_compute.
have hall : all_pow nrbits 0%uint63
              (fun r0 => if (nfsi <=? r0)%uint63 then true else f r0).
  by rewrite -all_powiE //; exact: hchk.
have := all_powP (k := nrbits) _ hall hlt.
have -> : (nfsi <=? r)%uint63 = false.
  by apply: negbTE; apply/negP => /nlebP; rewrite leqNgt h1.
by apply; vm_compute.
Qed.

(* the twist loop, the same at 2 ^ 12 *)
Lemma twist_of_check (f : int -> bool) :
  alltw f -> forall tw, (to_nat tw < ntwist)%N -> f tw.
Proof.
rewrite /alltw => hchk tw htw.
have hlt : (to_nat tw < 2 ^ ntwbits)%N by apply: leq_trans htw _; vm_compute.
have hall : all_pow ntwbits 0%uint63
              (fun tw0 => if (ntwisti <=? tw0)%uint63 then true else f tw0).
  by rewrite -all_powiE //; exact: hchk.
have := all_powP (k := ntwbits) _ hall hlt.
have -> : (ntwisti <=? tw)%uint63 = false.
  by apply: negbTE; apply/negP => /nlebP; rewrite leqNgt htw.
by apply; vm_compute.
Qed.

Lemma sym16i_mem s : (to_nat s < nsym)%N -> s \in sym16i.
Proof.
move=> sL; rewrite -(to_natK s).
have -> : sym16i = [seq of_nat i | i <- iota 0 16] by vm_compute.
by apply: map_f; rewrite mem_iota add0n leq0n sL.
Qed.

Lemma sym_of_check (f : int -> bool) :
  allsym f -> forall s, (to_nat s < nsym)%N -> f s.
Proof. by rewrite /allsym => hchk s sL; apply: (allP hchk); exact: sym16i_mem. Qed.

(* the eighteen moves, which are nats and so need no such care *)
Lemma move_of_check (f : nat -> bool) :
  allmv f -> forall k, (k < 18)%N -> f k.
Proof.
by rewrite /allmv => hchk k kL; apply: (allP hchk); rewrite mem_iota add0n leq0n kL.
Qed.

Lemma mv18i_mem k : (k < 18)%N -> of_nat k \in mv18i.
Proof.
move=> kL; have -> : mv18i = [seq of_nat i | i <- iota 0 18] by vm_compute.
by apply: map_f; rewrite mem_iota add0n leq0n kL.
Qed.

Lemma movei_of_check (f : int -> bool) :
  allmvi f -> forall k, (k < 18)%N -> f (of_nat k).
Proof. by rewrite /allmvi => hchk k kL; apply: (allP hchk); exact: mv18i_mem. Qed.

(* =========================================================================  *)
(*  2.  The data                                                              *)
(* =========================================================================  *)

(* THE RANK TABLE IS A VARIABLE.  Requiring the emitted one to STATE the
   checks costs 103 MB on every session open, and nothing below computes
   with it -- FoldChecksRun.v instantiates it once. *)
Section Obl.

Variable ractab : PArray.array arr.

(* the move on ranks is Farp1's actfsr.  A VARIABLE here: requiring Farp1
   pulls P1Fs and P1Fsm, and with them the session open goes past the cap. *)
Variable actr : int -> nat -> int.

(* AND THE SAME MOVE AT AN INT63 INDEX, which is Farp1's actfsri -- actfsr
   is that one after of_nat.  The checks below are stated over this form so
   their loops never leave int63; the theory above keeps the nat one. *)
Variable actri : int -> int -> int.
Hypothesis actriE : forall r k, actri r (of_nat k) = actr r k.

(* and the four folding tables, FoldTables.v's frepi, fsymi, twsymi and repsi.
   VARIABLES for the same reason: nothing below computes with them. *)
Variables frepi fsymi repsi : int -> int.
Variable twsymi : int -> int -> int.

(* the rank under a symmetry, chunked like the folded table: entry r * 16 + s
   at twenty bits, three to a word *)
Definition racti (r s : int) : int :=
  let i := Uint63.add (Uint63.mul r nsymi) s in
  let w := Uint63.div i nwide in
  let j := Uint63.sub i (Uint63.mul w nwide) in
  let c := Uint63.lsr w cwlogi in
  let o := Uint63.land w cwmaski in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get ractab c) o) (Uint63.mul j wbits))
    wmaski.

(* the rank of a rank's representative.  DEFINED through the two tables, so
   Fold.v's repsE is an identity and not a check. *)
Definition rrepi (r : int) : int := repsi (frepi r).

(* composing two of the sixteen.  Derived from Sym16's tables rather than
   emitted: the sixteen are closed under comp_tab by sym16GP, so index lands
   below sixteen -- smulC checks that it does. *)
Definition smult : seq nat :=
  Eval vm_compute in
  [seq index (comp_tab s t) sym16ts | s <- sym16ts, t <- sym16ts].

Definition smula : arr :=
  Eval vm_compute in mkarr 256%uint63 0%uint63 [seq of_nat i | i <- smult].

Definition smuli (s t : int) : int :=
  PArray.get smula (Uint63.add (Uint63.mul s nsymi) t).

(* the move a symmetry turns a move into, Sym16's relabelling read at an
   int63 symmetry index *)
Definition msymi (k : nat) (s : int) : nat := symmove (to_nat s) k.

(* THE SAME RELABELLING AS 288 INT63 ENTRIES, entry s * 18 + k.  symmove is
   two nth walks over a seq of seqs, after a to_nat, and msymRC ran it on
   every one of its 302 million iterations: MEASURED 1.56 us a value against
   ractAC's 254 ns for the same loop shape over the int63 smula.  This is
   smult/smula one definition over. *)
Definition nmvi : int := 18%uint63.                 (* the eighteen moves *)

Definition msymt : seq nat :=
  Eval vm_compute in [seq symmove s k | s <- iota 0 16, k <- iota 0 18].

Definition msyma : arr :=
  Eval vm_compute in mkarr 288%uint63 0%uint63 [seq of_nat i | i <- msymt].

Definition msymii (k s : int) : int :=
  PArray.get msyma (Uint63.add (Uint63.mul s nmvi) k).

(* that the table is the relabelling.  288 values, so it costs nothing. *)
Definition msymiC : bool :=
  allsym (fun s => allmvi (fun k =>
    (msymii k s =? of_nat (msymi (to_nat k) s))%uint63)).

Hypothesis msymiCP : msymiC.

(* so the table may be read as the relabelling, at a nat move index *)
Lemma msymiiE k s : (k < 18)%N -> (to_nat s < nsym)%N ->
  msymii (of_nat k) s = of_nat (msymi k s).
Proof.
move=> kL sL; apply/eqb_correct.
have kW : (k < nwB)%N.
  by apply: leq_trans kL _; apply: leq_trans (ltnW ndigitsLwB); vm_compute.
by have := movei_of_check (sym_of_check msymiCP sL) kL; rewrite (of_natK k kW).
Qed.

(* THE CHECKS ARE HYPOTHESES HERE.  Running them needs the emitted tables and
   a good half hour; everything below only needs to KNOW they hold, so it is
   proved once against a section hypothesis and FoldChecksRun.v pays the bill.
   A name that does not typecheck then costs a load, not a run. *)

(* =========================================================================  *)
(*  3.  The obligations that are pure bookkeeping                             *)
(* =========================================================================  *)

(* the orbit table and the representative table name the same rank: an
   identity, because rrepi is DEFINED through both *)
(* the guard is carried even though the equation does not need it: Fold.v's
   repsE has it, and an argument without it does not fit *)
Lemma repsEn r : (r <? nfsi)%uint63 -> repsi (frepi r) = rrepi r.
Proof. by []. Qed.

(* the symmetry a rank folds by is one of the sixteen.  FoldTables has the same
   check but no equation for it, and unfolding a loop by conversion is what
   the equations are there to avoid, so it is restated here. *)
Definition fsymLC : bool := allrank (fun r => (fsymi r <? nsymi)%uint63).

Hypothesis fsymLCP : fsymLC.

Lemma fsymLCE : fsymLC = allrank (fun r => (fsymi r <? nsymi)%uint63).
Proof. by []. Qed.

Lemma fsymLn r : (r <? nfsi)%uint63 -> (to_nat (fsymi r) < nsym)%N.
Proof.
move=> hr; have h := fsymLCP; rewrite fsymLCE in h.
have := rank_of_check h hr => /nltbP.
by rewrite (_ : to_nat nsymi = nsym); last by vm_compute.
Qed.

(* composing two of the sixteen gives one of the sixteen *)
Definition smulC : bool := allsym (fun s => allsym (fun t => (smuli s t <? nsymi)%uint63)).

Hypothesis smulCP : smulC.

Lemma smulCE : smulC = allsym (fun s => allsym (fun t => (smuli s t <? nsymi)%uint63)).
Proof. by []. Qed.

Lemma smulLn s t : (to_nat s < nsym)%N -> (to_nat t < nsym)%N ->
  (to_nat (smuli s t) < nsym)%N.
Proof.
move=> sL tL; have h := smulCP; rewrite smulCE in h.
have := sym_of_check (sym_of_check h sL) tL => /nltbP.
by rewrite (_ : to_nat nsymi = nsym); last by vm_compute.
Qed.

(* a symmetry sends a move to a move *)
Lemma msymLn k s : (k < 18)%N -> (to_nat s < nsym)%N -> (msymi k s < 18)%N.
Proof. by move=> kL sL; apply: symmove_lt. Qed.

(* =========================================================================  *)
(*  4.  The obligations that are checks over the emitted numbers              *)
(*                                                                            *)
(*  Each comes as a loop, its vm_compute, an EQUATION so that no proof ever   *)
(*  unfolds the loop by conversion, and the instance.                         *)
(* =========================================================================  *)

(* ---- the symmetry a rank folds by reaches its representative ------------- *)

Definition fsymEC : bool := allrank (fun r => (racti r (fsymi r) =? rrepi r)%uint63).

Hypothesis fsymECP : fsymEC.

Lemma fsymECE : fsymEC = allrank (fun r => (racti r (fsymi r) =? rrepi r)%uint63).
Proof. by []. Qed.

Lemma fsymEn r : (r <? nfsi)%uint63 -> racti r (fsymi r) = rrepi r.
Proof.
move=> hr; have h := fsymECP; rewrite fsymECE in h.
by apply/eqb_correct; have := rank_of_check h hr.
Qed.

(* ---- a symmetry keeps a rank a rank ------------------------------------- *)

Definition ractLC : bool := allrank (fun r => allsym (fun s => (racti r s <? nfsi)%uint63)).

Hypothesis ractLCP : ractLC.

Lemma ractLCE : ractLC = allrank (fun r => allsym (fun s => (racti r s <? nfsi)%uint63)).
Proof. by []. Qed.

Lemma ractLn r s : (r <? nfsi)%uint63 -> (to_nat s < nsym)%N ->
  (racti r s <? nfsi)%uint63.
Proof.
move=> hr sL; have h := ractLCP; rewrite ractLCE in h.
by have := sym_of_check (rank_of_check h hr) sL.
Qed.

(* ---- and a move likewise ------------------------------------------------- *)

Definition actrLC : bool := allrank (fun r => allmv (fun k => (actr r k <? nfsi)%uint63)).

Hypothesis actrLCP : actrLC.

Lemma actrLCE : actrLC = allrank (fun r => allmv (fun k => (actr r k <? nfsi)%uint63)).
Proof. by []. Qed.

Lemma actrLn r k : (r <? nfsi)%uint63 -> (k < 18)%N ->
  (actr r k <? nfsi)%uint63.
Proof.
move=> hr kL; have h := actrLCP; rewrite actrLCE in h.
by have := move_of_check (rank_of_check h hr) kL.
Qed.

(* ---- the orbit does not move inside itself ------------------------------- *)

Definition frepSC : bool :=
  allrank (fun r => allsym (fun s => (frepi (racti r s) =? frepi r)%uint63)).

Hypothesis frepSCP : frepSC.

Lemma frepSCE : frepSC =
  allrank (fun r => allsym (fun s => (frepi (racti r s) =? frepi r)%uint63)).
Proof. by []. Qed.

Lemma frepSn r s : (r <? nfsi)%uint63 -> (to_nat s < nsym)%N ->
  frepi (racti r s) = frepi r.
Proof.
move=> hr sL; have h := frepSCP; rewrite frepSCE in h.
by apply/eqb_correct; have := sym_of_check (rank_of_check h hr) sL.
Qed.

(* the representative follows the orbit, so this one is not a check *)
Lemma rrepSn r s : (r <? nfsi)%uint63 -> (to_nat s < nsym)%N ->
  rrepi (racti r s) = rrepi r.
Proof. by move=> hr sL; rewrite /rrepi (frepSn hr sL). Qed.

(* ---- the symmetries act on ranks ---------------------------------------- *)

Definition ractAC : bool :=
  allrank (fun r => allsym (fun s => allsym (fun t =>
    (racti (racti r s) t =? racti r (smuli s t))%uint63))).

Hypothesis ractACP : ractAC.

Lemma ractACE : ractAC =
  allrank (fun r => allsym (fun s => allsym (fun t =>
    (racti (racti r s) t =? racti r (smuli s t))%uint63))).
Proof. by []. Qed.

Lemma ractAn r s t : (r <? nfsi)%uint63 -> (to_nat s < nsym)%N ->
  (to_nat t < nsym)%N -> racti (racti r s) t = racti r (smuli s t).
Proof.
move=> hr sL tL; have h := ractACP; rewrite ractACE in h.
apply/eqb_correct.
by have := sym_of_check (sym_of_check (rank_of_check h hr) sL) tL.
Qed.

(* ---- the symmetries permute the moves, on ranks -------------------------- *)

Definition msymRC : bool :=
  allrank (fun r => allsym (fun s => allmvi (fun k =>
    (actri (racti r s) (msymii k s) =? racti (actri r k) s)%uint63))).

Hypothesis msymRCP : msymRC.

Lemma msymRCE : msymRC =
  allrank (fun r => allsym (fun s => allmvi (fun k =>
    (actri (racti r s) (msymii k s) =? racti (actri r k) s)%uint63))).
Proof. by []. Qed.

Lemma msymRn r k s : (r <? nfsi)%uint63 -> (k < 18)%N ->
  (to_nat s < nsym)%N -> actr (racti r s) (msymi k s) = racti (actr r k) s.
Proof.
move=> hr kL sL; have h := msymRCP; rewrite msymRCE in h.
apply/eqb_correct.
have := movei_of_check (sym_of_check (rank_of_check h hr) sL) kL.
by rewrite (msymiiE kL sL) !actriE.
Qed.

(* ---- the twist half ------------------------------------------------------ *)

Definition twsymLC : bool :=
  alltw (fun tw => allsym (fun s => (twsymi tw s <? ntwisti)%uint63)).

Hypothesis twsymLCP : twsymLC.

Lemma twsymLCE : twsymLC = alltw (fun tw => allsym (fun s => (twsymi tw s <? ntwisti)%uint63)).
Proof. by []. Qed.

Lemma twsymLn tw s : (to_nat tw < ntwist)%N -> (to_nat s < nsym)%N ->
  (to_nat (twsymi tw s) < ntwist)%N.
Proof.
move=> twL sL; have h := twsymLCP; rewrite twsymLCE in h.
have := sym_of_check (twist_of_check h twL) sL => /nltbP.
by rewrite (_ : to_nat ntwisti = ntwist); last by vm_compute.
Qed.

Definition acttwiLC : bool := alltw (fun tw => allmv (fun k => (acttwi tw k <? ntwisti)%uint63)).

Hypothesis acttwiLCP : acttwiLC.

Lemma acttwiLCE : acttwiLC = alltw (fun tw => allmv (fun k => (acttwi tw k <? ntwisti)%uint63)).
Proof. by []. Qed.

Lemma acttwiLn tw k : (to_nat tw < ntwist)%N -> (k < 18)%N ->
  (to_nat (acttwi tw k) < ntwist)%N.
Proof.
move=> twL kL; have h := acttwiLCP; rewrite acttwiLCE in h.
have hb := move_of_check (twist_of_check h twL) kL.
(* acttwi READS THE EMITTED TWIST TABLE, so the bound must be moved to int63
   before anything looks at it: `apply/nltbP' on a goal bounded by the nat
   ntwist has to unify it against to_nat _, and that evaluates the table.
   Rewrite the bound first, then elimT, which unifies nothing. *)
rewrite (_ : ntwist = to_nat ntwisti); last by vm_compute.
exact: (elimT (nltbP _ _) hb).
Qed.

Definition twsymAC : bool :=
  alltw (fun tw => allsym (fun s => allsym (fun t =>
    (twsymi (twsymi tw s) t =? twsymi tw (smuli s t))%uint63))).

Hypothesis twsymACP : twsymAC.

Lemma twsymACE : twsymAC =
  alltw (fun tw => allsym (fun s => allsym (fun t =>
    (twsymi (twsymi tw s) t =? twsymi tw (smuli s t))%uint63))).
Proof. by []. Qed.

Lemma twsymAn tw s t : (to_nat tw < ntwist)%N -> (to_nat s < nsym)%N ->
  (to_nat t < nsym)%N -> twsymi (twsymi tw s) t = twsymi tw (smuli s t).
Proof.
move=> twL sL tL; have h := twsymACP; rewrite twsymACE in h.
apply/eqb_correct.
by have := sym_of_check (sym_of_check (twist_of_check h twL) sL) tL.
Qed.

Definition msymTC : bool :=
  alltw (fun tw => allsym (fun s => allmv (fun k =>
    (acttwi (twsymi tw s) (msymi k s) =? twsymi (acttwi tw k) s)%uint63))).

Hypothesis msymTCP : msymTC.

Lemma msymTCE : msymTC =
  alltw (fun tw => allsym (fun s => allmv (fun k =>
    (acttwi (twsymi tw s) (msymi k s) =? twsymi (acttwi tw k) s)%uint63))).
Proof. by []. Qed.

Lemma msymTn tw k s : (to_nat tw < ntwist)%N -> (k < 18)%N ->
  (to_nat s < nsym)%N ->
  acttwi (twsymi tw s) (msymi k s) = twsymi (acttwi tw k) s.
Proof.
move=> twL kL sL; have h := msymTCP; rewrite msymTCE in h.
have hb := move_of_check (sym_of_check (twist_of_check h twL) sL) kL.
(* NOT `by ...', for the same reason as acttwiLn *)
apply/eqb_correct; exact: hb.
Qed.

End Obl.
