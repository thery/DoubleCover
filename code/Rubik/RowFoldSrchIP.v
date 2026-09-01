(* =========================================================================  *)
(*  RowFoldSrchIP.v -- the folded search that carries the depth is the same.  *)
(* =========================================================================  *)

(* NOTHING NEW IS PROVED ABOUT THE CUBE.  fsrchki is shown EQUAL to fsrchk    *)
(* when the int it carries is the depth left, so RowFoldRun's own soundness   *)
(* carries over as it stands: rewrite with frunski_eq and apply frunsk_sound. *)
(* There are two side conditions and no more: of_nat round trips below nwB,   *)
(* so a bound on the depth travels with it, and neither subtraction wraps.    *)
(*                                                                            *)
(* The four small lemmas below are written again rather than taken from       *)
(* RowSrchP: the two sides must not depend on each other.                     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask.
Require Import RowFold RowFoldSrch RowFoldSrchI.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FSrchIP.

Variable e8num e4bit : arr.
Variable fpg fsrc fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation wmask := (mmask dnlo dnhi fllo flhi).

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

Variables forb fpop : arr.
Variable ishm : int.

Local Notation fsrk :=
  (fsrchk e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation fsrsk :=
  (fsrchsk e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation flvsk :=
  (flvlsk e8num e4bit fpg fsrc fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).
Local Notation frnsk :=
  (frunsk e8num e4bit fpg fsrc fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).

Local Notation fsrki :=
  (fsrchki e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation fsrski :=
  (fsrchski e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation flvski :=
  (flvlski e8num e4bit fpg fsrc fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).
Local Notation frnski :=
  (frunski e8num e4bit fpg fsrc fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).

(* two walks that take the same step are the same walk                        *)
Lemma fifold_eqf (A : Type) n j (f g : int -> A -> A) a :
  (forall i b, f i b = g i b) -> ifold n j f a = ifold n j g a.
Proof.
by move=> hfg; elim: n j a => [|n ih] j a //=; rewrite hfg; apply: ih.
Qed.

(* the folded search keeps hcoset's cut as a conjunction -- RowFoldSrch is    *)
(* not touched -- so the two sides are read into the same shape first.        *)
Lemma andE3 (a b c : bool) :
  [&& a, b & c] = (if a then (if b then c else false) else false).
Proof. by case: a; case: b. Qed.

(* the two tests, as equations rather than views                              *)
Lemma fnleE (a b : int) : (a <=? b) = (to_nat a <= to_nat b)%N.
Proof. by apply/nlebP/idP. Qed.

Lemma fneqE (a b : int) : (a =? b) = (to_nat a == to_nat b)%N.
Proof. by apply/neqbP/eqP. Qed.

Lemma fto_nat2 : to_nat 2 = 2%N.
Proof. by vm_compute. Qed.

Lemma fto_nat5 : to_nat 5 = 5%N.
Proof. by vm_compute. Qed.

(* mmask asks its slack whether it is two or more and whether it is one, and  *)
(* nothing else, so the int slack and its nat give the same mask              *)
Lemma fmmaskiE w s : wmask w (fsslack s) = wmask w (to_nat s).
Proof.
rewrite /fsslack; case E2 : (2 <=? s).
  have hs : (2 <= to_nat s)%N by rewrite -fto_nat2 -fnleE E2.
  by rewrite /mmask hs.
have hs2 : (to_nat s < 2)%N by rewrite -fto_nat2 ltnNge -fnleE E2.
case E1 : (s =? 1).
  have hs1 : to_nat s = 1%N by rewrite -to_nat_1; apply/eqP; rewrite -fneqE E1.
  by rewrite hs1.
have hs0 : to_nat s = 0%N.
  case E : (to_nat s) hs2 => [|n] // hn.
  have hn0 : n = 0%N by move: hn; rewrite ltnS ltnS leqn0 => /eqP.
  by move: E1; rewrite fneqE to_nat_1 E hn0 eqxx.
by rewrite hs0.
Qed.


(* the nested tests, against the conjunction they replace.  A lemma of its   *)
(* own because the induction hypothesis mentions cut, so it cannot be taken  *)
(* apart inside the proof.                                                   *)
Lemma fcondE (cut : bool) (w togoi' : int) (togo : nat) :
  to_nat togoi' = togo -> (togo <= 62)%N ->
  (if w <=? togoi'
   then (if cut
         then (if w =? togoi' then true else frcutii <=? Uint63.add togoi' w)
         else true)
   else false)
  = [&& (to_nat w <= togo)%N
      & [|| ~~ cut, (to_nat w == togo)%N | (rcuti <= togo + to_nat w)%N]].
Proof.
move=> htg ht62.
rewrite fnleE htg; case E1 : (to_nat w <= togo)%N; last by [].
rewrite /=; case: cut; last by [].
rewrite /= fneqE htg; case E2 : (to_nat w == togo)%N; first by [].
rewrite /=.
have hw : (to_nat w <= togo)%N by rewrite E1.
have hlt : (to_nat togoi' + to_nat w < nwB)%N.
  apply: (@ltn_nwB 8); first by [].
  rewrite htg; apply: (@leq_ltn_trans (62 + 62)%N); last by [].
  by apply: leq_add => //; apply: leq_trans hw ht62.
by rewrite fnleE /frcutii /rcuti fto_nat5 (to_nat_add togoi' w hlt) htg.
Qed.

(* ---- the search ---------------------------------------------------------- *)

Lemma fsrchki_eq cut togo :
  forall togoi c x msk pv m, to_nat togoi = togo -> (togo <= 63)%N ->
  fsrki cut togo togoi c x msk pv m = fsrk cut togo c x msk pv m.
Proof.
elim: togo => [|togo ih] togoi c x msk pv m htg hb; first by [].
rewrite /fsrchki -/fsrchki /fsrchk -/fsrchk.
cbv zeta; apply: fifold_eqf => k m'.
have hbd : (to_nat togoi < nwB)%N := to_nat_bounded togoi.
have h1t : (to_nat 1 <= to_nat togoi)%N by rewrite to_nat_1 htg.
have htg' : to_nat (Uint63.sub togoi 1) = togo.
  by rewrite (to_nat_sub togoi 1 h1t hbd) to_nat_1 htg subn1.
have ht62 : (togo <= 62)%N by rewrite -ltnS.
case: ifP => _; first by [].
case: ifP => _; first by [].
rewrite andE3; case: ifP => _; first by [].
set w := mdist _.
rewrite (fcondE cut w htg' ht62).
case: ifP => hif; last by [].
have hwt : (to_nat w <= togo)%N by move: hif => /andP[].
have hbd' : (to_nat (Uint63.sub togoi 1) < nwB)%N :=
  to_nat_bounded (Uint63.sub togoi 1).
have hwle : (to_nat w <= to_nat (Uint63.sub togoi 1))%N by rewrite htg'.
rewrite fmmaskiE (to_nat_sub (Uint63.sub togoi 1) w hwle hbd') htg'.
by apply: ih; [exact: htg' | exact: ltnW].
Qed.

Lemma fsrchski_eq cut togo :
  forall togoi c x msk pv enough mn, to_nat togoi = togo -> (togo <= 63)%N ->
  fsrski cut togo togoi c x msk pv enough mn
  = fsrsk cut togo c x msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x msk pv enough mn htg hb; first by [].
rewrite /fsrchski -/fsrchski /fsrchsk -/fsrchsk.
case: (Uint63.leb enough mn.2); first by [].
cbv zeta; apply: fifold_eqf => k a.
have hbd : (to_nat togoi < nwB)%N := to_nat_bounded togoi.
have h1t : (to_nat 1 <= to_nat togoi)%N by rewrite to_nat_1 htg.
have htg' : to_nat (Uint63.sub togoi 1) = togo.
  by rewrite (to_nat_sub togoi 1 h1t hbd) to_nat_1 htg subn1.
have ht62 : (togo <= 62)%N by rewrite -ltnS.
case: ifP => _; first by [].
case: ifP => _; first by [].
rewrite andE3; case: ifP => _; first by [].
set w := mdist _.
rewrite (fcondE cut w htg' ht62).
case: ifP => hif; last by [].
have hwt : (to_nat w <= togo)%N by move: hif => /andP[].
have hbd' : (to_nat (Uint63.sub togoi 1) < nwB)%N :=
  to_nat_bounded (Uint63.sub togoi 1).
have hwle : (to_nat w <= to_nat (Uint63.sub togoi 1))%N by rewrite htg'.
rewrite fmmaskiE (to_nat_sub (Uint63.sub togoi 1) w hwle hbd') htg'.
by apply: ih; [exact: htg' | exact: ltnW].
Qed.

(* ---- the level and the run ----------------------------------------------- *)

Lemma flvlski_eq cut d m dst : (d <= 63)%N ->
  flvski cut d m dst = flvsk cut d m dst.
Proof.
move=> hb; rewrite /flvlski -/flvlski.
rewrite /flvlsk -/flvlsk; cbv zeta.
case: ifP => _; last by [].
have hdw : (d < nwB)%N.
  by apply: (@ltn_nwB 6); [ | exact: hb].
have hd : to_nat (of_nat d) = d := of_natK d hdw.
set w := mdist _.
rewrite fnleE hd; case: ifP => hle; last by [].
have hbd : (to_nat (of_nat d) < nwB)%N := to_nat_bounded (of_nat d).
have hwle : (to_nat w <= to_nat (of_nat d))%N by rewrite hd; exact: hle.
rewrite fmmaskiE (to_nat_sub (of_nat d) w hwle hbd) hd.
by case: ifP => _; [rewrite fsrchski_eq | rewrite fsrchki_eq].
Qed.

(* the two runs read one level down, and both are reflexivity                 *)
Lemma frunskiS n d n0 m dst :
  frnski n.+1 d n0 m dst
  = frnski n d.+1 (fcount forb fpop (flvski (Uint63.ltb ncutb n0) d.+1 m dst))
           (flvski (Uint63.ltb ncutb n0) d.+1 m dst) m.
Proof. by []. Qed.

Lemma frunskSb n d n0 m dst :
  frnsk n.+1 d n0 m dst
  = frnsk n d.+1 (fcount forb fpop (flvsk (Uint63.ltb ncutb n0) d.+1 m dst))
          (flvsk (Uint63.ltb ncutb n0) d.+1 m dst) m.
Proof. by []. Qed.

Lemma frunski_eq n d n0 m dst : (d + n <= 63)%N ->
  frnski n d n0 m dst = frnsk n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hb; first by [].
have hd1 : (d.+1 <= 63)%N.
  by apply: leq_trans hb; rewrite -addSnnS; exact: leq_addr.
rewrite frunskiS frunskSb flvlski_eq; last exact: hd1.
rewrite ih; first by [].
by rewrite addSnnS.
Qed.


End FSrchIP.
