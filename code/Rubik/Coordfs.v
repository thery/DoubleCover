(* =========================================================================  *)
(*  Coordfs.v                                                                 *)
(*                                                                            *)
(*  The flip x slice summary, packed into 24 bits of an int63.                *)
(*                                                                            *)
(*  No admits: the summary, the guard and the bit toolbox are all proved.    *)
(*                                                                            *)
(*  WHY 24 BITS.  Coord.v turns any summary satisfying                        *)
(*                                                                            *)
(*      coord (g * m) = act (coord g) m                                       *)
(*                                                                            *)
(*  into an admissible heuristic, whatever table is put on it -- the table is *)
(*  never proved correct, it only has to pass Dfs0 and DfsStep.  DfsStep is a *)
(*  statement about every element of the summary type, so that type has to be *)
(*  ENUMERABLE BY A LOOP: a finfun will not do, an int below 2 ^ 24 will.     *)
(*  Hence the packing, and hence the bit level reasoning below, which is the  *)
(*  only real work in this file.                                              *)
(*                                                                            *)
(*  WHY A GUARD.  The summary is about CUBIES: bit p of the flip half says    *)
(*  whether the sticker now at the primary facelet of edge position p is a    *)
(*  primary sticker.  For that to have an action one needs the two facelets   *)
(*  of an edge to stay together, which holds for a cube move but not for an   *)
(*  arbitrary permutation of 'I_48.  So coordM is guarded by cubP -- g        *)
(*  commutes with the involution pairing the two facelets of each edge.       *)
(*  Section Heuristic below shows the guard costs nothing downstream: h is    *)
(*  defined to be 0 off the guarded set, and then Search.v's two conditions   *)
(*  hold unconditionally, so Search.v does not change.                        *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Rubik333.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* uint63_scope is deliberately NOT opened: this file is mostly about perms
   and nat, and the scope would turn every 1 into an int.  The three int
   expressions below carry their own %uint63.                                *)

(* ---- 1. A summary that is only an action on part of the group ------------ *)

(* Coord.v's Section Heuristic asks for the equivariance at every g.  This is *)
(* the same construction with the equivariance only on a subgroup P, which is *)
(* all a cubie summary can offer.  h is 0 off P, and since P is closed under  *)
(* the moves the two conditions Search.v wants come out unconditional.        *)

Section HeuristicG.

Variable X : Type.
Variable P : pred {perm facelet}.
Hypothesis P1 : P 1.
Hypothesis PM : forall g m, P g -> m \in Sset -> P (g * m).

Variable coord : {perm facelet} -> X.
Variable act : X -> {perm facelet} -> X.
Hypothesis coordM :
  forall g m, P g -> m \in Sset -> coord (g * m) = act (coord g) m.

Variable D : X -> nat.
Hypothesis D0 : D (coord 1) = 0.
Hypothesis Dstep : forall x m, m \in Sset -> D x <= (D (act x m)).+1.

Definition hcoordg (g : {perm facelet}) : nat := if P g then D (coord g) else 0.

Lemma hcoordg0 : hcoordg 1 = 0.
Proof. by rewrite /hcoordg P1 D0. Qed.

(* The one place the guard is paid: off P there is nothing to prove because   *)
(* 0 is below everything, and on P the guard propagates by PM.                *)
Lemma hcoordgS g m : m \in Sset -> hcoordg g <= (hcoordg (g * m)).+1.
Proof.
move=> mS; rewrite /hcoordg; case: ifP => [Pg|_]; last by [].
by rewrite (PM Pg mS) coordM //; apply: Dstep.
Qed.

End HeuristicG.

(* ---- 2. The twelve edges ------------------------------------------------- *)

(* Read off the cycles of Rubik333.v.  A face holds its eight facelets as     *)
(*                                                                            *)
(*      0 1 2                                                                 *)
(*      3   4          U with B at the top, D with F at the top,              *)
(*      5 6 7          the side faces with U at the top,                      *)
(*                                                                            *)
(* so the edge facelets of a face are its offsets 1, 3, 4 and 6, and U is     *)
(* 0..7, L is 8..15, F is 16..23, R is 24..31, B is 32..39, D is 40..47.      *)
(* The pairing is forced by the cycles: Umove sends 3 to 1 and 9 to 33, so    *)
(* the edge (3, 9) goes to the edge (1, 33), and so on round the cube.        *)

(* The order is the classical one, UR UF UL UB DR DF DL DB FR FL BL BR.       *)
(* eprim is the U or D facelet of a U/D edge and the F or B facelet of a      *)
(* slice edge: exactly the convention under which F and B quarter turns flip  *)
(* the four edges they move and the other four faces flip nothing.            *)
Definition eprim : seq nat :=
  [:: 4; 6; 3; 1; 44; 41; 43; 46; 20; 19; 36; 35]%N.
Definition esec : seq nat :=
  [:: 25; 17; 9; 33; 30; 22; 14; 38; 27; 12; 11; 28]%N.

(* the twelve positions, and the four of them in the middle slice            *)
Definition nedge := 12.
Definition nslice := 4.
Definition nfacelet := 48.

Definition eprimf (p : nat) : facelet := inord (nth 0%N eprim p).

(* the two colourings the summary reads.  pcol is one facelet of each edge,  *)
(* scol is both facelets of each slice edge -- that is what makes the slice  *)
(* half a plain permutation of bits with no correction term.                 *)
Definition pcol (f : facelet) : bool := (f : nat) \in eprim.
Definition scol (f : facelet) : bool :=
  (f : nat) \in drop 8 eprim ++ drop 8 esec.

(* the partner facelet, and the position an edge facelet belongs to          *)
Definition epair (f : facelet) : facelet :=
  nth f [seq (inord i : facelet) | i <- esec ++ eprim]
        (index (f : nat) (eprim ++ esec)).

Definition epos (f : facelet) : nat := index (f : nat) (eprim ++ esec) %% nedge.

(* ---- 2b. Moving the data to nat ------------------------------------------ *)

(* Nothing about 'I_48 reduces -- inord does not -- so every fact about the
   twelve edges is proved by pushing it to nat, where the lists are literals
   and vm_compute decides.  These three are the whole bridge.               *)

Lemma all_iota_lt (P : nat -> bool) n i : all P (iota 0 n) -> i < n -> P i.
Proof. by move=> /allP hP iL; apply: hP; rewrite mem_iota. Qed.

Definition epairn (f : nat) : nat := nth f (esec ++ eprim) (index f (eprim ++ esec)).

Lemma epairE f : epair f = inord (epairn f).
Proof.
rewrite /epair /epairn -{1}(inord_val f).
have [iL|iG] := ltnP (index (f : nat) (eprim ++ esec)) (size (esec ++ eprim)).
  by rewrite (nth_map (f : nat)).
by rewrite !nth_default ?size_map.
Qed.

Lemma epairn_lt m : m \in eprim ++ esec -> epairn m < nfacelet.
Proof.
by apply: (allP (_ : all (fun m => epairn m < nfacelet) (eprim ++ esec)));
   vm_compute.
Qed.

Lemma epairnN m : m \notin eprim ++ esec -> epairn m = m.
Proof.
by move=> mN; rewrite /epairn (memNindex mN) nth_default // !size_cat addnC.
Qed.

Lemma eprim_lt p : p < nedge -> nth 0%N eprim p < nfacelet.
Proof.
by apply: (all_iota_lt (P := fun p => nth 0%N eprim p < nfacelet) (n := nedge));
   vm_compute.
Qed.

Lemma eprimfK p : p < nedge -> (eprimf p : nat) = nth 0%N eprim p.
Proof. by move=> pL; rewrite /eprimf inordK // eprim_lt. Qed.

Lemma epos_lt f : epos f < nedge.
Proof. by rewrite /epos ltn_mod. Qed.

(* the pairing has no fixed point on the edge facelets and is the identity
   elsewhere, which is what says a permutation commuting with it keeps edge
   facelets edge facelets                                                   *)
Lemma epair_fix (f : facelet) : (epair f == f) = ((f : nat) \notin eprim ++ esec).
Proof.
have [fM|fN] := boolP ((f : nat) \in eprim ++ esec); last first.
  by rewrite epairE (epairnN fN) inord_val eqxx.
have hne : epairn (f : nat) != (f : nat).
  by apply: (allP (_ : all (fun m => epairn m != m) (eprim ++ esec)));
     [vm_compute | exact: fM].
apply/negbTE; rewrite epairE; apply: contra hne => /eqP e.
by rewrite -(inordK (epairn_lt fM)) e.
Qed.

(* ---- 3. What the data has to satisfy ------------------------------------- *)

(* All four are decided by vm_compute on the two lists, once inord is out of  *)
(* the way -- the values are literals, so each is a 24 element check.         *)

Lemma epairK : involutive epair.
Proof.
move=> f; rewrite !epairE.
have [fM|fN] := boolP ((f : nat) \in eprim ++ esec); last first.
  by rewrite (epairnN fN) inord_val (epairnN fN) inord_val.
rewrite inordK ?epairn_lt // -{2}(inord_val f); congr (inord _).
by apply/eqP;
   apply: (allP (_ : all (fun m => epairn (epairn m) == m) (eprim ++ esec)));
   [vm_compute | exact: fM].
Qed.

Lemma pcol_epair (f : facelet) : (f : nat) \in eprim ++ esec -> pcol (epair f) = ~~ pcol f.
Proof.
move=> fM; rewrite /pcol epairE inordK ?epairn_lt //; apply/eqP.
by apply: (allP (_ : all (fun m => (epairn m \in eprim) == ~~ (m \in eprim))
                        (eprim ++ esec))); [vm_compute | exact: fM].
Qed.

Lemma scol_epair f : scol (epair f) = scol f.
Proof.
rewrite /scol epairE.
have [fM|fN] := boolP ((f : nat) \in eprim ++ esec); last first.
  by rewrite (epairnN fN) inord_val.
rewrite inordK ?epairn_lt //; apply/eqP.
apply: (allP (_ : all (fun m => (epairn m \in drop 8 eprim ++ drop 8 esec)
                             == (m \in drop 8 eprim ++ drop 8 esec))
                      (eprim ++ esec))); [by vm_compute | exact: fM].
Qed.

Lemma epos_prim p : p < nedge -> epos (eprimf p) = p.
Proof.
move=> pL; rewrite /epos eprimfK //; apply/eqP.
by apply: (all_iota_lt (n := nedge)
  (P := fun p => index (nth 0%N eprim p) (eprim ++ esec) %% nedge == p));
  [vm_compute | exact: pL].
Qed.

(* an edge facelet is the primary or the secondary facelet of its position    *)
Lemma edge_case (f : facelet) : (f : nat) \in eprim ++ esec ->
  f = eprimf (epos f) \/ f = epair (eprimf (epos f)).
Proof.
move=> fM.
have key : ((f : nat) == nth 0%N eprim (epos f))
        || ((f : nat) == epairn (nth 0%N eprim (epos f))).
  rewrite /epos.
  apply: (allP (_ : all (fun m =>
             (m == nth 0%N eprim (index m (eprim ++ esec) %% nedge))
          || (m == epairn (nth 0%N eprim (index m (eprim ++ esec) %% nedge))))
                        (eprim ++ esec))); [by vm_compute | exact: fM].
case/orP: key => /eqP e; [left | right].
  by rewrite /eprimf -e inord_val.
by rewrite epairE eprimfK ?epos_lt // -e inord_val.
Qed.

(* ---- 4. The guard: permutations that keep the two facelets of an edge      *)
(*         together --------------------------------------------------------- *)

Definition cubP (g : {perm facelet}) : bool :=
  [forall f : facelet, epair (g f) == g (epair f)].

(* It is the centraliser of an involution, so a subgroup; nothing here is     *)
(* about the cube.                                                            *)
Lemma cubP1 : cubP 1.
Proof. by apply/forallP => f; rewrite !perm1. Qed.

Lemma cubPM g h : cubP g -> cubP h -> cubP (g * h).
Proof.
move=> /forallP hg /forallP hh; apply/forallP => f; rewrite !permM.
by rewrite (eqP (hh _)) (eqP (hg _)).
Qed.

Lemma cubPV g : cubP g -> cubP (g^-1).
Proof.
move=> /forallP hg; apply/forallP => f; apply/eqP.
have := eqP (hg (g^-1 f)); rewrite permKV => e.
by rewrite e permK.
Qed.

(* The moves keep cubies together -- moves_cubP -- but nothing about a
   permutation reduces, so that fact has to be read on the tables and it
   lives in Coordfsi.v with the rest of the table bridge.  So does everything
   downstream of it: cubP_step, hfs and the search.                          *)

(* an edge facelet stays an edge facelet                                      *)
Lemma cubP_edge g f :
  cubP g -> ((g f : nat) \in eprim ++ esec) = ((f : nat) \in eprim ++ esec).
Proof.
move=> /forallP hg; apply/negb_inj; rewrite -!epair_fix (eqP (hg f)).
by rewrite (inj_eq (@perm_inj _ g)).
Qed.

(* ---- 5. Bits ------------------------------------------------------------- *)

(* nat indexed bits, because everything above is indexed by a position, and   *)
(* setbit/packn because the summary is built one position at a time.  All     *)
(* three compute: they are shifts and ors, no to_nat anywhere.                *)

Definition nbit (x : int) (k : nat) : bool := bit x (of_nat k).

Definition setbit (x : int) (k : nat) (b : bool) : int :=
  if b then (x lor lsl 1 (of_nat k))%uint63 else x.

Fixpoint packn (k : nat) (f : nat -> bool) : int :=
  if k is k1.+1 then setbit (packn k1 f) k1 (f k1) else 0%uint63.

(* the bound that makes the DfStep loop finite, and the defining property     *)

Lemma to_nat_lsl1 k : k < ndigits -> to_nat (lsl 1 (of_nat k)) = (2 ^ k)%N.
Proof.
move=> kL; rewrite to_nat_lslW to_nat_1 mul1n of_natK; last first.
  by apply: leq_trans kL _; apply: ltnW; exact: ndigitsLwB.
by rewrite modn_small // nwB_pow ltn_exp2l.
Qed.

Lemma packn_lt k f : k <= ndigits -> to_nat (packn k f) < 2 ^ k.
Proof.
elim: k => [_|k IH kL] /=; first by [].
have hX : to_nat (packn k f) < (2 ^ k.+1)%N.
  by apply: leq_trans (IH (ltnW kL)) _; rewrite leq_exp2l.
rewrite /setbit; case: (f k) => //.
apply: to_nat_lor_bound => //.
by rewrite to_nat_lsl1 // ltn_exp2l.
Qed.

Lemma nbit_packn k f j : j < k -> k <= ndigits -> nbit (packn k f) j = f j.
Proof.
elim: k j => [//|k IH] j jL kL /=.
have hnw : forall m, m <= ndigits -> m < nwB.
  by move=> m mL; apply: leq_ltn_trans mL ndigitsLwB.
have jk' : j <= k by [].
have kd : (of_nat k <? digits)%uint63.
  by apply/nltbP; rewrite of_natK ?hnw //; apply: ltnW.
have jd : (of_nat j <? digits)%uint63.
  apply/nltbP; rewrite of_natK; first exact: leq_ltn_trans jk' kL.
  by apply: hnw; apply: leq_trans jk' (ltnW kL).
have [->|jk] := eqVneq j k.
  rewrite /setbit; case: (f k).
    by rewrite /nbit lor_spec bit_onenn // eqxx orbT.
  rewrite /nbit; apply: (@bit_false_lt (packn k f) k (of_nat k)).
    by rewrite of_natK ?hnw //; apply: ltnW.
  by apply: packn_lt; apply: ltnW.
have jltk : j < k by rewrite ltn_neqAle jk.
rewrite /setbit; case: (f k); last by apply: IH => //; apply: ltnW.
rewrite /nbit lor_spec bit_onenn //.
have -> : (of_nat k == of_nat j) = false.
  apply/eqP => e; have {}e := congr1 (fun x : int => to_nat x) e.
  move: e; rewrite of_natK; last by apply: hnw; apply: ltnW.
  rewrite of_natK; last by apply: hnw; apply: leq_trans jk' (ltnW kL).
  by move=> e; move: jltk; rewrite e ltnn.
by rewrite orbF; apply: IH => //; apply: ltnW.
Qed.

(* two words agreeing on the first k bits are equal, which is how every       *)
(* equation between packed summaries is proved                               *)
Lemma eq_packn k (f1 f2 : nat -> bool) :
  (forall j, j < k -> f1 j = f2 j) -> packn k f1 = packn k f2.
Proof.
elim: k => //= k IH h; rewrite IH => [|j jL]; last by rewrite h // ltnW.
by rewrite h.
Qed.

Lemma packn_eq k (x y : int) :
  to_nat x < 2 ^ k -> to_nat y < 2 ^ k ->
  (forall j, j < k -> nbit x j = nbit y j) -> x = y.
Proof.
move=> hx hy h; apply: bit_ext => n.
have [nk|nk] := ltnP (to_nat n) k.
  by have := h _ nk; rewrite /nbit !to_natK.
by rewrite (@bit_false_lt x k n) // (@bit_false_lt y k n).
Qed.

(* ---- 6. The summary ------------------------------------------------------ *)

(* The summary is read on g^-1: mathcomp has (g * m) f = m (g f), so the      *)
(* facelet sitting at f is g^-1 f, and the cocycle comes out on that side --  *)
(* the same convention as coordf in Coord.v.                                  *)

(* bit p: the sticker now at the primary facelet of position p is NOT a       *)
(* primary sticker, i.e. the edge at p is flipped                             *)
Definition flipb (g : {perm facelet}) (p : nat) : bool :=
  ~~ pcol (g^-1 (eprimf p)).

(* bit p: the edge now at position p is a slice edge                          *)
Definition sliceb (g : {perm facelet}) (p : nat) : bool :=
  scol (g^-1 (eprimf p)).

Definition ncoord := (nedge + nedge)%N.       (* 24 bits *)

Definition coordfs (g : {perm facelet}) : int :=
  packn ncoord
    (fun k => if k < nedge then flipb g k else sliceb g (k - nedge)).

(* ---- 7. The action ------------------------------------------------------- *)

(* Applying m sends the primary facelet of p to m^-1 (eprimf p), which is a   *)
(* facelet of some position q -- primary or secondary.  Primary and the bit   *)
(* moves unchanged; secondary and the flip bit is complemented, which is      *)
(* exactly xbit.  The slice bit never gets a correction because scol does not *)
(* tell the two facelets of an edge apart.                                    *)

Definition src (m : {perm facelet}) (p : nat) : nat := epos (m^-1 (eprimf p)).

Definition xbit (m : {perm facelet}) (p : nat) : bool :=
  ~~ pcol (m^-1 (eprimf p)).

Definition actfs (x : int) (m : {perm facelet}) : int :=
  packn ncoord
    (fun k => if k < nedge then nbit x (src m k) (+) xbit m k
              else nbit x (nedge + src m (k - nedge))).

(* ---- 8. The three statements this file exists for ------------------------ *)

(* the bound, so that x ranges over a segment of int and DfStep is a loop     *)
Lemma coordfs_lt g : to_nat (coordfs g) < 2 ^ ncoord.
Proof. by apply: packn_lt. Qed.

Lemma actfs_lt x m : to_nat (actfs x m) < 2 ^ ncoord.
Proof. by apply: packn_lt. Qed.

(* THE EQUIVARIANCE.  Both halves reduce to one bit, and one bit to the two   *)
(* cases of edge_case: m^-1 (eprimf p) is eprimf q, and then pcol of it is    *)
(* true so xbit is false and the bit is copied; or it is epair (eprimf q),    *)
(* and then pcol_epair complements the flip bit while scol_epair leaves the   *)
(* slice bit alone.  cubP g is what lets g^-1 be pushed through epair.        *)
(* the two halves, where the content is.  Each is one application of
   edge_case: m^-1 (eprimf j) is eprimf q, and then pcol of it is true so
   xbit is false and the bit is copied; or it is epair (eprimf q), and then
   pcol_epair complements the flip bit while scol_epair leaves the slice bit
   alone.  cubP g is what lets g^-1 be pushed through epair.                *)

Lemma ncoord_dig : ncoord <= ndigits.
Proof. by vm_compute. Qed.

Lemma eprimf_edge q : q < nedge -> (eprimf q : nat) \in eprim ++ esec.
Proof. by move=> qL; rewrite eprimfK // mem_cat mem_nth ?orbT //; vm_compute. Qed.

Lemma pcol_eprimf q : q < nedge -> pcol (eprimf q).
Proof. by move=> qL; rewrite /pcol eprimfK // mem_nth //; vm_compute. Qed.

Lemma cubP_epairV g f : cubP g -> g^-1 (epair f) = epair (g^-1 f).
Proof. by move=> /cubPV/forallP hg; rewrite (eqP (hg f)). Qed.

Lemma coordfs_flip g m j :
  cubP g -> cubP m -> j < nedge ->
  flipb (g * m) j = flipb g (src m j) (+) xbit m j.
Proof.
move=> cg cm jL.
have jE : (eprimf j : nat) \in eprim ++ esec := eprimf_edge jL.
have xE : ((m^-1 (eprimf j)) : nat) \in eprim ++ esec.
  by rewrite (cubP_edge _ (cubPV cm)).
rewrite /flipb /xbit /src invMg permM.
case: (edge_case xE) => [xP|xS].
  have hx : pcol (m^-1 (eprimf j)) by rewrite {1}xP pcol_eprimf // epos_lt.
  by rewrite hx addbF {1}xP.
have hx : pcol (m^-1 (eprimf j)) = false.
  by rewrite {1}xS pcol_epair ?eprimf_edge ?epos_lt // pcol_eprimf // epos_lt.
have gE : ((g^-1 (eprimf (epos (m^-1 (eprimf j))))) : nat) \in eprim ++ esec.
  by rewrite (cubP_edge _ (cubPV cg)) eprimf_edge // epos_lt.
by rewrite hx addbT {1}xS cubP_epairV // pcol_epair // negbK.
Qed.

Lemma coordfs_slice g m j :
  cubP g -> cubP m -> j < nedge ->
  sliceb (g * m) j = sliceb g (src m j).
Proof.
move=> cg cm jL.
have jE : (eprimf j : nat) \in eprim ++ esec := eprimf_edge jL.
have xE : ((m^-1 (eprimf j)) : nat) \in eprim ++ esec.
  by rewrite (cubP_edge _ (cubPV cm)).
rewrite /sliceb /src invMg permM.
case: (edge_case xE) => [xP|xS].
  by rewrite {1}xP.
by rewrite {1}xS cubP_epairV // scol_epair.
Qed.

(* and the equivariance is the two halves, routed through the packing *)
(* stated on cubP m rather than on m \in Sset: that the moves satisfy cubP is
   a table fact and lives in Coordfsi.v, so keeping it out here leaves this
   file about the summary alone.                                            *)
Lemma coordfsM g m :
  cubP g -> cubP m -> coordfs (g * m) = actfs (coordfs g) m.
Proof.
move=> cg mS; apply: (@packn_eq ncoord);
  [exact: (@packn_lt ncoord _ ncoord_dig) |
   exact: (@packn_lt ncoord _ ncoord_dig) | ].
have el q : src m q < nedge by rewrite /src epos_lt.
have el1 q : src m q < ncoord.
  by rewrite (leq_trans (el q)) // /ncoord leq_addr.
have el2 q : nedge + src m q < ncoord by rewrite /ncoord ltn_add2l el.
move=> j jL; rewrite /coordfs /actfs !nbit_packn ?ncoord_dig ?el1 ?el2 //.
have [jn|jn] := ltnP j nedge.
  by rewrite el coordfs_flip.
rewrite ltnNge leq_addr /= addKn coordfs_slice //.
by rewrite -(ltn_add2l nedge) subnKC.
Qed.

(* Section 9, what this gives Search.v, is in Coordfsi.v: it needs
   moves_cubP, and moves_cubP needs the tables.                              *)
