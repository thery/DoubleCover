(* =========================================================================  *)
(*  RowSrchN.v -- the plain run, its count kept as it goes.                   *)
(* =========================================================================  *)

(* RowSrchC's run counts the map once a level, and on the plain map one count *)
(* is a walk of 6.5 GB: measured on roquableu, 29.6 s, and thirteen of them   *)
(* were most of the 416 s of a run to thirteen.  hcoset keeps the count as    *)
(* it goes: every new bit adds one.  Here the level runs the counting search  *)
(* at every depth, not only at the last one, and hands its count on; the map  *)
(* is walked only after a prepass, which is itself a walk of the map.         *)
(*                                                                            *)
(* THE COUNT IS NOT PART OF WHAT IS PROVED.  It only decides when the cuts    *)
(* and the early stop come on, and every level is sound whatever it decides.  *)
(* Below the last search depth the counting search is given a threshold no   *)
(* count reaches; were it reached, the stop would still be sound.             *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask RowSrch RowSrchP RowSrchC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* a threshold no count of the row reaches: the row has 2 ^ 34 members       *)
Definition nbig : int := 4611686018427387904.

Section SrchN.

(* ---- the layout, the prepass and the table: RowRun's own ----------------- *)

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place e8num e4bit).
Local Notation unplc := (unplace e8inv e4of par8 par4).

Variable cpg cfl mgr msw mlo mhi : arr.

(* THE PREPASS IS A PARAMETER.  RowMap's is one; RowLvl's prepassD, which     *)
(* reads each page's chunk once and puts it back once, is another and is      *)
(* proved equal to it.  The run takes whichever it is handed.  The proof asks *)
(* only that it be RowMap's.                                                  *)
Variable prep : rmap -> rmap -> rmap.

Hypothesis prep_eq : forall m dst,
  prep m dst = prepass cpg cfl mgr msw mlo mhi m dst.

(* ---- the phase one table, folded, and the moves it names ----------------- *)

(* THE OTHER FOLD, AND IT IS NOT THE MAP'S.  Rokicki folds the phase one      *)
(* table by the sixteen symmetries and stores one rank of each orbit; beside  *)
(* the distance an entry names which moves bring the state nearer H and which *)
(* at least do not take it further.  A node then offers three or four moves   *)
(* where RowRun's table left it offering eighteen.                            *)
(*                                                                            *)
(* THIS IS THE SAME READ THE FOLDED RUN MAKES.  Only the MAP is unfolded      *)
(* here; the table is folded on both sides, because that fold costs the run   *)
(* nothing and is what makes the search finish.                               *)
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).
Local Notation nmvn := RowRun.nmvn.

(* ---- what the search carries: RowRun's own ------------------------------- *)

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable posp : pst -> {perm facelet}.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

(* the moves of H, one bit each                                               *)
Variable ishm : int.

Local Notation p1g := (sp1g F frep fsym twsym).
Local Notation srchk := (RowSrch.srchk e8num e4bit F frep fsym twsym
                           dnlo dnhi fllo flhi cstep xstep tomemb okmv
                           csolved ishm).
Local Notation srchsk := (RowSrch.srchsk e8num e4bit F frep fsym twsym
                            dnlo dnhi fllo flhi cstep xstep tomemb okmv
                            csolved ishm).
Local Notation levelsk := (RowSrch.levelsk e8num e4bit prep
                             F frep fsym twsym dnlo dnhi fllo flhi
                             cstep xstep tomemb okmv csolved croot sroot
                             dsrch ishm).
Local Notation runsk := (RowSrch.runsk e8num e4bit prep
                           F frep fsym twsym dnlo dnhi fllo flhi
                           cstep xstep tomemb okmv csolved croot sroot
                           dsrch ishm).

(* ---- what the map claims ------------------------------------------------- *)

Variable pos : memb -> {perm facelet}.

Local Notation wthn := (RowRun.wthn pos).
Local Notation soundat := (RowRun.soundat e8inv e4of par8 par4 pos).

(* ---- the bridge to the cube: RowRun's own -------------------------------- *)

Variable coordP : int -> pst -> Prop.
Variable pstok : pst -> bool.

Hypothesis coord_root : coordP croot sroot.
Hypothesis root_ball : posp sroot \in ball Sset 0.
Hypothesis root_pok : pstok sroot.

Hypothesis coord_step : forall c x k, (to_nat k < nmvn)%N -> pstok x ->
  coordP c x -> coordP (cstep c k) (xstep x k).
Hypothesis xstep_pok : forall x k, (to_nat k < nmvn)%N ->
  pstok x -> pstok (xstep x k).
Hypothesis xstep_pos : forall x k, (to_nat k < nmvn)%N -> pstok x ->
  posp (xstep x k) = (posp x * nth 1%g moves (to_nat k))%g.
Hypothesis leaf_memb : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> membok par8 par4 (tomemb x).
Hypothesis leaf_pos : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> pos (tomemb x) = posp x.

(* ---- and the prepass's bridge: RowRun's own ------------------------------ *)

Variable btmv : int -> int -> int.
Variable hmv : int -> {perm facelet}.

Hypothesis hmv_Sset : forall k, (to_nat k < nhn)%N -> hmv k \in Sset.

Hypothesis grpmvP : forall k v bt', (to_nat k < nhn)%N ->
  (bt' <? nbit48i) ->
  ~~ (Uint63.land (RowMap.grpmv cfl msw mlo mhi k v) (bitof bt') =? 0) ->
  exists2 bt, (bt <? nbit48i) &
    btmv k bt = bt' /\ ~~ (Uint63.land v (bitof bt) =? 0).

Hypothesis prep_move : forall k pg gr bt, (to_nat k < nhn)%N ->
  inrange pg gr bt ->
  inrange (RowMap.pgmv cpg k pg) (RowMap.grmv mgr k gr) (btmv k bt) /\
  pos (unplc (RowMap.pgmv cpg k pg) (RowMap.grmv mgr k gr) (btmv k bt))
  = (pos (unplc pg gr bt) * hmv k)%g.

(* ---- the search with the cuts, which is RowRun.srch_sound with two more    *)
(*      branches, each closed by the hypothesis it was given ---------------- *)

(* WHAT IS NOT CLAIMED: nothing here says the cuts lose no member.  They do   *)
(* lose members.  What is proved is that the map filled.                      *)
Local Notation srchki := (RowSrch.srchki e8num e4bit F frep fsym twsym
                            dnlo dnhi fllo flhi cstep xstep tomemb okmv
                            csolved ishm).
Local Notation srchski := (RowSrch.srchski e8num e4bit F frep fsym twsym
                             dnlo dnhi fllo flhi cstep xstep tomemb okmv
                             csolved ishm).
Local Notation levelski := (RowSrch.levelski e8num e4bit prep
                              F frep fsym twsym dnlo dnhi fllo flhi
                              cstep xstep tomemb okmv csolved croot sroot
                              dsrch ishm).
Local Notation runski := (RowSrch.runski e8num e4bit prep
                            F frep fsym twsym dnlo dnhi fllo flhi
                            cstep xstep tomemb okmv csolved croot sroot
                            dsrch ishm).


Local Notation srchkL := (RowSrchC.srchkL e8num e4bit F frep fsym twsym
                            dnlo dnhi fllo flhi cstep xstep tomemb okmv
                            csolved ishm).
Local Notation srchskL := (RowSrchC.srchskL e8num e4bit F frep fsym twsym
                             dnlo dnhi fllo flhi cstep xstep tomemb okmv
                             csolved ishm).
Local Notation srchskiL := (RowSrchC.srchskiL e8num e4bit F frep fsym twsym
                              dnlo dnhi fllo flhi cstep xstep tomemb okmv
                              csolved ishm).

(* ---- the level, with its count -------------------------------------------- *)

(* the map, and how many members it holds; nb is the count of the map it     *)
(* starts from                                                                *)
Definition slvlskn (cut : bool) (d : nat) (m' : rmap) (nb : int) : rmap * int :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then
      let e := if (d == dsrch)%N
               then Uint63.add enoughb (Uint63.div nb enoughd) else nbig in
      srchskL cut d croot sroot (wmask w (d - nd)) 18 e (m', nb)
    else (m', nb)
  else (m', nb).

(* the map is walked only after a prepass                                    *)
Fixpoint runskn (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m1 := prep m dst in
      let mn := slvlskn true d.+1 m1 (mcount m1) in
      runskn n1 d.+1 mn.2 mn.1 m
    else
      let mn := slvlskn false d.+1 m n0 in
      runskn n1 d.+1 mn.2 mn.1 dst
  else m.

Lemma slvlskn_sound cut m nb d :
  soundat m d.+1 -> soundat (slvlskn cut d.+1 m nb).1 d.+1.
Proof.
move=> hp; rewrite /slvlskn; cbv zeta.
case: ifP => _; last exact: hp.
case: ifP => _; last exact: hp.
apply: srchskL_sound; try eassumption; first exact: leqnn.
by rewrite subnn.
Qed.

Lemma runskn_sound n d n0 m dst :
  soundat m d -> soundat dst d -> soundat (runskn n d n0 m dst) (d + n).
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hm hd; first by rewrite addn0.
rewrite addnS -addSn /= -/runskn; case: ifP => _.
  apply: ih; last exact: RowRun.soundatW.
  apply: slvlskn_sound; rewrite !prep_eq.
  apply: (RowRun.prepass_sound hmv_Sset grpmvP prep_move hm).
  exact: RowRun.soundatW.
apply: ih; last exact: RowRun.soundatW.
by apply: slvlskn_sound; exact: RowRun.soundatW.
Qed.

(* ---- the same over the int search ----------------------------------------- *)

Definition slvlskni (cut : bool) (d : nat) (m' : rmap) (nb : int) : rmap * int :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (sslack (Uint63.sub di (wdist w))) in
      let e := if (d == dsrch)%N
               then Uint63.add enoughb (Uint63.div nb enoughd) else nbig in
      srchskiL cut d di croot sroot msk 18 e (m', nb)
    else (m', nb)
  else (m', nb).

Fixpoint runskni (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m1 := prep m dst in
      let mn := slvlskni true d.+1 m1 (mcount m1) in
      runskni n1 d.+1 mn.2 mn.1 m
    else
      let mn := slvlskni false d.+1 m n0 in
      runskni n1 d.+1 mn.2 mn.1 dst
  else m.

Lemma slvlskni_eq cut d m nb : (d <= 63)%N ->
  slvlskni cut d m nb = slvlskn cut d m nb.
Proof.
move=> hb; rewrite /slvlskni /slvlskn; cbv zeta.
case: ifP => _; last by [].
have hdw : (d < nwB)%N.
  by apply: (@ltn_nwB 6); [ | exact: hb].
have hd : to_nat (of_nat d) = d := of_natK d hdw.
set w := mdist _.
rewrite nleE hd; case: ifP => hle; last by [].
have hbd : (to_nat (of_nat d) < nwB)%N := to_nat_bounded (of_nat d).
have hwle : (to_nat w <= to_nat (of_nat d))%N by rewrite hd; exact: hle.
rewrite mmaskiE (to_nat_sub (of_nat d) w hwle hbd) hd.
by rewrite srchskiL_eq.
Qed.

Lemma runskni_eq n d n0 m dst : (d + n <= 63)%N ->
  runskni n d n0 m dst = runskn n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hb; first by [].
have hd1 : (d.+1 <= 63)%N.
  by apply: leq_trans hb; rewrite -addSnnS; exact: leq_addr.
have hb' : (d.+1 + n <= 63)%N by rewrite addSnnS.
rewrite /= -/runskni -/runskn.
by case: ifP => _; rewrite slvlskni_eq // ih.
Qed.

End SrchN.
