(* =========================================================================  *)
(*  RowFoldN.v -- the folded run with its count kept as it goes.              *)
(* =========================================================================  *)

(* RowFoldSrchIC's run counts its map after every level with fcount, a walk  *)
(* of the whole map.  hcoset never does: it adds up the bits as it sets them. *)
(* Here too.  The mark returns the map and the count, the count going up by   *)
(* what fcount would give the new bit -- the size of the orbit of its kept    *)
(* page, and only for the low half of a cell, as fcount reads it.  The map is *)
(* walked once only after a prepass, which writes too many bits to follow.    *)
(*                                                                            *)
(* NOTHING NEW ABOUT THE CUBE.  The count only decides when the cuts and the *)
(* early stop come on, and the searches are sound whatever it is: the map of  *)
(* the counting search is the map of isrchkL, and the level at the last       *)
(* search depth is isrchskL itself.                                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask.
Require Import RowFold RowFoldOk RowFoldLvl RowFoldSrch RowFoldRun.
Require Import RowFoldSrchI RowFoldSrchIP RowFoldRunC RowFoldSrchIC RowFoldSim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- the mark that counts ------------------------------------------------ *)

(* fmarkn, the count going up by the weight fcount gives the bit              *)
Definition fmarknw (fpg fsgr fsbt forb : arr) (mn : rmap * int)
                   (pg gr bt : int) : rmap * int :=
  let: (m, n) := mn in
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12)%uint63 then 0 else 1) in
  let r := fkpt w in
  let g := sgrmv fsgr u pty gr in
  let v := bitof (fbit (fhlf w) (sbtmv fsbt u bt)) in
  let c := pchk r in
  let i := Uint63.add (poff r) g in
  let a := PArray.get m c in
  let old := PArray.get a i in
  let w' := Uint63.lor old v in
  if Uint63.eqb w' old then mn
  else (PArray.set m c (PArray.set a i w'),
        if Uint63.eqb (fhlf w) 0 then Uint63.add n (PArray.get forb r) else n).

(* its map is fmark's                                                         *)
Lemma fmarknw_fst fpg fsgr fsbt forb mn pg gr bt :
  (fmarknw fpg fsgr fsbt forb mn pg gr bt).1
  = fmark fpg fsgr fsbt mn.1 pg gr bt.
Proof.
case: mn => m n; rewrite /fmarknw /fmark /ffor; cbv zeta.
by case: ifP.
Qed.

(* ---- folds and ifs under a projection ------------------------------------ *)

Lemma ifold_fst (A B : Type) n j (f : int -> A * B -> A * B)
      (g : int -> A -> A) a :
  (j + n <= nwB)%N ->
  (forall k b, (to_nat k < j + n)%N -> (f k b).1 = g k b.1) ->
  (ifold n (advn j 0%uint63) f a).1 = ifold n (advn j 0%uint63) g a.1.
Proof.
elim: n j a => [|n ih] j a hb hfg //=.
have -> : Uint63.add (advn j 0%uint63) 1%uint63 = advn j.+1 0%uint63.
  by rewrite advnS.
have hk : (to_nat (advn j 0%uint63) < j + n.+1)%N.
  rewrite to_nat_advn0; first by rewrite addnS ltnS leq_addr.
  by apply: leq_trans hb; rewrite addnS ltnS leq_addr.
rewrite -(hfg _ _ hk); apply: ih; first by rewrite addSnnS.
by move=> k b hk'; apply: hfg; rewrite -addSnnS.
Qed.

Lemma ifold_fsti (A B : Type) n (f : int -> A * B -> A * B)
      (g : int -> A -> A) a :
  (n <= nwB)%N ->
  (forall k b, (to_nat k < n)%N -> (f k b).1 = g k b.1) ->
  (ifold n 0%uint63 f a).1 = ifold n 0%uint63 g a.1.
Proof. by move=> hb hfg; apply: (@ifold_fst _ _ n 0). Qed.

(* the two sides keep the same test and the same first branch                 *)
Lemma fst_if_else (A B : Type) (b : bool) (a x : A * B) (y : A) :
  x.1 = y -> (if b then a else x).1 = if b then a.1 else y.
Proof. by case: b. Qed.

Lemma fst_if_then (A B : Type) (b : bool) (x z : A * B) (y : A) :
  (b -> x.1 = y) -> (if b then x else z).1 = if b then y else z.1.
Proof. by case: b => // ->. Qed.

Section FN.

Variable e8num e4bit : arr.
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation plc := (place24 e8num e4bit).
Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Local Notation p1g := (fp1g F frep fsym twsym).
Local Notation wdist := mdist.
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

Local Notation fmknw := (fmarknw fpg fsgr fsbt forb).
Local Notation fsrki :=
  (fsrchki e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation isrkL :=
  (isrchkL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation isrskL :=
  (isrchskL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).

(* ---- the counting search ------------------------------------------------- *)

(* a leaf, counted                                                            *)
Definition wleaf (c : int) (x : pst) (a : rmap * int) : rmap * int :=
  if csolved c then let: (pg, gr, bt) := plc (tomemb x) in fmknw a pg gr bt
  else a.

(* isrchkL, the count carried beside the map; nothing stops it               *)
Fixpoint iwsrchL (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                 (msk pv : int) (a : rmap * int) : rmap * int :=
  if togo is togo'.+1 then
    if togo' is 0 then
      ifold RowRun.nmvn 0
        (fun k a' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
           else if ~~ okmv pv k then a'
           else if cut && ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
           then a'
           else wleaf (cstep c k) (xstep x k) a')
        a
    else
    let togoi' := Uint63.sub togoi 1 in
    ifold RowRun.nmvn 0
      (fun k a' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
         else if ~~ okmv pv k then a'
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then a'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then iwsrchL cut togo' togoi' c' (xstep x k)
                        (wmask w (fsslack (Uint63.sub togoi' nd))) k a'
           else a')
      a
  else wleaf c x a.

Lemma wleaf_fst cut togoi c x msk pv a :
  (wleaf c x a).1 = fsrki cut 0 togoi c x msk pv a.1.
Proof.
rewrite /wleaf /fsrchki; case: (csolved c); last by [].
case: (plc (tomemb x)) => [[pg gr] bt].
exact: fmarknw_fst.
Qed.

(* ITS MAP IS isrchkL's                                                       *)
Lemma iwsrchL_fst cut togo :
  forall togoi c x msk pv a,
  (iwsrchL cut togo togoi c x msk pv a).1 = isrkL cut togo togoi c x msk pv a.1.
Proof.
elim: togo => [|togo ih] togoi c x msk pv a.
  exact: wleaf_fst.
case: togo ih => [|togo] ih.
  rewrite /iwsrchL /isrchkL.
  apply: ifold_fsti; first exact: nmvn_nwB.
  move=> k b hk.
  apply: fst_if_else; apply: fst_if_else; apply: fst_if_else.
  exact: wleaf_fst.
rewrite /iwsrchL /isrchkL; cbv zeta.
apply: ifold_fsti; first exact: nmvn_nwB.
move=> k b hk.
apply: fst_if_else; apply: fst_if_else; apply: fst_if_else.
apply: fst_if_then => _.
exact: ih.
Qed.

(* ---- the level and the run ---------------------------------------------- *)

(* THE UNREACHABLE STOP.  Below the last search depth the counting search    *)
(* runs to the end.                                                          *)

(* the level, from the count nb of the map it starts from                     *)
Definition wslv (cut : bool) (d : nat) (m' : rmap) (nb : int) : rmap * int :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (fsslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let e := Uint63.add enoughb (Uint63.div nb enoughd) in
        isrskL cut d di croot sroot msk 18 e (m', nb)
      else iwsrchL cut d di croot sroot msk 18 (m', nb)
    else (m', nb)
  else (m', nb).

(* THE RUN.  With the cuts on the prepass writes the map, and it is counted   *)
(* once; with the cuts off the count is the one carried.                      *)
Fixpoint wrun (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m1 := flev m dst in
      let a := wslv true d.+1 m1 (fcount forb fpop m1) in
      wrun n1 d.+1 a.2 a.1 m
    else
      let a := wslv false d.+1 m n0 in
      wrun n1 d.+1 a.2 a.1 dst
  else m.

End FN.

Section FNS.

(* ---- the layout, from Row.v ---------------------------------------------- *)

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place24 e8num e4bit).
Local Notation unplc := (unplace24 e8inv e4of par8 par4).

(* ---- the fold, and the move on groups and bits --------------------------- *)

Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.

Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Local Notation fmk := (fmark fpg fsgr fsbt).

(* ---- the folded phase one table, which nothing here reads ---------------- *)

Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

(* ---- what the search carries --------------------------------------------- *)

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

Local Notation fsr :=
  (fsrch e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved).
Local Notation flv :=
  (flvl e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch).
Local Notation frn :=
  (frun e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch).

(* ---- what the map claims, and what a member is --------------------------- *)

Variable pos : memb -> {perm facelet}.

Local Notation Pd := (Pd e8inv e4of par8 par4 pos).
Local Notation soundatd := (soundatd e8inv e4of par8 par4 fpg fsgr fsbt pos).

Hypothesis Porbd : forall d, forall p q c pg gr bt,
  inrange24 p q c -> inrange24 pg gr bt ->
  pchk (fkpt (PArray.get fpg p)) = pchk (fkpt (PArray.get fpg pg)) ->
  Uint63.add (poff (fkpt (PArray.get fpg p)))
    (sgrmv fsgr (fren (PArray.get fpg p))
       (fpar (PArray.get fpg p) lxor (if c <? 12 then 0 else 1)) q)
  = Uint63.add (poff (fkpt (PArray.get fpg pg)))
      (sgrmv fsgr (fren (PArray.get fpg pg))
         (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
  ~~ (Uint63.land (bitof (fbit (fhlf (PArray.get fpg p))
                     (sbtmv fsbt (fren (PArray.get fpg p)) c)))
                  (bitof (fbit (fhlf (PArray.get fpg pg))
                     (sbtmv fsbt (fren (PArray.get fpg pg)) bt))) =? 0) ->
  Pd d p q c -> Pd d pg gr bt.

Hypothesis Qlod : forall d,
  Qlo_st fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi (Pd d) (Pd d.+1).
Hypothesis Qhid : forall d,
  Qhi_st fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi (Pd d) (Pd d.+1).

(* ---- and the five the search owes, which are RowRun's own ---------------- *)

Variable coordP : int -> pst -> Prop.
Variable pstok : pst -> bool.

Hypothesis coord_root : coordP croot sroot.
Hypothesis root_ball : posp sroot \in ball Sset 0.
Hypothesis root_pok : pstok sroot.

Hypothesis coord_step : forall c x k, (to_nat k < RowRun.nmvn)%N -> pstok x ->
  coordP c x -> coordP (cstep c k) (xstep x k).
Hypothesis xstep_pok : forall x k, (to_nat k < RowRun.nmvn)%N ->
  pstok x -> pstok (xstep x k).
Hypothesis xstep_pos : forall x k, (to_nat k < RowRun.nmvn)%N -> pstok x ->
  posp (xstep x k) = (posp x * nth 1%g moves (to_nat k))%g.
Hypothesis leaf_memb : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> membok par8 par4 (tomemb x).
Hypothesis leaf_pos : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> pos (tomemb x) = posp x.

(* ---- the search does not change how long the map is ---------------------- *)

Variables forb fpop : arr.
Variable ishm : int.

Local Notation fsrk :=
  (fsrchk e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation fsrsk :=
  (fsrchsk e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation flvsk :=
  (flvlsk e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).
Local Notation p1g := (fp1g F frep fsym twsym).
Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).


Local Notation wslvN :=
  (wslv e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb ishm).
Local Notation wrunN :=
  (wrun e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).

Lemma dS63 d : (d.+1 <= 63)%N -> to_nat (of_nat d.+1) = d.+1.
Proof. by move=> hb; apply: of_natK; apply: (@ltn_nwB 6). Qed.

Lemma wslv_len cut d m nb : (d.+1 <= 63)%N ->
  PArray.length (wslvN cut d.+1 m nb).1 = PArray.length m.
Proof.
move=> hb; rewrite /wslv; cbv zeta.
case: ifP => _; last by [].
case: ifP => _; last by [].
case: ifP => _.
  erewrite isrchskL_eq; [ | exact: dS63 hb | exact: hb].
  exact: fsrchskL_len.
rewrite iwsrchL_fst.
erewrite isrchkL_eq; [ | exact: dS63 hb | exact: hb].
exact: fsrchkL_len.
Qed.

Lemma wslv_sound cut d m nb : (d.+1 <= 63)%N ->
  soundatd m d.+1 -> soundatd (wslvN cut d.+1 m nb).1 d.+1.
Proof.
move=> hb hg; rewrite /wslv; cbv zeta.
case: ifP => _; last exact: hg.
case: ifP => _; last exact: hg.
case: ifP => _.
  erewrite isrchskL_eq; [ | exact: dS63 hb | exact: hb].
  apply: fsrchskL_sound; try eassumption; first exact: leqnn.
  by rewrite subnn; exact: root_ball.
rewrite iwsrchL_fst.
erewrite isrchkL_eq; [ | exact: dS63 hb | exact: hb].
apply: fsrchkL_sound; try eassumption; first exact: leqnn.
by rewrite subnn; exact: root_ball.
Qed.

(* THE RUN IS SOUND, whatever its counts are                                  *)
Lemma wrun_sound n d n0 m dst : (d + n <= 63)%N ->
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length m)) ->
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length dst)) ->
  soundatd m d -> soundatd dst d -> soundatd (wrunN n d n0 m dst) (d + n).
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hb hlm hld hm hd.
  by rewrite addn0; exact: hm.
have hd1 : (d.+1 <= 63)%N.
  by apply: leq_trans hb; rewrite -addSnnS; exact: leq_addr.
have hb' : (d.+1 + n <= 63)%N by rewrite addSnnS.
rewrite addnS -addSn /wrun -/wrun; case: ifP => _.
  apply: ih.
  - exact: hb'.
  - by move=> r hr; rewrite (wslv_len _ _ _ hd1) flevel_length; apply: hld.
  - exact: hlm.
  - apply: wslv_sound; first exact: hd1.
    rewrite /soundatd; apply: flevel_sound.
    + exact: Qlod.
    + exact: Qhid.
    + exact: PdW.
    + exact: hld.
    + exact: hm.
    exact: soundatdW.
  exact: soundatdW.
apply: ih.
- exact: hb'.
- by move=> r hr; rewrite (wslv_len _ _ _ hd1); apply: hlm.
- exact: hld.
- by apply: wslv_sound; [exact: hd1 | exact: soundatdW].
exact: soundatdW.
Qed.

End FNS.
