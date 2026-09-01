(* =========================================================================  *)
(*  RowCubInst.v -- the row again, with the twenty cubies carried.            *)
(* =========================================================================  *)

(* RowInst CARRIES A FORTY EIGHT ENTRY TABLE and this file carries twenty     *)
(* int63 instead.  Nothing here is new mathematics: every fact RowInst        *)
(* proves of the table transfers, because the twenty NAME a table and the     *)
(* things the row asks of a position -- the coordinate, whether it is a cube, *)
(* the position itself -- depend on that table alone.                         *)
(*                                                                            *)
(* THE TWO EQUATIONS IT ALL RESTS ON.  Stepping the twenty and reading the    *)
(* table back is stepping the table (ystep_ti), and the root names the root   *)
(* (yroot_ti).  The first is RowCubi's two bridges put together.              *)
(*                                                                            *)
(* WHY IT IS WORTH IT.  MEASURED at depth thirteen on roquableu: the search   *)
(* is 236.5 s carrying the table and 141.7 s carrying the twenty, against a   *)
(* floor of 68.9 s with no position at all.                                   *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import Lehmer RowTabP RowMemb RowCub RowCubi.
Require Import Fold RowMask RowSrch RowSrchP RowMark.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* ---- what only the table it names decides -------------------------------- *)

(* pstok, the coordinate and the position all read the table and nothing      *)
(* else, so two arrays with the same table agree on all three.                *)
Lemma pstok_ti a b : tabi_ok flast a -> ti2t flast a = ti2t flast b ->
  RowInst.pstok a = RowInst.pstok b.
Proof.
move=> ha he.
have hb : tabi_ok flast b by rewrite /tabi_ok -he.
rewrite /RowInst.pstok /tabi_ok he (cubtiE ha) (cubtiE hb) he.
by rewrite /RowInst.twPti he (coordiE ha) (coordiE hb) he.
Qed.

Lemma coordof_ti a b : tabi_ok flast a -> ti2t flast a = ti2t flast b ->
  RowInst.coordof a = RowInst.coordof b.
Proof.
move=> ha he.
have hb : tabi_ok flast b by rewrite /tabi_ok -he.
rewrite /RowInst.coordof (ctwistiE ha) (ctwistiE hb).
by rewrite (coordiE ha) (coordiE hb) he.
Qed.

Lemma posp_ti a b : ti2t flast a = ti2t flast b ->
  RowInst.posp a = RowInst.posp b.
Proof. by move=> he; rewrite /RowInst.posp he. Qed.

(* ---- the twenty that hold cubies ----------------------------------------- *)

(* naming places is enough: a corner place under eight with a turn under      *)
(* three is a number under twenty four, and so is an edge place with a flip.  *)
Lemma yok_yoki y : yok (a2y y) -> yoki y.
Proof.
move=> /andP[/allP hc /allP he]; apply/allP => q.
rewrite mem_iota add0n leq0n /= => hq.
rewrite -(a2y_nth y hq).
case: (ltnP q 8) => hq8.
  have h1 : (ycg (a2y y) q < 8)%N.
    by apply: hc; rewrite mem_iota add0n leq0n hq8.
  by move: h1; rewrite /ycg ltn_divLR.
have hq12 : (q - 8 < 12)%N by rewrite ltn_subLR.
have h2 : (yeg (a2y y) (q - 8) < 12)%N.
  by apply: he; rewrite mem_iota add0n leq0n hq12.
by move: h2; rewrite /yeg subnKC // ltn_divLR.
Qed.

(* WHAT THE SEARCH CARRIES: twenty that name a cube, and the table they name  *)
(* is one RowInst would accept.                                               *)
Definition ypstok (y : arr) : bool :=
  cubok (a2y y) && RowInst.pstok (y2ti y).

Lemma ypstok_ti y : ypstok y -> ti2t flast (y2ti y) = cub2tabR (a2y y).
Proof.
move=> /andP[hc _]; apply: ti2t_y2ti => //.
by apply: yok_yoki; case/andP: hc.
Qed.

Lemma ypstok_tabi y : ypstok y -> tabi_ok flast (y2ti y).
Proof. by move=> /andP[_ /and3P[h _ _]]. Qed.

Lemma n18_small : (18 < nwB)%N. Proof. by apply: (@ltn_nwB 5). Qed.

Lemma int_of_nat_k (k : int) : (to_nat k < 18)%N -> k = of_nat (to_nat k).
Proof.
move=> hk; apply: to_nat_inj; rewrite of_natK //.
by apply: (ltn_trans hk n18_small).
Qed.

(* ---- THE TRANSFER: stepping the twenty is stepping the table ------------- *)

Lemma ystep_ti y k : (k < 18)%N -> ypstok y ->
  ti2t flast (y2ti (zstepi y (of_nat k)))
  = ti2t flast (RowInst.xstep (y2ti y) (of_nat k)).
Proof.
move=> hk hy.
have hkb : (k < nwB)%N by apply: (ltn_trans hk n18_small).
have /andP[hc hp] := hy.
have hyi : yoki y by apply: yok_yoki; case/andP: hc.
have hcs : cubok (a2y (zstepi y (of_nat k))).
  by rewrite (a2y_zstepi hk hyi); apply: cubok_zstep.
have hyis : yoki (zstepi y (of_nat k)) by apply: yok_yoki; case/andP: hcs.
have hkn : (to_nat (of_nat k) < nmvn)%N by rewrite of_natK.
have hmok : tabi_ok flast (RowInst.mvi (of_nat k)) by apply: RowInst.mvi_ok.
rewrite (ti2t_y2ti hyis hcs) (a2y_zstepi hk hyi) (cub2tabR_zstep hk hc).
rewrite /RowInst.xstep (ti2t_comp n47_small n47_len (ypstok_tabi hy) hmok).
by rewrite (ypstok_ti hy) -mvt'E.
Qed.

Lemma ypstok_step y k : (k < 18)%N -> ypstok y -> ypstok (zstepi y (of_nat k)).
Proof.
move=> hk hy; have /andP[hc hp] := hy.
have hyi : yoki y by apply: yok_yoki; case/andP: hc.
have hcs : cubok (a2y (zstepi y (of_nat k))).
  by rewrite (a2y_zstepi hk hyi); apply: cubok_zstep.
have hyis : yoki (zstepi y (of_nat k)) by apply: yok_yoki; case/andP: hcs.
have hkn : (to_nat (of_nat k) < nmvn)%N.
  by rewrite of_natK //; apply: (ltn_trans hk n18_small).
apply/andP; split => //.
rewrite (pstok_ti _ (ystep_ti hk hy)); first by apply: RowInst.xstep_pok.
rewrite /tabi_ok (ti2t_y2ti hyis hcs) /cub2tabR.
by apply: tab_ok_inv; case/andP: hcs.
Qed.

(* ---- and the root names the root ----------------------------------------- *)

Lemma a2y_yrooti : a2y yrooti = yroot.
Proof. by have /andP[/eqP h _] := zstepiCP. Qed.

Lemma yroot_ti : ti2t flast (y2ti yrooti) = ti2t flast RowInst.sroot.
Proof.
have /andP[hc /eqP he] := yrootCP.
have hyi : yoki yrooti by apply: yok_yoki; rewrite a2y_yrooti; case/andP: hc.
by rewrite (ti2t_y2ti hyi _) ?a2y_yrooti.
Qed.

Lemma yroot_pok : ypstok yrooti.
Proof.
have /andP[hc _] := yrootCP.
have hyi : yoki yrooti by apply: yok_yoki; rewrite a2y_yrooti; case/andP: hc.
apply/andP; split; first by rewrite a2y_yrooti.
rewrite (pstok_ti _ yroot_ti); first exact: RowInst.root_pok.
by rewrite /tabi_ok (ti2t_y2ti hyi _) ?a2y_yrooti //; case/andP: hc.
Qed.

(* =========================================================================  *)
(*  THE ROW, WITH THE TWENTY CARRIED                                          *)
(* =========================================================================  *)

(* The same tables RowInst asks for, and the same facts about them.  Nothing  *)
(* below is proved again: each of the nine things the run wants is RowInst's, *)
(* moved across by the two equations above.                                   *)

Section CubInst.

Variable e8num e8inv e4bit e4of par8 par4 : arr.
Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Variable mpg mgr msw mlo mhi btmvt : arr.
Variable p1 : PArray.array arr.

(* THE PHASE ONE TABLE IS THE FOLDED ONE, and that fold is not the map's.    *)
(* Rokicki folds the table by the sixteen symmetries and names, beside the    *)
(* distance, the moves worth trying: a node offers three or four where p1     *)
(* left it offering eighteen.  The map here stays unfolded; only the table    *)
(* is folded, exactly as the folded run reads it.                             *)
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

(* the moves of H, one bit each                                              *)
Variable ishm : int.

(* THE PREPASS IS A PARAMETER.  RowMap's is one; RowLvl's prepassD, which     *)
(* reads each page's chunk once and puts it back once, is another and is      *)
(* proved equal to it.  Nothing here cares which, only that it be RowMap's.   *)
Variable prep : rmap -> rmap -> rmap.

Hypothesis prep_eq : forall m dst,
  prep m dst = prepass mpg mgr msw mlo mhi m dst.
Variable fsstep : int -> int -> int.
Variable memb2tab : memb -> seq nat.
Hypothesis memb2tab_ok : forall x, tab_ok flast (memb2tab x).
Variable tomembt : pstt -> memb.
Hypothesis hsrc : RowInst.srcok msw btmvt.
Hypothesis hhalf : RowInst.halfok msw mlo mhi btmvt.
Variable okmv : int -> int -> bool.
Variable dsrch nlev : nat.
Variable wl : seq (int * int * int * seq nat).

Hypothesis fsstepP : forall x k, (to_nat k < nmvn)%N -> RowInst.pstok x ->
  fsstep (fsidx (coordi x)) k = fsidx (coordi (RowInst.xstep x k)).

Hypothesis leaf_memb : forall c x, RowInst.coordP c x -> RowInst.pstok x ->
  pt flast (ti2t flast x) \in G -> ctwisti x = 0%uint63 ->
  coordi x = coordfs 1 -> membok par8 par4 (tomembt x).

Hypothesis tomemb_tab : forall c x, RowInst.coordP c x -> RowInst.pstok x ->
  pt flast (ti2t flast x) \in G -> ctwisti x = 0%uint63 ->
  coordi x = coordfs 1 ->
  pt flast (memb2tab (tomembt x)) = pt flast (ti2t flast x).

Hypothesis hpg : pgok mpg.
Hypothesis hgr : grok mgr.
Hypothesis hbt : btok btmvt.

Hypothesis memb2tab_move : forall k pg gr bt, (to_nat k < nhn)%N ->
  inrange pg gr bt ->
  pt flast (memb2tab (unplace e8inv e4of par8 par4
                        (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)))
  = pt flast (memb2tab (unplace e8inv e4of par8 par4 pg gr bt)) * hmv k.

(* ---- what the run carries, in terms of the twenty ------------------------ *)

Definition ytomemb (y : arr) : memb := tomembt (y2ti y).
Definition ycoordP (c : int) (y : arr) : Prop := RowInst.coordP c (y2ti y).
Definition yposp (y : arr) : {perm facelet} := RowInst.posp (y2ti y).
Definition ycsolved (c : int) : bool := RowInst.csolvedb c.

Lemma ycoord_root : ycoordP RowInst.croot yrooti.
Proof.
rewrite /ycoordP /RowInst.coordP.
rewrite (coordof_ti (ypstok_tabi yroot_pok) yroot_ti).
exact: RowInst.coord_root.
Qed.

Lemma yroot_ball : yposp yrooti \in ball Sset 0.
Proof. by rewrite /yposp (posp_ti yroot_ti); exact: RowInst.root_ball. Qed.

Lemma ycoord_step c y k : (to_nat k < nmvn)%N -> ypstok y -> ycoordP c y ->
  ycoordP (RowInst.cstep fsstep c k) (zstepi y k).
Proof.
move=> hk hy hc.
have hk18 : (to_nat k < 18)%N by [].
have hke := int_of_nat_k hk18.
have hs : ypstok (zstepi y (of_nat (to_nat k))) by apply: ypstok_step.
rewrite /ycoordP {2}hke /RowInst.coordP.
rewrite (coordof_ti (ypstok_tabi hs) (ystep_ti hk18 hy)) -hke.
by apply: (RowInst.coord_step fsstepP hk _ hc); case/andP: hy.
Qed.

Lemma yxstep_pok y k : (to_nat k < nmvn)%N -> ypstok y -> ypstok (zstepi y k).
Proof.
move=> hk hy; have hk18 : (to_nat k < 18)%N by [].
by rewrite (int_of_nat_k hk18); apply: ypstok_step.
Qed.

Lemma yxstep_pos y k : (to_nat k < nmvn)%N -> ypstok y ->
  yposp (zstepi y k) = yposp y * nth 1 moves (to_nat k).
Proof.
move=> hk hy; have hk18 : (to_nat k < 18)%N by [].
have hke := int_of_nat_k hk18.
rewrite /yposp {1}hke (posp_ti (ystep_ti hk18 hy)) -hke.
by apply: RowInst.xstep_pos => //; case/andP: hy.
Qed.

Lemma yleaf_memb c y : ycoordP c y -> ypstok y -> yposp y \in G ->
  ycsolved c -> membok par8 par4 (ytomemb y).
Proof.
move=> hc hy hg hs.
by apply: (RowInst.leaf_membW leaf_memb hc _ hg hs); case/andP: hy.
Qed.

Lemma yleaf_pos c y : ycoordP c y -> ypstok y -> yposp y \in G ->
  ycsolved c ->
  RowFinal.pos (RowInst.ptab memb2tab) (ytomemb y) = yposp y.
Proof.
move=> hc hy hg hs.
by apply: (RowInst.leaf_pos memb2tab_ok tomemb_tab hc _ hg hs); case/andP: hy.
Qed.

(* ---- the map the run leaves ---------------------------------------------- *)

(* two maps, allocated once and swapped at every level                        *)
Definition ymfin : PArray.array arr :=
  run e8num e4bit mpg mgr msw mlo mhi p1 (RowInst.cstep fsstep) zstepi
      ytomemb okmv ycsolved RowInst.croot yrooti dsrch nlev 0
      (mkempty tt) (mkempty tt).

Lemma ymfin_sound :
  soundat e8inv e4of par8 par4
          (RowFinal.pos (RowInst.ptab memb2tab)) ymfin nlev.
Proof.
rewrite /ymfin -{2}[nlev]add0n.
apply: (run_sound he8 he4 ycoord_root yroot_ball yroot_pok ycoord_step
                  yxstep_pok yxstep_pos yleaf_memb yleaf_pos
                  RowInst.hmv_Sset (RowInst.grpmvP hsrc hhalf)
                  (RowInst.prep_move memb2tab_ok hpg hgr hbt memb2tab_move));
  exact: RowInst.sound_mempty.
Qed.

(* ---- and the row --------------------------------------------------------- *)

Theorem yrow_within_20 : nlev = 20%N ->
  witsok e8inv e4of par8 par4 (RowInst.ptab memb2tab) wl ->
  mfull2 ymfin (wmap wl) ->
  forall x, membok par8 par4 x ->
  RowRun.wthn (RowFinal.pos (RowInst.ptab memb2tab)) 20 x.
Proof.
move=> hn hw hf x hx.
apply: (row_within_20 he8 he4 (RowInst.ptab_ok memb2tab_ok) _ hw hf hx).
by rewrite -hn; exact: ymfin_sound.
Qed.

Theorem ysuperflip_row_within_20 : nlev = 20%N ->
  witsok e8inv e4of par8 par4 (RowInst.ptab memb2tab) wl ->
  mfull2 ymfin (wmap wl) ->
  (forall h, h \in H ->
     exists x, membok par8 par4 x /\ pt flast (memb2tab x) = h) ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
move=> hn hw hf hcov h hh.
have [x [hx hxe]] := hcov h hh.
have := yrow_within_20 hn hw hf hx.
by rewrite /RowRun.wthn (RowInst.posE memb2tab_ok) hxe.
Qed.

(* ---- the same run, with hcoset's cuts and Rokicki's early stop ------------ *)

(* THE THREE THINGS THE FOLDED RUN HAS HAD FROM THE START and this one had    *)
(* not: the two cuts, the stop, and the count that drives them.  RowSrch      *)
(* proves them sound, so all that changes here is which run the map comes     *)
(* from.  Without them the plain row does not finish.                         *)

Definition ymfinsk : PArray.array arr :=
  runsk e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
        (RowInst.cstep fsstep) zstepi
        ytomemb okmv ycsolved RowInst.croot yrooti dsrch ishm
        nlev 0 0%uint63 (mkempty tt) (mkempty tt).

(* The same run over the search that converts nothing.  runsk's own           *)
(* arguments, in the same order.                                              *)
Definition ymfinski : PArray.array arr :=
  runski e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
         (RowInst.cstep fsstep) zstepi
         ytomemb okmv ycsolved RowInst.croot yrooti dsrch ishm
         nlev 0 0%uint63 (mkempty tt) (mkempty tt).

Lemma ymfinsk_sound :
  soundat e8inv e4of par8 par4
          (RowFinal.pos (RowInst.ptab memb2tab)) ymfinsk nlev.
Proof.
rewrite /ymfinsk -{2}[nlev]add0n.
apply: (runsk_sound he8 he4 prep_eq ycoord_root yroot_ball yroot_pok ycoord_step
                    yxstep_pok yxstep_pos yleaf_memb yleaf_pos
                    RowInst.hmv_Sset (RowInst.grpmvP hsrc hhalf)
                    (RowInst.prep_move memb2tab_ok hpg hgr hbt memb2tab_move));
  exact: RowInst.sound_mempty.
Qed.

(* THE TWO RUNS ARE THE SAME RUN.  runski carries the depth left as an int   *)
(* and RowSrchP proves it equal to runsk, so nothing here is proved twice.    *)
Lemma ymfinskiE : (nlev <= 63)%N -> ymfinski = ymfinsk.
Proof.
by move=> hn; rewrite /ymfinski /ymfinsk; apply: runski_eq; rewrite add0n.
Qed.

Lemma ymfinski_sound : (nlev <= 63)%N ->
  soundat e8inv e4of par8 par4
          (RowFinal.pos (RowInst.ptab memb2tab)) ymfinski nlev.
Proof. by move=> hn; rewrite (ymfinskiE hn); exact: ymfinsk_sound. Qed.

Theorem yrowsk_within_20 : nlev = 20%N ->
  witsok e8inv e4of par8 par4 (RowInst.ptab memb2tab) wl ->
  mfull2 ymfinsk (wmap wl) ->
  forall x, membok par8 par4 x ->
  RowRun.wthn (RowFinal.pos (RowInst.ptab memb2tab)) 20 x.
Proof.
move=> hn hw hf x hx.
apply: (row_within_20 he8 he4 (RowInst.ptab_ok memb2tab_ok) _ hw hf hx).
by rewrite -hn; exact: ymfinsk_sound.
Qed.

Theorem ysuperflipsk_row_within_20 : nlev = 20%N ->
  witsok e8inv e4of par8 par4 (RowInst.ptab memb2tab) wl ->
  mfull2 ymfinsk (wmap wl) ->
  (forall h, h \in H ->
     exists x, membok par8 par4 x /\ pt flast (memb2tab x) = h) ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
move=> hn hw hf hcov h hh.
have [x [hx hxe]] := hcov h hh.
have := yrowsk_within_20 hn hw hf hx.
by rewrite /RowRun.wthn (RowInst.posE memb2tab_ok) hxe.
Qed.

(* ---- and the witnesses marked in, instead of a second whole map ---------- *)

(* wmap is a map the size of this one holding thirty two bits, and mfull2     *)
(* reads both at every word.  RowMark says a mark keeps the map sound, so     *)
(* the witnesses go into the map the run leaves and mfull alone is the test.  *)
Definition ycwitsp : rmap := wmarkof wl ymfinsk.

Theorem yrowsk_marked_within_20 : nlev = 20%N ->
  witsok e8inv e4of par8 par4 (RowInst.ptab memb2tab) wl ->
  mfull ycwitsp ->
  forall x, membok par8 par4 x ->
  RowRun.wthn (RowFinal.pos (RowInst.ptab memb2tab)) 20 x.
Proof.
move=> hn hw hf x hx.
apply: (row_within_20_marked he8 he4 (RowInst.ptab_ok memb2tab_ok) _ hw hf hx).
by rewrite -hn; exact: ymfinsk_sound.
Qed.

Theorem ysuperflipsk_marked_within_20 : nlev = 20%N ->
  witsok e8inv e4of par8 par4 (RowInst.ptab memb2tab) wl ->
  mfull ycwitsp ->
  (forall h, h \in H ->
     exists x, membok par8 par4 x /\ pt flast (memb2tab x) = h) ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
move=> hn hw hf hcov h hh.
have [x [hx hxe]] := hcov h hh.
have := yrowsk_marked_within_20 hn hw hf hx.
by rewrite /RowRun.wthn (RowInst.posE memb2tab_ok) hxe.
Qed.

End CubInst.
