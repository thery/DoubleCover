(* =========================================================================  *)
(*  RowMemb.v -- the cube a member names, and the member a cube gives.        *)
(* =========================================================================  *)

(* THIS IS THE ONE PLACE WHERE THREE RANKS MEET FORTY EIGHT FACELETS, and     *)
(* neither half of it is new: the corners are Phase1's -- ctrip is the eight  *)
(* as facelet triples, cpos and cslot say which corner a facelet belongs to   *)
(* and how far round -- and the edges are Coordfs's, eprim and esec, in the   *)
(* order the prototype uses, so the outer eight are the first eight and the   *)
(* middle four the last.                                                      *)
(*                                                                            *)
(* WHAT IS BUILT IS THE INVERSE, because that is the direction that needs no  *)
(* search: at the facelet of slot p, the position's inverse gives the home    *)
(* facelet of whatever cubie sits at p, and the tables say which cubie that   *)
(* is.  The member's own table is that inverted, which Table.inv_tab does.    *)
(*                                                                            *)
(* Nothing here is turned or flipped: a member of H is three permutations and *)
(* nothing else, which is exactly why three ranks are enough.                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the permutation of a rank ------------------------------------------- *)

(* Unranking is a computation and the layout tables are written in terms of   *)
(* it, so the prototype writes it out: eight numbers to a corner rank, four   *)
(* to a middle one.                                                           *)

Definition up8i : arr := Eval vm_compute in
  mkarr 322560%uint63 0%uint63 up8_data.
Definition up4i : arr := Eval vm_compute in
  mkarr 96%uint63 0%uint63 up4_data.

Definition up8 (r : int) (p : nat) : nat :=
  to_nat (PArray.get up8i (Uint63.add (Uint63.mul r 8%uint63) (of_nat p))).

Definition up4 (r : int) (p : nat) : nat :=
  to_nat (PArray.get up4i (Uint63.add (Uint63.mul r 4%uint63) (of_nat p))).

(* ---- what a table is, and what a part of one is -------------------------- *)

(* Read once here because the layout below needs them: a composition read at  *)
(* a facelet, the size of a table, when two are equal, and what it is for a   *)
(* table to be a part -- a permutation that leaves every facelet outside its  *)
(* own set alone and keeps its own.                                           *)

Lemma comp_tabE (s t : seq nat) f : (f < seq.size s)%N ->
  nth 0%N (comp_tab s t) f = nth 0%N t (nth 0%N s f).
Proof. by move=> h; rewrite /comp_tab (nth_map 0%N). Qed.

Lemma tab_ok_size (t : seq nat) : tab_ok flast t -> seq.size t = 48%N.
Proof. by case/and3P => /eqP. Qed.

Lemma tab_eq (s t : seq nat) : tab_ok flast s -> tab_ok flast t ->
  (forall f, (f < 48)%N -> nth 0%N s f = nth 0%N t f) -> s = t.
Proof.
move=> hs ht h; apply: (@eq_from_nth _ 0%N).
  by rewrite (tab_ok_size hs) (tab_ok_size ht).
by move=> i; rewrite (tab_ok_size hs) => hi; apply: h.
Qed.

Definition partok (S : nat -> bool) (t : seq nat) : bool :=
  [&& tab_ok flast t,
      all (fun f => S f || (nth 0%N t f == f)) (iota 0 48) &
      all (fun f => S f ==> S (nth 0%N t f)) (iota 0 48)].

Lemma partok_tab S t : partok S t -> tab_ok flast t.
Proof. by case/and3P. Qed.

(* a table cut down to one set, leaving the rest alone                        *)
Definition restr (S : nat -> bool) (t : seq nat) : seq nat :=
  mkseq (fun f => if S f then nth 0%N t f else f) 48.

(* ---- a layout, and the one thing all three parts are --------------------- *)

(* THE THREE PARTS ARE THE SAME CONSTRUCTION THREE TIMES, and saying so once  *)
(* is what makes the checks small.  A LAYOUT is a set of facelets listed      *)
(* place by place, so many facelets at each place: the corners are eight      *)
(* places of three, the outer eight and the middle four are places of two,    *)
(* the primary facelet and the other one.  A rank names a permutation of the  *)
(* PLACES, and the part it gives moves each facelet to the same slot of the   *)
(* place the permutation names.                                               *)
(*                                                                            *)
(* Everything a walk had to say about the forty eight facelets is then said   *)
(* about eight numbers instead, which is the whole of the saving: a part is a *)
(* permutation exactly when the rank names one, and a move carries a part     *)
(* exactly when it carries the places.                                        *)

Section Lay.

Variable lay : seq nat.          (* the facelets, place by place              *)
Variable nsl npl : nat.          (* facelets at a place, and places           *)
Variable inL : nat -> bool.      (* the set of them, as a table               *)
Variable plc slt : nat -> nat.   (* which place a facelet is at, and its slot *)

(* a place and a slot name an index of the layout                             *)
Lemma lidx p q : (p < npl)%N -> (q < nsl)%N -> (p * nsl + q < npl * nsl)%N.
Proof.
move=> hp hq.
have h0 : (0 < nsl)%N by apply: leq_ltn_trans hq.
have h1 : (p * nsl + q < p.+1 * nsl)%N.
  by rewrite mulSn [(nsl + _)%N]addnC ltn_add2l.
by apply: leq_trans h1 _; rewrite leq_pmul2r.
Qed.

Definition part (u : nat -> nat) : seq nat :=
  mkseq (fun f => if inL f then nth 0%N lay (u (plc f) * nsl + slt f)%N else f)
        48.

(* what a layout owes, and it is a walk over the places and the facelets      *)
Definition layok : bool :=
  [&& (0 < nsl)%N,
      all (fun i => [&& (nth 0%N lay i < 48)%N, inL (nth 0%N lay i),
                        plc (nth 0%N lay i) == i %/ nsl &
                        slt (nth 0%N lay i) == i %% nsl])
          (iota 0 (npl * nsl)),
      all (fun f => inL f ==> (nth 0%N lay (plc f * nsl + slt f)%N == f))
          (iota 0 48) &
      all (fun f => inL f ==> ((plc f < npl)%N && (slt f < nsl)%N))
          (iota 0 48)].

Lemma layP i : layok -> (i < npl * nsl)%N ->
  [&& (nth 0%N lay i < 48)%N, inL (nth 0%N lay i),
      plc (nth 0%N lay i) == i %/ nsl & slt (nth 0%N lay i) == i %% nsl].
Proof. by case/and4P => _ h _ _ hi; apply: all_iota_lt h hi. Qed.

Lemma layK f : layok -> (f < 48)%N -> inL f ->
  nth 0%N lay (plc f * nsl + slt f)%N = f.
Proof.
by case/and4P => _ _ h _ hf hL; move: (all_iota_lt h hf); rewrite hL => /eqP.
Qed.

Lemma lay_rng f : layok -> (f < 48)%N -> inL f ->
  (plc f < npl)%N && (slt f < nsl)%N.
Proof.
by case/and4P => _ _ _ h hf hL; move: (all_iota_lt h hf); rewrite hL.
Qed.

(* an index of the layout is its place and its slot, so the layout is one to  *)
(* one                                                                        *)
Lemma lay_inj i j : layok -> (i < npl * nsl)%N -> (j < npl * nsl)%N ->
  nth 0%N lay i = nth 0%N lay j -> i = j.
Proof.
move=> hok hi hj hE.
have /and4P[_ _ /eqP hpi /eqP hsi] := layP hok hi.
have /and4P[_ _ /eqP hpj /eqP hsj] := layP hok hj.
have h0 : (0 < nsl)%N by case/and4P: hok.
by rewrite (divn_eq i nsl) (divn_eq j nsl) -hpi -hsi -hpj -hsj hE.
Qed.

(* ---- a rank that names a permutation gives a part that is one ------------ *)

Lemma part_partok u : layok ->
  perm_eq [seq u p | p <- iota 0 npl] (iota 0 npl) -> partok inL (part u).
Proof.
move=> hok hu.
have h0 : (0 < nsl)%N by case/and4P: hok.
(* the rank stays inside the places and is one to one on them                 *)
have hult p : (p < npl)%N -> (u p < npl)%N.
  move=> hp; have : u p \in [seq u q | q <- iota 0 npl].
    by apply/mapP; exists p => //; rewrite mem_iota.
  by rewrite (perm_mem hu) mem_iota.
have huinj p q : (p < npl)%N -> (q < npl)%N -> u p = u q -> p = q.
  move=> hp hq hpq.
  have hun : uniq [seq u p | p <- iota 0 npl].
    by rewrite (perm_uniq hu) iota_uniq.
  have hs : seq.size [seq u p | p <- iota 0 npl] = npl.
    by rewrite size_map size_iota.
  have hp' : (p < seq.size [seq u p | p <- iota 0 npl])%N by rewrite hs.
  have hq' : (q < seq.size [seq u p | p <- iota 0 npl])%N by rewrite hs.
  apply/eqP; rewrite -(nth_uniq 0%N hp' hq' hun).
  by rewrite !(nth_map 0%N) ?size_iota // !nth_iota // !add0n hpq.
have hidx f : (f < 48)%N -> inL f -> (u (plc f) * nsl + slt f < npl * nsl)%N.
  move=> hf hL; have /andP[hp hs] := lay_rng hok hf hL.
  by apply: lidx => //; exact: (hult _ hp).
have hval f : (f < 48)%N ->
  nth 0%N (part u) f = if inL f then nth 0%N lay (u (plc f) * nsl + slt f)%N
                       else f.
  by move=> hf; rewrite /part nth_mkseq.
(* one to one on the forty eight, and that is the only hard part              *)
have hinj : {in iota 0 48 &, injective
   (fun f => if inL f then nth 0%N lay (u (plc f) * nsl + slt f)%N else f)}.
  move=> f g; rewrite !mem_iota !add0n => /andP[_ hf] /andP[_ hg] /=.
  case: (boolP (inL f)) => hLf; case: (boolP (inL g)) => hLg.
  - move=> hE; have hij := lay_inj hok (hidx f hf hLf) (hidx g hg hLg) hE.
    have /andP[hpf hsf] := lay_rng hok hf hLf.
    have /andP[hpg hsg] := lay_rng hok hg hLg.
    have hsE : slt f = slt g.
      have h : (u (plc f) * nsl + slt f) %% nsl
             = (u (plc g) * nsl + slt g) %% nsl by rewrite hij.
      by move: h; rewrite !modnMDl !modn_small.
    have hpE : u (plc f) = u (plc g).
      have h : (u (plc f) * nsl + slt f) %/ nsl
             = (u (plc g) * nsl + slt g) %/ nsl by rewrite hij.
      by move: h; rewrite !divnMDl // !divn_small // !addn0.
    rewrite -(layK hok hf hLf) -(layK hok hg hLg) hsE.
    by rewrite (huinj _ _ hpf hpg hpE).
  - move=> hE; move: hLg; suff -> : inL g by [].
    by rewrite -hE; have /and4P[_ -> _ _] := layP hok (hidx f hf hLf).
  - move=> hE; move: hLf; suff -> : inL f by [].
    by rewrite hE; have /and4P[_ -> _ _] := layP hok (hidx g hg hLg).
  by [].
apply/and3P; split; last 1 first.
- apply/allP => f; rewrite mem_iota add0n => /andP[_ hf].
  apply/implyP => hL; rewrite hval // hL.
  by have /and4P[_ -> _ _] := layP hok (hidx f hf hL).
- apply/and3P; split.
  + by rewrite size_mkseq.
  + apply/allP => v /(nthP 0%N)[i]; rewrite size_mkseq => hi <-.
    rewrite hval //; case: (boolP (inL i)) => hL //.
    by have /and4P[-> _ _ _] := layP hok (hidx i hi hL).
  by rewrite /part /mkseq map_inj_in_uniq // iota_uniq.
apply/allP => f; rewrite mem_iota add0n => /andP[_ hf].
by rewrite hval //; case: (boolP (inL f)) => hL //=; rewrite eqxx orbT.
Qed.

(* ---- and a move that carries the places carries the part ----------------- *)

(* The place a move sends a place to, read off the layout at the first slot.  *)
Definition lperm (t : seq nat) : seq nat :=
  [seq plc (nth 0%N t (nth 0%N lay (p * nsl)%N)) | p <- iota 0 npl].

(* and the walk that says the move really does act that way, the same at      *)
(* every slot: for the corners that is a move of H not twisting a corner, and *)
(* it is twenty four tests a move                                             *)
Definition lslot (t : seq nat) : bool :=
  all (fun i => nth 0%N t (nth 0%N lay i)
                == nth 0%N lay
                     (nth 0%N (lperm t) (i %/ nsl) * nsl + i %% nsl)%N)
      (iota 0 (npl * nsl)).

Lemma part_move u v t : layok -> lslot t ->
  all (fun p => v p == u (nth 0%N (lperm t) p)) (iota 0 npl) ->
  all (fun p => (u p < npl)%N) (iota 0 npl) ->
  all (fun p => (nth 0%N (lperm t) p < npl)%N) (iota 0 npl) ->
  part v = comp_tab (restr inL t) (part u).
Proof.
move=> hok hsl hvu hun hln.
have h0 : (0 < nsl)%N by case/and4P: hok.
apply: (@eq_from_nth _ 0%N).
  by rewrite /part /comp_tab !size_map !size_iota.
move=> f; rewrite size_mkseq => hf.
have hsz : seq.size (restr inL t) = 48%N by rewrite /restr size_mkseq.
have hr : nth 0%N (restr inL t) f = if inL f then nth 0%N t f else f.
  by rewrite /restr nth_mkseq.
have hpv : nth 0%N (part v) f
         = if inL f then nth 0%N lay (v (plc f) * nsl + slt f)%N else f.
  by rewrite /part nth_mkseq.
rewrite comp_tabE ?hsz // hr hpv.
case: (boolP (inL f)) => hL; last by rewrite /part nth_mkseq // (negbTE hL).
have /andP[hpf hsf] := lay_rng hok hf hL.
(* where the move takes this facelet: the same slot of the place lperm names  *)
have hE : nth 0%N t f
        = nth 0%N lay (nth 0%N (lperm t) (plc f) * nsl + slt f)%N.
  have := all_iota_lt hsl (lidx hpf hsf).
  rewrite (layK hok hf hL) divnMDl // divn_small // addn0 modnMDl modn_small //.
  by move=> /eqP.
have hlt : (nth 0%N (lperm t) (plc f) < npl)%N by apply: all_iota_lt hln hpf.
have hj := lidx hlt hsf.
have /and4P[hj48 hjL /eqP hjp /eqP hjs] := layP hok hj.
rewrite hE /part nth_mkseq // hjL hjp hjs divnMDl // divn_small // addn0.
rewrite modnMDl modn_small //.
by have := all_iota_lt hvu hpf => /eqP ->.
Qed.

End Lay.

(* ---- the cube a member names --------------------------------------------- *)

(* THE THREE ACT ON DISJOINT FACELETS, so the cube a member names is their    *)
(* composition, and each depends on ONE rank: the corners on the corner rank, *)
(* the outer eight on the outer rank, the middle four on the middle one.      *)
(* That is what makes every one of them a walk Rocq can check -- 40320, 40320 *)
(* and 24 -- where the three together are nineteen billion.                   *)
(*                                                                            *)
(* Each is the identity away from its own facelets, which is what lets them   *)
(* be composed at all.                                                        *)

(* THE TWO SIDES NUMBER THE CORNERS DIFFERENTLY, and nothing else does.  The  *)
(* prototype takes them URF UFL ULB UBR DFR DLF DBL DRB; cflat takes them in  *)
(* the order its facelets come, which reads ULB UBR UFL URF DLF DFR DBL DRB.  *)
(* A rank the prototype wrote names a permutation of ITS eight, so it has to  *)
(* be read in its order.  The edges need nothing of the kind: eprim and esec  *)
(* are already UR UF UL UB DR DF DL DB FR FL BL BR.                           *)
(*                                                                            *)
(* This is the prototype's order written in our own numbers, and it is not a  *)
(* choice: cordok below turns each face and reads the corner every place      *)
(* receives, and only this order gives the prototype's own numbers.           *)
Definition cordn : seq nat := [:: 3; 2; 0; 1; 5; 4; 6; 7]%N.

(* the twenty four facelets again, the corners in the prototype's order       *)
Definition cflatp : seq nat :=
  flatten [seq [seq nth 0%N cflat (3 * c + j)%N | j <- iota 0 3]
          | c <- cordn].

(* the primary facelet of each place, in the same order                       *)
Definition cprimp : seq nat := [seq nth 0%N cflatp (3 * p)%N | p <- iota 0 8].

(* ---- the facelet is looked up, not searched for -------------------------- *)

(* EVERY ONE OF THESE IS A FUNCTION OF THE FACELET ALONE, and every one of    *)
(* them used to be a scan: which place a facelet belongs to, how far round    *)
(* it sits, and whether it is a corner, an outer edge or a middle one.  A     *)
(* part asks all of them at each of forty eight facelets and a walk builds a  *)
(* part at each of forty thousand ranks, so the scans were the whole cost --  *)
(* measured, the membership alone was seven eighths of it.  Read once into    *)
(* tables of forty eight, they are a lookup.                                  *)

Definition eouts : seq nat := take 8 eprim ++ take 8 esec.
Definition emids : seq nat := drop 8 eprim ++ drop 8 esec.

Definition cposv : seq nat := Eval vm_compute in
  [seq (index f cflatp) %/ 3 | f <- iota 0 48].
Definition cslotv : seq nat := Eval vm_compute in
  [seq (index f cflatp) %% 3 | f <- iota 0 48].
Definition eposv : seq nat := Eval vm_compute in
  [seq (index f (eprim ++ esec)) %% nedge | f <- iota 0 48].

Definition inCv : seq bool := Eval vm_compute in
  [seq f \in cflatp | f <- iota 0 48].
Definition inUv : seq bool := Eval vm_compute in
  [seq f \in eouts | f <- iota 0 48].
Definition inMv : seq bool := Eval vm_compute in
  [seq f \in emids | f <- iota 0 48].
Definition inPv : seq bool := Eval vm_compute in
  [seq f \in eprim | f <- iota 0 48].
Definition inSv : seq bool := Eval vm_compute in
  [seq f \in esec | f <- iota 0 48].

Definition inC (f : nat) : bool := nth false inCv f.
Definition inU (f : nat) : bool := nth false inUv f.
Definition inM (f : nat) : bool := nth false inMv f.
Definition inP (f : nat) : bool := nth false inPv f.
Definition inS (f : nat) : bool := nth false inSv f.

(* CPOS AND EPOS AT THE NAT LEVEL, and this is not a nicety: inord does not   *)
(* reduce, so cposn f under a vm_compute does not come back.  Coordfs         *)
(* says the same thing about its own twelve -- every fact there is pushed to  *)
(* nat for exactly this reason.  These are the same functions with the        *)
(* ordinal taken out, and now read off a table.                               *)
Definition cposn (f : nat) : nat := nth 0%N cposv f.
Definition cslotn (f : nat) : nat := nth 0%N cslotv f.
Definition eposn (f : nat) : nat := nth 0%N eposv f.

(* AND THE ORDER IS CHECKED, not asserted.  These are the prototype's own six *)
(* cp arrays, copied out of rubik_row.ml's `basic'.  Turn a face, ask which   *)
(* corner each place receives, and the eight numbers have to be its.  The six *)
(* turns move the corners every way there is, so nothing but the right order  *)
(* passes.                                                                    *)
Definition cparr : seq (seq nat) :=
  [:: [:: 3; 0; 1; 2; 4; 5; 6; 7]; [:: 4; 1; 2; 0; 7; 5; 6; 3];
      [:: 1; 5; 2; 3; 0; 4; 6; 7]; [:: 0; 1; 2; 3; 5; 6; 7; 4];
      [:: 0; 2; 6; 3; 4; 1; 5; 7]; [:: 0; 1; 3; 7; 4; 5; 2; 6]]%N.

Definition cordok : bool :=
  all (fun k => [seq cposn (nth 0%N (inv_tab flast (nth [::] mtabs (3 * k)%N))
                                    (nth 0%N cprimp p)) | p <- iota 0 8]
                == nth [::] cparr k) (iota 0 6).

Lemma cordokC : cordok.
Proof. by vm_compute. Qed.

(* The three layouts.  The corners are eight places of three facelets, in the *)
(* prototype's order; the outer eight and the middle four are places of two,  *)
(* the primary facelet and the other one.                                     *)

Definition ulay : seq nat :=
  flatten [seq [:: nth 0%N eprim p; nth 0%N esec p] | p <- iota 0 8].

Definition mlay : seq nat :=
  flatten [seq [:: nth 0%N eprim (8 + p)%N; nth 0%N esec (8 + p)%N]
          | p <- iota 0 4].

(* an edge facelet is at slot nought if it is the primary one                 *)
Definition eslt (f : nat) : nat := if inP f then 0%N else 1%N.

(* and a middle edge is at place eight and up                                 *)
Definition mplc (f : nat) : nat := (eposn f - 8)%N.

Definition cpart (r : int) : seq nat := part cflatp 3 inC cposn cslotn (up8 r).
Definition upart (r : int) : seq nat := part ulay 2 inU eposn eslt (up8 r).
Definition mpart (r : int) : seq nat := part mlay 2 inM mplc eslt (up4 r).

(* ---- and the three layouts are layouts, which is one walk over each ------ *)

Definition clayok : bool := layok cflatp 3 8 inC cposn cslotn.
Definition ulayok : bool := layok ulay 2 8 inU eposn eslt.
Definition mlayok : bool := layok mlay 2 4 inM mplc eslt.

Lemma clayokC : clayok.  Proof. by vm_compute. Qed.
Lemma ulayokC : ulayok.  Proof. by vm_compute. Qed.
Lemma mlayokC : mlayok.  Proof. by vm_compute. Qed.

(* A MEMBER OUT OF RANGE NAMES THE SOLVED CUBE.  What is wanted above is      *)
(* that every member names a permutation with no premise attached, and a rank *)
(* past the end of a table reads nought and names nothing.  The guard costs   *)
(* one test and everything that cares carries the range anyway.               *)
Definition membrng (x : memb) : bool :=
  [&& (mcp x <? npagei)%uint63, (mud x <? npagei)%uint63 &
      (mmp x <? nbiti)%uint63].

(* the inverse: at the facelet of a place, the home facelet of what sits      *)
(* there                                                                      *)
Definition membinv (x : memb) : seq nat :=
  if ~~ membrng x then id_tab flast
  else comp_tab (comp_tab (cpart (mcp x)) (upart (mud x))) (mpart (mmp x)).

Definition memb2tab (x : memb) : seq nat := inv_tab flast (membinv x).

(* ---- and the member a cube gives ----------------------------------------- *)

(* The three ranks read off a position, which is what the search does at a    *)
(* leaf.  It is only meant for a position of H: outside it the edges are      *)
(* mixed between the outer eight and the middle four and there is no outer    *)
(* permutation to rank.                                                       *)
(* the rank of a permutation, the prototype's own: fold over the places, and  *)
(* at each one count how many later places hold something smaller.  It is a   *)
(* computation over eight numbers, so no table is wanted.                     *)
Definition lrank (n : nat) (f : nat -> nat) : nat :=
  foldl (fun r i =>
           (r * (n - i)
            + count (fun j => (f j < f i)%N) (iota i.+1 (n - i.+1)))%N)
        0%N (iota 0 n).

Definition rank8 (f : nat -> nat) : int := of_nat (lrank 8 f).
Definition rank4 (f : nat -> nat) : int := of_nat (lrank 4 f).

(* The search calls this at every leaf, so it reads the INVERSE TABLE and     *)
(* never builds a permutation: Tabi.inv_tabi is the same inverse csrc takes   *)
(* of the position, and at the primary facelet of a place it gives the home   *)
(* facelet of whatever sits there.                                            *)
Definition tomemb (a : arr) : memb :=
  let u := ti2t flast (inv_tabi flast a) in
  (rank8 (fun p => cposn (nth 0%N u (nth 0%N cprimp p))),
   rank8 (fun p => eposn (nth 0%N u (nth 0%N eprim p))),
   rank4 (fun p => (eposn (nth 0%N u (nth 0%N eprim (8 + p))) - 8)%N)).

(* ---- what the unrank tables have to be ----------------------------------- *)

(* A row of up8 is a permutation of the eight, and a row of up4 of the four.  *)
(* That is a walk over 40320 rows and 24, and it is all the tables are asked  *)
(* for -- nothing here cares WHICH permutation a rank names, only that the    *)
(* naming is one to one.                                                      *)

Definition up8ok1 (r : int) : bool :=
  perm_eq [seq up8 r p | p <- iota 0 8] (iota 0 8).
Definition up8ok : bool := iter npagen 0%uint63 up8ok1.

Definition up4ok1 (r : int) : bool :=
  perm_eq [seq up4 r p | p <- iota 0 4] (iota 0 4).
Definition up4ok : bool := iter nbitn 0%uint63 up4ok1.

(* ---- what the three parts owe, and it is three walks --------------------- *)

(* Each part is a permutation of the forty eight facelets.  Over the ranks    *)
(* that is 40320, 40320 and 24 tests, and it is the whole of what the unrank  *)
(* tables are asked for -- nothing cares WHICH permutation a rank names, only *)
(* that each names one.                                                       *)


(* ---- disjoint tables commute --------------------------------------------- *)

(* The three parts of a member act on disjoint facelets, and so do the three  *)
(* halves of a move of H.  That is what lets the composition be rearranged,   *)
(* and it is the one structural fact the prepass proof needs.                 *)

Lemma comp_disj (S T : nat -> bool) (s t : seq nat) :
  tab_ok flast s -> tab_ok flast t ->
  all (fun f => S f || (nth 0%N s f == f)) (iota 0 48) ->
  all (fun f => T f || (nth 0%N t f == f)) (iota 0 48) ->
  all (fun f => S f ==> S (nth 0%N s f)) (iota 0 48) ->
  all (fun f => T f ==> T (nth 0%N t f)) (iota 0 48) ->
  all (fun f => ~~ (S f && T f)) (iota 0 48) ->
  comp_tab s t = comp_tab t s.
Proof.
move=> hs ht hsid htid hss htt hd.
have hsl f : (f < 48)%N -> (nth 0%N s f < 48)%N.
  by move=> hf; move: (hs) => /and3P[_ /allP hh _]; apply: hh; apply: mem_nth;
     rewrite (tab_ok_size hs).
apply: tab_eq; try by apply: tab_ok_comp.
move=> f hf.
rewrite comp_tabE ?(tab_ok_size hs) // comp_tabE ?(tab_ok_size ht) //.
have hfS := all_iota_lt hsid hf.
have hfT := all_iota_lt htid hf.
have hfD := all_iota_lt hd hf.
case: (boolP (S f)) => hS.
  have hsS : S (nth 0%N s f) by move: (all_iota_lt hss hf); rewrite hS.
  have -> : nth 0%N t (nth 0%N s f) = nth 0%N s f.
    move: (all_iota_lt htid (hsl f hf)).
    by move: (all_iota_lt hd (hsl f hf)); rewrite hsS /= => /negbTE -> /= /eqP.
  by move: hfT; move: hfD; rewrite hS /= => /negbTE -> /= /eqP ->.
have hsf : nth 0%N s f = f by move: hfS; rewrite (negbTE hS) /= => /eqP.
rewrite hsf.
have htl f' : (f' < 48)%N -> (nth 0%N t f' < 48)%N.
  by move=> hf'; move: (ht) => /and3P[_ /allP hh _]; apply: hh; apply: mem_nth;
     rewrite (tab_ok_size ht).
case: (boolP (T f)) => hT.
  have htT : T (nth 0%N t f) by move: (all_iota_lt htt hf); rewrite hT.
  move: (all_iota_lt hsid (htl f hf)).
  by move: (all_iota_lt hd (htl f hf)); rewrite htT andbT => /negbTE -> /= /eqP.
by move: hfT; rewrite (negbTE hT) /= => /eqP ht2; rewrite ht2 hsf.
Qed.


(* ---- the three halves of a move of H --------------------------------------*)

(* A move of H sends corner facelets to corner facelets, outer edges to outer *)
(* edges and middle to middle -- that is what being in H MEANS -- so it is    *)
(* the composition of its three halves, and they are disjoint.  restr cuts a  *)
(* table down to one set and leaves the rest alone.                           *)

(* the move a place is carried by, undone: membinv is the inverse of the      *)
(* member, so what acts on it is the move the other way round                 *)
Definition hinv (k : int) : seq nat := inv_tab flast (mvt (hmvi k)).

Definition hcT (k : int) : seq nat := restr inC (hinv k).
Definition huT (k : int) : seq nat := restr inU (hinv k).
Definition hmT (k : int) : seq nat := restr inM (hinv k).

(* ---- and a move is eight numbers, not forty eight ------------------------ *)

(* A move of H carries a place to a place and leaves the slot alone: it never *)
(* twists a corner and never flips an edge, which is what being in H MEANS.   *)
(* So each half of it is named by a permutation of the places, read off the   *)
(* layout at the first slot, and everything the walks used to say about the   *)
(* forty eight facelets is said about eight numbers instead.                  *)
Definition chp (k : int) : seq nat := lperm cflatp 3 8 cposn (hinv k).
Definition uhp (k : int) : seq nat := lperm ulay 2 8 eposn (hinv k).
Definition mhp (k : int) : seq nat := lperm mlay 2 4 mplc (hinv k).

(* that it really does act that way, and that it stays inside the places:     *)
(* twenty four tests a move for the corners, sixteen and eight for the edges  *)
Definition hlayok : bool :=
  iter nhn 0%uint63 (fun k =>
    [&& lslot cflatp 3 8 cposn (hinv k),
        lslot ulay 2 8 eposn (hinv k),
        lslot mlay 2 4 mplc (hinv k) &
        [&& all (fun p => (nth 0%N (chp k) p < 8)%N) (iota 0 8),
            all (fun p => (nth 0%N (uhp k) p < 8)%N) (iota 0 8) &
            all (fun p => (nth 0%N (mhp k) p < 4)%N) (iota 0 4)]]).

Lemma hlayokC : hlayok.  Proof. by vm_compute. Qed.

(* ---- what any part of a member or of a move owes -------------------------*)

(* Three things, and each is settled facelet by facelet: the part is a        *)
(* permutation of the forty eight, it leaves every facelet outside its own    *)
(* alone, and it keeps its own.  The last two are what let the three parts of *)
(* a member be shuffled past the three halves of a move, which is the whole   *)
(* of the prepass proof.                                                      *)
Definition dsj (S T : nat -> bool) : bool :=
  all (fun f => ~~ (S f && T f)) (iota 0 48).

(* the three sets of a member are disjoint, and that is a walk over forty     *)
(* eight facelets with no table in it                                         *)
Lemma dsj_cu : dsj inC inU.  Proof. by vm_compute. Qed.
Lemma dsj_cm : dsj inC inM.  Proof. by vm_compute. Qed.
Lemma dsj_um : dsj inU inM.    Proof. by vm_compute. Qed.

(* and then two parts of disjoint facelets commute, as tables and as          *)
(* permutations.  The permutation form is the one the assembly uses, because  *)
(* multiplication in a group is associative and comp_tab is not.              *)
Lemma partok_comm S T s t : partok S s -> partok T t -> dsj S T ->
  comp_tab s t = comp_tab t s.
Proof.
case/and3P => hs h1 h2; case/and3P => ht h3 h4 hd.
exact: (comp_disj hs ht h1 h3 h2 h4 hd).
Qed.

Lemma pt_comm S T s t : partok S s -> partok T t -> dsj S T ->
  pt flast s * pt flast t = pt flast t * pt flast s.
Proof.
move=> hs ht hd.
by rewrite !ptM ?(partok_tab hs) ?(partok_tab ht) // (partok_comm hs ht hd).
Qed.

(* AND THIS IS THE WHOLE OF THE PREPASS PROOF, with the cube taken out of it. *)
(* Six things in a row, three of them going past three; the three crossings   *)
(* are the three disjointness facts and nothing else is used.                 *)
Lemma six_shuffle (gT : finGroupType) (a b c x y z : gT) :
  x * b = b * x -> x * c = c * x -> y * c = c * y ->
  a * x * (b * y) * (c * z) = a * b * c * (x * y * z).
Proof.
move=> h1 h2 h3.
rewrite -!mulgA; congr (_ * _).
rewrite mulgA h1 -mulgA; congr (_ * _).
by rewrite [y * (c * z)]mulgA h3 -mulgA mulgA h2 -mulgA.
Qed.

(* ---- what the three tables owe, part by part ------------------------------*)

(* Each is a walk, and that is the whole point of splitting the member into   *)
(* three: the corners against the page table, the outer eight against the     *)
(* group table, the middle four against btmv.  Over the places together they  *)
(* would be nineteen billion; apart they are 403 200, 403 200 and 240.        *)

Section Move.

Variable mpg mgr btmvt e8invt e4oft par8t par4t : arr.

(* the corner half: the page table is the corner permutation moved, and that  *)
(* is eight numbers at each page rather than a table of forty eight           *)
(* THE PLACE PERMUTATION IS READ ONCE.  It does not depend on the page, but  *)
(* nothing hoists it out of the loop, and rebuilding it means rebuilding the  *)
(* move undone -- an inv_tab, measured at 1.2 ms.  Forty thousand pages by    *)
(* ten moves of that is eight minutes; with the let it is nothing.            *)
Definition cmvok1 (k : int) : bool :=
  let c := chp k in
  iter npagen 0%uint63 (fun pg =>
    all (fun p => up8 (pgmv mpg k pg) p == up8 pg (nth 0%N c p))
        (iota 0 8)).
Definition cmvok : bool := iter nhn 0%uint63 cmvok1.

(* the middle half: btmv is the middle permutation moved                      *)
(* mpart takes the middle RANK, which is what e4of reads off a bit, so the    *)
(* check has to go through it or it is checking the wrong thing.              *)
Definition mmvok1 (k : int) : bool :=
  let m := mhp k in
  iter nbitn 0%uint63 (fun bt =>
    all (fun p => up4 (PArray.get e4oft (btmv btmvt k bt)) p
                  == up4 (PArray.get e4oft bt) (nth 0%N m p))
        (iota 0 4)).
Definition mmvok : bool := iter nhn 0%uint63 mmvok1.

(* ---- and the parity, which is not carried across ------------------------- *)

(* WHICH OF A PAIR A PLACE MEANS IS SETTLED BY A PARITY, and a move CHANGES   *)
(* that parity.  Eight of the ten do: U, U' and R2 are all odd on the outer   *)
(* eight, and only U2 and D2 are not.  So the moved place does not take the   *)
(* same half of its pair, and a check that used the same one on both sides    *)
(* would simply be false.                                                     *)
(*                                                                            *)
(* What IS fixed is how much the parity moves.  A move changes the corner     *)
(* parity by the same amount at every page and the middle parity by the same  *)
(* amount at every bit, so reading the two at nought gives the whole story    *)
(* and parok is the walk that says so: ten by 40320 and ten by 24.            *)
Definition dcpar (k : int) : int :=
  Uint63.lxor (PArray.get par8t (pgmv mpg k 0%uint63))
              (PArray.get par8t 0%uint63).

Definition dmpar (k : int) : int :=
  Uint63.lxor (PArray.get par4t (PArray.get e4oft (btmv btmvt k 0%uint63)))
              (PArray.get par4t (PArray.get e4oft 0%uint63)).

(* and the outer parity moves by the two together, because a member's three   *)
(* parities always agree                                                      *)
Definition hpar (k : int) : int := Uint63.lxor (dcpar k) (dmpar k).

Definition parok1 (k : int) : bool :=
  let dc := dcpar k in
  let dm := dmpar k in
  iter npagen 0%uint63 (fun pg =>
    (PArray.get par8t (pgmv mpg k pg) =?
     Uint63.lxor (PArray.get par8t pg) dc)%uint63)
  &&
  iter nbitn 0%uint63 (fun bt =>
    (PArray.get par4t (PArray.get e4oft (btmv btmvt k bt)) =?
     Uint63.lxor (PArray.get par4t (PArray.get e4oft bt)) dm)%uint63).
Definition parok : bool := iter nhn 0%uint63 parok1.

(* ---- the outer half ------------------------------------------------------ *)

(* A group is a PAIR of outer permutations and the last place of the number   *)
(* says which.  The move carries the pair across whole -- that is what mgr    *)
(* is -- and moves the parity by hpar, so the check runs over the group and   *)
(* the parity, 20160 by two by ten.                                           *)
Definition umvok1 (k : int) : bool :=
  let u := uhp k in
  let h := hpar k in
  iter ngroupn 0%uint63 (fun gr =>
    iter 2 0%uint63 (fun p =>
      all (fun q =>
        up8 (PArray.get e8invt
               (Uint63.add (Uint63.mul (grmv mgr k gr) 2%uint63)
                           (Uint63.lxor p h))) q
        == up8 (PArray.get e8invt (Uint63.add (Uint63.mul gr 2%uint63) p))
               (nth 0%N u q))
        (iota 0 8))).
Definition umvok : bool := iter nhn 0%uint63 umvok1.

(* ---- and the move itself is its three halves ------------------------------*)

(* Ten tables, ten checks: undoing a move of H is its corner half, its outer  *)
(* half and its middle half, composed, and each half is a part of its own set *)
(* of facelets.  It is what being in H means, written down.                   *)
Definition hmvok : bool :=
  iter nhn 0%uint63 (fun k =>
    [&& partok inC (hcT k), partok inU (huT k), partok inM (hmT k) &
        hinv k == comp_tab (comp_tab (hcT k) (huT k)) (hmT k)]).

End Move.

Section Parts.

(* A PART IS A PERMUTATION EXACTLY WHEN THE RANK NAMES ONE, so what was a     *)
(* walk over the forty eight facelets at each of forty thousand ranks is a    *)
(* walk over eight numbers -- and up8ok was already here, unused.             *)
Definition cpartok : bool := clayok && up8ok.
Definition upartok : bool := ulayok && up8ok.
Definition mpartok : bool := mlayok && up4ok.

(* a rank that names a permutation of the places stays inside them            *)
Lemma up8_rng r : up8ok1 r -> all (fun p => (up8 r p < 8)%N) (iota 0 8).
Proof.
move=> h; apply/allP => p; rewrite mem_iota add0n => /andP[_ hp].
have : up8 r p \in [seq up8 r q | q <- iota 0 8].
  by apply/mapP; exists p => //; rewrite mem_iota.
by rewrite (perm_mem h) mem_iota.
Qed.

Lemma up4_rng r : up4ok1 r -> all (fun p => (up4 r p < 4)%N) (iota 0 4).
Proof.
move=> h; apply/allP => p; rewrite mem_iota add0n => /andP[_ hp].
have : up4 r p \in [seq up4 r q | q <- iota 0 4].
  by apply/mapP; exists p => //; rewrite mem_iota.
by rewrite (perm_mem h) mem_iota.
Qed.

Lemma cpartokP r : cpartok -> (r <? npagei)%uint63 -> partok inC (cpart r).
Proof.
(* NOT `part_partok => //': what done would evaluate is the layout walk, and  *)
(* that measured 172 seconds.  The layout is handed over, not looked for.     *)
case/andP => hl hu hr.
exact: (part_partok hl (iter_at hu (ltn_npagei hr))).
Qed.

Lemma upartokP r : upartok -> (r <? npagei)%uint63 -> partok inU (upart r).
Proof.
(* NOT `part_partok => //': what done would evaluate is the layout walk, and  *)
(* that measured 172 seconds.  The layout is handed over, not looked for.     *)
case/andP => hl hu hr.
exact: (part_partok hl (iter_at hu (ltn_npagei hr))).
Qed.

Lemma mpartokP r : mpartok -> (r <? nbiti)%uint63 -> partok inM (mpart r).
Proof.
(* NOT `part_partok => //': what done would evaluate is the layout walk, and  *)
(* that measured 172 seconds.  The layout is handed over, not looked for.     *)
case/andP => hl hu hr.
exact: (part_partok hl (iter_at hu (ltn_nbiti hr))).
Qed.

Hypothesis hcp : cpartok.
Hypothesis hup : upartok.
Hypothesis hmp : mpartok.

(* and then a member names a permutation, with no premise at all              *)
Lemma membinv_ok x : tab_ok flast (membinv x).
Proof.
rewrite /membinv; case: ifPn => [_|]; first exact: tab_ok_id.
rewrite negbK => /and3P[hc hu hm].
apply: tab_ok_comp; last by apply: partok_tab (mpartokP hmp hm).
apply: tab_ok_comp; first by apply: partok_tab (cpartokP hcp hc).
by apply: partok_tab (upartokP hup hu).
Qed.

Lemma memb2tab_ok x : tab_ok flast (memb2tab x).
Proof. by apply: tab_ok_inv; apply: membinv_ok. Qed.

End Parts.

(* ---- the prepass moves a member ------------------------------------------ *)

(* AND THIS IS THE BRIDGE: moving the place moves the member by that move of  *)
(* H.  Nothing here is a new fact about the cube -- the four walks above are  *)
(* the facts -- and all that is left is to shuffle six tables into a          *)
(* different order.  The shuffling is done on PERMUTATIONS rather than on     *)
(* tables, because a group is associative and comp_tab is not.                *)

Section Prep.

Variable mpg mgr btmvt : arr.
Variable e8numt e8invt e4bitt e4oft par8t par4t : arr.

Hypothesis he8 : e8ok e8numt e8invt par8t.
Hypothesis he4 : e4ok e4bitt e4oft par4t.
Hypothesis hpgo : pgok mpg.
Hypothesis hgro : grok mgr.
Hypothesis hbto : btok btmvt.
Hypothesis hcp : cpartok.
Hypothesis hup : upartok.
Hypothesis hmp : mpartok.
Hypothesis hcmv : cmvok mpg.
Hypothesis hmmv : mmvok btmvt e4oft.
Hypothesis humv : umvok mpg mgr btmvt e8invt e4oft par8t par4t.
Hypothesis hmvo : hmvok.
Hypothesis hprk : parok mpg btmvt e4oft par8t par4t.

Local Notation unpl := (unplace e8invt e4oft par8t par4t).
Local Notation prty pg bt :=
  (Uint63.lxor (PArray.get par8t pg) (PArray.get par4t (PArray.get e4oft bt))).

(* the three ranks a place names, read straight off unplace                   *)
Lemma unplE pg gr bt :
  unpl pg gr bt =
  (pg, PArray.get e8invt (Uint63.add (Uint63.mul gr 2%uint63) (prty pg bt)),
   PArray.get e4oft bt).
Proof. by []. Qed.

(* a place in range names a member whose three ranks are in range             *)
Lemma membrng_unpl pg gr bt : inrange pg gr bt -> membrng (unpl pg gr bt).
Proof.
(* NOT apply/and3P: what done would evaluate here is the layout tables.       *)
move=> hr; have [/and4P[h1 h2 h3 _] _] := place_unplace he8 he4 hr.
by rewrite /membrng h1 h2 h3.
Qed.

(* a parity is nought or one, whichever table it came from                    *)
Lemma prty_lt2 pg bt : (pg <? npagei)%uint63 -> (bt <? nbiti)%uint63 ->
  (to_nat (prty pg bt) < 2)%N.
Proof.
move=> hp hb; apply: lxor_lt2; first by apply: (par8_lt2 he8).
by apply: (par4_lt2 he4); case/and5P: (e4at he4 hb).
Qed.

(* HOW FAR THE PARITY MOVES, and it is the same everywhere.  parok says the   *)
(* corner parity and the middle parity each shift by a fixed amount, so their *)
(* exclusive or -- which is the outer parity -- shifts by hpar.               *)
Lemma prty_move k pg bt : (to_nat k < nhn)%N ->
  (pg <? npagei)%uint63 -> (bt <? nbiti)%uint63 ->
  prty (pgmv mpg k pg) (btmv btmvt k bt)
  = Uint63.lxor (prty pg bt) (hpar mpg btmvt e4oft par8t par4t k).
Proof.
move=> kL hp hb; have /andP[hc hm] := iter_at hprk kL.
rewrite (eqP (iter_at hc (ltn_npagei hp))) (eqP (iter_at hm (ltn_nbiti hb))).
rewrite /hpar.
have z8 : (to_nat 0%uint63 < npagen)%N by apply: ltn_npagei.
have z4 : (to_nat 0%uint63 < nbitn)%N by apply: ltn_nbiti.
have h1 : (to_nat (PArray.get par8t pg) < 2)%N by apply: (par8_lt2 he8).
have h2 : (to_nat (PArray.get par4t (PArray.get e4oft bt)) < 2)%N.
  by apply: (par4_lt2 he4); case/and5P: (e4at he4 hb).
have hz8 : (0%uint63 <? npagei)%uint63 by [].
have hz4 : (0%uint63 <? nbiti)%uint63 by [].
have h3 : (to_nat (dcpar mpg par8t k) < 2)%N.
  apply: lxor_lt2; apply: (par8_lt2 he8); last by [].
  by apply: (iter_at (iter_at hpgo kL) z8).
have h4 : (to_nat (dmpar btmvt e4oft par4t k) < 2)%N.
  apply: lxor_lt2; apply: (par4_lt2 he4).
  - by case/and5P: (e4at he4 (iter_at (iter_at hbto kL) z4)).
  by case/and5P: (e4at he4 hz4).
by case: (int_lt2 h1) => ->; case: (int_lt2 h2) => ->;
   case: (int_lt2 h3) => ->; case: (int_lt2 h4) => ->; vm_compute.
Qed.

(* ---- the six tables, and the three that have to move past three ---------- *)

Lemma hcT_ok k : (to_nat k < nhn)%N -> partok inC (hcT k).
Proof. by move=> kL; case/and4P: (iter_at hmvo kL). Qed.

Lemma huT_ok k : (to_nat k < nhn)%N -> partok inU (huT k).
Proof. by move=> kL; case/and4P: (iter_at hmvo kL). Qed.

Lemma hmT_ok k : (to_nat k < nhn)%N -> partok inM (hmT k).
Proof. by move=> kL; case/and4P: (iter_at hmvo kL). Qed.

Lemma hinvE k : (to_nat k < nhn)%N ->
  hinv k = comp_tab (comp_tab (hcT k) (huT k)) (hmT k).
Proof. by move=> kL; case/and4P: (iter_at hmvo kL) => _ _ _ /eqP. Qed.

Lemma cpart_ok r : (r <? npagei)%uint63 -> partok inC (cpart r).
Proof. exact: cpartokP hcp. Qed.

Lemma upart_ok r : (r <? npagei)%uint63 -> partok inU (upart r).
Proof. exact: upartokP hup. Qed.

Lemma mpart_ok r : (r <? nbiti)%uint63 -> partok inM (mpart r).
Proof. exact: mpartokP hmp. Qed.

(* the member a place names, as a permutation of the forty eight              *)
Lemma pt_membinv pg gr bt : inrange pg gr bt ->
  pt flast (membinv (unpl pg gr bt))
  = pt flast (cpart (mcp (unpl pg gr bt))) *
    pt flast (upart (mud (unpl pg gr bt))) *
    pt flast (mpart (mmp (unpl pg gr bt))).
Proof.
(* NO /= ANYWHERE HERE.  cpart is an mkseq, so a simpl unfolds it into a      *)
(* forty eight place list and the shape the rewrites look for is gone.        *)
move=> hr; have hb := membrng_unpl hr.
have [/and4P[h1 h2 h3 _] _] := place_unplace he8 he4 hr.
have hC := partok_tab (cpart_ok h1).
have hU := partok_tab (upart_ok h2).
have hM := partok_tab (mpart_ok h3).
rewrite /membinv; case: ifPn => [hn|_]; first by rewrite hb in hn.
by rewrite -(ptM (tab_ok_comp hC hU) hM) -(ptM hC hU).
Qed.

(* ---- and the move, part by part ------------------------------------------ *)

Lemma pt_membinv_move k pg gr bt : (to_nat k < nhn)%N -> inrange pg gr bt ->
  pt flast (membinv (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)))
  = pt flast (hinv k) * pt flast (membinv (unpl pg gr bt)).
Proof.
move=> kL hr; have hr' := prep_range hpgo hgro hbto kL hr.
have /and3P[hp hg hb] := hr.
have /and3P[hp' hg' hb'] := hr'.
rewrite (pt_membinv hr) (pt_membinv hr') !unplE /mcp /mud /mmp.
have [/and4P[_ o2 o3 _] _] := place_unplace he8 he4 hr.
have q2 : (PArray.get e8invt
             (Uint63.add (Uint63.mul gr 2%uint63) (prty pg bt))
           <? npagei)%uint63 := o2.
have q3 : (PArray.get e4oft bt <? nbiti)%uint63 := o3.
have /and4P[hsc hsu hsm /and3P[hnc hnu hnm]] := iter_at hlayokC kL.
(* THE THREE PARTS FOLLOW THE THREE RANKS, and that is part_move: the move    *)
(* carries the places, the rank check says where, and the forty eight         *)
(* facelets follow.                                                           *)
have hc : cpart (pgmv mpg k pg) = comp_tab (hcT k) (cpart pg).
  apply: (@part_move cflatp 3 8 inC cposn cslotn (up8 pg)
            (up8 (pgmv mpg k pg)) (hinv k) clayokC hsc
            (iter_at (iter_at hcmv kL) (ltn_npagei hp)) _ hnc).
  apply: up8_rng; case/andP: hcp => _ hu.
  exact: (iter_at hu (ltn_npagei hp)).
have hm : mpart (PArray.get e4oft (btmv btmvt k bt))
        = comp_tab (hmT k) (mpart (PArray.get e4oft bt)).
  apply: (@part_move mlay 2 4 inM mplc eslt (up4 (PArray.get e4oft bt))
            (up4 (PArray.get e4oft (btmv btmvt k bt))) (hinv k) mlayokC hsm
            (iter_at (iter_at hmmv kL) (ltn_nbiti hb)) _ hnm).
  by apply: up4_rng; case/andP: hmp => _ hu; exact: (iter_at hu (ltn_nbiti q3)).
have hu : upart (PArray.get e8invt
            (Uint63.add (Uint63.mul (grmv mgr k gr) 2%uint63)
                        (prty (pgmv mpg k pg) (btmv btmvt k bt))))
        = comp_tab (huT k)
            (upart (PArray.get e8invt
                      (Uint63.add (Uint63.mul gr 2%uint63) (prty pg bt)))).
  rewrite (prty_move kL hp hb).
  apply: (@part_move ulay 2 8 inU eposn eslt
            (up8 (PArray.get e8invt (Uint63.add (Uint63.mul gr 2%uint63)
                                                (prty pg bt))))
            (up8 (PArray.get e8invt
                    (Uint63.add (Uint63.mul (grmv mgr k gr) 2%uint63)
                                (Uint63.lxor (prty pg bt)
                                   (hpar mpg btmvt e4oft par8t par4t k)))))
            (hinv k) ulayokC hsu _ _ hnu).
  - apply: (iter_at (iter_at (iter_at humv kL) (ltn_ngroupi hg))).
    by apply: prty_lt2.
  apply: up8_rng; case/andP: hup => _ hv.
  exact: (iter_at hv (ltn_npagei q2)).
rewrite hc hm hu (hinvE kL).
(* the six tables become six permutations, and from there it is a group       *)
have hct := partok_tab (hcT_ok kL).
have hut := partok_tab (huT_ok kL).
have hmt := partok_tab (hmT_ok kL).
have hcc := partok_tab (cpart_ok hp).
have huc := partok_tab (upart_ok q2).
have hmc := partok_tab (mpart_ok q3).
rewrite -(ptM hct hcc) -(ptM hut huc) -(ptM hmt hmc).
rewrite -(ptM (tab_ok_comp hct hut) hmt) -(ptM hct hut).
apply: six_shuffle.
- exact: (pt_comm (cpart_ok hp) (huT_ok kL) dsj_cu).
- exact: (pt_comm (cpart_ok hp) (hmT_ok kL) dsj_cm).
exact: (pt_comm (upart_ok q2) (hmT_ok kL) dsj_um).
Qed.

(* ---- and the same thing the other way up, which is what RowInst asks for - *)

(* memb2tab is membinv inverted, so the move that acted on the left acts on   *)
(* the right and the other way round -- and the move undone, undone, is the   *)
(* move.                                                                      *)
Lemma memb2tab_move k pg gr bt : (to_nat k < nhn)%N -> inrange pg gr bt ->
  pt flast (memb2tab (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)))
  = pt flast (memb2tab (unpl pg gr bt)) * hmv k.
Proof.
move=> kL hr; have hr' := prep_range hpgo hgro hbto kL hr.
have hi : (hmvi k < 18)%N.
  by apply: (all_nthP 0%N (_ : all (fun m => (m < 18)%N) hmvn)).
have hmk := mvt_ok hi.
(* the two tables named, not left to be guessed: an underscore here sends the *)
(* unifier into the member itself.                                            *)
have ho1 := membinv_ok hcp hup hmp (unpl pg gr bt).
have ho2 := membinv_ok hcp hup hmp
              (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)).
(* the three inversions are CONVERSIONS, given as terms.  Left to rewrite,    *)
(* the match against memb2tab does not come back.                             *)
have E1 : pt flast (memb2tab (unpl pg gr bt))
        = (pt flast (membinv (unpl pg gr bt)))^-1 := esym (ptV ho1).
have E2 : pt flast (memb2tab
            (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt)))
        = (pt flast (membinv
            (unpl (pgmv mpg k pg) (grmv mgr k gr) (btmv btmvt k bt))))^-1
        := esym (ptV ho2).
have E3 : pt flast (hinv k) = (pt flast (mvt (hmvi k)))^-1 := esym (ptV hmk).
(* AND NO congr HERE.  congr tries to close its side goals by conversion,     *)
(* and the two sides are permutations of the forty eight facelets: what it    *)
(* would evaluate is the tables.  Both sides are brought to the same shape    *)
(* instead, and the last step is reflexivity on equal terms.                  *)
apply: (etrans E2).
rewrite (pt_membinv_move kL hr).
rewrite invMg.
rewrite E1.
rewrite E3.
rewrite invgK.
rewrite /hmv -(mvtE hi).
exact: erefl.
Qed.

End Prep.
