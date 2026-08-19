(* =========================================================================  *)
(*  HSweepC.v -- the three sweeps obligation C owes, and their proofs.        *)
(* =========================================================================  *)

(* The mathematics of C is proved: a turn moves the datum -- where each cubie *)
(* sits and how it lies -- by a rule with no position in it (HEdge.eslot_step,*)
(* HCorner.cplace_step, HCorner.ctwist_step), and the three coordinates read  *)
(* nothing but that datum.  What is left is that the three move tables ARE the*)
(* rankings of those rules, and that is a computation, one per coordinate.    *)
(* This file cuts each of the three down to one boolean, so that running the  *)
(* boolean is the whole of what remains.                                      *)
(*                                                                            *)
(* THE SHAPE, three times over.  The datum is what the coordinate reads and   *)
(* nothing more, so the coordinate is the rank of the datum (ecoordiE,        *)
(* clcoordiE, ctcoordiE); a turn moves the datum by a rule (edat_step,        *)
(* cldat_step, ctdat_step); a position can only show a datum the sweep visits *)
(* (edat_valid, cldat_valid); and the sweep says the table is the rank of the *)
(* stepped datum.  Put together that is the obligation, at every position.    *)
(*                                                                            *)
(* THE SIZES.  The edges are 190080 data, which is 24 * 22 * 20 * 18 and is   *)
(* n_e exactly; the U corners among the eight places are 70; the twists are   *)
(* 2187.  Times twelve turns each.  The edge sweep is cut into jobs on the    *)
(* first of the four slots, the other two are one file each.                  *)
(*                                                                            *)
(* THE TWIST SWEEP HAS A WRINKLE.  ctcoordi ranks SEVEN twists, the eighth    *)
(* being determined -- but only for a position whose eight twists sum to zero *)
(* mod three.  ctwist_step moves all eight, so the rule on seven needs the    *)
(* eighth, and it is recomputed as minus the sum of the seven.  That is the   *)
(* prototype's way, and it is why ctsum is a hypothesis of sweep_ct: the      *)
(* invariant belongs to the positions the search meets, and ctsum_step is     *)
(* what says a turn keeps it.                                                 *)
(*                                                                            *)
(* THE INVERSIONS ARE DONE ONCE.  einv, cplc and ctw each invert a forty      *)
(* eight entry table, and asking for one inside a sweep costs a thousandfold  *)
(* -- estept, cplct and ctwt are those numbers computed once, and the _tab    *)
(* lemmas say they are the same numbers.                                      *)
(*                                                                            *)
(* AND THE SWEEPS COUNT IN nat, not int63, which the edge sweep can afford    *)
(* only because the datum is four numbers below twenty four: the rank they    *)
(* are compared through is int63, as the table is.                            *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound HEdge
        HCorner.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* the eight corner places, and the seven twists the coordinate carries       *)
Definition ncorn := 8.
Definition nfree := 7.

Section Sweeps.

Variable mt_e mt_cl mt_ct : arr.

(* ======================= THE EDGES ======================================== *)

(* ---- the datum, and its rank --------------------------------------------- *)

(* The datum is the four values eslot reads, one per slice cubie: twice the   *)
(* place plus the flip.  erk is ecoordi with the position taken out of it.    *)
Definition edat (u : arr) : seq nat := [seq eslot u i | i <- iota 0 nslicec].

Definition erk (s : seq nat) : int :=
  (foldl (fun ru i => let: (r, used) := ru in
       let x := nth 0%N s i in
       let p := (x %/ 2)%N in
       let idx := (2 * count (fun q => q \notin used) (iota 0 p))%N in
       (Uint63.add (Uint63.add (Uint63.mul r (of_nat (2 * nedge - 2 * i)%N))
                               (of_nat idx))
                   (of_nat (x %% 2)%N), p :: used))
     (0%uint63, [::]) (iota 0 nslicec)).1.

(* the coordinate reads nothing but the datum                                 *)
Lemma ecoordiE u : ecoordi u = erk (edat u).
Proof. by rewrite /ecoordi /erk /edat /nslicec /=. Qed.

(* ---- the rule, as a table ------------------------------------------------ *)

(* THE INVERSION IS DONE ONCE.  einv inverts a forty eight entry table, and   *)
(* asking for it inside the sweep would cost a thousandfold.  estept is the   *)
(* rule itself computed once: for each turn, where each of the twenty four    *)
(* values of a slot goes.                                                     *)
Definition estept : seq (seq nat) := Eval vm_compute in
  [seq [seq (let j' := einv m (x %/ 2)%N in
             (2 * j' + (x %% 2 + eflp m j') %% 2)%N) | x <- iota 0 (2 * nedge)]
  | m <- iota 0 nq].

Definition estep (m : nat) (s : seq nat) : seq nat :=
  [seq (let j' := einv m (x %/ 2)%N in (2 * j' + (x %% 2 + eflp m j') %% 2)%N)
  | x <- s].

Definition estepn (m : nat) (s : seq nat) : seq nat :=
  [seq nth 0%N (nth [::] estept m) x | x <- s].

Lemma estept_tab :
  all (fun m => all (fun x => nth 0%N (nth [::] estept m) x ==
        (let j' := einv m (x %/ 2)%N in (2 * j' + (x %% 2 + eflp m j') %% 2)%N))
      (iota 0 (2 * nedge))) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma estepnE m s : (m < nq)%N -> all (fun x => (x < 2 * nedge)%N) s ->
  estepn m s = estep m s.
Proof.
move=> mL /allP hs; apply/eq_in_map => x /hs xL.
by apply/eqP; apply: (allP (allP estept_tab _ (mem_iota0 mL)) _ (mem_iota0 xL)).
Qed.

(* the datum after a turn, which is HEdge.eslot_step read on the four         *)
Lemma edat_step (a : arr) m : tabi_ok flast a -> cubt (ti2t flast a) ->
  (m < nq)%N ->
  edat (inv_tabi flast (comp_tabi flast a (mvq m)))
    = estep m (edat (inv_tabi flast a)).
Proof.
move=> aok ca mL; rewrite /edat /estep -map_comp.
by apply/eq_in_map => i; rewrite mem_iota /= => iL; apply: eslot_step.
Qed.

(* ---- which data a position can show -------------------------------------- *)

(* Twice a place plus a flip, and no two slice cubies in the same place.      *)
Definition evalid (s : seq nat) : bool :=
  all (fun x => (x < 2 * nedge)%N) s && uniq [seq (x %/ 2)%N | x <- s].

Lemma eslot_spec (u : arr) i : tabi_ok flast u -> cubt (ti2t flast u) ->
  (i < nslicec)%N ->
  exists j, [/\ (j < nedge)%N, eplace u j = (nedge - nslicec + i)%N &
                eslot u i = (2 * j + eflipn u j)%N].
Proof.
move=> uok cu iL.
have vL : (nedge - nslicec + i < nedge)%N.
  by rewrite /nedge /nslicec; case: i iL.
have [j jL hj] := eplace_onto uok cu vL.
by exists j; split => //; apply: eslotE.
Qed.

Lemma edat_valid (u : arr) : tabi_ok flast u -> cubt (ti2t flast u) ->
  evalid (edat u).
Proof.
move=> uok cu; apply/andP; split.
  apply/allP => x /mapP[i]; rewrite mem_iota /= => iL ->.
  have [j [jL _ ->]] := eslot_spec uok cu iL.
  have f2 := eflipn_lt u j.
  apply: leq_trans (_ : 2 * j.+1 <= 2 * nedge)%N; last by rewrite leq_pmul2l.
  by rewrite mulnS [(2 + _)%N]addnC ltn_add2l.
rewrite /edat -map_comp map_inj_in_uniq ?iota_uniq //.
move=> i1 i2; rewrite !mem_iota /= => i1L i2L.
have [j1 [j1L hp1 he1]] := eslot_spec uok cu i1L.
have [j2 [j2L hp2 he2]] := eslot_spec uok cu i2L.
have d1 : (eslot u i1 %/ 2)%N = j1.
  by rewrite he1 mulnC divnMDl // divn_small ?addn0 // eflipn_lt.
have d2 : (eslot u i2 %/ 2)%N = j2.
  by rewrite he2 mulnC divnMDl // divn_small ?addn0 // eflipn_lt.
rewrite /= d1 d2 => e12.
by move: hp1; rewrite e12 hp2 => /eqP; rewrite eqn_add2l => /eqP.
Qed.


(* ======================= THE CORNER PLACES ================================ *)

(* ---- a position permutes the eight places -------------------------------- *)

(* cldat says which places hold the four U corners, so it is only four ones   *)
(* out of eight because the places a position shows are all eight of them.    *)
(* That is the corner side of HEdge.eplace_inj, and it is proved the same     *)
(* way: two places holding the same cubie would hold three of its facelets    *)
(* between them, and the guard and injectivity put two on one.                *)
Definition ccyc (f : nat) : nat := nth 0%N ccyct f.

Lemma cposn_orbit :
  all (fun f1 => all (fun f2 => (cposn f1 == cposn f2) ==>
        (f2 \in [seq iter s ccyc f1 | s <- iota 0 nslot])) cflat) cflat.
Proof. by vm_compute. Qed.

Lemma cprim_orbit :
  all (fun p1 => all (fun p2 => all (fun s =>
        (iter s ccyc (nth 0%N cprim p1) == nth 0%N cprim p2) ==> (p1 == p2))
      (iota 0 nslot)) (iota 0 ncorn)) (iota 0 ncorn).
Proof. by vm_compute. Qed.

Lemma rplace_inj :
  all (fun j1 => all (fun j2 => (rplace j1 == rplace j2) ==> (j1 == j2))
      (iota 0 ncorn)) (iota 0 ncorn).
Proof. by vm_compute. Qed.

Lemma getn_inj (u : arr) f1 f2 : tabi_ok flast u ->
  (f1 < 48)%N -> (f2 < 48)%N -> getn u f1 = getn u f2 -> f1 = f2.
Proof.
move=> uok f1L f2L.
have /and3P[/eqP usz _ uuniq] := uok.
have h1 : getn u f1 = nth 0%N (ti2t flast u) f1.
  by rewrite /getn (nth_ti2t u f1L).
have h2 : getn u f2 = nth 0%N (ti2t flast u) f2.
  by rewrite /getn (nth_ti2t u f2L).
have i1 : (f1 < seq.size (ti2t flast u))%N by rewrite usz.
have i2 : (f2 < seq.size (ti2t flast u))%N by rewrite usz.
by rewrite h1 h2 => /eqP; rewrite (nth_uniq _ i1 i2 uuniq) => /eqP.
Qed.

Lemma cplace_inj (u : arr) j1 j2 : tabi_ok flast u -> cubct (ti2t flast u) ->
  (j1 < ncorn)%N -> (j2 < ncorn)%N -> cplace u j1 = cplace u j2 -> j1 = j2.
Proof.
move=> uok cu j1L j2L he.
have rL : all (fun j => (rplace j < ncorn)%N) (iota 0 ncorn) by vm_compute.
have p1L : (rplace j1 < ncorn)%N by apply: (allP rL); apply: mem_iota0.
have p2L : (rplace j2 < ncorn)%N by apply: (allP rL); apply: mem_iota0.
have f1L := allP cprim_lt48 _ (mem_iota0 p1L).
have f2L := allP cprim_lt48 _ (mem_iota0 p2L).
have f1M := cprim_cflat p1L.
have f2M := cprim_cflat p2L.
have x1M := getn_corner uok cu f1L f1M.
have x2M := getn_corner uok cu f2L f2M.
have /implyP := allP (allP cposn_orbit _ x1M) _ x2M.
move=> /(_ (introT eqP he)) /mapP[s]; rewrite mem_iota /= => sL hx2.
have hg : getn u (iter s ccyc (nth 0%N cprim (rplace j1)))
            = getn u (nth 0%N cprim (rplace j2)).
  by rewrite (getn_iter _ uok cu f1L) -hx2.
have hi : (iter s ccyc (nth 0%N cprim (rplace j1)) < 48)%N.
  by elim: s {sL hx2 hg} => [//|k ihk]; apply: ccyct_lt.
have /eqP he2 := getn_inj uok hi f2L hg.
have /implyP := allP (allP (allP cprim_orbit _ (mem_iota0 p1L)) _
                        (mem_iota0 p2L)) _ (mem_iota0 sL).
move=> /(_ he2) /eqP hp.
by have /implyP := allP (allP rplace_inj _ (mem_iota0 j1L)) _ (mem_iota0 j2L);
   move=> /(_ (introT eqP hp)) /eqP.
Qed.

Definition cldat (u : arr) : seq bool :=
  [seq (cplace u j < nslicec)%N | j <- iota 0 ncorn].

Lemma cposn_lt : all (fun f => (cposn f < ncorn)%N) cflat.
Proof. by vm_compute. Qed.

Lemma cplace_ltn (u : arr) j : tabi_ok flast u -> cubct (ti2t flast u) ->
  (j < ncorn)%N -> (cplace u j < ncorn)%N.
Proof.
move=> uok cu jL.
have rL : all (fun j => (rplace j < ncorn)%N) (iota 0 ncorn) by vm_compute.
have pL : (rplace j < ncorn)%N by apply: (allP rL); apply: mem_iota0.
by apply: (allP cposn_lt); apply: getn_corner => //;
   [apply: (allP cprim_lt48); apply: mem_iota0 | apply: cprim_cflat].
Qed.

Lemma cldat_valid (u : arr) : tabi_ok flast u -> cubct (ti2t flast u) ->
  count id (cldat u) == nslicec.
Proof.
move=> uok cu.
have huniq : uniq [seq cplace u j | j <- iota 0 ncorn].
  have hinj : {in iota 0 ncorn &, injective (cplace u)}.
    by move=> x y; rewrite !mem_iota /= => xL yL; apply: cplace_inj.
  by rewrite (map_inj_in_uniq hinj); exact: iota_uniq.
have hsub : {subset [seq cplace u j | j <- iota 0 ncorn] <= iota 0 ncorn}.
  move=> x /mapP[j]; rewrite mem_iota add0n => /andP[_ jL] ->.
  by apply: mem_iota0; apply: cplace_ltn.
have hsz : (seq.size (iota 0 ncorn)
              <= seq.size [seq cplace u j | j <- iota 0 ncorn])%N.
  by rewrite size_map.
have [_ hi] := uniq_min_size huniq hsub hsz.
have hp : perm_eq [seq cplace u j | j <- iota 0 ncorn] (iota 0 ncorn).
  by apply: uniq_perm => //; apply: iota_uniq.
rewrite /cldat count_map.
have -> : count (preim (fun j : nat => (cplace u j < nslicec)%N) id)
              (iota 0 ncorn)
            = count (fun p => (p < nslicec)%N)
                [seq cplace u j | j <- iota 0 ncorn] by rewrite count_map.
by rewrite (seq.permP hp).
Qed.

(* ---- the rule, as a table ------------------------------------------------ *)

Definition cplct : seq (seq nat) := Eval vm_compute in
  [seq [seq cplc m j | j <- iota 0 ncorn] | m <- iota 0 nq].

Definition cplcn (m j : nat) : nat := nth 0%N (nth [::] cplct m) j.

Lemma cplcn_tab :
  all (fun m => all (fun j => (cplcn m j == cplc m j) && (cplcn m j < ncorn))
      (iota 0 ncorn)) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma cplcnE m j : (m < nq)%N -> (j < ncorn)%N -> cplcn m j = cplc m j.
Proof.
move=> mL jL.
by have /andP[/eqP h _] := allP (allP cplcn_tab _ (mem_iota0 mL)) _
  (mem_iota0 jL).
Qed.

Lemma cplcn_lt m j : (m < nq)%N -> (j < ncorn)%N -> (cplcn m j < ncorn)%N.
Proof.
move=> mL jL.
by have /andP[_ h] := allP (allP cplcn_tab _ (mem_iota0 mL)) _ (mem_iota0 jL).
Qed.

Definition clstep (m : nat) (b : seq bool) : seq bool :=
  [seq nth false b (cplcn m j) | j <- iota 0 ncorn].

Lemma cldat_step (a : arr) m : tabi_ok flast a -> cubct (ti2t flast a) ->
  (m < nq)%N ->
  cldat (inv_tabi flast (comp_tabi flast a (mvq m)))
    = clstep m (cldat (inv_tabi flast a)).
Proof.
move=> aok ca mL; rewrite /cldat /clstep.
apply/eq_in_map => j; rewrite mem_iota add0n => /andP[_ jL].
have hc : (cplcn m j < ncorn)%N by apply: cplcn_lt.
rewrite (cplace_step aok ca mL jL) -(cplcnE mL jL).
rewrite (nth_map 0%N); last by rewrite size_iota.
by rewrite (nth_iota _ _ hc) add0n.
Qed.

(* ---- the datum, and its rank --------------------------------------------- *)

(* clrk is clcoordi with the position taken out of it: the rank of the four   *)
(* ones among the eight, counted from the last place down.                    *)
Definition clrk (b : seq bool) : int :=
  (foldl (fun ax j => let: (a, x) := ax in
       if nth false b j
       then (Uint63.add a (of_nat 'C(7 - j, x + 1)), (x + 1)%N)
       else (a, x))
     (0%uint63, 0%N) (rev (iota 0 ncorn))).1.

Lemma clcoordiE u : clcoordi u = clrk (cldat u).
Proof. by rewrite /clcoordi /clrk /cldat /ncorn /=. Qed.

(* ======================= THE TWISTS ======================================= *)

(* ---- the datum, and its rank --------------------------------------------- *)

(* The datum is the seven twists the coordinate ranks, and ctrk is ctcoordi   *)
(* with the position taken out of it.                                         *)
Definition ctdat (u : arr) : seq nat := [seq ctwist u j | j <- iota 0 nfree].

Definition ctrk (t : seq nat) : int :=
  foldl (fun a j => Uint63.add (Uint63.mul a (of_nat nslot))
                               (of_nat (nth 0%N t j)))
        0%uint63 (rev (iota 0 nfree)).

Lemma ctcoordiE u : ctcoordi u = ctrk (ctdat u).
Proof. by rewrite /ctcoordi /ctrk /ctdat /nfree /=. Qed.

Lemma ctwist_ltn (u : arr) j : (ctwist u j < nslot)%N.
Proof. by rewrite /ctwist ltn_mod. Qed.

(* ---- the eighth twist ---------------------------------------------------- *)

(* The rule wants all eight twists and the datum carries seven, so the eighth *)
(* is recomputed as minus the sum of the seven.  That is the eighth twist of  *)
(* a position exactly when the eight sum to zero mod three, which is ctsum.   *)
Definition ct8 (t : seq nat) : nat := ((nslot - sumn t %% nslot) %% nslot)%N.

Definition ctget (t : seq nat) (j : nat) : nat :=
  if (j < nfree)%N then nth 0%N t j else ct8 t.

Definition ctsum (u : arr) : bool :=
  (sumn [seq ctwist u j | j <- iota 0 ncorn] %% nslot == 0)%N.

Lemma ct8_arith s c : (c < nslot)%N -> ((s + c) %% nslot = 0)%N ->
  ((nslot - s %% nslot) %% nslot = c)%N.
Proof.
move=> cL; rewrite -modnDml => hs.
have sL : (s %% nslot < nslot)%N by rewrite ltn_mod.
by move: hs sL cL; case: (s %% nslot)%N => [|[|[|]]] //; case: c => [|[|[|]]].
Qed.

Lemma ctgetE (u : arr) j : ctsum u -> (j < ncorn)%N ->
  ctget (ctdat u) j = ctwist u j.
Proof.
move=> hs jL; rewrite /ctget; case: ltnP => jF.
  rewrite /ctdat (nth_map 0%N); last by rewrite size_iota.
  by rewrite (nth_iota _ _ jF) add0n.
have je : j = nfree by apply/eqP; rewrite eqn_leq jF andbT -ltnS.
rewrite je; apply: ct8_arith; first by apply: ctwist_ltn.
move: hs; rewrite /ctsum -[ncorn]/(nfree + 1)%N iotaD map_cat sumn_cat add0n.
have -> : sumn [seq ctwist u k | k <- iota nfree 1] = ctwist u nfree.
  by rewrite /= addn0.
by move=> /eqP.
Qed.

(* ---- the rule, as a table ------------------------------------------------ *)

Definition ctwt : seq (seq nat) := Eval vm_compute in
  [seq [seq ctw m j | j <- iota 0 ncorn] | m <- iota 0 nq].

Definition ctwn (m j : nat) : nat := nth 0%N (nth [::] ctwt m) j.

Lemma ctwn_tab :
  all (fun m => all (fun j => ctwn m j == ctw m j) (iota 0 ncorn)) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma ctwnE m j : (m < nq)%N -> (j < ncorn)%N -> ctwn m j = ctw m j.
Proof.
move=> mL jL.
by apply/eqP; apply: (allP (allP ctwn_tab _ (mem_iota0 mL)) _ (mem_iota0 jL)).
Qed.

(* a turn permutes the twists and adds the one it brings in                   *)
Definition ctstep (m : nat) (t : seq nat) : seq nat :=
  [seq ((ctget t (cplcn m j) + (nslot - ctwn m j)) %% nslot)%N
  | j <- iota 0 nfree].

Lemma ctdat_step (a : arr) m : tabi_ok flast a -> cubct (ti2t flast a) ->
  (m < nq)%N -> ctsum (inv_tabi flast a) ->
  ctdat (inv_tabi flast (comp_tabi flast a (mvq m)))
    = ctstep m (ctdat (inv_tabi flast a)).
Proof.
move=> aok ca mL hs; rewrite /ctdat /ctstep.
apply/eq_in_map => j; rewrite mem_iota add0n => /andP[_ jL].
have jL8 : (j < ncorn)%N by apply: leq_trans jL _.
have hc : (cplcn m j < ncorn)%N by apply: cplcn_lt.
rewrite (ctwist_step aok ca mL jL8) -(cplcnE mL jL8) -(ctwnE mL jL8).
by rewrite (ctgetE hs hc).
Qed.

(* ---- the guard is kept by a turn ----------------------------------------- *)

(* A turn permutes the eight places and adds the twists it brings in, and     *)
(* those add up to nothing mod three -- so the eight twists still sum to zero *)
(* after it.  This is what puts ctsum in pok.                                 *)
Lemma cplc_perm :
  all (fun m => perm_eq [seq cplc m j | j <- iota 0 ncorn] (iota 0 ncorn))
      (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma ctw_sum :
  all (fun m => sumn [seq (nslot - ctw m j)%N | j <- iota 0 ncorn] %% nslot
                  == 0) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma sumn_modn (s : seq nat) (f : nat -> nat) k :
  (sumn [seq (f j %% k)%N | j <- s] %% k = sumn [seq f j | j <- s] %% k)%N.
Proof.
elim: s => [//|j s ih] /=.
by rewrite modnDml -modnDmr ih modnDmr.
Qed.

Lemma sumn_addn (s : seq nat) (f g : nat -> nat) :
  sumn [seq (f j + g j)%N | j <- s]
    = (sumn [seq f j | j <- s] + sumn [seq g j | j <- s])%N.
Proof. by elim: s => [//|j s ih] /=; rewrite ih addnACA. Qed.

Lemma ctsum_step (a : arr) m : tabi_ok flast a -> cubct (ti2t flast a) ->
  (m < nq)%N -> ctsum (inv_tabi flast a) ->
  ctsum (inv_tabi flast (comp_tabi flast a (mvq m))).
Proof.
move=> aok ca mL hs; rewrite /ctsum.
have -> : [seq ctwist (inv_tabi flast (comp_tabi flast a (mvq m))) j
          | j <- iota 0 ncorn]
        = [seq ((ctwist (inv_tabi flast a) (cplc m j) + (nslot - ctw m j))
                 %% nslot)%N | j <- iota 0 ncorn].
  apply/eq_in_map => j; rewrite mem_iota add0n => /andP[_ jL].
  by apply: ctwist_step.
rewrite (sumn_modn _ (fun j => (ctwist (inv_tabi flast a) (cplc m j)
                                 + (nslot - ctw m j))%N)) sumn_addn.
have hp := allP cplc_perm _ (mem_iota0 mL).
have h2 := allP ctw_sum _ (mem_iota0 mL).
have hmap : forall (f g : nat -> nat) s,
    [seq f (g j) | j <- s] = [seq f p | p <- [seq g j | j <- s]].
  by move=> f g; elim=> [//|x s ih] /=; rewrite ih.
rewrite hmap (perm_sumn (perm_map _ hp)) -modnDm (eqP h2).
by move: hs; rewrite /ctsum => /eqP ->.
Qed.

(* ======================= WHAT EACH SWEEP HAS TO SAY ======================= *)

(* For each coordinate: the table entry at a value and a turn is the value    *)
(* the rule gives.  Stated on positions, because that is how the step lemmas  *)
(* deliver it and how agree consumes it; the computation behind it ranges     *)
(* over data, of which there are 190080, 70 and 2187.                         *)
Definition sweep_e : Prop :=
  forall (a : arr) m, tabi_ok flast a -> cubt (ti2t flast a) -> (m < nq)%N ->
    ecoordi (inv_tabi flast (comp_tabi flast a (mvq m)))
      = PArray.get mt_e (Uint63.add
          (Uint63.mul (ecoordi (inv_tabi flast a)) nqti) (of_nat m)).

Definition sweep_cl : Prop :=
  forall (a : arr) m, tabi_ok flast a -> cubct (ti2t flast a) -> (m < nq)%N ->
    clcoordi (inv_tabi flast (comp_tabi flast a (mvq m)))
      = PArray.get mt_cl (Uint63.add
          (Uint63.mul (clcoordi (inv_tabi flast a)) nqti) (of_nat m)).

(* the eighth twist is recomputed, so this one asks for ctsum as well         *)
Definition sweep_ct : Prop :=
  forall (a : arr) m, tabi_ok flast a -> cubct (ti2t flast a) ->
    ctsum (inv_tabi flast a) -> (m < nq)%N ->
    ctcoordi (inv_tabi flast (comp_tabi flast a (mvq m)))
      = PArray.get mt_ct (Uint63.add
          (Uint63.mul (ctcoordi (inv_tabi flast a)) nqti) (of_nat m)).

(* ---- and what they give -------------------------------------------------- *)

(* The three together are HAgree.agree, which is what HRunS.hsearch_complete  *)
(* takes as stt_step and what HAdmis needs to read the sweep of D through the *)
(* coordinates.  htriple is the three of them side by side.                   *)
Lemma sweeps_agree : sweep_e -> sweep_cl -> sweep_ct ->
  forall (a : arr) m, tabi_ok flast a -> cubt (ti2t flast a) ->
    cubct (ti2t flast a) -> ctsum (inv_tabi flast a) -> (m < nq)%N ->
    htriple (comp_tabi flast a (mvq m))
      = stepa mt_e mt_cl mt_ct (htriple a) (of_nat m).
Proof.
move=> he hcl hct a m aok ca cca cta mL.
by rewrite /htriple /stepa (he _ _ aok ca mL) (hcl _ _ aok cca mL)
           (hct _ _ aok cca cta mL).
Qed.

(* ======================= THE THREE SWEEPS ================================= *)

(* a value ranges over the two booleans                                       *)
Definition allb (f : bool -> bool) : bool := f true && f false.

Lemma allbP (f : bool -> bool) b : allb f -> f b.
Proof. by case: b => /andP[]. Qed.

(* ---- the edges ----------------------------------------------------------- *)

(* One datum: the rank of the stepped datum is what the table says, for all   *)
(* twelve turns.  The rank of the datum itself is taken once.                 *)
Definition eone (s : seq nat) : bool :=
  let r := erk s in
  all (fun m => erk (estepn m s) ==
        PArray.get mt_e (Uint63.add (Uint63.mul r nqti) (of_nat m)))
      (iota 0 nq).

(* the data whose first slot is a, which is 7920 of the 190080                *)
Definition echk1 (a : nat) : bool :=
  all (fun b => all (fun c => all (fun d =>
        let s := [:: a; b; c; d] in evalid s ==> eone s)
      (iota 0 (2 * nedge))) (iota 0 (2 * nedge))) (iota 0 (2 * nedge)).

(* k of the first slots from n on, which is what one job takes                *)
Definition echk_from (n k : nat) : bool := all echk1 (iota n k).

(* the whole sweep                                                            *)
Definition echk : bool := echk_from 0 (2 * nedge).

(* one job stops where the next starts                                        *)
Lemma echk_split n k1 k2 :
  echk_from n k1 -> echk_from (n + k1) k2 -> echk_from n (k1 + k2).
Proof. by rewrite /echk_from iotaD all_cat => -> ->. Qed.

(* what the sweep gives at one datum                                          *)
Lemma echkP s : echk -> seq.size s = nslicec -> evalid s -> eone s.
Proof.
case: s => [|a [|b [|c [|d [|x s]]]]] // hchk _ hv.
have /andP[/allP hall _] := hv.
have hb : forall y, y \in [:: a; b; c; d] -> (y < 2 * nedge)%N.
  by move=> y /hall.
have aL : (a < 2 * nedge)%N by apply: hb; rewrite !inE eqxx.
have bL : (b < 2 * nedge)%N by apply: hb; rewrite !inE eqxx orbT.
have cL : (c < 2 * nedge)%N by apply: hb; rewrite !inE eqxx !orbT.
have dL : (d < 2 * nedge)%N by apply: hb; rewrite !inE eqxx !orbT.
have h1 := allP hchk _ (mem_iota0 aL).
have h2 := allP h1 _ (mem_iota0 bL).
have h3 := allP h2 _ (mem_iota0 cL).
by have /implyP := allP h3 _ (mem_iota0 dL); apply.
Qed.

Lemma sweep_e_of_chk : echk -> sweep_e.
Proof.
move=> hchk a m aok ca mL.
have uok := tabi_ok_invi aok; have cu := cubt_invi aok ca.
have hv := edat_valid uok cu.
have hsz : seq.size (edat (inv_tabi flast a)) = nslicec.
  by rewrite size_map size_iota.
have /allP/(_ m (mem_iota0 mL))/eqP h1 := echkP hchk hsz hv.
have /andP[hb _] := hv.
by rewrite !ecoordiE (edat_step aok ca mL) -(estepnE mL hb).
Qed.

(* ---- the corner places --------------------------------------------------- *)

Definition clone (b : seq bool) : bool :=
  let r := clrk b in
  all (fun m => clrk (clstep m b) ==
        PArray.get mt_cl (Uint63.add (Uint63.mul r nqti) (of_nat m)))
      (iota 0 nq).

(* the two hundred and fifty six eight bit vectors, of which the seventy with *)
(* four ones are the data                                                     *)
Definition clchk : bool :=
  allb (fun b0 => allb (fun b1 => allb (fun b2 => allb (fun b3 =>
  allb (fun b4 => allb (fun b5 => allb (fun b6 => allb (fun b7 =>
    let b := [:: b0; b1; b2; b3; b4; b5; b6; b7] in
    (count id b == nslicec) ==> clone b)))))))).

Lemma clchkP b :
  clchk -> seq.size b = ncorn -> count id b == nslicec -> clone b.
Proof.
case: b => [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|x s]]]]]]]]] // hchk _ hc.
have h0 := allbP b0 hchk.
have h1 := allbP b1 h0.
have h2 := allbP b2 h1.
have h3 := allbP b3 h2.
have h4 := allbP b4 h3.
have h5 := allbP b5 h4.
have h6 := allbP b6 h5.
by have /implyP := allbP b7 h6; apply.
Qed.

Lemma sweep_cl_of_chk : clchk -> sweep_cl.
Proof.
move=> hchk a m aok ca mL.
have uok := tabi_ok_invi aok; have cu := cubct_invi aok ca.
have hsz : seq.size (cldat (inv_tabi flast a)) = ncorn.
  by rewrite size_map size_iota.
have /allP/(_ m (mem_iota0 mL))/eqP h1 := clchkP hchk hsz (cldat_valid uok cu).
by rewrite !clcoordiE (cldat_step aok ca mL).
Qed.

(* ---- the twists ---------------------------------------------------------- *)

Definition ctone (t : seq nat) : bool :=
  let r := ctrk t in
  all (fun m => ctrk (ctstep m t) ==
        PArray.get mt_ct (Uint63.add (Uint63.mul r nqti) (of_nat m)))
      (iota 0 nq).

(* all three to the seventh, and every one of them is a datum                 *)
Definition ctchk : bool :=
  all (fun t0 => all (fun t1 => all (fun t2 => all (fun t3 =>
  all (fun t4 => all (fun t5 => all (fun t6 =>
    ctone [:: t0; t1; t2; t3; t4; t5; t6])
      (iota 0 nslot)) (iota 0 nslot)) (iota 0 nslot)) (iota 0 nslot))
      (iota 0 nslot)) (iota 0 nslot)) (iota 0 nslot).

Lemma ctchkP t : ctchk -> seq.size t = nfree ->
  all (fun x => (x < nslot)%N) t -> ctone t.
Proof.
case: t => [|t0 [|t1 [|t2 [|t3 [|t4 [|t5 [|t6 [|x s]]]]]]]] // hchk _ /allP hb.
have l0 : (t0 < nslot)%N by apply: hb; rewrite !inE eqxx.
have l1 : (t1 < nslot)%N by apply: hb; rewrite !inE eqxx orbT.
have l2 : (t2 < nslot)%N by apply: hb; rewrite !inE eqxx !orbT.
have l3 : (t3 < nslot)%N by apply: hb; rewrite !inE eqxx !orbT.
have l4 : (t4 < nslot)%N by apply: hb; rewrite !inE eqxx !orbT.
have l5 : (t5 < nslot)%N by apply: hb; rewrite !inE eqxx !orbT.
have l6 : (t6 < nslot)%N by apply: hb; rewrite !inE eqxx !orbT.
have h0 := allP hchk _ (mem_iota0 l0).
have h1 := allP h0 _ (mem_iota0 l1).
have h2 := allP h1 _ (mem_iota0 l2).
have h3 := allP h2 _ (mem_iota0 l3).
have h4 := allP h3 _ (mem_iota0 l4).
have h5 := allP h4 _ (mem_iota0 l5).
by have := allP h5 _ (mem_iota0 l6).
Qed.

Lemma sweep_ct_of_chk : ctchk -> sweep_ct.
Proof.
move=> hchk a m aok ca hs mL.
have hsz : seq.size (ctdat (inv_tabi flast a)) = nfree.
  by rewrite size_map size_iota.
have hb : all (fun x => (x < nslot)%N) (ctdat (inv_tabi flast a)).
  by apply/allP => x /mapP[j _ ->]; apply: ctwist_ltn.
have /allP/(_ m (mem_iota0 mL))/eqP h1 := ctchkP hchk hsz hb.
by rewrite !ctcoordiE (ctdat_step aok ca mL hs).
Qed.

End Sweeps.

(* ---- what is left -------------------------------------------------------- *)

(* Nothing of C but the three booleans: echk cut into jobs on the first slot, *)
(* clchk and ctchk one file each, all three at the real move tables.  What    *)
(* they cost is what a sweep of 190080, 70 and 2187 data times twelve turns   *)
(* costs, and only the first is more than a moment.                           *)
(*                                                                            *)
(* ctsum_step is not part of a sweep: it is what lets the twist invariant sit *)
(* in pok, where sweep_ct's hypothesis is answered.                           *)
