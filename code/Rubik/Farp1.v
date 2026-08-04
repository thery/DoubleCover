(* =========================================================================  *)
(*  Farp1.v -- the three axis views, which is what rubik_par's heuristic is   *)
(*             the max over.                                                  *)
(*                                                                            *)
(*  ocaml/rubik_par.ml reads THREE lower bounds at each of THREE views and    *)
(*  takes the max of the nine.  The three views are {1, r, r ^ 2} for r the   *)
(*  120 degree rotation about a corner, which permutes the six faces in two   *)
(*  3-cycles.                                                                 *)
(*                                                                            *)
(*  THIS IS NOT Far.v's FIVE VIEWS.  Far.v conjugates by {1, Sy, Sx, SySx,    *)
(*  SxSy} for its flip x slice search.  The two sets are different and must   *)
(*  not be mixed: the node counts that make bench/p1gen.ml a node for node    *)
(*  reference for rubik_par are the three axis ones.                          *)
(*                                                                            *)
(*  WHICH rotation it is was DERIVED, not transcribed: bench/p1gen.ml `views' *)
(*  searches the 48 symmetries for an order 3 element whose conjugation       *)
(*  permutes the move set, and prints it as the table below together with the *)
(*  two move relabellings.  Its own check reports 0 mismatches of 36, and     *)
(*  rot3_relabel reproduces that check here.  Same rule as the corner data in *)
(*  Phase1.v: derive, do not transcribe.                                      *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- 1. The rotation, and what conjugation by it does to the moves ------- *)

Definition rot3t : seq nat :=
  [:: 21; 19; 16; 22; 17; 23; 20; 18; 40; 41; 42; 43; 44; 45; 46; 47;
      29; 27; 24; 30; 25; 31; 28; 26; 7; 6; 5; 4; 3; 2; 1; 0;
      10; 12; 15; 9; 14; 8; 11; 13; 37; 35; 32; 38; 33; 39; 36; 34]%N.

(* the move relabellings: conjugating by r sends move k to move mv3a k, and
   by r ^ 2 to move mv3b k *)
Definition mv3a : seq nat :=
  [:: 6; 7; 8; 0; 1; 2; 3; 4; 5; 15; 16; 17; 9; 10; 11; 12; 13; 14]%N.

Definition mv3b : seq nat :=
  [:: 3; 4; 5; 6; 7; 8; 0; 1; 2; 12; 13; 14; 15; 16; 17; 9; 10; 11]%N.

Definition rot3t2 : seq nat := comp_tab rot3t rot3t.

Lemma rot3t_ok : tab_ok 47 rot3t.
Proof. by vm_compute. Qed.

Lemma rot3t2_ok : tab_ok 47 rot3t2.
Proof. by vm_compute. Qed.

(* it really is an order 3 element *)
Lemma rot3t_order3 : comp_tab rot3t rot3t2 = id_tab 47.
Proof. by vm_compute. Qed.

(* it keeps cubies together, which every view has to *)
Lemma cubt_rot3 : cubt rot3t.
Proof. by vm_compute. Qed.

Lemma cubt_rot3t2 : cubt rot3t2.
Proof. by vm_compute. Qed.

(* THE FACT EVERYTHING RESTS ON, and the same one p1gen checks in OCaml:
   conjugation by each view permutes the move set, by the relabelling. *)
Lemma rot3_relabel :
  all (fun k =>
         (conjt rot3t (nth [::] mtabs k)
            == nth [::] mtabs (nth 0%N mv3a k)) &&
         (conjt rot3t2 (nth [::] mtabs k)
            == nth [::] mtabs (nth 0%N mv3b k)))
      (iota 0 18).
Proof. by vm_compute. Qed.

(* so each view sends a move to a move -- Far.v's view_move, for these views *)
Lemma size_mtabs18 : seq.size mtabs = 18%N.
Proof. by vm_compute. Qed.

(* the relabellings land in range, so the conjugated move is a move *)
Lemma mv3a_lt : all (fun k => (nth 0%N mv3a k < 18)%N) (iota 0 18).
Proof. by vm_compute. Qed.

Lemma mv3b_lt : all (fun k => (nth 0%N mv3b k < 18)%N) (iota 0 18).
Proof. by vm_compute. Qed.

Lemma rot3_move k : (k < 18)%N -> conjt rot3t (nth [::] mtabs k) \in mtabs.
Proof.
move=> kL; have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have /andP[/eqP -> _] := allP rot3_relabel _ kM.
by apply: mem_nth; rewrite size_mtabs18; exact: (allP mv3a_lt _ kM).
Qed.

Lemma rot3t2_move k : (k < 18)%N -> conjt rot3t2 (nth [::] mtabs k) \in mtabs.
Proof.
move=> kL; have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have /andP[_ /eqP ->] := allP rot3_relabel _ kM.
by apply: mem_nth; rewrite size_mtabs18; exact: (allP mv3b_lt _ kM).
Qed.

(* and Far.v's sigma -- the index of the conjugated move -- is the
   relabelling, so every lemma Far.v states in terms of sigma applies *)
Lemma sigma_rot3a : all (fun k => sigma rot3t k == nth 0%N mv3a k) (iota 0 18).
Proof. by vm_compute. Qed.

Lemma sigma_rot3b : all (fun k => sigma rot3t2 k == nth 0%N mv3b k) (iota 0 18).
Proof. by vm_compute. Qed.

(* ---- 2. Conjugation as an array operation -------------------------------- *)

(* the same shape as Far.v's conjy / conjx: the conjugating tables are closed
   literals so the VM shares them, and the bracketing is ri . (a . r) to match
   conji. *)
Definition r3ti     : arr := Eval vm_compute in t2ti 47 rot3t.
Definition r3ti_inv : arr := Eval vm_compute in inv_tabi 47 r3ti.

Definition conj3 (a : arr) : arr :=
  comp_tabi 47 r3ti_inv (comp_tabi 47 a r3ti).

Lemma r3ti_ok : tabi_ok 47 r3ti.
Proof. by vm_compute. Qed.

Lemma conj3E a : conj3 a = conji rot3t a.
Proof. by rewrite /conj3 /conji; congr (comp_tabi _ _ (comp_tabi _ _ _)). Qed.

(* ---- 3. The search, mimicking rubik_par's dfs ---------------------------- *)

(* THE STATE.  rubik_par carries, per node, three (twist, flip x slice) pairs
   -- one per axis view -- and steps each by the RELABELLED move:

     for k = 0 to 2:
       tw.(d').(k) <- twmove.(tw.(d).(k) * nmoves + mv.(k).(m));
       fs.(d').(k) <- fsmove.(fs.(d).(k) * nmoves + mv.(k).(m))

   Both coordinates are stepped by a TABLE, never recomputed.  That is the
   whole reason P1Fsm.v exists: Phase1.v's actf recomputes the flip x slice
   action at 79 us, where rubik_par reads an array. *)

(* CHUNKED, and it has to be: 1 013 760 x 18 values at three to a word is
   6 082 560 words, 1.45x PArray.max_length = 4 194 303.  PArray.make caps
   silently there and every read past it returns the default 0 -- which is
   what made the whole flip x slice half of the search read as zero.  Same
   split as p1get, on the word index at a power of two. *)
Definition fcwlog := 21.

Definition fsmtabs : PArray.array arr :=
  let a := PArray.make 3%uint63 (PArray.make 1%uint63 0%uint63) in
  let a := PArray.set a 0%uint63 (mkarr 2097152%uint63 0%uint63 fsm_chunk_00) in
  let a := PArray.set a 1%uint63 (mkarr 2097152%uint63 0%uint63 fsm_chunk_01) in
  let a := PArray.set a 2%uint63 (mkarr 1888256%uint63 0%uint63 fsm_chunk_02) in
  a.

(* three values to a word, twenty bits each; the word index splits into a
   chunk and an offset exactly as p1get's does *)
Definition actfsr (r : int) (k : nat) : int :=
  let i := Uint63.add (Uint63.mul r 18%uint63) (of_nat k) in
  let w := Uint63.div i 3%uint63 in
  let j := Uint63.sub i (Uint63.mul w 3%uint63) in
  let c := Uint63.lsr w (of_nat fcwlog) in
  let o := Uint63.land w (Uint63.sub (Uint63.lsl 1%uint63 (of_nat fcwlog))
                                     1%uint63) in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get fsmtabs c) o) (Uint63.mul j 20%uint63))
    1048575%uint63.

(* rubik_par's pfs, the flip x slice distance by rank *)
Definition nfswordsi : int := 67584%uint63.      (* ceil (1013760 / 15)      *)

Definition fsdtab : arr := mkarr nfswordsi 0%uint63 fs_data.

Definition Dfsri (r : int) : int :=
  let w := Uint63.div r 15%uint63 in
  let j := Uint63.sub r (Uint63.mul w 15%uint63) in
  Uint63.land (Uint63.lsr (PArray.get fsdtab w) (Uint63.mul j 4%uint63))
              15%uint63.

Definition c3 := ((int * int) * (int * int) * (int * int))%type.

Definition step3 (x : c3) (k : nat) : c3 :=
  let: (x0, x1, x2) := x in
  let ka := nth 0%N mv3a k in
  let kb := nth 0%N mv3b k in
  ((acttwi x0.1 k, actfsr x0.2 k),
   (acttwi x1.1 ka, actfsr x1.2 ka),
   (acttwi x2.1 kb, actfsr x2.2 kb)).

(* THE HEURISTIC: nine lookups, exactly rubik_par's heur --

     a = pfs[f];  b = pts[t * nslice + f mod nslice];  c = p[t * nfs + f]

   at each of the three views, and the max of all nine.  *)
Definition maxi (a b : int) : int := if (a <=? b)%uint63 then b else a.

(* BY RANK.  Phase1's p1idx takes the PACKED value and ranks it itself
   (p1idx tw x = tw * nfsi + fsidx x), but what the search carries is already
   the rank, so p1idx would rank it TWICE and read a wrong slot.  The
   reference is c = p[t * nfs + f] with f the rank -- p1gen.ml's heur.
   Reading a wrong slot can OVERSTATE the distance, which prunes a real
   solution: this is a soundness bug, not a slowdown.  p1idxE is the bridge
   back to Phase1's packed form. *)
Definition p1idxr (tw r : int) : int := Uint63.add (Uint63.mul tw nfsi) r.

Lemma p1idxE tw x : p1idx tw x = p1idxr tw (fsidx x).
Proof. by []. Qed.

Definition hv1 (T : PArray.array arr) (tf : int * int) : int :=
  maxi (maxi (Dfsri tf.2) (Dtsi tf.1 (slrank tf.2)))
       (p1get T (p1idxr tf.1 tf.2)).

Definition h3 (T : PArray.array arr) (x : c3) : nat :=
  let: (x0, x1, x2) := x in
  to_nat (maxi (hv1 T x0) (maxi (hv1 T x1) (hv1 T x2))).

(* the three views of the root: the coordinate of each conjugate.  At the
   superflip all three agree -- it is fixed by all 48 symmetries -- and they
   diverge as the search descends. *)
Definition init3 (a : arr) : c3 :=
  ((ctwisti a, fsidx (coordi a)),
   (ctwisti (conj3 a), fsidx (coordi (conj3 a))),
   (ctwisti (conj3 (conj3 a)), fsidx (coordi (conj3 (conj3 a))))).

(* and the search itself, the same shape as Far.v's searchz5 *)
Fixpoint searchz3 (T : PArray.array arr) (d : nat) (a : arr) (x : c3) (p : nat)
    : bool :=
  if h3 T x <= d then
    if eq_tabi 47 a (id_tabi 47) then true
    else if d is d'.+1 then
      (fix go (l : seq nat) : bool :=
         if l is k :: l' then
           if searchz3 T d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                          (step3 x k) (fcpos k)
           then true else go l'
         else false) (allowedr mtis nfcube oppf fcpos p)
    else false
  else false.

Lemma searchz3S T d a x p :
  searchz3 T d.+1 a x p =
  (h3 T x <= d.+1) &&
  (eq_tabi 47 a (id_tabi 47) ||
   has (fun k => searchz3 T d (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                            (step3 x k) (fcpos k))
       (allowedr mtis nfcube oppf fcpos p)).
Proof.
rewrite {1}/searchz3 -/searchz3.
by case: (h3 T x <= d.+1) => //=; case: (eq_tabi 47 a (id_tabi 47)) => //=.
Qed.

(* ---- 4. What has to be proved -------------------------------------------- *)

(* the rebuilt heuristic: the same nine lookups, but recomputing the three
   views from the array rather than carrying them.  Far.v's Dsymd, one
   quotient up. *)
(* init3 IS the rebuild, so Dsym3 is it -- no second computational form and
   no DsymdE-style bridge to prove, which is where Far.v had to work. *)
Definition Dsym3 (T : PArray.array arr) (a : arr) : nat := h3 T (init3 a).

(* NOT `by []': done searches for a proof, unfolds h3, and goes off
   evaluating the tables -- it does not return.  One delta step does. *)
Lemma h3_init T a : h3 T (init3 a) = Dsym3 T a.
Proof. by rewrite /Dsym3. Qed.

(* the twist invariant at the array level.  Stated through pt for now; the
   computable form (cubcPt and twsumt at the table level, mirroring cubt) is
   what a root will need to discharge it by vm_compute. *)
Definition twPti (a : arr) : bool := twP (pt 47 (ti2t 47 a)).

(* AT ALL THREE VIEWS.  acttwi_step needs the invariant at the conjugate, and
   deriving it -- twsum (g ^ u) = twsum g -- is a real theorem about the total
   twist under conjugation.  It does not have to be derived: twPti is a
   BOOLEAN, so the three views are checked at the ROOT and propagated by
   twP3_step.  The rotation does preserve the corner 3-cycle, which is the
   cubcP half and is a table check (ccyct_rot3), but the twsum half is not
   needed at all this way. *)
Definition twP3 (a : arr) : bool :=
  [&& twPti a, twPti (conj3 a) & twPti (conj3 (conj3 a))].

Lemma ccyct_rot3 : conjt rot3t ccyct = ccyct.
Proof. by vm_compute. Qed.

Lemma ccyct_rot3t2 : conjt rot3t2 ccyct = ccyct.
Proof. by vm_compute. Qed.

(* -- what step3_init decomposes into -------------------------------------- *)

(* THE TWIST HALF is a theorem: acttwi is Phase1's computed action and
   coordtw_step says the coordinate is an action. *)
Lemma acttwi_step b j : tabi_ok 47 b -> cubti b -> twPti b -> (j < 18)%N ->
  acttwi (ctwisti b) j
  = ctwisti (comp_tabi 47 b (nth (id_tabi 47) mtis j)).
Proof.
move=> bok cb tw jL.
have /andP[cc /eqP ts] := tw.
have jL' : (j < seq.size mtis)%N by rewrite size_mtis.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis j)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have cok : tabi_ok 47 (comp_tabi 47 b (nth (id_tabi 47) mtis j))
  by apply: (tabi_ok_comp n47_small n47_len).
have hmt : ti2t 47 (nth (id_tabi 47) mtis j) = nth [::] mtabs j.
  by rewrite -ti2t_mtis (nth_map (id_tabi 47)).
rewrite (ctwistiE bok) -(ctwisttE bok).
rewrite (acttwiE (coordtw_lt _) jL) -(coordtw_step jL cc ts).
rewrite (ctwistiE cok) -(ctwisttE cok).
by rewrite (ti2t_comp n47_small n47_len bok mtok) -(ptM bok mtok) hmt.
Qed.

(* THE FLIP x SLICE HALF IS NOT A THEOREM -- it is a certificate.  actfsr
   reads the EMITTED fsmove table, so "stepping the rank steps the
   coordinate" is a statement about emitted numbers and can only be
   discharged by computing.  It is the honest place for it: once here, not
   once per phase 1 state.

   OVER PACKED VALUES, NOT OVER RANKS, for the reason Phase1.v's p1stepF
   gives.  Ranking first is sixteen times fewer iterations, but the checked
   instance would then sit at unranki (fsidx x) rather than at x, and closing
   that gap needs fsidx injective on the summaries -- which Coordfs does not
   provide.  Over packed values all_powP hands the instance back at coordi a
   itself, and the fsidx guard leaves only the 6 % that are summaries.  Same
   shape as p1stepF, same move data hoisted for the same reason. *)
Definition fsmstepF (x : int) : bool :=
  let md := p1mdata in
  if (nfsi <=? fsidx x)%uint63 then true
  else all (fun km => actfsr (fsidx x) km.1 == fsidx (actf x km.2)) md.

Definition fsmoveC : bool := all_pow ncoord 0%uint63 fsmstepF.

(* an EQUATION, not a delta step: any conversion that sees through fsmoveC
   unfolds the all_pow fixpoint at ncoord = 24, i.e. 2 ^ 24 conjuncts.  Same
   trap and same fix as p1checkTwE. *)
Lemma fsmoveCE : fsmoveC = all_pow ncoord 0%uint63 fsmstepF.
Proof. by rewrite /fsmoveC. Qed.

Lemma fsmoveCP : fsmoveC.
Proof. Admitted.

(* split in two, as Phase1.v splits p1stepF_of_check from p1checkStep_inst:
   getting the checked instance out of the loop, then reading the k-th move
   out of it *)
Lemma fsmstepF_of_check x : fsmoveC -> (to_nat x < 2 ^ ncoord)%N -> fsmstepF x.
Proof.
move=> hcheck xL; rewrite fsmoveCE in hcheck.
exact: (all_powP ncoord_dig hcheck xL).
Qed.

Lemma fsmoveC_inst x k :
  fsmstepF x -> (fsidx x <? nfsi)%uint63 -> (k < 18)%N ->
  actfsr (fsidx x) k = fsidx (actf x (mdatf_of_tab (nth [::] mtabs k))).
Proof.
move=> hall fsL kL.
have hcond : (nfsi <=? fsidx x)%uint63 = false.
  apply/idP => /nlebP h1; move/nltbP: fsL => h2.
  by rewrite leqNgt h2 in h1.
move: hall; rewrite /fsmstepF hcond => hstep.
move: hstep => /(all_nthP (0%N, mdatf_of_tab [::])).
rewrite size_map size_iota => /(_ k kL).
by rewrite (nth_map_iota _ _ kL) => /eqP.
Qed.

(* and the array level: the certificate at x = coordi a, with the two side
   conditions discharged where they belong -- the packed bound from Coordfs,
   the fsidx guard from fsidx_lt. *)
Lemma actfsr_step a k : fsmoveC -> tabi_ok 47 a -> cubti a -> (k < 18)%N ->
  actfsr (fsidx (coordi a)) k
  = fsidx (coordi (comp_tabi 47 a (nth (id_tabi 47) mtis k))).
Proof.
move=> hc aok ca kL.
have kL' : (k < seq.size mtis)%N by rewrite size_mtis.
have hcd : coordi a = coordfs (pt 47 (ti2t 47 a)).
  by rewrite (coordiE aok) (coordtE aok).
rewrite (actcdE kL' aok ca) /actcd.
have -> : nth (mdatf_of_tab [::]) mdatafd k = mdatf_of_tab (nth [::] mtabs k).
  by rewrite mdatafdE /mdataf (nth_map [::]) // size_mtabs18.
(* cA is NOT redundant: without it `exact: fsidx_lt' leaves cubP to `done',
   which unfolds it and evaluates the tables -- it does not return. *)
have cA : cubP (pt 47 (ti2t 47 a)) by rewrite (cubtE aok) -(cubtiE aok).
apply: fsmoveC_inst kL; last by rewrite hcd; exact: fsidx_lt cA.
by apply: fsmstepF_of_check hc _; rewrite hcd; exact: coordfs_lt.
Qed.

(* the views keep cubies together, so cubti travels to them *)
Lemma cubti_conj3 a : tabi_ok 47 a -> cubti a -> cubti (conj3 a).
Proof.
by move=> aok ca; rewrite conj3E; apply: cubti_conji rot3t_ok cubt_rot3 aok ca.
Qed.

(* the twist coordinate, like twPti, only sees the table *)
Lemma ctwisti_ti2t X Y : tabi_ok 47 X -> tabi_ok 47 Y ->
  ti2t 47 X = ti2t 47 Y -> ctwisti X = ctwisti Y.
Proof. by move=> Xok Yok h; rewrite (ctwistiE Xok) (ctwistiE Yok) h. Qed.

(* THE INVARIANT: stepping the three carried pairs agrees with rebuilding
   them after the move.  The flip x slice half is Far.v's coordi_step -- the
   views are usable there because sigma_rot3a says Far's sigma IS mv3a -- plus
   the fsmove certificate; the twist half is acttwi_step. *)
(* the three views of a moved table are the moved three views, with the move
   relabelled -- Far.v's ti2t_step at s = rot3t, which applies because
   rot3_move gives its side condition and sigma_rot3a says Far's sigma is
   mv3a. *)
Lemma conj3_step a k : tabi_ok 47 a -> (k < 18)%N ->
  ti2t 47 (conj3 (comp_tabi 47 a (nth (id_tabi 47) mtis k)))
  = ti2t 47 (comp_tabi 47 (conj3 a)
                          (nth (id_tabi 47) mtis (nth 0%N mv3a k))).
Proof.
move=> aok kL.
have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have kL' : (k < seq.size mtis)%N by rewrite size_mtis.
have /eqP hs := allP sigma_rot3a _ kM.
rewrite !conj3E -hs.
exact: ti2t_step rot3t_ok aok kL' (rot3_move kL).
Qed.

Lemma tabi_ok_conj3 a : tabi_ok 47 a -> tabi_ok 47 (conj3 a).
Proof. by move=> aok; rewrite conj3E; apply: tabi_ok_conji rot3t_ok aok. Qed.

(* the second view: conjugating twice is conjugating by r ^ 2, which is
   Far.v's ti2t_yx for these views -- conjtM, at the table level. *)
Lemma ti2t_conj33 a : tabi_ok 47 a ->
  ti2t 47 (conj3 (conj3 a)) = ti2t 47 (conji rot3t2 a).
Proof.
move=> aok; have ok3 := tabi_ok_conj3 aok.
(* the RHS FIRST: with conji rot3t2 a still in the goal, matching
   ti2t_conji at rot3t makes ssreflect unify rot3t with comp_tab rot3t
   rot3t, and that does not return. *)
rewrite (ti2t_conji rot3t2_ok aok) {1}conj3E (ti2t_conji rot3t_ok ok3).
rewrite conj3E (ti2t_conji rot3t_ok aok).
by rewrite (conjtM rot3t_ok rot3t_ok aok).
Qed.

Lemma conj3_step2 a k : tabi_ok 47 a -> (k < 18)%N ->
  ti2t 47 (conj3 (conj3 (comp_tabi 47 a (nth (id_tabi 47) mtis k))))
  = ti2t 47 (comp_tabi 47 (conj3 (conj3 a))
                          (nth (id_tabi 47) mtis (nth 0%N mv3b k))).
Proof.
move=> aok kL.
have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have kL' : (k < seq.size mtis)%N by rewrite size_mtis.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have kbL : (nth 0%N mv3b k < seq.size mtis)%N
  by rewrite size_mtis; exact: (allP mv3b_lt _ kM).
have mtok2 : tabi_ok 47 (nth (id_tabi 47) mtis (nth 0%N mv3b k))
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have cok := tabi_ok_comp n47_small n47_len aok mtok.
have ok33 := tabi_ok_conj3 (tabi_ok_conj3 aok).
have okc2 : tabi_ok 47 (conji rot3t2 a) by apply: tabi_ok_conji rot3t2_ok aok.
have /eqP hs := allP sigma_rot3b _ kM.
rewrite (ti2t_comp n47_small n47_len ok33 mtok2) (ti2t_conj33 aok).
rewrite -(ti2t_comp n47_small n47_len okc2 mtok2) -hs.
rewrite (ti2t_conj33 cok).
exact: ti2t_step rot3t2_ok aok kL' (rot3t2_move kL).
Qed.

(* twPti only sees the table, so ti2t-equal arrays are interchangeable *)
Lemma twPti_ti2t X Y : ti2t 47 X = ti2t 47 Y -> twPti X = twPti Y.
Proof. by rewrite /twPti => ->. Qed.

(* the twist guard propagates along a move, which is twPM at the array level *)
Lemma twPti_step a k : tabi_ok 47 a -> twPti a -> (k < 18)%N ->
  twPti (comp_tabi 47 a (nth (id_tabi 47) mtis k)).
Proof.
move=> aok tw kL.
have kL' : (k < seq.size mtis)%N by rewrite size_mtis.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
rewrite /twPti (ti2t_comp n47_small n47_len aok mtok) -(ptM aok mtok).
have -> : ti2t 47 (nth (id_tabi 47) mtis k) = nth [::] mtabs k.
  by rewrite -ti2t_mtis (nth_map (id_tabi 47)).
exact: twPM kL tw.
Qed.

Lemma twP3_step a k : tabi_ok 47 a -> twP3 a -> (k < 18)%N ->
  twP3 (comp_tabi 47 a (nth (id_tabi 47) mtis k)).
Proof.
move=> aok /and3P[t1 t2 t3] kL.
have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have kaL := allP mv3a_lt _ kM.
have kbL := allP mv3b_lt _ kM.
have ok3 := tabi_ok_conj3 aok.
have ok33 := tabi_ok_conj3 ok3.
apply/and3P; split.
- exact: twPti_step aok t1 kL.
- rewrite (twPti_ti2t (conj3_step aok kL)).
  exact: twPti_step ok3 t2 kaL.
rewrite (twPti_ti2t (conj3_step2 aok kL)).
exact: twPti_step ok33 t3 kbL.
Qed.

Lemma step3_init a k : fsmoveC ->
  tabi_ok 47 a -> cubti a -> twP3 a -> (k < 18)%N ->
  step3 (init3 a) k = init3 (comp_tabi 47 a (nth (id_tabi 47) mtis k)).
Proof.
move=> hc aok ca /and3P[t1 t2 t3] kL.
have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have kaL := allP mv3a_lt _ kM.
have kbL := allP mv3b_lt _ kM.
have kL' : (k < seq.size mtis)%N by rewrite size_mtis.
have kaL' : (nth 0%N mv3a k < seq.size mtis)%N by rewrite size_mtis.
have kbL' : (nth 0%N mv3b k < seq.size mtis)%N by rewrite size_mtis.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have maok : tabi_ok 47 (nth (id_tabi 47) mtis (nth 0%N mv3a k))
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have mbok : tabi_ok 47 (nth (id_tabi 47) mtis (nth 0%N mv3b k))
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have Aok := tabi_ok_comp n47_small n47_len aok mtok.
have ok3 := tabi_ok_conj3 aok.
have ok33 := tabi_ok_conj3 ok3.
have okA3 := tabi_ok_conj3 Aok.
have okA33 := tabi_ok_conj3 okA3.
have C3 := tabi_ok_comp n47_small n47_len ok3 maok.
have C33 := tabi_ok_comp n47_small n47_len ok33 mbok.
have c3a := cubti_conj3 aok ca.
have c33a := cubti_conj3 ok3 c3a.
have e3 := conj3_step aok kL.
have e33 := conj3_step2 aok kL.
rewrite /step3 /init3.
(* the projections of the literal pairs, by delta -- NOT by /=, which goes
   on to unfold the tables underneath *)
rewrite [in LHS]/fst [in LHS]/snd.
rewrite (acttwi_step aok ca t1 kL) (actfsr_step hc aok ca kL).
rewrite (acttwi_step ok3 c3a t2 kaL) (actfsr_step hc ok3 c3a kaL).
rewrite (acttwi_step ok33 c33a t3 kbL) (actfsr_step hc ok33 c33a kbL).
rewrite (ctwisti_ti2t okA3 C3 e3) (coordi_ti2t okA3 C3 e3).
rewrite (ctwisti_ti2t okA33 C33 e33) (coordi_ti2t okA33 C33 e33).
exact: refl_equal.
Qed.

(* and then the search is the reference search, by induction on the depth.
   Far.v's searchz5E line for line, with the twist guard threaded. *)
Lemma searchz3E T d a p : fsmoveC -> tabi_ok 47 a -> cubti a -> twP3 a ->
  searchz3 T d a (init3 a) p
  = searchir 47 mtis (Dsym3 T) nfcube oppf fcpos d a p.
Proof.
move=> hc; elim: d a p => [|d IH] a p aok ca tw.
  rewrite {1}/searchz3 {1}/searchir h3_init.
  by case: (Dsym3 T a <= 0); case: (eq_tabi 47 a (id_tabi 47)).
rewrite searchz3S (searchirS 47 mtis (Dsym3 T) nfcube oppf fcpos d a p).
rewrite h3_init.
apply: f_equal2; first by apply: refl_equal.
apply: f_equal2; first by apply: refl_equal.
apply: eq_in_has => k; rewrite mem_filter mem_iota => /andP[_ /andP[_ kL]].
have kL18 : (k < 18)%N by move: kL; rewrite add0n size_mtis.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok); move: kL; rewrite add0n.
have Aok : tabi_ok 47 (comp_tabi 47 a (nth (id_tabi 47) mtis k))
  by apply: (tabi_ok_comp n47_small n47_len).
have cA : cubti (comp_tabi 47 a (nth (id_tabi 47) mtis k))
  by apply: cubti_comp; [move: kL; rewrite add0n | exact: aok | exact: ca].
have twA := twP3_step aok tw kL18.
by rewrite (step3_init hc aok ca tw kL18) (IH _ (fcpos k) Aok cA twA).
Qed.

(* THE PAYOFF, the analogue of Far.far_of_searchz5.  The two check
   hypotheses are what make the heuristic admissible; with p1dummy they are
   p1check0_dummy and p1checkStep_dummy, with the real table they are the
   emitted certificate. *)
Lemma far_of_searchz3 T d a :
  p1check0 T -> p1checkStep T -> ts_check0 -> ts_checkStep ->
  fsmoveC -> tabi_ok 47 a -> cubti a -> twP3 a ->
  searchz3 T d a (init3 a) nfcube = false ->
  pt 47 (ti2t 47 a) \notin ball Sset d.
Proof. Admitted.

(* ---- 5. The same search, counting nodes ---------------------------------- *)

(* rubik_par increments `nodes' at the top of dfs, before the heuristic, so a
   node is one call.  searchz3c counts the same thing, and is otherwise
   searchz3 verbatim -- it exists to compare node for node against
   `p1gen 9 pieces', which is the only way to tell "we expand more nodes"
   from "each node costs more". *)
Fixpoint searchz3c (T : PArray.array arr) (d : nat) (a : arr) (x : c3) (p : nat)
    : bool * nat :=
  if h3 T x <= d then
    if eq_tabi 47 a (id_tabi 47) then (true, 1%N)
    else if d is d'.+1 then
      (fix go (l : seq nat) (n : nat) : bool * nat :=
         if l is k :: l' then
           let: (r, m) :=
              searchz3c T d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                             (step3 x k) (fcpos k) in
           if r then (true, (n + m)%N) else go l' (n + m)%N
         else (false, n)) (allowedr mtis nfcube oppf fcpos p) 1%N
    else (false, 1%N)
  else (false, 1%N).

(* one piece, as Runp1_NN.v runs it, but reporting the node count *)
Definition countp1 (T : PArray.array arr) (d j : nat) : bool * nat :=
  let: (r0, n0) := searchz3c T d (prefixi 0 j) (init3 (prefixi 0 j)) nfcube in
  let: (r1, n1) := searchz3c T d (prefixi 1 j) (init3 (prefixi 1 j)) nfcube in
  (r0 || r1, (n0 + n1)%N).
