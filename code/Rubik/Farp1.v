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
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Fsparity.

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

(* the chunks are PRIMITIVE ARRAY LITERALS, so this is three pointers and
   mkarr is not needed: nothing is converted and nothing is held twice. *)
Definition fsmtabs : PArray.array arr :=
  let a := PArray.make 3%uint63 (PArray.make 1%uint63 0%uint63) in
  let a := PArray.set a 0%uint63 fsm_chunk_00 in
  let a := PArray.set a 1%uint63 fsm_chunk_01 in
  let a := PArray.set a 2%uint63 fsm_chunk_02 in
  a.

(* three values to a word, twenty bits each; the word index splits into a
   chunk and an offset exactly as p1get's does *)
(* THE SHIFT AS A LITERAL, for the reason cwlogi records in Phase1: of_nat
   on a nat is 1.53 us, the array read it indexes is 0.04, and actfsr did it
   twice.  MEASURED: actfsr 4.60 us -> 0.12 us with the two shifts and the
   move index as int63. *)
Definition fcwlogi : int := 21%uint63.     (* = of_nat fcwlog, see fcwlogiE *)

Lemma fcwlogiE : of_nat fcwlog = fcwlogi.
Proof. by vm_compute. Qed.

(* the eighteen move indices as int63 literals, once, for the same reason
   p1mdata hoists the move data: a `seq nat' index makes every use run
   of_nat.  midxiE ties it to iota 0 18 so the proofs are unaffected. *)
Definition midxi : seq int :=
  [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17]%uint63.

Lemma midxiE : midxi = [seq of_nat k | k <- iota 0 18].
Proof. by vm_compute. Qed.

(* the move index as an int63 -- see acttwii in Phase1.v for the measurement *)
Definition actfsri (r k : int) : int :=
  let i := Uint63.add (Uint63.mul r 18%uint63) k in
  let w := Uint63.div i 3%uint63 in
  let j := Uint63.sub i (Uint63.mul w 3%uint63) in
  let c := Uint63.lsr w fcwlogi in
  let o := Uint63.land w (Uint63.sub (Uint63.lsl 1%uint63 fcwlogi)
                                     1%uint63) in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get fsmtabs c) o) (Uint63.mul j 20%uint63))
    1048575%uint63.

Definition actfsr (r : int) (k : nat) : int := actfsri r (of_nat k).

(* /actfsr, not `by []': see acttwiiE in Phase1.v *)
Lemma actfsriE r k : actfsri r (of_nat k) = actfsr r k.
Proof. by rewrite /actfsr. Qed.

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

(* IN int63, and h3 is its to_nat.  The search compares the heuristic with
   the depth, and to_nat builds a UNARY nat: MEASURED, to_nat 9 is 7.97 us
   against 1.6 us for the nine lookups it converts.  of_nat is 13x cheaper
   per unit than to_nat -- of_nat 21 is 1.5 us, to_nat 9 is 8.0 -- so the
   search converts the DEPTH int-ward rather than the heuristic nat-ward,
   and h3iE says the two tests agree. *)
Definition h3i (T : PArray.array arr) (x : c3) : int :=
  let: (x0, x1, x2) := x in
  maxi (hv1 T x0) (maxi (hv1 T x1) (hv1 T x2)).

Definition h3 (T : PArray.array arr) (x : c3) : nat := to_nat (h3i T x).

(* `n < nwB' left to done diverges: nwB is 2 ^ 63 as a unary nat.  Every
   depth here is at most 63, and ndigits is 63. *)
Lemma small_nwB n : (n <= 63)%N -> (n < nwB)%N.
Proof.
move=> nL; apply: leq_ltn_trans nL _; exact: ndigitsLwB.
Qed.

Lemma h3iE T x d : (d <= 63)%N ->
  (h3i T x <=? of_nat d)%uint63 = (h3 T x <= d)%N.
Proof.
move=> dL; rewrite /h3.
by apply/nlebP/idP; rewrite (@of_natK d (small_nwB dL)).
Qed.

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
  if (h3i T x <=? of_nat d)%uint63 then
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

(* stated with the nat test, which is the one the proofs use; h3iE turns the
   int63 test the definition runs into it, once, here *)
Lemma searchz3S T d a x p : (d.+1 <= 63)%N ->
  searchz3 T d.+1 a x p =
  (h3 T x <= d.+1) &&
  (eq_tabi 47 a (id_tabi 47) ||
   has (fun k => searchz3 T d (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                            (step3 x k) (fcpos k))
       (allowedr mtis nfcube oppf fcpos p)).
Proof.
move=> dL; rewrite {1}/searchz3 -/searchz3 (h3iE T x dL).
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
(* AND THE FLIP PARITY, carried in the same boolean.  It is not a consequence
   of cubti: a single flipped edge is a rigid cubie permutation and fails it.
   It is the edge analogue of twsum g = 0, and it rides along twPti for free,
   since twP3 is threaded through the whole development already. *)
Definition twPti (a : arr) : bool :=
  twP (pt 47 (ti2t 47 a)) && ~~ fpar (coordi a).

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
have /andP[/andP[cc /eqP ts] _] := tw.
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
  if ~~ fsok x then true
  else all (fun km => actfsr (fsidx x) km.1 == fsidx (actf x km.2)) md.

Definition fsmoveC : bool := all_pow ncoord 0%uint63 fsmstepF.

(* an EQUATION, not a delta step: any conversion that sees through fsmoveC
   unfolds the all_pow fixpoint at ncoord = 24, i.e. 2 ^ 24 conjuncts.  Same
   trap and same fix as p1checkTwE. *)
Lemma fsmoveCE : fsmoveC = all_pow ncoord 0%uint63 fsmstepF.
Proof. by rewrite /fsmoveC. Qed.

(* the certificate itself is discharged in FsmChk.v, by
   native_cast_no_check, so a day to day build does not pay for it *)

(* split in two, as Phase1.v splits p1stepF_of_check from p1checkStep_inst:
   getting the checked instance out of the loop, then reading the k-th move
   out of it *)
Lemma fsmstepF_of_check x : fsmoveC -> (to_nat x < 2 ^ ncoord)%N -> fsmstepF x.
Proof.
move=> hcheck xL; rewrite fsmoveCE in hcheck.
exact: (all_powP ncoord_dig hcheck xL).
Qed.

(* the guard, settled once: fsok x makes the certificates' `if' take its
   second branch *)
Lemma fsguard x : fsok x -> ~~ fsok x = false.
Proof. by move=> hs; rewrite hs. Qed.

Lemma fsmoveC_inst x k :
  fsmstepF x -> fsok x -> (k < 18)%N ->
  actfsr (fsidx x) k = fsidx (actf x (mdatf_of_tab (nth [::] mtabs k))).
Proof.
move=> hall fsL kL.
move: hall; rewrite /fsmstepF (fsguard fsL) => hstep.
move: hstep => /(all_nthP (0%N, mdatf_of_tab [::])).
rewrite size_map size_iota => /(_ k kL).
by rewrite (nth_map_iota _ _ kL) => /eqP.
Qed.

(* and the array level: the certificate at x = coordi a, with the two side
   conditions discharged where they belong -- the packed bound from Coordfs,
   the fsok guard from sok_coordfs and the carried parity. *)
Lemma actfsr_step a k : fsmoveC -> tabi_ok 47 a -> cubti a -> twPti a ->
  (k < 18)%N ->
  actfsr (fsidx (coordi a)) k
  = fsidx (coordi (comp_tabi 47 a (nth (id_tabi 47) mtis k))).
Proof.
move=> hc aok ca tw kL.
have kL' : (k < seq.size mtis)%N by rewrite size_mtis.
have hcd : coordi a = coordfs (pt 47 (ti2t 47 a)).
  by rewrite (coordiE aok) (coordtE aok).
rewrite (actcdE kL' aok ca) /actcd.
have -> : nth (mdatf_of_tab [::]) mdatafd k = mdatf_of_tab (nth [::] mtabs k).
  by rewrite mdatafdE /mdataf (nth_map [::]) // size_mtabs18.
(* cA is NOT redundant: without it `exact: sok_coordfs' leaves cubP to
   `done', which unfolds it and evaluates the tables -- it does not
   return. *)
have cA : cubP (pt 47 (ti2t 47 a)) by rewrite (cubtE aok) -(cubtiE aok).
(* the guard is now fsok, and its two halves come from two different places:
   the slice half from cubP, the parity half from the carried invariant *)
have hfs : fsok (coordi a).
  rewrite /fsok; apply/andP; split.
    by rewrite hcd; exact: sok_coordfs cA.
  by move: tw; rewrite /twPti => /andP[_].
(* every argument pinned, no `apply ... ; last': with fsmoveC in the context
   the unification apply leaves behind goes looking at it, and fsmoveC is an
   all_pow at ncoord = 24 *)
have hstep : fsmstepF (coordi a).
  by apply: fsmstepF_of_check hc _; rewrite hcd; exact: coordfs_lt.
exact: fsmoveC_inst hstep hfs kL.
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
(* tabi_ok on BOTH sides now: twPti also reads coordi, which ti2t alone does
   not determine -- coordiE is what ties the two, and it wants the array
   well formed. *)
Lemma twPti_ti2t X Y : tabi_ok 47 X -> tabi_ok 47 Y ->
  ti2t 47 X = ti2t 47 Y -> twPti X = twPti Y.
Proof. by move=> Xok Yok h; rewrite /twPti (coordiE Xok) (coordiE Yok) h. Qed.

(* the twist guard propagates along a move, which is twPM at the array level *)
Lemma twPti_step a k : tabi_ok 47 a -> cubti a -> twPti a -> (k < 18)%N ->
  twPti (comp_tabi 47 a (nth (id_tabi 47) mtis k)).
Proof.
move=> aok ca /andP[tw fp] kL.
have kL' : (k < seq.size mtis)%N by rewrite size_mtis.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
rewrite /twPti (fpar_step aok ca kL) fp andbT.
rewrite (ti2t_comp n47_small n47_len aok mtok) -(ptM aok mtok).
have -> : ti2t 47 (nth (id_tabi 47) mtis k) = nth [::] mtabs k.
  by rewrite -ti2t_mtis (nth_map (id_tabi 47)).
exact: twPM kL tw.
Qed.

Lemma twP3_step a k : tabi_ok 47 a -> cubti a -> twP3 a -> (k < 18)%N ->
  twP3 (comp_tabi 47 a (nth (id_tabi 47) mtis k)).
Proof.
move=> aok ca /and3P[t1 t2 t3] kL.
have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have kaL := allP mv3a_lt _ kM.
have kbL := allP mv3b_lt _ kM.
(* one place for `the k-th move table is well formed', as prefixi_twP3 has:
   all_nthP wants j < size mtis, and mv3a_lt / mv3b_lt give j < 18 *)
have hm j : (j < 18)%N -> tabi_ok 47 (nth (id_tabi 47) mtis j)
  by move=> jL; apply: (all_nthP (id_tabi 47) mtis_ok); rewrite size_mtis.
have ok3 := tabi_ok_conj3 aok.
have ok33 := tabi_ok_conj3 ok3.
have ca3 := cubti_conj3 aok ca.
have ca33 := cubti_conj3 ok3 ca3.
have okc := tabi_ok_comp n47_small n47_len aok (hm _ kL).
apply/and3P; split.
- exact: twPti_step aok ca t1 kL.
- rewrite (twPti_ti2t (tabi_ok_conj3 okc)
             (tabi_ok_comp n47_small n47_len ok3 (hm _ kaL))
             (conj3_step aok kL)).
  exact: twPti_step ok3 ca3 t2 kaL.
rewrite (twPti_ti2t (tabi_ok_conj3 (tabi_ok_conj3 okc))
           (tabi_ok_comp n47_small n47_len ok33 (hm _ kbL))
           (conj3_step2 aok kL)).
exact: twPti_step ok33 ca33 t3 kbL.
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
rewrite (acttwi_step aok ca t1 kL) (actfsr_step hc aok ca t1 kL).
rewrite (acttwi_step ok3 c3a t2 kaL) (actfsr_step hc ok3 c3a t2 kaL).
rewrite (acttwi_step ok33 c33a t3 kbL) (actfsr_step hc ok33 c33a t3 kbL).
rewrite (ctwisti_ti2t okA3 C3 e3) (coordi_ti2t okA3 C3 e3).
rewrite (ctwisti_ti2t okA33 C33 e33) (coordi_ti2t okA33 C33 e33).
exact: refl_equal.
Qed.

(* and then the search is the reference search, by induction on the depth.
   Far.v's searchz5E line for line, with the twist guard threaded. *)
Lemma searchz3E T d a p : (d <= 63)%N ->
  fsmoveC -> tabi_ok 47 a -> cubti a -> twP3 a ->
  searchz3 T d a (init3 a) p
  = searchir 47 mtis (Dsym3 T) nfcube oppf fcpos d a p.
Proof.
move=> dL hc; move: dL; elim: d a p => [|d IH] a p dL aok ca tw.
  rewrite {1}/searchz3 {1}/searchir (h3iE T (init3 a) dL) h3_init.
  by case: (Dsym3 T a <= 0); case: (eq_tabi 47 a (id_tabi 47)).
have dL' : (d <= 63)%N by apply: leq_trans dL; exact: leqnSn.
rewrite (searchz3S _ _ _ _ dL).
rewrite (searchirS 47 mtis (Dsym3 T) nfcube oppf fcpos d a p).
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
have twA := twP3_step aok ca tw kL18.
by rewrite (step3_init hc aok ca tw kL18) (IH _ (fcpos k) dL' Aok cA twA).
Qed.

(* THE PAYOFF, the analogue of Far.far_of_searchz5.  The two check
   hypotheses are what make the heuristic admissible; with p1dummy they are
   p1check0_dummy and p1checkStep_dummy, with the real table they are the
   emitted certificate. *)
(* ---- 5. The heuristic at the permutation level --------------------------- *)

(* THE VIEWS ARE SYMMETRIES.  Far.v's views are Sy and Sx, which are two of
   Symg's three generators and so are in Symg for nothing.  The 120 degree
   rotation is not a generator, so it has to be exhibited as a word in them.
   Found by breadth first search over Symset, which closes at 48 elements:
   rot3t is at length four. *)
Lemma rot3tE : rot3t = comp_tab (comp_tab (comp_tab Sytab Sxtab) Sytab) Sytab.
Proof. by vm_compute. Qed.

Lemma pt_rot3_Symg : pt 47 rot3t \in Symg.
Proof.
have o1 : tab_ok 47 (comp_tab Sytab Sxtab) by apply: tab_ok_comp okSy okSx.
have s1 : pt 47 (comp_tab Sytab Sxtab) \in Symg
  by apply: pt_comp_Symg okSy okSx pt_Sy_Symg pt_Sx_Symg.
have o2 : tab_ok 47 (comp_tab (comp_tab Sytab Sxtab) Sytab)
  by apply: tab_ok_comp o1 okSy.
have s2 : pt 47 (comp_tab (comp_tab Sytab Sxtab) Sytab) \in Symg
  by apply: pt_comp_Symg o1 okSy s1 pt_Sy_Symg.
by rewrite rot3tE; apply: pt_comp_Symg o2 okSy s2 pt_Sy_Symg.
Qed.

Lemma pt_rot3t2_Symg : pt 47 rot3t2 \in Symg.
Proof.
by rewrite /rot3t2; apply: pt_comp_Symg rot3t_ok rot3t_ok pt_rot3_Symg
                                        pt_rot3_Symg.
Qed.

Definition views3 : seq (seq nat) := [:: id_tab 47; rot3t; rot3t2].

Definition views3p : seq {perm facelet} := [seq pt 47 s | s <- views3].

Lemma views3_Symg u : u \in views3p -> u \in Symg.
Proof.
case/mapP => s; rewrite !inE => /orP[/eqP->|/orP[/eqP->|/eqP->]] ->.
- by rewrite pt1 group1.
- exact: pt_rot3_Symg.
exact: pt_rot3t2_Symg.
Qed.

(* -- CERTIFICATE 2: the flip x slice distances, by rank -------------------- *)

(* Dfsri reads the emitted P1Fs table by RANK, as rubik_par's pfs is read.
   Far.v's Dfsd reads fstab by PACKED value and has Dfsd_0 and Dfsd_step
   already proved, so all that is missing is that the two agree.  Over
   PACKED values, for the same reason fsmoveC is: at x rather than at
   unranki (fsidx x), so no injectivity of fsidx is needed. *)
Definition fsrstepF (x : int) : bool :=
  ~~ fsok x || (Dfsri (fsidx x) =? Dfsi fstab x)%uint63.

Definition fsrC : bool := all_pow ncoord 0%uint63 fsrstepF.

Lemma fsrCE : fsrC = all_pow ncoord 0%uint63 fsrstepF.
Proof. by rewrite /fsrC. Qed.

(* the certificate itself is discharged in FsrChk.v, by
   native_cast_no_check, so a day to day build does not pay for it *)

(* -- CERTIFICATE 3: the slice rank move table ------------------------------ *)

(* The ts bound is read at slrank (fsidx x), and stepping it uses actslri,
   which reads the emitted slmove_data.  Nothing backed that table either.
   Same shape and same loop as fsmoveC. *)
Definition slrstepF (x : int) : bool :=
  ~~ fsok x ||
  all (fun km => actslri (slrank (fsidx x)) km.1 =?
                 slrank (fsidx (actf x km.2)))%uint63 p1mdata.

Definition slrC : bool := all_pow ncoord 0%uint63 slrstepF.

Lemma slrCE : slrC = all_pow ncoord 0%uint63 slrstepF.
Proof. by rewrite /slrC. Qed.

(* the certificate itself is discharged in SlrChk.v, by
   native_cast_no_check, so a day to day build does not pay for it *)

(* -- getting the checked instances out of the two loops -------------------- *)

Lemma fsr_of_check x : fsrC -> (to_nat x < 2 ^ ncoord)%N -> fsrstepF x.
Proof.
move=> hcheck xL; rewrite fsrCE in hcheck.
exact: (all_powP ncoord_dig hcheck xL).
Qed.

Lemma fsrC_inst x :
  fsrstepF x -> fsok x -> Dfsri (fsidx x) = Dfsi fstab x.
Proof.
(* orFb, NOT /=: simpl here goes on to unfold Dfsri and fstab and evaluate
   them.  Same trap as everywhere else on these tables. *)
by move=> hall fsL; move: hall; rewrite /fsrstepF (fsguard fsL) orFb => /eqP.
Qed.

Lemma slr_of_check x : slrC -> (to_nat x < 2 ^ ncoord)%N -> slrstepF x.
Proof.
move=> hcheck xL; rewrite slrCE in hcheck.
exact: (all_powP ncoord_dig hcheck xL).
Qed.

Lemma slrC_inst x k :
  slrstepF x -> fsok x -> (k < 18)%N ->
  actslri (slrank (fsidx x)) k
  = slrank (fsidx (actf x (mdatf_of_tab (nth [::] mtabs k)))).
Proof.
move=> hall fsL kL.
move: hall; rewrite /slrstepF (fsguard fsL) orFb => hstep.
move: hstep => /(all_nthP (0%N, mdatf_of_tab [::])).
rewrite size_map size_iota => /(_ k kL).
by rewrite (nth_map_iota _ _ kL) => /eqP.
Qed.

(* -- the twist x slice bound: getting its checked instance out ------------- *)

Lemma ltb_lebF a b : (a <? b)%uint63 -> (b <=? a)%uint63 = false.
Proof.
move=> ab; apply/idP => /nlebP h1; move/nltbP: ab => h2.
by rewrite leqNgt h2 in h1.
Qed.

Lemma to_nat_nsranki : to_nat nsranki = nsrank.
Proof. by vm_compute. Qed.

(* the guard ts_checkStep is written with: the rank of a summary is below 495,
   which is the int63 statement that slrank is a remainder *)
Lemma slrank_ltB f : (slrank f <? nsranki)%uint63.
Proof.
apply/nltbP; rewrite to_nat_nsranki /slrank.
have hle : (to_nat f %/ nsrank * nsrank <= to_nat f)%N by exact: leq_divM.
have hq : to_nat (Uint63.mul (Uint63.div f nsranki) nsranki)
        = (to_nat f %/ nsrank * nsrank)%N.
  rewrite to_nat_mulW to_nat_div to_nat_nsranki modn_small //.
  exact: leq_ltn_trans hle (to_nat_bounded f).
rewrite to_nat_sub ?hq //; last exact: to_nat_bounded.
by rewrite {1}(divn_eq (to_nat f) nsrank) addKn ltn_pmod.
Qed.

(* four bits, so far below the wrap point -- Phase1's Dp1i_small, verbatim *)
Lemma Dtsi_small tw s : (to_nat (Dtsi tw s) < nwB.-1)%N.
Proof.
rewrite /Dtsi /tsget.
set v := (X in (X land _)%uint63); rewrite landC.
apply: ltn_trans (_ : 2 ^ 4 < _); last first.
  rewrite -ltnS prednK; last by apply: ltn_trans ndigitsLwB.
  by apply: ltn_trans ndigitsLwB.
by apply: to_nat_land_bound.
Qed.

Lemma nine_dig : (9 <= ndigits)%N.
Proof. by vm_compute. Qed.

Lemma nsrank_pow9 : (nsrank <= 2 ^ 9)%N.
Proof. by []. Qed.

(* an EQUATION, not a delta step.  `rewrite /ts_checkStep' makes the kernel
   unfold the check at Qed -- 2187 twists x 512 ranks -- and it does not
   return.  Phase1's p1checkTwE records the same trap. *)
Lemma ts_checkStepE : ts_checkStep =
  all (fun t => all_pow 9 0%uint63
                  (fun s => (nsranki <=? s)%uint63 || tsstepF (of_nat t) s))
      (iota 0 ntwist).
Proof. by rewrite /ts_checkStep. Qed.

(* AND THE CHECK NEVER ENTERS THE CONTEXT.  With a hypothesis of type
   ts_checkStep in scope every `done' tries `assumption', which unifies the
   goal against it -- same is_true head -- and unfolds the whole check: even
   `1 <= 2' stops returning.  So the premise is rewritten in the GOAL and
   consumed on the way in. *)
Lemma tsstepF_of_check tw s : ts_checkStep -> (to_nat tw < ntwist)%N ->
  (s <? nsranki)%uint63 -> tsstepF tw s.
Proof.
rewrite ts_checkStepE => /allP h twL sB.
have sN : (to_nat s < nsrank)%N by rewrite -to_nat_nsranki; apply/nltbP.
have sP : (to_nat s < 2 ^ 9)%N by apply: leq_trans sN nsrank_pow9.
have hm : to_nat tw \in iota 0 ntwist by rewrite mem_iota add0n leq0n twL.
have htw : all_pow 9 0%uint63 (fun r => (nsranki <=? r)%uint63 || tsstepF tw r).
  by move: (h _ hm); rewrite to_natK; exact: id.
have := all_powP nine_dig htw sP.
rewrite (ltb_lebF sB) orFb; exact: id.
Qed.

(* another equation, and for the same reason: `rewrite /tsstepF' inside the
   proof below makes its Qed diverge, while rewriting with this does not *)
Lemma tsstepFE tw s : tsstepF tw s =
  all (fun k => (Dtsi tw s <=?
                 incr (Dtsi (acttwi tw k) (actslri s k)))%uint63) (iota 0 18).
Proof. by rewrite /tsstepF. Qed.

(* split from the above so the Qeds are separate, as Phase1 splits
   p1stepF_of_check from p1checkStep_inst *)
Lemma ts_checkStep_inst tw s k : tsstepF tw s -> (k < 18)%N ->
  (Dtsi tw s <=? incr (Dtsi (acttwi tw k) (actslri s k)))%uint63.
Proof.
rewrite tsstepFE => hall kL.
have hm : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
exact: (allP hall _ hm).
Qed.

(* THE TWIST x SLICE STEP, at the coordinate level.  Phase1's
   Dp1_step_of_check for the other table, with the slice rank stepping
   through the certified actslri. *)
Lemma Dts_step_of_check tw x k :
  ts_checkStep -> slrC -> (to_nat tw < ntwist)%N -> (to_nat x < 2 ^ ncoord)%N ->
  fsok x -> (k < 18)%N ->
  (Dts tw (slrank (fsidx x))
   <= (Dts (acttwi tw k) (slrank (fsidx (actfs x moves`_k)))).+1)%N.
Proof.
move=> hchk hsl twL xL fsL kL.
have F := ts_checkStep_inst
            (tsstepF_of_check hchk twL (slrank_ltB (fsidx x))) kL.
have S := slrC_inst (slr_of_check hsl xL) fsL kL.
clear hchk hsl.
rewrite S in F.
rewrite (actfs_actfE _ kL) /Dts.
by apply: leb_incr_le F _; exact: Dtsi_small.
Qed.

(* -- the three bounds, at the permutation level ---------------------------- *)

(* the twist x slice bound.  Zero off the invariant, exactly as Phase1's hp1
   is, so that the two obligations below are unconditional. *)
Definition hts (g : {perm facelet}) : nat :=
  if twcP g then Dts (coordtw g) (slrank (fsidx (coordfs g))) else 0%N.

Lemma htsE g : twcP g -> hts g = Dts (coordtw g) (slrank (fsidx (coordfs g))).
Proof. by rewrite /hts => ->. Qed.

Lemma htsN g : ~~ twcP g -> hts g = 0%N.
Proof. by rewrite /hts => /negbTE ->. Qed.

Lemma hts0 : hts 1 = 0%N.
Proof.
rewrite /hts twcP1 coordtw1E coordfs1E /Dts.
(* /ts_check0 in the HYPOTHESIS first: `/eqP ts_check0P' straight makes
   unification look through the check and it does not return *)
have := ts_check0P; rewrite /ts_check0 => /eqP ->.
exact: to_nat_0.
Qed.

(* the checks are turned into applied facts and CLEARED at once: left in the
   context, every later `done' unifies its goal against them and unfolds the
   check. *)
Lemma htsS g m : ts_checkStep -> slrC -> m \in Sset ->
  hts g <= (hts (g * m)).+1.
Proof.
move=> hchk hsl mS.
have D := fun tw x k => @Dts_step_of_check tw x k hchk hsl.
clear hchk hsl.
have [Pg|nPg] := boolP (twcP g); last by rewrite (htsN nPg).
rewrite (htsE Pg) (htsE (twcPM Pg mS)).
have /and3P[cg /andP[cc /eqP tsum] _] := Pg.
have [k kL mE] := Sset_move mS.
rewrite mE (coordfsMS cg _); last by rewrite -mE.
rewrite (coordtw_step kL cc tsum) -(acttwiE (coordtw_lt g) kL) -(hmovesE kL).
exact: (D _ _ _ (coordtw_lt g) (coordfs_lt _) (fsok_twcP Pg) kL).
Qed.

(* THE PER VIEW HEURISTIC: the max of the three, which is rubik_par's
   max (pfs, pts, p) at one view. *)
Definition h3p (T : PArray.array arr) (g : {perm facelet}) : nat :=
  maxn (maxn (hfs Dfsd g) (hts g)) (hp1 T g).

Lemma h3p0 T : p1check0 T -> h3p T 1 = 0%N.
Proof. by move=> hc; rewrite /h3p (hfs0 Dfsd_0) hts0 (hp10 hc). Qed.

Lemma h3pS T g m : p1checkStep T -> ts_checkStep -> slrC -> m \in Sset ->
  h3p T g <= (h3p T (g * m)).+1.
Proof.
move=> hS hchk hsl mS.
have A := hfsS Dfsd_step g mS.
have B := htsS g hchk hsl mS.
have C := hp1S hS g mS.
clear hS hchk hsl.
rewrite /h3p geq_max; apply/andP; split; last first.
  by apply: leq_trans C _; rewrite ltnS leq_max leqnn orbT.
rewrite geq_max; apply/andP; split.
  by apply: leq_trans A _; rewrite ltnS leq_max leq_max leqnn.
by apply: leq_trans B _; rewrite ltnS leq_max leq_max leqnn orbT.
Qed.

(* -- and the max over the three views -------------------------------------- *)

Definition hsym3 (T : PArray.array arr) (g : {perm facelet}) : nat :=
  \max_(u <- views3p) h3p T (g ^ u).

Lemma hsym30 T : p1check0 T -> hsym3 T 1 = 0%N.
Proof.
move=> hc; rewrite /hsym3; apply/eqP; rewrite -leqn0.
by apply/bigmax_leqP_seq => u _ _; rewrite conj1g (h3p0 hc).
Qed.

(* view-wise, exactly Far.v's hsympS: (g * m) ^ u = g ^ u * m ^ u, and m ^ u
   is again a move because Symg stabilises Sset -- Sym.Symg_stab. *)
Lemma hsym3S T g m : p1checkStep T -> ts_checkStep -> slrC -> m \in Sset ->
  hsym3 T g <= (hsym3 T (g * m)).+1.
Proof.
move=> hS hchk hsl mS.
have D := fun g' m' (h : m' \in Sset) => @h3pS T g' m' hS hchk hsl h.
clear hS hchk hsl.
rewrite /hsym3; apply/bigmax_leqP_seq => u uV _.
have uS : u \in Symg by apply: views3_Symg.
have muS : m ^ u \in Sset by rewrite -(Symg_stab uS) memJ_conjg.
apply: leq_trans (_ : (h3p T (g ^ u * m ^ u)).+1 <= _).
  exact: D _ _ muS.
rewrite -conjMg ltnS.
exact: (leq_bigmax_seq u uV isT).
Qed.

(* -- from the array computation down to the permutation heuristic ---------- *)

Lemma to_nat_maxi a b : to_nat (maxi a b) = maxn (to_nat a) (to_nat b).
Proof.
rewrite /maxi; case: nlebP => h; first by rewrite (maxn_idPr h).
by move/negP: h; rewrite -ltnNge => h; rewrite (maxn_idPl (ltnW h)).
Qed.

(* THREE AT ONCE, over opaque variables.  Rewriting with to_nat_maxi twice on
   the real goal does not return: its key is to_nat, and the right hand side
   has a to_nat under hts -- Dts is to_nat (Dtsi ...) -- so the matcher walks
   into the twist x slice table and evaluates it. *)
Lemma to_nat_maxi3 a b c :
  to_nat (maxi a (maxi b c))
  = maxn (to_nat a) (maxn (to_nat b) (to_nat c)).
Proof. by rewrite to_nat_maxi to_nat_maxi. Qed.

(* ONE VIEW: the int63 triple of lookups is the nat heuristic at that view.
   The invariant is needed on all three: hfs is 0 off cubP, hts and hp1 are 0
   off twcP, while the array reads the tables regardless. *)
Lemma hv1E T X : fsrC -> tabi_ok 47 X -> cubti X -> twPti X ->
  to_nat (hv1 T (ctwisti X, fsidx (coordi X)))
  = h3p T (pt 47 (ti2t 47 X)).
Proof.
move=> hfr Xok cX tX.
have cA : cubP (pt 47 (ti2t 47 X)) by rewrite (cubtE Xok) -(cubtiE Xok).
have hcd : coordi X = coordfs (pt 47 (ti2t 47 X))
  by rewrite (coordiE Xok) (coordtE Xok).
have htw : ctwisti X = coordtw (pt 47 (ti2t 47 X))
  by rewrite (ctwistiE Xok) (ctwisttE Xok).
(* andTb, NOT /=: simpl on a goal holding twP unfolds cubcP and twsum and
   goes off evaluating the tables.  [&& a, b & c] IS a && (b && c). *)
have twg : twcP (pt 47 (ti2t 47 X)).
  by rewrite /twcP cA andTb -hcd; exact: tX.
rewrite /hv1 [in LHS]/fst [in LHS]/snd.
rewrite to_nat_maxi to_nat_maxi.
rewrite /h3p /hfs /hcoordg cA (htsE twg) (hp1E T twg) hcd htw.
rewrite (fsrC_inst (fsr_of_check hfr (coordfs_lt _)) (fsok_twcP twg)).
rewrite /Dfsd /Dfs /Dts /Dp1 /Dp1i p1idxE.
exact: refl_equal.
Qed.

(* AND THE THREE VIEWS: Dsym3, which is what the search evaluates, is hsym3,
   which is what the two obligations are proved for.  The conjugates line up
   through ptJ -- pt of a conjugated table is the conjugated permutation. *)
Lemma Dsym3E T a : fsrC -> tabi_ok 47 a -> cubti a -> twP3 a ->
  Dsym3 T a = hsym3 T (pt 47 (ti2t 47 a)).
Proof.
move=> hfr aok ca /and3P[t1 t2 t3].
have ok3 := tabi_ok_conj3 aok.
have ok33 := tabi_ok_conj3 ok3.
have c3 := cubti_conj3 aok ca.
have c33 := cubti_conj3 ok3 c3.
rewrite /Dsym3 /h3 /init3.
rewrite /hsym3 /views3p /views3.
rewrite big_map.
(* big_cons one at a time, and maxn0 under a lock: `3!big_cons' and a bare
   maxn0 both walk off into the tables.  Far.v's DsymdE records the same. *)
rewrite big_cons big_cons big_cons big_nil.
rewrite {-3}[maxn]lock maxn0 -lock.
rewrite pt1 conjg1.
rewrite to_nat_maxi3.
have aokt : tab_ok 47 (ti2t 47 a) by [].
have J1 : pt 47 (ti2t 47 a) ^ pt 47 rot3t = pt 47 (ti2t 47 (conj3 a)).
  by rewrite (ptJ aokt rot3t_ok) conj3E (ti2t_conji rot3t_ok aok).
have J2 : pt 47 (ti2t 47 a) ^ pt 47 rot3t2
        = pt 47 (ti2t 47 (conj3 (conj3 a))).
  by rewrite (ptJ aokt rot3t2_ok) (ti2t_conj33 aok) (ti2t_conji rot3t2_ok aok).
rewrite J1 J2.
(* BACKWARDS, hsym3 side to array side: forwards, the matcher looks for
   to_nat (hv1 ...) and walks into h3p on the other side instead. *)
rewrite -(hv1E T hfr aok ca t1).
rewrite -(hv1E T hfr ok3 c3 t2).
rewrite -(hv1E T hfr ok33 c33 t3).
exact: refl_equal.
Qed.

(* -- the search, from the array down to the ball --------------------------- *)

(* AN INVARIANT AWARE searchirE.  Searchir's own searchirE wants the array
   to table bridge for EVERY tabi_ok array, and Dsym3E holds only on cubes
   carrying the twist invariant -- off it the array still reads the tables
   while hsym3 is 0.  The search never visits such an array, so this is the
   same induction with the invariant threaded: it holds at the root, and
   cubti_comp and twP3_step carry it along a move. *)
Lemma searchirE3 T d : fsrC -> forall a p,
  tabi_ok 47 a -> cubti a -> twP3 a ->
  searchir 47 mtis (Dsym3 T) nfcube oppf fcpos d a p
  = searchtr 47 [seq ti2t 47 mt | mt <- mtis] (fun t => hsym3 T (pt 47 t))
             nfcube oppf fcpos d (ti2t 47 a) p.
Proof.
move=> hfr; elim: d => [|d IH] a p aok ca tw.
  rewrite {1}/searchir {1}/searchtr.
  by rewrite (Dsym3E T hfr aok ca tw) (eq_tabi_id n47_small n47_len aok).
rewrite searchirS searchtrS.
rewrite (Dsym3E T hfr aok ca tw) (eq_tabi_id n47_small n47_len aok).
congr (_ && (_ || _)).
rewrite /allowedr has_filter_and seq.size_map.
apply: eq_in_has => k; rewrite mem_iota => /andP[_ kL].
congr (_ && _).
have kL18 : (k < 18)%N by move: kL; rewrite add0n size_mtis.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok); move: kL; rewrite add0n.
rewrite (nth_map (id_tabi 47)); last by move: kL; rewrite add0n.
rewrite -(ti2t_comp n47_small n47_len aok mtok).
apply: IH.
- exact: (tabi_ok_comp n47_small n47_len aok mtok).
- by apply: cubti_comp; [move: kL; rewrite add0n | exact: aok | exact: ca].
exact: twP3_step aok ca tw kL18.
Qed.

(* HOISTED, all three, rather than proved inline where far_of_searchz3 needs
   them: there the context holds ts_checkStep and fsmoveC, and every // and
   every trailing done then unifies its goal against them and unfolds the
   check.  Far.v proves the same three inline because its context is clean. *)
Lemma fcE3 k : k < seq.size [seq ti2t 47 mt | mt <- mtis] ->
  fcube (pt 47 (nth [::] [seq ti2t 47 mt | mt <- mtis] k)) = fcpos k.
Proof.
rewrite seq.size_map => kL.
have kL' : k < nmoves by rewrite /mtis seq.size_map in kL.
by rewrite (nth_map sfti) // -nth_movesE // fcpos_moves.
Qed.

Lemma mtsok3 : all (tab_ok 47) [seq ti2t 47 mt | mt <- mtis].
Proof. by rewrite all_map; exact: mtis_ok. Qed.

Lemma hE3 T t : tab_ok 47 t -> hsym3 T (pt 47 t) = hsym3 T (pt 47 t).
Proof. by []. Qed.

(* AND THE THEOREM: a search that comes back false puts the state outside
   the ball.  Far.v's far_of_searchsym, over three views and three tables:
   searchz3E to the reduced search, searchirE3 down to tables, searchtrE
   down to permutations, then Searchr's searchrN. *)
Lemma far_of_searchz3 T d a : (d <= 63)%N ->
  p1check0 T -> p1checkStep T -> ts_checkStep ->
  fsmoveC -> fsrC -> slrC -> tabi_ok 47 a -> cubti a -> twP3 a ->
  searchz3 T d a (init3 a) nfcube = false ->
  pt 47 (ti2t 47 a) \notin ball Sset d.
Proof.
move=> dL hc0 hcS htsS hfm hfr hsl aok ca tw hs.
have hstep : forall g m, m \in Sset -> hsym3 T g <= (hsym3 T (g * m)).+1.
  by move=> g m mS; exact: (@hsym3S T g m hcS htsS hsl mS).
have e0 : searchz3 T d a (init3 a) nfcube
        = searchir 47 mtis (Dsym3 T) nfcube oppf fcpos d a nfcube
  := @searchz3E T d a nfcube dL hfm aok ca tw.
have e1 := searchirE3 T d hfr nfcube aok ca tw.
have e2 := searchtrE mtsok3 nfcube oppf (hE3 T) fcE3 d nfcube aok.
(* cleared as soon as they are used, for the reason above *)
clear hcS htsS hfm hfr hsl.
apply: (searchrN Sset_inv (hsym30 hc0) hstep
                 fcube_ltS oppfK fcube_close fcube_comm).
rewrite mtisE -e2 -e1 -e0; exact: hs.
Qed.

(* -- the invariant at the root --------------------------------------------- *)

(* THE INVARIANT AT THE ROOT, COMPUTABLY.  twP is stated over
   {perm facelet}, and permutations do not evaluate -- vm_compute on
   twP3 sfti runs past 240 s with no answer.  So it is transported to the
   TABLE level first, where it is a comparison of two 48 entry tables and a
   sum over eight corners, and THAT computes in milliseconds.  Same shape as
   the cubtE and ctwisttE that already exist. *)

(* cubcP g says g commutes with the corner 3-cycle *)
Lemma cubcPE g : cubcP g = (g * ccyc == ccyc * g).
Proof.
apply/forallP/eqP => [h|h f].
  by apply/permP => f; rewrite !permM (eqP (h f)).
by rewrite -!permM h.
Qed.

Definition cubcPt (t : seq nat) : bool := comp_tab t ccyct == comp_tab ccyct t.

Lemma cubcPtE t : tab_ok 47 t -> cubcP (pt 47 t) = cubcPt t.
Proof.
move=> tok.
have o1 : tab_ok 47 (comp_tab t ccyct) by apply: tab_ok_comp tok ccyct_ok.
have o2 : tab_ok 47 (comp_tab ccyct t) by apply: tab_ok_comp ccyct_ok tok.
rewrite cubcPE /ccyc (ptM tok ccyct_ok) (ptM ccyct_ok tok) /cubcPt.
by apply/eqP/eqP => [/(pt_inj_in o1 o2)|->].
Qed.

(* the per corner bridge, which ctwisttE proves inline for its own fold *)
Lemma corientgtE t p : tab_ok 47 t ->
  corientg (pt 47 t) p = corientt (inv_tab 47 t) (nth (0, 0, 0)%N ctrip p).
Proof.
move=> tok; have iok := tab_ok_inv tok.
have ilt c : (c < 48)%N -> (nth 0%N (inv_tab 47 t) c < 48)%N.
  move=> cL; have /and3P[/eqP sz /allP hall _] := iok.
  by apply: hall; rewrite mem_nth // sz.
have hval c : (c < 48)%N ->
    udcol ((pt 47 t)^-1 (inord c)) = (nth 0%N (inv_tab 47 t) c \in cprim).
  move=> cL; rewrite (ptV tok) ptE; last exact: iok.
  by rewrite /udcol (inordK cL) (inordK (ilt _ cL)).
have hb : all (fun tr => ((tr.1.1 < 48) && (tr.1.2 < 48) &&
                          (tr.2 < 48))%N) ctrip.
  by vm_compute.
move/(all_nthP (0, 0, 0)%N): hb => hb'.
have hsz : seq.size ctrip = 8 by [].
have hbp : (((nth (0, 0, 0)%N ctrip p).1.1 < 48) &&
            ((nth (0, 0, 0)%N ctrip p).1.2 < 48))%N.
  have [pL|pL] := ltnP p 8.
    have ps : (p < seq.size ctrip)%N by rewrite hsz.
    by have /andP[/andP[-> ->] _] := hb' p ps.
  by rewrite nth_default ?hsz.
rewrite /corientg /corientt.
have /andP[h0 h1] := hbp.
case: (nth (0, 0, 0)%N ctrip p) h0 h1 => [[c0 c1] c2] h0 h1.
by rewrite (hval _ h0) (hval _ h1).
Qed.

Definition twsumt (t : seq nat) : nat :=
  (foldr (fun p a => a + corientt (inv_tab 47 t) (nth (0, 0, 0)%N ctrip p))
         0%N (iota 0 8)) %% 3.

Lemma twsumtE t : tab_ok 47 t -> twsum (pt 47 t) = twsumt t.
Proof.
move=> tok; rewrite /twsum /twsumt; congr (_ %% 3).
by elim: (iota 0 8) => //= p l ->; rewrite (corientgtE p tok).
Qed.

Definition twPt (t : seq nat) : bool := cubcPt t && (twsumt t == 0%N).

Lemma twPtE t : tab_ok 47 t -> twP (pt 47 t) = twPt t.
Proof. by move=> tok; rewrite /twP (cubcPtE tok) (twsumtE tok). Qed.

(* the flip parity stays as it is: coordi already only reads the table *)
Lemma twPtiE a : tabi_ok 47 a ->
  twPti a = twPt (ti2t 47 a) && ~~ fpar (coordi a).
Proof. by move=> aok; rewrite /twPti (twPtE _). Qed.

Lemma twP3_sfti : twP3 sfti.
Proof.
(* sfok, not sok: sok is now the slice half of the guard, in Phase1.v *)
have sfok : tabi_ok 47 sfti by vm_compute.
have ok3 := tabi_ok_conj3 sfok.
have ok33 := tabi_ok_conj3 ok3.
apply/and3P; split.
- by rewrite (twPtiE sfok); vm_compute.
- by rewrite (twPtiE ok3); vm_compute.
by rewrite (twPtiE ok33); vm_compute.
Qed.

(* prefixi's nth defaults to sfti, twP3_step's to id_tabi; in range they
   agree *)
Lemma nth_mtis_default k : (k < 18)%N ->
  nth sfti mtis k = nth (id_tabi 47) mtis k.
Proof. by move=> kL; apply: set_nth_default; rewrite size_mtis. Qed.

(* and so the invariant holds at every one of the eighteen roots *)
Lemma prefixi_twP3 i j : (i < nmoves)%N -> (j < nmoves)%N ->
  twP3 (prefixi i j).
Proof.
move=> iL jL.
have i18 : (i < 18)%N by [].
have j18 : (j < 18)%N by [].
have hm k : (k < 18)%N -> tabi_ok 47 (nth (id_tabi 47) mtis k)
  by move=> kL; apply: (all_nthP (id_tabi 47) mtis_ok); rewrite size_mtis.
(* sfok, not sok: sok is now the slice half of the guard, in Phase1.v *)
have sfok : tabi_ok 47 sfti by vm_compute.
have csf : cubti sfti by vm_compute.
have ok1 : tabi_ok 47 (comp_tabi 47 sfti (nth (id_tabi 47) mtis i))
  by apply: (tabi_ok_comp n47_small n47_len sfok (hm _ i18)).
have c1 : cubti (comp_tabi 47 sfti (nth (id_tabi 47) mtis i))
  by apply: cubti_comp; [exact: i18 | exact: sfok | exact: csf].
rewrite /prefixi (nth_mtis_default i18) (nth_mtis_default j18).
apply: twP3_step ok1 c1 _ j18.
exact: twP3_step sfok csf twP3_sfti i18.
Qed.

(* ---- 6. The node counter, for comparing against the OCaml ---------------- *)

(* THE COUNTER IS int63.  It used to be a nat, and `n + m' on a unary nat
   costs O(n): the count reaches millions, so every measurement taken with
   it -- every ./runp1.sh count -- was reporting the counter's cost as well
   as the search's.  The production searchz3 has no counter, so the runs
   themselves were never affected, only the timings I derived from them.

   Otherwise this is searchz3 exactly, so the node counts it reports are the
   ones the real search visits. *)
Fixpoint searchz3c (T : PArray.array arr) (d : nat) (a : arr) (x : c3)
                   (p : nat) : bool * int :=
  if (h3i T x <=? of_nat d)%uint63 then
    if eq_tabi 47 a (id_tabi 47) then (true, 1%uint63)
    else if d is d'.+1 then
      (fix go (l : seq nat) (n : int) : bool * int :=
         if l is k :: l' then
           let: (r, m) :=
              searchz3c T d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                             (step3 x k) (fcpos k) in
           if r then (true, Uint63.add n m) else go l' (Uint63.add n m)
         else (false, n)) (allowedr mtis nfcube oppf fcpos p) 1%uint63
    else (false, 1%uint63)
  else (false, 1%uint63).

(* one piece, as Runp1_NN.v runs it, but reporting the node count *)
Definition countp1 (T : PArray.array arr) (d j : nat) : bool * int :=
  let: (r0, n0) := searchz3c T d (prefixi 0 j) (init3 (prefixi 0 j)) nfcube in
  let: (r1, n1) := searchz3c T d (prefixi 1 j) (init3 (prefixi 1 j)) nfcube in
  (r0 || r1, Uint63.add n0 n1).

(* ---- 7. The cheap phase 1 step certificate ------------------------------- *)

(* all_pow visits exactly the 2 ^ k values from i, so a pointwise implication
   that holds ON THAT RANGE is enough.  Mirrors all_pow_gen's induction. *)
Lemma all_pow_imp k i (f g : int -> bool) :
  k <= ndigits -> to_nat i + (2 ^ k)%N <= nwB ->
  (forall x, to_nat i <= to_nat x < to_nat i + (2 ^ k)%N -> f x -> g x) ->
  all_pow k i f -> all_pow k i g.
Proof.
elim: k i => [|k IH] i kL hb /=.
  by move=> h; apply: h; rewrite expn0 addn1 leqnn ltnSn.
move=> h /andP[h1 h2].
have kL' : k <= ndigits by apply: ltnW.
have hhalf : to_nat i + 2 ^ k <= nwB.
  by apply: leq_trans hb; rewrite leq_add2l leq_exp2l.
have hi2 : to_nat (i + lsl 1 (of_nat k))%uint63 = to_nat i + 2 ^ k.
  by apply: to_nat_addlsl => //; apply: leq_trans hb;
     rewrite ltn_add2l ltn_exp2l.
apply/andP; split.
  apply: (IH i) => // x /andP[hx1 hx2]; apply: h; rewrite hx1 /=.
  by apply: leq_trans hx2 _; rewrite leq_add2l leq_exp2l.
apply: (IH (i + lsl 1 (of_nat k))%uint63) => //.
- by rewrite hi2 -addnA addnn -mul2n -expnS.
move=> x; rewrite hi2 => /andP[hx1 hx2]; apply: h.
rewrite (leq_trans _ hx1) ?leq_addr //=.
by move: hx2; rewrite -addnA addnn -mul2n -expnS.
Qed.

(* ---- the cheap step ------------------------------------------------------ *)

(* p1stepF recomputes the flip x slice action with actf, at 6.2 us a call and
   eighteen calls for each of the 1 013 760 summaries in each of the 2187
   twists.  actfsr reads the emitted move table instead, at 0.12 us, and
   fsmoveC is exactly the lemma that says the two agree. *)
Definition p1stepFr (T : PArray.array arr) (tw x : int) : bool :=
  let r := fsidx x in
  if ~~ fsok x then true
  else all (fun k =>
              (p1get T (p1idxr tw r) <=?
               incr (p1get T (p1idxr (acttwii tw k) (actfsri r k))))%uint63)
           midxi.

Definition p1checkTwr (T : PArray.array arr) (tw : int) : bool :=
  all_pow ncoord 0%uint63 (p1stepFr T tw).

Definition p1checkStepr (T : PArray.array arr) : bool :=
  all (fun t => p1checkTwr T (of_nat t)) (iota 0 ntwist).

Lemma p1checkTwrE T tw :
  p1checkTwr T tw = all_pow ncoord 0%uint63 (p1stepFr T tw).
Proof. by rewrite /p1checkTwr. Qed.

(* p1stepF's all is over p1mdata, a map; this is the same all over the
   indices, so that fsmoveC_inst can be applied at k directly.  Conversion
   does the preim delta, the beta and the two projections in one step --
   rewriting them apart does not return. *)
Lemma p1stepFE T tw x :
  p1stepF T tw x =
  (if ~~ fsok x then true
   else all (fun k =>
               (Dp1i T tw x <=?
                incr (Dp1i T (acttwi tw k)
                        (actf x (mdatf_of_tab (nth [::] mtabs k)))))%uint63)
            (iota 0 18)).
Proof. by rewrite /p1stepF /p1mdata all_map. Qed.

(* the two step functions agree wherever the certificate looks *)
Lemma p1stepFrE T tw x : fsmoveC -> (to_nat x < 2 ^ ncoord)%N ->
  p1stepFr T tw x = p1stepF T tw x.
Proof.
(* exact: erefl for the guard branch, NOT `by []': done there does not
   return.  And boolP SUBSTITUTES -- in the second branch the goal already
   reads `if ~~ false', so there is no `~~ fsok x' left for rewrite hg. *)
move=> hfm xL; rewrite p1stepFE /p1stepFr.
case: (boolP (fsok x)) => hg; last exact: erefl.
rewrite midxiE all_map.
apply: eq_in_all => k; rewrite mem_iota add0n => /andP[_ kL].
rewrite /preim /= acttwiiE actfsriE /Dp1i p1idxE p1idxE.
by rewrite (fsmoveC_inst (fsmstepF_of_check hfm xL) hg kL).
Qed.

(* AND SO THE CHEAP CHECK SUFFICES.  fsmoveC is itself a certificate, but a
   2 ^ 24 one, against 2187 x 2 ^ 24 here -- and it is needed anyway.

   TWO TRAPS.  fsmoveC is turned into a forall and CLEARED at once: left in
   the context it is is_true headed, so every // and every trailing done
   unifies its goal against an all_pow at ncoord = 24 and stops returning.
   And allP is not usable here -- applying its view makes the unifier look
   at `all _ (iota 0 2187)' whose elements are themselves all_pow at 2 ^ 24.
   sub_all takes the pointwise implication without ever forming that. *)
Lemma p1checkStepr_ok T : fsmoveC -> p1checkStepr T -> p1checkStep T.
Proof.
move=> hfm.
have hE : forall tw x, (to_nat x < 2 ^ ncoord)%N ->
                       p1stepFr T tw x = p1stepF T tw x.
  by move=> tw x xL; apply: p1stepFrE hfm xL.
clear hfm.
have hb : (to_nat 0%uint63 + 2 ^ ncoord <= nwB)%N.
  by rewrite to_nat_0 add0n nwB_pow leq_exp2l // ncoord_dig.
rewrite /p1checkStepr /p1checkStep.
apply: sub_all => t.
rewrite p1checkTwE p1checkTwrE.
apply: (all_pow_imp ncoord_dig hb) => x hx.
(* hx gives the range the rewrite needs, and // discharges it *)
by rewrite hE //; move: hx; rewrite to_nat_0 add0n => /andP[_].
Qed.

(* the slices version, mirroring Phase1.p1checkStep_of_slices *)
Lemma p1checkStepr_of_slices T (s : seq nat) : s = iota 0 ntwist ->
  all (fun t => p1checkTwr T (of_nat t)) s -> p1checkStepr T.
Proof. by move=> ->. Qed.

