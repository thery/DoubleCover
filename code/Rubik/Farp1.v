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

Definition nfsmwordsi : int := 6082560%uint63.   (* ceil (1013760 * 18 / 3) *)

Definition fsmtab : arr := mkarr nfsmwordsi 0%uint63 fsmove_data.

(* three values to a word, twenty bits each *)
Definition actfsr (r : int) (k : nat) : int :=
  let i := Uint63.add (Uint63.mul r 18%uint63) (of_nat k) in
  let w := Uint63.div i 3%uint63 in
  let j := Uint63.sub i (Uint63.mul w 3%uint63) in
  Uint63.land (Uint63.lsr (PArray.get fsmtab w) (Uint63.mul j 20%uint63))
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

Definition hv1 (T : PArray.array arr) (tf : int * int) : int :=
  maxi (maxi (Dfsri tf.2) (Dtsi tf.1 (slrank tf.2)))
       (p1get T (p1idx tf.1 tf.2)).

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

(* THE INVARIANT: stepping the three carried pairs agrees with rebuilding
   them after the move.  The flip x slice half is Far.v's coordi_step -- the
   views are usable there because sigma_rot3a says Far's sigma IS mv3a -- plus
   the fsmove table; the twist half is coordtw_step and acttwiE.  It is the
   one place the two tables have to line up with the theory. *)
Lemma step3_init a k : tabi_ok 47 a -> cubti a -> twPti a -> (k < 18)%N ->
  step3 (init3 a) k = init3 (comp_tabi 47 a (nth (id_tabi 47) mtis k)).
Proof. Admitted.

(* the twist guard propagates along a move, which is twPM at the array level *)
Lemma twPti_step a k : tabi_ok 47 a -> twPti a -> (k < 18)%N ->
  twPti (comp_tabi 47 a (nth (id_tabi 47) mtis k)).
Proof. Admitted.

(* and then the search is the reference search, by induction on the depth.
   Far.v's searchz5E line for line, with the twist guard threaded. *)
Lemma searchz3E T d a p : tabi_ok 47 a -> cubti a -> twPti a ->
  searchz3 T d a (init3 a) p
  = searchir 47 mtis (Dsym3 T) nfcube oppf fcpos d a p.
Proof.
elim: d a p => [|d IH] a p aok ca tw.
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
have twA := twPti_step aok tw kL18.
by rewrite (step3_init aok ca tw kL18) (IH _ (fcpos k) Aok cA twA).
Qed.

(* THE PAYOFF, the analogue of Far.far_of_searchz5.  The two check
   hypotheses are what make the heuristic admissible; with p1dummy they are
   p1check0_dummy and p1checkStep_dummy, with the real table they are the
   emitted certificate. *)
Lemma far_of_searchz3 T d a :
  p1check0 T -> p1checkStep T -> ts_check0 -> ts_checkStep ->
  tabi_ok 47 a -> cubti a -> twPti a ->
  searchz3 T d a (init3 a) nfcube = false ->
  pt 47 (ti2t 47 a) \notin ball Sset d.
Proof. Admitted.
