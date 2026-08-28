(* =========================================================================  *)
(*  RowRun.v -- the search, the level loop, and what each owes.               *)
(* =========================================================================  *)

(* A level does two things.  The PREPASS plays the ten moves of H on the      *)
(* whole map at once, which accounts for every word ending in a move of H --  *)
(* and that is nearly all of them.  The SEARCH then looks for the words of    *)
(* that length whose last move is not in H.                                   *)
(*                                                                            *)
(* EVERY CUT HERE IS SAFE, and that is the whole reason a row is cheaper to   *)
(* prove than a lower bound.  What is proved is that the map FILLED, not that *)
(* the search was complete, so a cut that loses words can only make the row   *)
(* finish later or not at all -- it can never call a member covered when it   *)
(* is not.  So nothing below asks the search for completeness.  Compare       *)
(* HSound.canon and HRunS, which are that missing half for the quarter turns  *)
(* and which cost more than everything else together.                         *)
(*                                                                            *)
(* The search stops at a depth of its own and the prepass carries on alone,   *)
(* which is how twenty is reached: hcoset searches to about sixteen.          *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* ---- the eighteen moves, and one step of a ball -------------------------- *)

Lemma size_mtabs : seq.size mtabs = 18%N.
Proof. by vm_compute. Qed.

Lemma size_moves : seq.size moves = 18%N.
Proof. by rewrite mtabsE seq.size_map size_mtabs. Qed.

Lemma mv_Sset k : (k < 18)%N -> nth 1 moves k \in Sset.
Proof. by move=> kL; rewrite inE mem_nth // size_moves. Qed.

(* one move takes the ball of n to the ball of n plus one                     *)
Lemma ball_step g mv n :
  g \in ball Sset n -> mv \in Sset -> g * mv \in ball Sset n.+1.
Proof. by move=> hg hm; rewrite /= inE; apply/orP; right; apply: mem_mulg. Qed.

Section Run.

(* ---- the layout, from Row.v ---------------------------------------------- *)

Variable e8num e8inv e4bit e4of par8 par4 : arr.

(* the two table checks, which is all Row.v asks of the layout                *)
Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place e8num e4bit).
Local Notation unplc := (unplace e8inv e4of par8 par4).
Local Notation mok := (membok par8 par4).

(* ---- the prepass, from RowMap.v ------------------------------------------ *)

Variable mpg mgr msw mlo mhi : arr.

Local Notation prep := (prepass mpg mgr msw mlo mhi).
Local Notation prepm := (prepmv mpg mgr msw mlo mhi).
Local Notation pgm := (pgmv mpg).
Local Notation grm := (grmv mgr).
Local Notation grpm := (grpmv msw mlo mhi).

(* ---- the phase one table, and the moves ---------------------------------- *)

(* The table hcoset's phase1prune carries: beside the distance to H, WHICH    *)
(* MOVES GO CLOSER.  A node then tries three or four moves instead of         *)
(* eighteen.  It is chunked like every other big table.                       *)
Variable p1 : PArray.array arr.

(* FOUR BITS AN ENTRY, FIFTEEN TO A WORD, which is the packing the phase one *)
(* table is generated in and the one Phase1 reads.  The four bits ARE the     *)
(* distance, so wdist has nothing to strip.                                   *)
Definition cwlogi : int := 21%uint63.
Definition cwmaski : int := Eval vm_compute in
  Uint63.sub (Uint63.lsl 1%uint63 cwlogi) 1%uint63.

Definition p1get (c : int) : int :=
  let w := Uint63.div c 15%uint63 in
  let r := Uint63.sub c (Uint63.mul w 15%uint63) in
  let ch := Uint63.lsr w cwlogi in
  let o := Uint63.land w cwmaski in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get p1 ch) o) (Uint63.mul r 4%uint63))
    15%uint63.

Definition wdist (w : int) : int := w.
Definition allmv : int := 262143%uint63.       (* the eighteen moves          *)

(* A move changes the distance by at most one, so a node with s moves to      *)
(* spare beyond its distance may take any move if s is two or more, one that  *)
(* does not raise if s is one, and only one that drops if s is nought.        *)
(* THE TABLE NO LONGER CARRIES WHICH MOVES GO CLOSER.  A word of it is four  *)
(* bits and holds the distance alone, so there is nothing to read a mask      *)
(* from and every move is offered.  That costs breadth at each node and       *)
(* nothing else: a mask that offers too much makes the search bigger, never   *)
(* wrong, and srch_sound never looks at it.                                   *)
Definition wmask (w : int) (s : nat) : int := allmv.

(* THE SEARCH CARRIES A POSITION, NOT A MEMBER.  A member of the row is what  *)
(* the search reaches when the coordinate is solved, and only then, so what   *)
(* is carried down the tree is the position played so far, and tomemb reads   *)
(* the member off it at a leaf.  posp is the position OF THE ROW that it      *)
(* stands for -- the word played, which is the row's representative undone    *)
(* and the carried position put back -- so at the root posp is the identity   *)
(* and a move takes it one step further out.                                  *)
Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable posp : pst -> {perm facelet}.

(* the redundancy rule, as the moves each face allows next                    *)
Variable okmv : int -> int -> bool.

Definition nmvn : nat := 18.

(* THE PRUNING TABLE IS NEVER TRUSTED.  A distance of nought in it is a HINT  *)
(* that the coordinate is solved and nothing more: a table of noughts is      *)
(* admissible, so reading a leaf off the table would make the run only as     *)
(* sound as the table.  The bottom of the search therefore ASKS the position, *)
(* and the table is left to do the one thing it is for, which is to prune.    *)
Variable csolved : int -> pst -> bool.

(* ---- the search ---------------------------------------------------------- *)

(* It is handed the moves worth trying, so it never builds a position the     *)
(* table has already ruled out.  At the bottom the coordinate is solved, so   *)
(* the member reached is one of the row and its bit goes in.                  *)
Fixpoint srch (togo : nat) (c : int) (x : pst) (msk : int) (pv : int)
              (m : rmap) : rmap :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then m'
         else if ~~ okmv pv k then m'
         else
           let c' := cstep c k in
           let w := p1get c' in
           let nd := Uint63.to_nat (wdist w) in
           if (nd <= togo')%N
           then srch togo' c' (xstep x k) (wmask w (togo' - nd)) k m'
           else m')
      m
  else if csolved c x
       then let: (pg, gr, bt) := plc (tomemb x) in mmark m pg gr bt
       else m.

(* ---- one level, and the run ---------------------------------------------- *)

Variable croot : int.                  (* the row's coordinate                *)
Variable sroot : pst.                  (* and the position it starts from     *)
Variable dsrch : nat.                  (* where the search gives up           *)

(* The two maps: the level reads m and fills dst, and the caller swaps.       *)
Definition level (d : nat) (m dst : rmap) : rmap :=
  let m' := prep m dst in
  if (d <= dsrch)%N then
    let w := p1get croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then srch d croot sroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

Fixpoint run (n : nat) (d : nat) (m dst : rmap) : rmap :=
  if n is n1.+1 then run n1 d.+1 (level d.+1 m dst) m else m.

(* ---- what the two halves owe --------------------------------------------- *)

(* The bridge to the cube: which position of the row a member stands for.     *)
Variable pos : memb -> {perm facelet}.

Definition wthn (d : nat) (x : memb) : Prop := pos x \in ball Sset d.

(* a map is sound at d when every bit it has set is a member within d         *)
Definition soundat (m : rmap) (d : nat) : Prop :=
  forall pg gr bt,
    inrange pg gr bt -> mtest m pg gr bt -> wthn d (unplc pg gr bt).

(* ---- the bridge to the cube ---------------------------------------------- *)

(* The search carries three things that have to agree: a coordinate, an       *)
(* abstract position, and the word played from the row's representative.      *)
(* These five say so, and they are the whole of what an instance has to make  *)
(* good -- nothing else in the file looks at the cube.                        *)
(*                                                                            *)
(* THE LAST ONE IS WHERE THE PHASE ONE TABLE IS SPENT.  A distance of nought  *)
(* means the position is in H, and only there do the three ranks the search   *)
(* reads off determine it -- so only there is a leaf a member of the row.     *)

Variable coordP : int -> pst -> Prop.

(* WHAT THE SEARCH CARRIES IS A TABLE, and a table has to be a permutation    *)
(* for playing a move on it to mean anything.  pstok is that, and it is an    *)
(* invariant: the root has it and a move keeps it.                            *)
Variable pstok : pst -> bool.

(* the root of the search is the row's representative, no moves out           *)
Hypothesis coord_root : coordP croot sroot.
Hypothesis root_ball : posp sroot \in ball Sset 0.
Hypothesis root_pok : pstok sroot.

(* a move steps the coordinate and the position together, and keeps a table   *)
(* a table                                                                    *)
Hypothesis coord_step : forall c x k, (to_nat k < nmvn)%N -> pstok x ->
  coordP c x -> coordP (cstep c k) (xstep x k).

Hypothesis xstep_pok : forall x k, (to_nat k < nmvn)%N ->
  pstok x -> pstok (xstep x k).

(* and what it plays is the k-th move                                         *)
Hypothesis xstep_pos : forall x k, (to_nat k < nmvn)%N -> pstok x ->
  posp (xstep x k) = posp x * nth 1 moves (to_nat k).

(* WHERE THE DISTANCE IS NOUGHT the position is in H, and only there do the   *)
(* three ranks the search reads off mean anything: outside H the edges are    *)
(* mixed between the outer eight and the middle four, and there is no outer   *)
(* permutation to rank.  So both of the last two carry that premise.          *)
(* THE WORD PLAYED IS IN THE GROUP, and the two below are given it.  A leaf   *)
(* is reached by a word from the root, so its position is in the ball and the *)
(* ball is inside the group; without it a state that is a table and nothing   *)
(* more can have a solved coordinate and still not be in H.                   *)
Hypothesis leaf_memb : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c x -> membok par8 par4 (tomemb x).

Hypothesis leaf_pos : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c x -> pos (tomemb x) = posp x.

(* ---- and the bridge for the prepass -------------------------------------- *)

(* The prepass plays one move of H on the whole map at once, by three tables: *)
(* a page goes to a page, a group to a group, and the twenty four bits of a   *)
(* group are rearranged.  Which bit goes where is btmv; hmv is the move       *)
(* itself.  These three say that the rearrangement is what the tables do, and *)
(* that page, group and bit together are that one move.                       *)

Variable btmv : int -> int -> int.
Variable hmv : int -> {perm facelet}.

(* the ten moves of H are moves                                               *)
Hypothesis hmv_Sset : forall k, (to_nat k < nhn)%N -> hmv k \in Sset.

(* a bit the rearrangement sets came from a bit of the word it was given      *)
Hypothesis grpmvP : forall k v bt', (to_nat k < nhn)%N ->
  (bt' <? nbiti)%uint63 ->
  ~~ (Uint63.land (grpm k v) (bitof bt') =? 0)%uint63 ->
  exists2 bt, (bt <? nbiti)%uint63 &
    btmv k bt = bt' /\ ~~ (Uint63.land v (bitof bt) =? 0)%uint63.

(* and the three tables together are one move of H played on the member       *)
Hypothesis prep_move : forall k pg gr bt, (to_nat k < nhn)%N ->
  inrange pg gr bt ->
  inrange (pgm k pg) (grm k gr) (btmv k bt) /\
  pos (unplc (pgm k pg) (grm k gr) (btmv k bt)) = pos (unplc pg gr bt) * hmv k.

(* ---- the prepass, which owes nothing any more ---------------------------- *)

(* a map sound at d is sound at d plus one, which is what carrying it over    *)
(* costs                                                                      *)
Lemma soundatW m d : soundat m d -> soundat m d.+1.
Proof.
move=> hm pg gr bt hr ht; rewrite /wthn.
by apply: (subsetP (ball_mono Sset d)); apply: hm.
Qed.

(* The bit one move of H writes: it is a member one move further out than a   *)
(* bit of the source, so a source sound at d makes it sound at d plus one.    *)
(* This is the only place the page, group and bit tables are spent.           *)
Lemma prepmv_bit k src pg gr P Q B : (to_nat k < nhn)%N ->
  (to_nat pg < npagen)%N -> (to_nat gr < ngroupn)%N ->
  inrange P Q B ->
  grpof (pgm k pg) (grm k gr) = grpof P Q ->
  ~~ (Uint63.land (grpm k (gget src (grpof pg gr))) (bitof B) =? 0)%uint63 ->
  forall d, soundat src d -> wthn d.+1 (unplc P Q B).
Proof.
move=> hk hpg hgr hr hG hbit d hm.
have hbi : (B <? nbiti)%uint63 by case/and3P: hr.
have [bt hbt [hbtE hv]] := grpmvP hk hbi hbit.
(* where it came from is a bit of the source, and so a member within d        *)
have hri : inrange pg gr bt.
  by rewrite /inrange hbt !andbT; apply/andP; split; apply/nltbP.
have hin : mtest src pg gr bt by [].
have [hr' hpm] := prep_move hk hri.
(* and the two places are the same place                                      *)
have [<- <-] : pgm k pg = P /\ grm k gr = Q.
  by apply: grpof_inj hG; [case/and3P: hr'|case/and3P: hr'|case/and3P: hr|
                           case/and3P: hr].
rewrite /wthn -hbtE hpm.
by apply: ball_step; [apply: hm | apply: hmv_Sset].
Qed.

(* one move of H over the whole map, writing where it is told                 *)
Lemma prepmv_sound k src dst d : (to_nat k < nhn)%N ->
  soundat src d -> soundat dst d.+1 -> soundat (prepm k src dst) d.+1.
Proof.
move=> hk hm hdst; rewrite /prepmv.
(* every page                                                                 *)
apply: (@ifold_indi _ (fun a => soundat a d.+1)); [| |exact: hdst].
  by apply: ltnW; exact: npagen_nwB.
move=> pg a hpg ha; cbv zeta.
(* and every group in it                                                      *)
apply: (@ifold_indi _ (fun a' => soundat a' d.+1)); [| |exact: ha].
  by apply: ltnW; exact: ngroupn_nwB.
move=> gr a' hgr ha'; cbv zeta.
case: ifP => _ //.
move=> P Q B hr ht.
(* the bit was there already, or it is one of the twenty four just written    *)
case: (mtest_gor ht) => [hold|[hG hbit]]; first by apply: ha'.
by apply: prepmv_bit hk hpg hgr hr hG hbit _ hm.
Qed.

(* the same move, also carrying the source across: the extra bit it writes is *)
(* the source's own, which is a member within d and so within d plus one      *)
Lemma prepmv0_sound k src dst d : (to_nat k < nhn)%N ->
  soundat src d -> soundat dst d.+1 -> soundat (prepmv0 mpg mgr msw mlo mhi
    k src dst) d.+1.
Proof.
move=> hk hm hdst; rewrite /prepmv0.
apply: (@ifold_indi _ (fun a => soundat a d.+1)); [| |exact: hdst].
  by apply: ltnW; exact: npagen_nwB.
move=> pg a hpg ha; cbv zeta.
apply: (@ifold_indi _ (fun a' => soundat a' d.+1)); [| |exact: ha].
  by apply: ltnW; exact: ngroupn_nwB.
move=> gr a' hgr ha'; cbv zeta.
case: ifP => _ //.
move=> P Q B hr ht.
(* the move's own bit, the bit carried across, or one already there           *)
case: (mtest_gor ht) => [ht'|[hG hbit]]; last first.
  by apply: prepmv_bit hk hpg hgr hr hG hbit _ hm.
case: (mtest_gor ht') => [hold|[hG hbit]]; first by apply: ha'.
(* the carried bit stands at the very place it was read from                  *)
have [<- <-] : pg = P /\ gr = Q.
  by apply: grpof_inj hG; [apply/nltbP|apply/nltbP|case/and3P: hr|
                           case/and3P: hr].
apply: (soundatW hm); last exact: hbit.
by rewrite /inrange; apply/and3P; split;
   [apply/nltbP|apply/nltbP|case/and3P: hr].
Qed.

(* A bit the prepass sets is a member one move of H further out than one      *)
(* already set.  It writes into the map it is given, which is the one from    *)
(* two levels back and so already sound at the depth being claimed.           *)
Lemma prepass_sound m dst d :
  soundat m d -> soundat dst d.+1 -> soundat (prep m dst) d.+1.
Proof.
move=> hm hd; rewrite /prepass.
apply: (@ifold_indi _ (fun a => soundat a d.+1)); [| |exact: hd].
  by apply: ltnW; apply: (@ltn_nwB 4).
move=> k a hk ha; case: ifP => _.
  by apply: prepmv0_sound hk hm ha.
by apply: prepmv_sound hk hm ha.
Qed.

(* ---- the search, which owes nothing any more ----------------------------- *)

(* A bit the search sets is a member of the row reached by the word it        *)
(* played.  An induction on the word and nothing more: the search is never    *)
(* asked to have found everything, which is the half a lower bound cannot do  *)
(* without.  The cuts, the mask and the redundancy rule never enter it -- a   *)
(* cut that loses words can only make the row finish later.                   *)
(*                                                                            *)
(* The two extra premises are what the caller already tests: the search never *)
(* runs deeper than the level it is at, and never enters a node the table has *)
(* put further from H than the moves it has left.                             *)
Lemma srch_sound togo c x msk pv m d :
  (togo <= d)%N -> coordP c x -> pstok x ->
  (to_nat (wdist (p1get c)) <= togo)%N ->
  soundat m d -> posp x \in ball Sset (d - togo) ->
  soundat (srch togo c x msk pv m) d.
Proof.
elim: togo c x msk pv m => [|togo ih] c x msk pv m hdt hc hp hnd hm hb.
  (* a leaf: the distance is nought, so the position is in H and the three    *)
  (* ranks the search reads off are the member it stands for                  *)
  have hG : posp x \in G := subsetP (ball_sub_gen Sset _) _ hb.
  rewrite /=; case: (boolP (csolved c x)) => [hs|_]; last exact: hm.
  have hok := leaf_memb hc hp hG hs.
  have E : plc (tomemb x) =
      (mcp (tomemb x),
       Uint63.div (PArray.get e8num (mud (tomemb x))) 2%uint63,
       PArray.get e4bit (mmp (tomemb x))) by [].
  move=> pg' gr' bt' hr ht.
  case: (mmarkP (place_range he8 he4 hok E) hr ht) => [[<- <- <-]|hb2];
    last by apply: hm.
  rewrite /wthn (unplace_place he8 he4 hok E) (leaf_pos hc hp hG hs).
  by move: hb; rewrite subn0.
(* a step: the same map, one move further out                                 *)
apply: (@ifold_indi _ (fun m' => soundat m' d)); [| |exact: hm].
  by apply: ltnW; apply: (@ltn_nwB 5).
move=> k m' hk hm'.
case: ifP => _ //; case: ifP => _ //.
(* THE THIRD TEST IS UNDER THREE lets, and case: ifP does not look through    *)
(* them: the branches speak of what the lets bind.  cbv zeta takes them out,  *)
(* and the lets stay in the definition because they are what stops the table  *)
(* being read three times at every node.                                      *)
cbv zeta; case: ifP => // hle.
apply: (ih _ _ _ _ _ _ (coord_step hk hp hc) (xstep_pok hk hp) hle hm');
    first by apply: ltnW.
rewrite (@xstep_pos x k hk hp) -(subnSK hdt).
by apply: ball_step => //; apply: mv_Sset; exact: hk.
Qed.

(* ---- and the assembly, which owes nothing -------------------------------- *)

(* From here down there is no new mathematics: the two lemmas above are put   *)
(* together, once for a level and once for the run.                           *)

Lemma level_sound m dst d :
  soundat m d -> soundat dst d.+1 -> soundat (level d.+1 m dst) d.+1.
Proof.
move=> hm hd; rewrite /level.
have hp := prepass_sound hm hd.
case: ifP => _ //; case: ifP => hnd //.
apply: (srch_sound _ coord_root root_pok hnd hp) => //.
by rewrite subnn.
Qed.

Lemma run_sound n d m dst :
  soundat m d -> soundat dst d -> soundat (run n d m dst) (d + n).
Proof.
elim: n d m dst => [|n ih] d m dst hm hd /=; first by rewrite addn0.
rewrite addnS -addSn.
by apply: ih; [apply: level_sound hm (soundatW hd) | apply: soundatW hm].
Qed.

End Run.
