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

(* ---- the phase one table, and the moves ---------------------------------- *)

(* The table hcoset's phase1prune carries: beside the distance to H, WHICH    *)
(* MOVES GO CLOSER.  A node then tries three or four moves instead of         *)
(* eighteen.  It is chunked like every other big table.                       *)
Variable p1 : PArray.array arr.

Definition p1get (c : int) : int :=
  PArray.get (PArray.get p1 (Uint63.lsr c cshft)) (Uint63.land c cmskw).

Definition wdist (w : int) : int := Uint63.land w 31%uint63.
Definition allmv : int := 262143%uint63.       (* the eighteen moves          *)

(* A move changes the distance by at most one, so a node with s moves to      *)
(* spare beyond its distance may take any move if s is two or more, one that  *)
(* does not raise if s is one, and only one that drops if s is nought.        *)
Definition wmask (w : int) (s : nat) : int :=
  if (2 <= s)%N then allmv
  else if s == 1%N then Uint63.land (Uint63.lsr w 23%uint63) allmv
  else Uint63.land (Uint63.lsr w 5%uint63) allmv.

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
  else let: (pg, gr, bt) := plc (tomemb x) in mmark m pg gr bt.

(* ---- one level, and the run ---------------------------------------------- *)

Variable croot : int.                  (* the row's coordinate                *)
Variable sroot : pst.                  (* and the position it starts from     *)
Variable dsrch : nat.                  (* where the search gives up           *)

Definition level (d : nat) (m : rmap) : rmap :=
  let m' := prep m in
  if (d <= dsrch)%N then
    let w := p1get croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then srch d croot sroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

Fixpoint run (n : nat) (d : nat) (m : rmap) : rmap :=
  if n is n1.+1 then run n1 d.+1 (level d.+1 m) else m.

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

(* the root of the search is the row's representative, no moves out           *)
Hypothesis coord_root : coordP croot sroot.
Hypothesis root_ball : posp sroot \in ball Sset 0.

(* a move steps the coordinate and the position together                      *)
Hypothesis coord_step : forall c x k, (to_nat k < nmvn)%N ->
  coordP c x -> coordP (cstep c k) (xstep x k).

(* and what it plays is the k-th move                                         *)
Hypothesis xstep_pos : forall x k, (to_nat k < nmvn)%N ->
  posp (xstep x k) = posp x * nth 1 moves (to_nat k).

(* what the search reads off is always three ranks that agree on parity       *)
Hypothesis leaf_memb : forall x, membok par8 par4 (tomemb x).

(* and where the distance is nought, it is the position that was played       *)
Hypothesis leaf_pos : forall c x, coordP c x ->
  wdist (p1get c) = 0%uint63 -> pos (tomemb x) = posp x.

(* ---- what the prepass still owes ----------------------------------------- *)

(* THE PREPASS OWES: a bit it sets is a member one move of H further than one *)
(* already set.  That is where the page, group and bit tables are spent, and  *)
(* it is one move -- not an induction over words.                             *)
Lemma prepass_sound m d : soundat m d -> soundat (prep m) d.+1.
Proof. Admitted.

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
  (togo <= d)%N -> coordP c x ->
  (to_nat (wdist (p1get c)) <= togo)%N ->
  soundat m d -> posp x \in ball Sset (d - togo) ->
  soundat (srch togo c x msk pv m) d.
Proof.
elim: togo c x msk pv m => [|togo ih] c x msk pv m hdt hc hnd hm hb.
  (* a leaf: the distance is nought, so the position is in H and the three    *)
  (* ranks the search reads off are the member it stands for                  *)
  have h0 : wdist (p1get c) = 0%uint63.
    by apply: to_nat_inj; rewrite to_nat_0; apply/eqP; rewrite -leqn0.
  have hok := leaf_memb x.
  rewrite /=.
  have E : plc (tomemb x) =
      (mcp (tomemb x),
       Uint63.div (PArray.get e8num (mud (tomemb x))) 2%uint63,
       PArray.get e4bit (mmp (tomemb x))) by [].
  move=> pg' gr' bt' hr ht.
  case: (mmarkP (place_range he8 he4 hok E) hr ht) => [[<- <- <-]|hb2];
    last by apply: hm.
  rewrite /wthn (unplace_place he8 he4 hok E) (leaf_pos hc h0).
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
apply: (ih _ _ _ _ _ _ (coord_step hk hc) hle hm'); first by apply: ltnW.
rewrite (@xstep_pos x k hk) -(subnSK hdt).
by apply: ball_step => //; apply: mv_Sset; exact: hk.
Qed.

(* ---- and the assembly, which owes nothing -------------------------------- *)

(* From here down there is no new mathematics: the two lemmas above are put   *)
(* together, once for a level and once for the run.                           *)

Lemma level_sound m d : soundat m d -> soundat (level d.+1 m) d.+1.
Proof.
move=> hm; rewrite /level.
have hp := prepass_sound hm.
case: ifP => _ //; case: ifP => hnd //.
apply: (srch_sound _ coord_root hnd hp) => //.
by rewrite subnn.
Qed.

Lemma run_sound n d m : soundat m d -> soundat (run n d m) (d + n).
Proof.
elim: n d m => [|n ih] d m hm /=; first by rewrite addn0.
by rewrite addnS -addSn; apply/ih/level_sound.
Qed.

End Run.
