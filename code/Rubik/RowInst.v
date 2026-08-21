(* =========================================================================  *)
(*  RowInst.v -- the instance: the row of the superflip.                      *)
(* =========================================================================  *)

(* Row.v, RowMap.v, RowRun.v and RowFinal.v owe nothing: what they say holds  *)
(* of ANY tables that pass their checks and of ANY search whose carried       *)
(* position agrees with the cube.  This file is the other half -- it says     *)
(* which tables and which search, and it owes everything those four asked.    *)
(*                                                                            *)
(* THE ROW IS THE SUPERFLIP'S.  Its representative is `superflip', which      *)
(* Moves.v already carries as a table, so the row needs no move sequence at   *)
(* all: a member is a position h of H and the word it stands for is the       *)
(* superflip undone and h put back.                                           *)
(*                                                                            *)
(* THE SEARCH CARRIES A FORTY EIGHT ENTRY TABLE -- the cube position played   *)
(* so far, starting at the superflip.  A move is one composition of tables,   *)
(* which is why the position is carried and not recomputed.                   *)
(*                                                                            *)
(* NOTHING IS ADMITTED HERE.  What the file cannot know it ASKS FOR, as a     *)
(* hypothesis beside the table it is about, and there are twelve of them:     *)
(* four checks on the tables, one on the fs step table, two saying what a     *)
(* leaf is, two saying what the prepass tables do to a member, the member's   *)
(* table being a permutation, and the two the run itself settles.             *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section Inst.

(* ---- the tables, which a generated file supplies ------------------------- *)

(* None of these is built in Rocq.  The prototype writes them and a generated *)
(* file carries them as array literals, exactly as the folded tables of the   *)
(* lower bound are carried; what Rocq does with them is CHECK them.           *)

(* the layout: rank to number and back, rank to bit and back, the parities    *)
Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

(* the prepass: a page to a page, a group to a group, the bits rearranged     *)
Variable mpg mgr msw mlo mhi : arr.

(* where a move of H sends a bit, twenty four of them for each of the ten     *)
Variable btmvt : arr.

(* and the phase one table itself, chunked like every other big table         *)
Variable p1 : PArray.array arr.

(* ---- the row is the superflip's ------------------------------------------ *)

Definition repi : arr := sfti.

(* ---- the search carries a table ------------------------------------------ *)

(* A position is a forty eight entry table; a move composes it with the       *)
(* move's own table, which Moves.v already carries.                           *)

Definition pstt := arr.

(* A TABLE IS NOT ENOUGH.  Stepping the coordinate wants the state to be a    *)
(* real cube -- Farp1's cubti says the table respects the cubies, and twPti   *)
(* that the twists sum to nought and the flips are even -- because that is    *)
(* what acttwi_step and actfsr_step ask for.  All three are booleans, the     *)
(* root has them by computation and a move keeps them.                        *)
(* twPti is Farp1's, written out here for the same reason actfsri is: its     *)
(* file will not load in this checkout.                                       *)
Definition twPti (a : arr) : bool :=
  twP (pt flast (ti2t flast a)) && ~~ fpar (coordi a).

Definition pstok (x : pstt) : bool :=
  [&& tabi_ok flast x, cubti x & twPti x].

Definition mvi (k : int) : arr := nth sfti mtis (to_nat k).

Definition xstep (x : pstt) (k : int) : pstt := comp_tabi flast x (mvi k).

Definition sroot : pstt := repi.

(* the word played: the representative undone and what is carried put back    *)
Definition posp (x : pstt) : {perm facelet} :=
  superflip^-1 * pt flast (ti2t flast x).

(* ---- the phase one coordinate -------------------------------------------- *)

(* Kociemba's three: the corner twists, the edge flips, and which four places *)
(* the middle edges are in.                                                   *)
(*                                                                            *)
(* AND THE DEVELOPMENT ALREADY HAS BOTH HALVES OF THIS, which is the one      *)
(* thing that makes the instance affordable.  The corners are in Phase1.v --  *)
(* ctrip is the eight of them as facelet triples, cpos and cslot say which    *)
(* corner a facelet belongs to and how far round, and ctwisti reads the twist *)
(* off a table.  The edges are in Coordfs.v -- eprim and esec are the twelve  *)
(* as facelet pairs IN THE PROTOTYPE'S OWN ORDER, UR UF UL UB DR DF DL DB FR  *)
(* FL BL BR, so the outer eight and the middle four are already the first     *)
(* eight and the last four -- and coordi reads the flip and the slice off a   *)
(* table.  Both are proved against the moves where they stand.                *)
(*                                                                            *)
(* THE COORDINATE IS THEREFORE PHASE1'S: 2187 twists times nfs = 1 013 760,   *)
(* which is 2 217 093 120, the phase one count exactly, and Phase1.fsidx is   *)
(* the same flip times 495 plus slice rank the prototype packs.               *)
(*                                                                            *)
(* AND THE STEP IS OFF THE SHELF TOO.  Farp1.actfsri is the flip and slice    *)
(* rank stepped by a move -- the prototype's own fsmove table, read three     *)
(* entries to a word -- and Phase1.acttwii is the twist stepped by a move.    *)
(* So the row's coordinate needs no new table and no new theorem: what is     *)
(* left is to put the two halves together, which is coord_step below.         *)

(* the twist times nfs plus the flip and slice rank, which is Phase1's own    *)
(* index and 2187 * 1 013 760 = 2 217 093 120 states                          *)
Definition coordof (x : pstt) : int :=
  Uint63.add (Uint63.mul (ctwisti x) nfsi) (fsidx (coordi x)).

Definition ctw (c : int) : int := Uint63.div c nfsi.
Definition cfs (c : int) : int := Uint63.mod c nfsi.

(* and a move steps the two halves apart: the twist by Phase1's table, the    *)
(* flip and slice by Farp1's actfsri, which is the prototype's own fsmove     *)
(* table read three entries to a word.  IT IS NOT IMPORTED HERE ONLY BECAUSE  *)
(* Farp1.vo in this checkout is older than ssrint63.vo and Rocq will not load *)
(* it; the definition below is that function and nothing else, and the two    *)
(* lemmas the step needs are Farp1.acttwi_step and Farp1.actfsr_step.         *)
Variable fsstep : int -> int -> int.

Definition cstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (ctw c) k) nfsi) (fsstep (cfs c) k).

Definition coordP (c : int) (x : pstt) : Prop := c = coordof x.

Definition croot : int := coordof sroot.

(* ---- a member, and the position it stands for ---------------------------- *)

(* A member is three ranks: the eight corners, the eight edges outside the    *)
(* middle layer, and the four inside it.  memb2tab builds the cube they name  *)
(* -- every cubie home, nothing turned or flipped -- as a forty eight entry   *)
(* table.  THAT IS THE BRIDGE between cubies and facelets and it is the one   *)
(* construction this file cannot borrow.                                      *)
Variable memb2tab : memb -> seq nat.

(* and what it builds is a permutation of the forty eight facelets            *)
Hypothesis memb2tab_ok : forall x, tab_ok flast (memb2tab x).

(* and the word the member stands for is the representative undone in front   *)
Definition ptab (x : memb) : seq nat :=
  comp_tab (inv_tab flast (ti2t flast repi)) (memb2tab x).

(* the other way: the three ranks read off a position of H                    *)
Variable tomemb : pstt -> memb.

(* ---- the moves of H, and the bits they move ------------------------------ *)

(* The ten moves of H: the two faces turned any way, the four sides turned    *)
(* twice.  A move is three times the face plus the amount, the faces U R F D  *)
(* L B, so these are the same ten numbers the prototype uses.                 *)
Definition hmvn : seq nat := [:: 0; 1; 2; 9; 10; 11; 4; 7; 13; 16]%N.

Definition hmvi (k : int) : nat := nth 0%N hmvn (to_nat k).

Definition hmv (k : int) : {perm facelet} := nth 1 moves (hmvi k).

Definition nhi : int := 10%uint63.

Definition btmv (k bt : int) : int :=
  PArray.get btmvt (Uint63.add (Uint63.mul bt nhi) k).

(* ---- what the two half tables do to the bits ----------------------------- *)

(* A group is two halves of twelve bits.  mlo rearranges the low half, mhi    *)
(* the high one, msw says whether the two change places, and btmvt says where *)
(* each of the twenty four bits ends up.  THE THREE MUST AGREE, and that is a *)
(* computation: ten moves by twenty four places by four thousand words.       *)

Definition nhalfi : int := 12%uint63.       (* the bits of half a group       *)
Definition nhalfn : nat := to_nat nhalfi.
Definition nloi : int := 4096%uint63.       (* what half a group holds        *)
Definition nlon : nat := to_nat nloi.

(* the bit a move brings to a place: the one of the twenty four that btmvt    *)
(* sends there, found by walking them                                         *)
Definition btsrc (k bt : int) : int :=
  ifold nbitn 0%uint63
    (fun i a => if (btmv k i =? bt)%uint63 then i else a) 0%uint63.

(* where a place of the low half ends up, and one of the high half: in the    *)
(* same half, or in the other one when the move changes them over             *)
Definition dstlo (k j : int) : int :=
  if (PArray.get msw k =? 0)%uint63 then j else Uint63.add j nhalfi.

Definition dsthi (k j : int) : int :=
  if (PArray.get msw k =? 0)%uint63 then Uint63.add j nhalfi else j.

(* THE FIRST CHECK, ten moves by twelve places: what btmvt brings to a place  *)
(* of the low half is a bit of the low half, and what it brings to a place of *)
(* the high half is a bit of the high half.  So a source is always a bit of   *)
(* the half the table was read from.                                          *)
Definition srcok : bool :=
  iter nhn 0%uint63 (fun k =>
    iter nhalfn 0%uint63 (fun j =>
      let s := btsrc k (dstlo k j) in
      let t := btsrc k (dsthi k j) in
      [&& (s <? nhalfi)%uint63, (btmv k s =? dstlo k j)%uint63,
          (nhalfi <=? t)%uint63, (t <? nbiti)%uint63 &
          (btmv k t =? dsthi k j)%uint63])).

(* THE SECOND CHECK, ten moves by twenty four places by four thousand words:  *)
(* a bit either table sets is inside the half, and it is set only when the    *)
(* place btmvt takes it from was set in the word.  Nothing above the twelfth  *)
(* place is ever set, which is what keeps the two halves apart.               *)

(* THE THREE LOOPS ARE THREE DEFINITIONS, and that is not decoration: as one  *)
(* term the walk is a million words wide, and reading a single step off it    *)
(* took a minute and a half -- all of it spent unfolding what was never asked *)
(* for.  A name at each level keeps every step small, and the three lemmas    *)
(* below put the name back into the shape the walk is read in.                *)

(* one place of one move, over the four thousand words a half can hold        *)
Definition halfw (k j s t : int) : bool :=
  iter nlon 0%uint63 (fun w =>
    [&& bit (lomv mlo k w) j ==> ((j <? nhalfi)%uint63 && bit w s) &
        bit (himv mhi k w) j ==> ((j <? nhalfi)%uint63 && bit w t)]).

(* one move, over the twenty four places                                      *)
Definition halfp (k : int) : bool :=
  iter nbitn 0%uint63 (fun j =>
    halfw k j (btsrc k (dstlo k j))
              (Uint63.sub (btsrc k (dsthi k j)) nhalfi)).

Definition halfok : bool := iter nhn 0%uint63 halfp.

Hypothesis hsrc : srcok.
Hypothesis hhalf : halfok.

(* ---- the redundancy rule ------------------------------------------------- *)

(* Which moves may follow which: never the same face twice, and of two        *)
(* opposite faces only one order.  It is a cut and cuts are free here, so     *)
(* nothing below has to know what it says.                                    *)
Variable okmv : int -> int -> bool.

(* ---- the run, and the witnesses ------------------------------------------ *)

Variable dsrch : nat.                     (* where the search gives up        *)
Variable nlev : nat.                      (* how many levels are run          *)

Definition mfin : rmap :=
  run e8num e4bit mpg mgr msw mlo mhi p1 cstep xstep tomemb okmv
      croot sroot dsrch nlev 0 mempty.

Variable wl : seq (int * int * int * seq nat).

(* =========================================================================  *)
(*  WHAT IS STILL OPEN                                                        *)
(* =========================================================================  *)

(* ---- the easy end: three lines of group theory --------------------------- *)

(* The root is the representative, so no moves have been played.              *)
Lemma root_ball : posp sroot \in ball Sset 0.
Proof. by rewrite /posp /sroot /repi -sftiE mulVg ball0; exact: set11. Qed.

(* The root's coordinate is the root's coordinate.                            *)
Lemma coord_root : coordP croot sroot.
Proof. by []. Qed.

(* A table stays a table: Tabi.tabi_ok_comp, once the move tables are known   *)
(* to be tables -- Moves.mtis is [seq t2ti mt | mt <- mtabs] and mtabs_ok     *)
(* says every one of them is.                                                 *)
Lemma mvi_ok k : (to_nat k < nmvn)%N -> tabi_ok flast (mvi k).
Proof.
(* allP would want an eqType and an array is not one, so the walk is read     *)
(* with all_nthP, which takes a default element and no equality at all.       *)
move=> kL; rewrite /mvi.
have szm : seq.size mtis = 18%N by rewrite /mtis seq.size_map size_mtabs.
by apply: (all_nthP sfti mtis_ok); rewrite szm.
Qed.

(* THE ONE GAP IS THE TWISTS.  twP holds of the identity and survives a move  *)
(* -- Phase1.twP1 and Phase1.twPM -- and Diameter.superflipE writes the       *)
(* superflip as Reid's twenty moves, so this is twenty steps and no thought.  *)
(* Better still would be twP of everything in G, by induction over the ball.  *)
Lemma twP_superflip : twP superflip.
Proof.
(* twP of everything in G, and the superflip is in G.  The induction is over  *)
(* the ball, so it needs no word for the superflip at all -- superflipE and   *)
(* its twenty moves never come into it.                                       *)
suff hG : forall g, g \in G -> twP g by apply: hG; exact: superflip_in_G.
move=> g /mem_gen_ball[n]; elim: n g => [g|n ih g].
  by rewrite ball0 inE => /eqP->; exact: twP1.
rewrite /= inE => /orP[/ih//|/mulsgP[b m bB mS ->]].
have mI : m \in moves by move: mS; rewrite inE.
have kL : (index m moves < seq.size moves)%N by rewrite index_mem.
rewrite size_moves in kL.
by rewrite -(nth_index 1 mI) (mvtE kL); apply: twPM => //; apply: ih.
Qed.

(* and the rest of the root is three computations: the table is a table, the  *)
(* cubies are cubies, and the flips are even                                  *)
Lemma root_pok : pstok sroot.
Proof.
rewrite /pstok /sroot /repi sfti_ok /=.
apply/andP; split; first by vm_compute.
rewrite /twPti; apply/andP; split; last by vm_compute.
by rewrite -sftiE; exact: twP_superflip.
Qed.

(* the move, as a permutation and as one of the eighteen                      *)
Lemma mviE k : (to_nat k < nmvn)%N ->
  pt flast (ti2t flast (mvi k)) = nth 1 moves (to_nat k).
Proof.
move=> kL; have kL18 : (to_nat k < 18)%N by [].
have szm : (to_nat k < seq.size mtis)%N.
  by rewrite /mtis seq.size_map size_mtabs.
by rewrite (mvtE kL18) /mvt -ti2t_mtis /mvi (nth_map sfti _ _ szm).
Qed.

(* the cubies stay cubies: a move keeps cubP, and cubti is cubP read off a    *)
(* table                                                                      *)
Lemma cubti_step x k : (to_nat k < nmvn)%N -> tabi_ok flast x -> cubti x ->
  cubti (xstep x k).
Proof.
move=> kL xok cx; have mok := mvi_ok kL.
have cok := tabi_ok_comp n47_small n47_len xok mok.
rewrite (cubtiE cok) -(cubtE cok).
rewrite (ti2t_comp n47_small n47_len xok mok) -(ptM xok mok).
apply: cubP_step; last by rewrite mviE //; apply: mv_Sset.
by rewrite (cubtE xok) -(cubtiE xok).
Qed.

(* THE FLIP PARITY IS THE ONE THING LEFT.  A move does not change it -- it is *)
(* the edge analogue of the twists summing to nought -- and Phase1 carries    *)
(* the invariant it belongs to; Farp1.twPti_step is the same statement.       *)
Lemma fpar_step x k : (to_nat k < nmvn)%N -> tabi_ok flast x -> cubti x ->
  ~~ fpar (coordi x) -> ~~ fpar (coordi (xstep x k)).
Proof.
(* the summary of a position moved is the summary moved, and a move does not  *)
(* touch the parity of the flips -- Coordfs.coordfsM and Phase1.fpar_actfsS   *)
move=> kL xok cx fp.
have mok := mvi_ok kL.
have cok := tabi_ok_comp n47_small n47_len xok mok.
have cg : cubP (pt flast (ti2t flast x)) by rewrite (cubtE xok) -(cubtiE xok).
have cm : cubP (nth 1 moves (to_nat k)) by apply: moves_cubP; apply: mv_Sset.
have -> : coordi (xstep x k) = actfs (coordi x) (nth 1 moves (to_nat k)).
  rewrite (coordiE cok) -(coordtE cok) (coordiE xok) -(coordtE xok).
  rewrite (ti2t_comp n47_small n47_len xok mok) -(ptM xok mok) mviE //.
  by rewrite (coordfsM cg cm).
by rewrite (fpar_actfsS _ (mv_Sset kL)).
Qed.

Lemma xstep_pok x k : (to_nat k < nmvn)%N -> pstok x -> pstok (xstep x k).
Proof.
move=> kL /and3P[xok cx tx]; have mok := mvi_ok kL.
rewrite /pstok; apply/and3P; split.
- exact: (tabi_ok_comp n47_small n47_len xok mok).
- exact: (cubti_step kL xok cx).
move: tx; rewrite /twPti => /andP[tw fp].
apply/andP; split; last exact: (fpar_step kL xok cx fp).
rewrite (ti2t_comp n47_small n47_len xok mok) -(ptM xok mok) mviE //.
have kL18 : (to_nat k < 18)%N by [].
by rewrite (mvtE kL18); apply: twPM.
Qed.

(* ---- one move played is one move ----------------------------------------- *)

(* ti2t_comp turns the composition of tables into the composition of the      *)
(* lists, ptM turns that into the product of the permutations, and            *)
(* Moves.mtabsE says the k-th list is the k-th move.  The only work is        *)
(* carrying tabi_ok through, which is what pstok is for.                      *)
Lemma xstep_pos x k : (to_nat k < nmvn)%N -> pstok x ->
  posp (xstep x k) = posp x * nth 1 moves (to_nat k).
Proof.
move=> kL /and3P[xok _ _]; have mok := mvi_ok kL.
rewrite /posp /xstep (ti2t_comp n47_small n47_len xok mok).
rewrite -(ptM xok mok) mulgA; congr (_ * _).
have kL18 : (to_nat k < 18)%N by [].
have szm : (to_nat k < seq.size mtis)%N.
  by rewrite /mtis seq.size_map size_mtabs.
by rewrite (mvtE kL18) /mvt -ti2t_mtis /mvi (nth_map sfti _ _ szm).
Qed.

(* ---- the coordinate steps with the position ------------------------------ *)

(* THE TWO HALVES ARE LEMMAS THE DEVELOPMENT ALREADY HAS, and each is named   *)
(* here rather than borrowed only because Farp1.vo will not load.             *)
(* Farp1.acttwi_step is the twist half; Farp1.actfsr_step is the other, on    *)
(* the fsmove certificate the lower bound has already run.                    *)

Hypothesis fsstepP : forall x k, (to_nat k < nmvn)%N -> pstok x ->
  fsstep (fsidx (coordi x)) k = fsidx (coordi (xstep x k)).

Lemma twstepP x k : (to_nat k < nmvn)%N -> pstok x ->
  acttwii (ctwisti x) k = ctwisti (xstep x k).
Proof.
(* the twist of a position moved is the twist moved: Phase1's acttwiE turns   *)
(* the table into the action and coordtw_stepP says the coordinate is one.    *)
(* That is where twP is spent, which is why the state carries it.             *)
move=> kL /and3P[xok cx tx].
have kL18 : (to_nat k < 18)%N by [].
have mok := mvi_ok kL.
have cok := tabi_ok_comp n47_small n47_len xok mok.
have tw : twP (pt flast (ti2t flast x)) by move: tx; rewrite /twPti => /andP[].
have hlt : (to_nat (ctwisti x) < ntwist)%N.
  by rewrite (ctwistiE xok) -(ctwisttE xok); apply: coordtw_lt.
rewrite -{1}(to_natK k) acttwiiE (acttwiE hlt kL18).
rewrite (ctwistiE xok) -(ctwisttE xok) -(coordtw_stepP kL18 tw).
rewrite (ctwistiE cok) -(ctwisttE cok).
by rewrite (ti2t_comp n47_small n47_len xok mok) -(ptM xok mok) mviE //
           (mvtE kL18).
Qed.

(* ---- and the packing comes apart again ----------------------------------- *)

(* THE BOUND IS SPELT OUT, not computed: 2187 times a million does not exist  *)
(* in unary.  A twist is under 2 ^ 12 and a flip and slice rank under 2 ^ 20. *)

Lemma nfsi_pow : (to_nat nfsi <= 2 ^ 20)%N.
Proof.
(* an inequality between powers must go through leq_exp2l: left to done it    *)
(* builds 2 ^ 20 in unary and overflows the stack.                            *)
rewrite nfsiE; apply: leq_trans (_ : 2 ^ 11 * 2 ^ 9 <= _)%N.
  by apply: leq_mul.
by rewrite -expnD leq_exp2l.
Qed.

Lemma pow33 : (2 ^ 32 + 2 ^ 20 < 2 ^ 33)%N.
Proof.
have -> : (33 = 32 + 1)%N by [].
by rewrite expnD expn1 muln2 -addnn ltn_add2l ltn_exp2l.
Qed.

Lemma pow33_split : (2 ^ 32 = 2 ^ 12 * 2 ^ 20)%N.
Proof. by rewrite -expnD. Qed.

Lemma ndigits33 : (33 <= ndigits)%N.
Proof. by []. Qed.

Lemma bound33 a b c :
  (a <= 2 ^ 12)%N -> (b <= 2 ^ 20)%N -> (c <= 2 ^ 20)%N ->
  (a * b + c < nwB)%N.
Proof.
move=> h1 h2 h3.
apply: (@ltn_nwB 33 _ ndigits33).
apply: leq_ltn_trans pow33.
by rewrite pow33_split; apply: leq_add; [apply: leq_mul | ].
Qed.

(* the twist of a state, and the rank of its flips and slices, both small     *)
Lemma ctwisti_lt x : tabi_ok flast x -> (to_nat (ctwisti x) < ntwist)%N.
Proof.
by move=> xok; rewrite (ctwistiE xok) -(ctwisttE xok); apply: coordtw_lt.
Qed.

Lemma fsidx_ltx x : tabi_ok flast x -> cubti x ->
  (to_nat (fsidx (coordi x)) < to_nat nfsi)%N.
Proof.
move=> xok cx; apply/nltbP.
rewrite (coordiE xok) -(coordtE xok); apply: fsidx_lt.
by rewrite (cubtE xok) -(cubtiE xok).
Qed.

Lemma coordofE x : tabi_ok flast x -> cubti x ->
  to_nat (coordof x)
  = (to_nat (ctwisti x) * to_nat nfsi + to_nat (fsidx (coordi x)))%N.
Proof.
move=> xok cx.
have h1 : (to_nat (ctwisti x) <= 2 ^ 12)%N.
  by apply: leq_trans (ltnW (ctwisti_lt xok)) _.
have h3 : (to_nat (fsidx (coordi x)) <= 2 ^ 20)%N.
  by apply: leq_trans (ltnW (fsidx_ltx xok cx)) _; apply: nfsi_pow.
have hb := bound33 h1 nfsi_pow h3.
have hm : to_nat (Uint63.mul (ctwisti x) nfsi)
        = (to_nat (ctwisti x) * to_nat nfsi)%N.
  by apply: to_nat_mul; apply: leq_ltn_trans hb; apply: leq_addr.
have ha : (to_nat (Uint63.mul (ctwisti x) nfsi)
           + to_nat (fsidx (coordi x)) < nwB)%N by rewrite hm.
by rewrite /coordof (@to_nat_add _ _ ha) hm.
Qed.

Lemma coord_step c x k : (to_nat k < nmvn)%N -> pstok x ->
  coordP c x -> coordP (cstep c k) (xstep x k).
Proof.
move=> kL px; have /and3P[xok cx _] := px.
rewrite /coordP => ->; rewrite /cstep.
have hfs : (0 < to_nat nfsi)%N by apply: leq_ltn_trans (fsidx_ltx xok cx).
have -> : ctw (coordof x) = ctwisti x.
  apply: to_nat_inj; rewrite to_nat_div (coordofE xok cx).
  by rewrite divnMDl // divn_small ?addn0 //; apply: fsidx_ltx.
have -> : cfs (coordof x) = fsidx (coordi x).
  apply: to_nat_inj; rewrite to_nat_mod (coordofE xok cx).
  by rewrite modnMDl modn_small //; apply: fsidx_ltx.
by rewrite (twstepP kL px) (fsstepP kL px).
Qed.

(* ---- what a member's table is -------------------------------------------  *)

(* The position a member stands for is the superflip undone and the member    *)
(* put back, and that is all pos ever is here.                                *)
Lemma posE x : RowFinal.pos ptab x = superflip^-1 * pt flast (memb2tab x).
Proof.
rewrite /RowFinal.pos /ptab.
rewrite -(ptM (tab_ok_inv sfti_ok) (memb2tab_ok x)).
by rewrite -(ptV sfti_ok) -sftiE.
Qed.

(* ---- a leaf is a member -------------------------------------------------- *)

(* WHAT A LEAF OWES, and there is no proving it here: tomemb is a function    *)
(* this file is handed, so what it does is a fact the instance supplies, like *)
(* the tables.  Both facts carry the same premise -- a distance of nought in  *)
(* the phase one table, which is what says the position is IN H, and only     *)
(* there do three ranks mean anything: outside H the edges are mixed between  *)
(* the outer eight and the middle four and there is no outer permutation to   *)
(* rank.                                                                      *)
(*                                                                            *)
(* The first is the parity invariant of the cube read off the three ranks.    *)
Hypothesis leaf_memb : forall c x, coordP c x -> pstok x ->
  wdist (p1get p1 c) = 0%uint63 -> membok par8 par4 (tomemb x).

(* AND THIS ONE COMES APART.  What a leaf owes is that the three ranks put    *)
(* the position back together -- and once they do, the rest is posE: the      *)
(* member's position is the superflip undone and the member put back, which   *)
(* is what posp already is.                                                   *)
Hypothesis tomemb_tab : forall c x, coordP c x -> pstok x ->
  wdist (p1get p1 c) = 0%uint63 ->
  pt flast (memb2tab (tomemb x)) = pt flast (ti2t flast x).

Lemma leaf_pos c x : coordP c x -> pstok x ->
  wdist (p1get p1 c) = 0%uint63 ->
  RowFinal.pos ptab (tomemb x) = posp x.
Proof. by move=> hc hp h0; rewrite posE (tomemb_tab hc hp h0). Qed.

(* ---- the prepass tables -------------------------------------------------- *)

(* The ten of H are ten of the eighteen: a computation on ten numbers.        *)
Lemma hmv_Sset k : (to_nat k < nhn)%N -> hmv k \in Sset.
Proof.
move=> kL; rewrite /hmv; apply: mv_Sset; rewrite /hmvi.
have hall : all (fun m => (m < 18)%N) hmvn by vm_compute.
by apply: (all_nthP 0%N hall).
Qed.

(* ---- reading a word one bit at a time ------------------------------------ *)

(* The map is written in terms of a word meeting a bit; the tables are        *)
(* written in terms of the bits themselves.  These say the two agree, and     *)
(* say which place of a word is which place of a half.                        *)

Lemma test_bit x b : (b <? digits)%uint63 ->
  ~~ (Uint63.land x (bitof b) =? 0)%uint63 = bit x b.
Proof.
move=> hbd; have hb1 : (1 = one)%uint63 by vm_compute.
apply/idP/idP; last first.
  move=> hx; apply/negP => /neqbP h0.
  have hz : Uint63.land x (bitof b) = 0%uint63 by apply: to_nat_inj.
  have : bit (Uint63.land x (bitof b)) b.
    by rewrite land_spec hx /bitof hb1 bit_onenn // eqxx.
  by rewrite hz bit_0.
apply: contraR => hnb; apply/neqbP.
suff -> : Uint63.land x (bitof b) = 0%uint63 by [].
apply: bit_ext => i; rewrite land_spec bit_0.
have [hid|hid] := boolP (i <? digits)%uint63; last first.
  rewrite bit_M ?andbF //.
  by apply/nlebP; rewrite leqNgt; apply/negP => /nltbP h; case/negP: hid.
rewrite /bitof hb1 bit_onenn //.
by case: eqP => [<-|_]; rewrite ?andbF // (negbTE hnb).
Qed.

(* twelve places are twenty four places, and both are inside a word           *)
Lemma lt_half_digits j : (j <? nhalfi)%uint63 -> (j <? digits)%uint63.
Proof.
move=> h; apply/nltbP; apply: leq_trans (_ : to_nat nhalfi <= _).
  by apply/nltbP.
by apply/nlebP; vm_compute.
Qed.

Lemma lt_half_nbiti j : (j <? nhalfi)%uint63 -> (j <? nbiti)%uint63.
Proof.
move=> h; apply/nltbP; apply: leq_trans (_ : to_nat nhalfi <= _).
  by apply/nltbP.
by apply/nlebP; vm_compute.
Qed.

Lemma nlonE : nlon = 4096%N.
Proof.
have h : (4096 < nwB)%N by apply: (@ltn_nwB 13).
rewrite /nlon; have -> : nloi = Uint63.of_nat 4096 by vm_compute.
by rewrite (@of_natK 4096 h).
Qed.

(* the low half of a word is the word at the places below twelve              *)
Lemma bit_lohalf v i : (i <? nhalfi)%uint63 ->
  bit (Uint63.land v lo12) i = bit v i.
Proof.
move=> hi; rewrite land_spec.
have -> : lo12 = decr (Uint63.lsl one nhalfi) by vm_compute.
by rewrite bit_decr ?hi ?andbT //; vm_compute.
Qed.

(* and the high half is the word twelve places up, masked back to a half      *)
Lemma bit_hihalf v s : (nhalfi <=? s)%uint63 -> (s <? nbiti)%uint63 ->
  bit (Uint63.land (Uint63.lsr v nhalfi) lo12) (Uint63.sub s nhalfi) = bit v s.
Proof.
move=> hs hs2; have hle : (to_nat nhalfi <= to_nat s)%N by apply/nlebP.
rewrite bit_lohalf; last first.
  apply/nltbP; rewrite to_nat_sub ?to_nat_bounded //.
  rewrite -(ltn_add2r (to_nat nhalfi)) subnK //.
  have -> : (to_nat nhalfi + to_nat nhalfi = to_nat nbiti)%N by vm_compute.
  by apply/nltbP.
rewrite bit_lsr.
have he : Uint63.add nhalfi (Uint63.sub s nhalfi) = s by rewrite laddC subK.
rewrite he ifT //; apply/nlebP.
by rewrite to_nat_sub ?leq_subr ?to_nat_bounded.
Qed.

(* a masked word is a half: the check is asked about it and no other word     *)
Lemma lo12_lt v : (Uint63.land v lo12 <? nloi)%uint63.
Proof.
have -> : lo12 = decr (Uint63.lsl one nhalfi) by vm_compute.
rewrite land_power2; last by vm_compute.
have -> : Uint63.lsl one nhalfi = nloi by vm_compute.
by apply/nltbP; rewrite to_nat_mod ltn_mod; have := nlonE; rewrite /nlon => ->.
Qed.

(* ---- reading the checks off, one step at a time -------------------------- *)

(* A name has to be put back into the shape a walk is read in, and it has to  *)
(* be put back BY A REWRITE: given the name, unification takes the walk apart *)
(* word by word and a step that should be free costs minutes.                 *)

Lemma halfokE : halfok = iter nhn 0%uint63 halfp.
Proof. by []. Qed.

Lemma halfpE k : halfp k = iter nbitn 0%uint63 (fun j =>
  halfw k j (btsrc k (dstlo k j))
            (Uint63.sub (btsrc k (dsthi k j)) nhalfi)).
Proof. by []. Qed.

Lemma halfwE k j s t : halfw k j s t = iter nlon 0%uint63 (fun w =>
  [&& bit (lomv mlo k w) j ==> ((j <? nhalfi)%uint63 && bit w s) &
      bit (himv mhi k w) j ==> ((j <? nhalfi)%uint63 && bit w t)]).
Proof. by []. Qed.

(* what the first check says of one move and one place of a half              *)
Lemma srcokP k j : (to_nat k < nhn)%N -> (j <? nhalfi)%uint63 ->
  [&& (btsrc k (dstlo k j) <? nhalfi)%uint63,
      (btmv k (btsrc k (dstlo k j)) =? dstlo k j)%uint63,
      (nhalfi <=? btsrc k (dsthi k j))%uint63,
      (btsrc k (dsthi k j) <? nbiti)%uint63 &
      (btmv k (btsrc k (dsthi k j)) =? dsthi k j)%uint63].
Proof.
move=> hk hj; have hj' : (to_nat j < nhalfn)%N by apply/nltbP.
by have h := iter_at (iter_at hsrc hk) hj'; cbv zeta in h.
Qed.

(* and what the second says of one move, one place and one word               *)
Lemma halfokP k j w : (to_nat k < nhn)%N -> (to_nat j < nbitn)%N ->
  (w <? nloi)%uint63 ->
  [&& bit (lomv mlo k w) j ==>
        ((j <? nhalfi)%uint63 && bit w (btsrc k (dstlo k j))) &
      bit (himv mhi k w) j ==>
        ((j <? nhalfi)%uint63 &&
           bit w (Uint63.sub (btsrc k (dsthi k j)) nhalfi))].
Proof.
move=> hk hj hw; have hw' : (to_nat w < nlon)%N by apply/nltbP.
have h1 := hhalf; rewrite halfokE in h1.
have h2 := iter_at h1 hk; rewrite halfpE in h2.
have h3 := iter_at h2 hj; rewrite halfwE in h3.
exact: iter_at h3 hw'.
Qed.

(* the moved group, with the two halves named                                 *)
Lemma grpmvE k v :
  grpmv msw mlo mhi k v =
    (if (PArray.get msw k =? 0)%uint63
     then Uint63.lor (lomv mlo k (Uint63.land v lo12))
            (Uint63.lsl
               (himv mhi k (Uint63.land (Uint63.lsr v nhalfi) lo12)) nhalfi)
     else Uint63.lor (himv mhi k (Uint63.land (Uint63.lsr v nhalfi) lo12))
            (Uint63.lsl (lomv mlo k (Uint63.land v lo12)) nhalfi)).
Proof. by []. Qed.

(* A CHECK, and a small one: the rearrangement of a group is a permutation    *)
(* of its twenty four bits, and btmvt says which.  It is enough to know it of *)
(* the two twelve bit halves -- ten moves by four thousand entries -- since a *)
(* group is the two halves and the exchange of them.                          *)

(* THE HIGH HALF IS MASKED and that is what makes this hold of every word.    *)
(* Read as v >> 12 alone, a word with a bit above the twenty fourth would     *)
(* land inside ANOTHER move's twelve bits of the table and come back with     *)
(* that move's rearrangement; the mask keeps the read inside this one.        *)
Lemma grpmvP k v bt' : (to_nat k < nhn)%N -> (bt' <? nbiti)%uint63 ->
  ~~ (Uint63.land (grpmv msw mlo mhi k v) (bitof bt') =? 0)%uint63 ->
  exists2 bt, (bt <? nbiti)%uint63 &
    btmv k bt = bt' /\ ~~ (Uint63.land v (bitof bt) =? 0)%uint63.
Proof.
move=> hk hbt hset.
have hbtd : (bt' <? digits)%uint63 := lt_digits hbt.
have hbtn : (to_nat bt' < nbitn)%N := ltn_nbiti hbt.
rewrite test_bit // grpmvE in hset.
(* a bit of the moved low half came from the place btmvt takes it from        *)
have hlo : forall j, (to_nat j < nbitn)%N ->
    bit (lomv mlo k (Uint63.land v lo12)) j ->
    exists2 bt, (bt <? nbiti)%uint63 & btmv k bt = dstlo k j /\ bit v bt.
  move=> j hj hb; have /andP[h1 _] := halfokP hk hj (lo12_lt v).
  have /andP[hj12 hbw] := implyP h1 hb.
  have /and5P[hs1 hs2 _ _ _] := srcokP hk hj12.
  exists (btsrc k (dstlo k j)); first exact: lt_half_nbiti hs1.
  split; first by apply: to_nat_inj; apply/neqbP.
  by rewrite -(bit_lohalf v hs1).
(* and one of the moved high half, twelve places up                           *)
have hhi : forall j, (to_nat j < nbitn)%N ->
    bit (himv mhi k (Uint63.land (Uint63.lsr v nhalfi) lo12)) j ->
    exists2 bt, (bt <? nbiti)%uint63 & btmv k bt = dsthi k j /\ bit v bt.
  move=> j hj hb.
  have /andP[_ h1] := halfokP hk hj (lo12_lt (Uint63.lsr v nhalfi)).
  have /andP[hj12 hbw] := implyP h1 hb.
  have /and5P[_ _ ht1 ht2 _] := srcokP hk hj12.
  have /and5P[_ _ _ _ ht3] := srcokP hk hj12.
  exists (btsrc k (dsthi k j)) => //.
  split; first by apply: to_nat_inj; apply/neqbP.
  by rewrite -(bit_hihalf v ht1 ht2).
(* a half put twelve places up is read twelve places down                     *)
have hshift : forall x, bit (Uint63.lsl x nhalfi) bt' ->
    [/\ (to_nat (Uint63.sub bt' nhalfi) < nbitn)%N,
        Uint63.add (Uint63.sub bt' nhalfi) nhalfi = bt' &
        bit x (Uint63.sub bt' nhalfi)].
  move=> x; rewrite bit_lsl; case: ifP => // hg hb.
  have hgl : (bt' <? nhalfi)%uint63 = false.
    by move: hg; case: (bt' <? nhalfi)%uint63.
  have hge : (nhalfi <=? bt')%uint63.
    by apply/nlebP; rewrite leqNgt; apply: contraFN hgl => h; apply/nltbP.
  split => //; last by rewrite subK.
  rewrite to_nat_sub ?to_nat_bounded //; last by apply/nlebP.
  by apply: leq_ltn_trans (leq_subr _ _) hbtn.
(* four cases: the two halves, and the move changing them over or not         *)
move: hset; case: ifP => hsw hset.
  have hdlo : forall j, dstlo k j = j by move=> j; rewrite /dstlo hsw.
  have hdhi : forall j, dsthi k j = Uint63.add j nhalfi.
    by move=> j; rewrite /dsthi hsw.
  move: hset; rewrite lor_spec => /orP[hb|hb].
    have [bt hbt1 [hbtE hbv]] := hlo _ hbtn hb.
    exists bt => //; split; first by rewrite hbtE hdlo.
    by rewrite (@test_bit v bt (lt_digits hbt1)).
  have [hj hje hb'] := hshift _ hb.
  have [bt hbt1 [hbtE hbv]] := hhi _ hj hb'.
  exists bt => //; split; first by rewrite hbtE hdhi hje.
  by rewrite (@test_bit v bt (lt_digits hbt1)).
have hdlo : forall j, dstlo k j = Uint63.add j nhalfi.
  by move=> j; rewrite /dstlo hsw.
have hdhi : forall j, dsthi k j = j by move=> j; rewrite /dsthi hsw.
move: hset; rewrite lor_spec => /orP[hb|hb].
  have [bt hbt1 [hbtE hbv]] := hhi _ hbtn hb.
  exists bt => //; split; first by rewrite hbtE hdhi.
  by rewrite (@test_bit v bt (lt_digits hbt1)).
have [hj hje hb'] := hshift _ hb.
have [bt hbt1 [hbtE hbv]] := hlo _ hj hb'.
exists bt => //; split; first by rewrite hbtE hdlo hje.
by rewrite (@test_bit v bt (lt_digits hbt1)).
Qed.

(* ---- and what the three tables do to a member ---------------------------- *)

(* A CHECK, and three small ones: a page goes to a page, a group to a group   *)
(* and a bit to a bit.  40320 by ten, 20160 by ten, 24 by ten.                *)
Hypothesis prep_range : forall k pg gr bt, (to_nat k < nhn)%N ->
  inrange pg gr bt -> inrange (pgmv mpg k pg) (grmv mgr k gr) (btmv k bt).

(* AND THE BRIDGE, which is the only thing here about the cube: moving the    *)
(* place moves the member by that move of H.  It is where the page, group and *)
(* bit tables are finally spent.                                              *)
Hypothesis memb2tab_move : forall k pg gr bt, (to_nat k < nhn)%N ->
  inrange pg gr bt ->
  pt flast (memb2tab (unplace e8inv e4of par8 par4
                        (pgmv mpg k pg) (grmv mgr k gr) (btmv k bt)))
  = pt flast (memb2tab (unplace e8inv e4of par8 par4 pg gr bt)) * hmv k.

Lemma prep_move k pg gr bt : (to_nat k < nhn)%N -> inrange pg gr bt ->
  inrange (pgmv mpg k pg) (grmv mgr k gr) (btmv k bt) /\
  RowFinal.pos ptab
    (unplace e8inv e4of par8 par4 (pgmv mpg k pg) (grmv mgr k gr) (btmv k bt))
  = RowFinal.pos ptab (unplace e8inv e4of par8 par4 pg gr bt) * hmv k.
Proof.
move=> kL hr; split; first by apply: prep_range.
by rewrite !posE (memb2tab_move kL hr) mulgA.
Qed.

(* ---- and one more the witnesses ask for ---------------------------------- *)

(* The word a member stands for is a table, which is what makes replaying a   *)
(* witness twenty compositions of a forty eight entry list.                   *)
Lemma ptab_ok x : tab_ok flast (ptab x).
Proof.
apply: Table.tab_ok_comp; last by apply: memb2tab_ok.
by apply: Table.tab_ok_inv; apply: sfti_ok.
Qed.

(* =========================================================================  *)
(*  THE ROW, PUT TOGETHER                                                     *)
(* =========================================================================  *)

(* From here down there is no new mathematics: the run is sound because the   *)
(* nine facts above hold, the empty map is sound because it has no bit set,   *)
(* and the theorem is RowFinal's.                                             *)

Lemma sound_mempty : soundat e8inv e4of par8 par4 (RowFinal.pos ptab) mempty 0.
Proof. by move=> pg gr bt _; rewrite memptyP. Qed.

Lemma mfin_sound : soundat e8inv e4of par8 par4 (RowFinal.pos ptab) mfin nlev.
Proof.
(* THE SECOND OCCURRENCE ONLY.  nlev is the depth reached AND the number of   *)
(* levels run, and rewriting both leaves the run at 0 + nlev where run_sound  *)
(* wants the same n it adds to d.                                             *)
rewrite /mfin -{2}[nlev]add0n.
apply: (run_sound he8 he4 coord_root root_ball root_pok coord_step xstep_pok
                  xstep_pos leaf_memb leaf_pos hmv_Sset grpmvP prep_move).
exact: sound_mempty.
Qed.

Theorem row_within_20_inst : nlev = 20%N ->
  witsok e8inv e4of par8 par4 ptab wl ->
  mfull (mor mfin (wmap wl)) ->
  forall x, membok par8 par4 x -> RowRun.wthn (RowFinal.pos ptab) 20 x.
Proof.
(* NOT ONE OF THESE MAY BE LEFT TO //: what done would evaluate here is the   *)
(* map, all 812 851 200 words of it.                                          *)
move=> hn hw hf x hx.
apply: (row_within_20 he8 he4 ptab_ok _ hw hf hx).
by rewrite -hn; exact: mfin_sound.
Qed.

End Inst.
