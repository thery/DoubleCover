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
(* WHAT IS STILL OPEN is at the bottom, one Admitted lemma each, and each     *)
(* says in its comment what it will take.  Three of them are checks a         *)
(* generated table settles by computation; the rest are the bridge between    *)
(* three ranks and a permutation of facelets, which is the real work.         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
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

(* the phase one coordinate, move by move: twists, flips, slices              *)
Variable mtw mfl msl : arr.

(* and the phase one table itself, chunked like every other big table         *)
Variable p1 : PArray.array arr.

(* ---- the row is the superflip's ------------------------------------------ *)

Definition repi : arr := sfti.

(* ---- the search carries a table ------------------------------------------ *)

(* A position is a forty eight entry table; a move composes it with the       *)
(* move's own table, which Moves.v already carries.                           *)

Definition pstt := arr.

Definition pstok (x : pstt) : bool := tabi_ok flast x.

Definition mvi (k : int) : arr := nth sfti mtis (to_nat k).

Definition xstep (x : pstt) (k : int) : pstt := comp_tabi flast x (mvi k).

Definition sroot : pstt := repi.

(* the word played: the representative undone and what is carried put back    *)
Definition posp (x : pstt) : {perm facelet} :=
  superflip^-1 * pt flast (ti2t flast x).

(* ---- the phase one coordinate -------------------------------------------- *)

(* Kociemba's three: the corner twists, the edge flips, and which four places *)
(* the middle edges are in.  They are packed the way the prototype packs      *)
(* them, and a move is three table reads.                                     *)

Definition ntwi : int := 2187%uint63.
Definition nfli : int := 2048%uint63.
Definition nsli : int := 495%uint63.
Definition nmvi : int := 18%uint63.

Definition ctw (c : int) : int := Uint63.div (Uint63.div c nsli) nfli.
Definition cfl (c : int) : int := Uint63.mod (Uint63.div c nsli) nfli.
Definition csl (c : int) : int := Uint63.mod c nsli.

Definition cpack (tw fl sl : int) : int :=
  Uint63.add (Uint63.mul (Uint63.add (Uint63.mul tw nfli) fl) nsli) sl.

Definition cstep (c k : int) : int :=
  cpack (PArray.get mtw (Uint63.add (Uint63.mul (ctw c) nmvi) k))
        (PArray.get mfl (Uint63.add (Uint63.mul (cfl c) nmvi) k))
        (PArray.get msl (Uint63.add (Uint63.mul (csl c) nmvi) k)).

(* The coordinate OF a position, which is only ever needed at the root: the   *)
(* search steps the coordinate with the table above and never reads it off a  *)
(* position again.                                                            *)
Variable coordof : pstt -> int.

Definition coordP (c : int) (x : pstt) : Prop := c = coordof x.

Definition croot : int := coordof sroot.

(* ---- a member, and the position it stands for ---------------------------- *)

(* A member is three ranks: the eight corners, the eight edges outside the    *)
(* middle layer, and the four inside it.  memb2tab builds the cube they name  *)
(* -- every cubie home, nothing turned or flipped -- as a forty eight entry   *)
(* table.  THAT IS THE BRIDGE between cubies and facelets and it is the one   *)
(* construction this file cannot borrow.                                      *)
Variable memb2tab : memb -> seq nat.

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
Proof.
(* posp sroot = superflip^-1 * superflip = 1, and ball _ 0 is 1.              *)
Admitted.

(* The root's coordinate is the root's coordinate.                            *)
Lemma coord_root : coordP croot sroot.
Proof. by []. Qed.

(* A table stays a table: Tabi.tabi_ok_comp, once the move tables are known   *)
(* to be tables -- Moves.mtis is [seq t2ti mt | mt <- mtabs] and mtabs_ok     *)
(* says every one of them is.                                                 *)
Lemma mvi_ok k : (to_nat k < nmvn)%N -> tabi_ok flast (mvi k).
Proof. Admitted.

Lemma root_pok : pstok sroot.
Proof. Admitted.

Lemma xstep_pok x k : (to_nat k < nmvn)%N -> pstok x -> pstok (xstep x k).
Proof. Admitted.

(* ---- one move played is one move ----------------------------------------- *)

(* ti2t_comp turns the composition of tables into the composition of the      *)
(* lists, ptM turns that into the product of the permutations, and            *)
(* Moves.mtabsE says the k-th list is the k-th move.  The only work is        *)
(* carrying tabi_ok through, which is what pstok is for.                      *)
Lemma xstep_pos x k : (to_nat k < nmvn)%N -> pstok x ->
  posp (xstep x k) = posp x * nth 1 moves (to_nat k).
Proof. Admitted.

(* ---- the coordinate steps with the position ------------------------------ *)

(* THE COORDINATE MOVE TABLES ARE RIGHT: reading the twist, the flip and the  *)
(* slice off a position and stepping them is the same as stepping the         *)
(* position and reading them off.  Three checks, one for each coordinate --   *)
(* 2187, 2048 and 495 entries by eighteen moves -- and then a proof that the  *)
(* three together are the packed coordinate.  Coordfs.v already has the flip  *)
(* and the slice as functions of a permutation.                               *)
Lemma coord_step c x k : (to_nat k < nmvn)%N ->
  coordP c x -> coordP (cstep c k) (xstep x k).
Proof. Admitted.

(* ---- a leaf is a member -------------------------------------------------- *)

(* THE HARD END, and both halves of it are the same fact: a distance of       *)
(* nought in the phase one table means the position is IN H, and only there   *)
(* do three ranks mean anything -- outside H the edges are mixed between the  *)
(* outer eight and the middle four and there is no outer permutation to rank. *)
(*                                                                            *)
(* So each of these two needs, first, that the table's nought is exactly H    *)
(* (which is what the table is for and is a property of the generated data),  *)
(* and then the cubie to facelet bridge again: leaf_memb is the parity        *)
(* invariant of the cube, leaf_pos is that the three ranks put the position   *)
(* back together.                                                             *)
Lemma leaf_memb c x : coordP c x -> pstok x ->
  wdist (p1get p1 c) = 0%uint63 -> membok par8 par4 (tomemb x).
Proof. Admitted.

Lemma leaf_pos c x : coordP c x -> pstok x ->
  wdist (p1get p1 c) = 0%uint63 ->
  RowFinal.pos ptab (tomemb x) = posp x.
Proof. Admitted.

(* ---- the prepass tables -------------------------------------------------- *)

(* The ten of H are ten of the eighteen: a computation on ten numbers.        *)
Lemma hmv_Sset k : (to_nat k < nhn)%N -> hmv k \in Sset.
Proof. Admitted.

(* A CHECK, and a small one: the rearrangement of a group is a permutation    *)
(* of its twenty four bits, and btmvt says which.  It is enough to know it of *)
(* the two twelve bit halves -- ten moves by four thousand entries -- since a *)
(* group is the two halves and the exchange of them.                          *)
Lemma grpmvP k v bt' : (to_nat k < nhn)%N -> (bt' <? nbiti)%uint63 ->
  ~~ (Uint63.land (grpmv msw mlo mhi k v) (bitof bt') =? 0)%uint63 ->
  exists2 bt, (bt <? nbiti)%uint63 &
    btmv k bt = bt' /\ ~~ (Uint63.land v (bitof bt) =? 0)%uint63.
Proof. Admitted.

(* THE OTHER HARD ONE.  It says the page, the group and the bit tables        *)
(* together are one move of H played on the member, and it cannot be checked  *)
(* -- there are nineteen billion members.  It factors into three that can:    *)
(* the page table is the corner permutation moved (40320 by 10), the group    *)
(* table is the pair of outer permutations moved (20160 by 10), the bit table *)
(* is the middle four moved (24 by 10).  What is left is that the three       *)
(* together rebuild the position, which is the cubie to facelet bridge once   *)
(* more.                                                                      *)
Lemma prep_move k pg gr bt : (to_nat k < nhn)%N -> inrange pg gr bt ->
  inrange (pgmv mpg k pg) (grmv mgr k gr) (btmv k bt) /\
  RowFinal.pos ptab
    (unplace e8inv e4of par8 par4 (pgmv mpg k pg) (grmv mgr k gr) (btmv k bt))
  = RowFinal.pos ptab (unplace e8inv e4of par8 par4 pg gr bt) * hmv k.
Proof. Admitted.

(* ---- and one more the witnesses ask for ---------------------------------- *)

(* The word a member stands for is a table, which is what makes replaying a   *)
(* witness twenty compositions of a forty eight entry list.                   *)
Lemma ptab_ok x : tab_ok flast (ptab x).
Proof. Admitted.

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
rewrite /mfin -[nlev]add0n.
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
