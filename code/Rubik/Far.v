(* =========================================================================  *)
(*  Far.v                                                                   *)
(*                                                                            *)
(*  superflip \notin ball Sset depth, assembled.                              *)
(*                                                                            *)
(*  One admit, and it is the computation itself -- everything else is        *)
(*  proved.  Nothing is run here.                                            *)
(*                                                                            *)
(*  WHAT IS BEING ASSEMBLED.  Five files, each proving its own piece:         *)
(*                                                                            *)
(*    Search.v    IDA star is sound                                           *)
(*    Root.v      the first move may be taken in Sroot -- a factor of 9       *)
(*    Coordfs.v   the flip x slice summary is equivariant                     *)
(*    Coordfsi.v  the summary agrees on perms, lists and arrays               *)
(*    Fstab.v     the table's two obligations are two booleans                *)
(*    FsTable.v   a table                                                     *)
(*                                                                            *)
(*  and here they meet: 36 searches of depth droot on arrays, and the theorem.*)
(*                                                                            *)
(*  WHY 36 SEARCHES OF DEPTH droot AND NOT ONE OF DEPTH depth.  ball_root2:   *)
(*  superflip is fixed by all 48 symmetries, so every maneuver is equivalent  *)
(*  to one whose first move is U or U2.  Two first moves instead of eighteen  *)
(*  is a factor of 9, and each of the 36 pairs is an independent search --    *)
(*  one generated file each when the depth makes that worth doing.            *)
(*                                                                            *)
(*  WITH THE PLACEHOLDER TABLE THIS IS BRUTE FORCE.  FsTable.v's table is all *)
(*  zeros, so the heuristic is 0 and searchd is the Toy.v brute force search  *)
(*  -- around 4 . 10 ^ 11 nodes, which is not going to be run.  It is still   *)
(*  the right thing to state: the statement does not change when the real     *)
(*  table arrives, only the time it takes to check.                           *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Toy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* THE ONE LINE TO CHANGE.  Everything below is stated in terms of depth and
   droot, and the eighteen generated files say droot, so setting depth to 10
   or 14 restates the theorem and every piece of it.  Only two things do not
   follow automatically.  First, depth must be at least 2, since ball_root2
   needs depth = droot.+2.  Second, the pieces are compiled, so after
   changing this line remove them -- but NOT with make clean, which would
   also throw away FsData.vo and its six minutes of parsing for nothing.
   Nothing outside the Far family depends on this file, so

       rm -f Far*.vo Far*.vok Far*.vos Far*.glob .coq-native/NRubik_Far*
       make -j18

   rebuilds exactly the twenty files that can have changed.                 *)
Definition depth := 12.
Definition droot := depth.-2.           (* depth = droot.+2                   *)
Definition nroot := 2.                  (* size Sroot                         *)
Definition nmoves := 18.                (* size moves                         *)

(* ---- 1. The heuristic, from the table ------------------------------------ *)

(* Toy.v supplies mtabs, mtis and their lemmas.  When the real run needs its  *)
(* own file those move out of Toy.v and both read them from there.            *)

Definition Dfsd : int -> nat := Dfs fstab.
Definition Dtid : arr -> nat := Dti Dfsd.

(* the two obligations Coordfs.v asks of a table, discharged through Fstab.v  *)
(* by the two boolean checks rather than proved about the table itself        *)
Lemma Dfsd_0 : Dfsd (coordfs 1) = 0.
Proof. by apply: Dfs0_of_check; exact: fstab_check0. Qed.

Lemma Dfsd_step x m : m \in Sset -> Dfsd x <= (Dfsd (actfs x m)).+1.
Proof.
rewrite /Dfsd.
by apply: (DfsStep_of_check fstab_len fstab_def mtabs_ok mtabsE (fstab_checkStep mtabs)).
Qed.

(* ---- 2. What the superflip has to satisfy -------------------------------- *)

(* fixed by the 48 symmetries -- this is what buys the factor of 9.  Sym.v    *)
(* has the conjugation on tables, so this is ptJ plus one comparison of two   *)
(* literal lists per generator of Symg.                                       *)
(* Being fixed by u is a subgroup condition, so it is enough on the three
   generators of Symg, and each of those is SyT/SxT/SmT then ptJ then one
   comparison of two literal tables -- the shape Sym.v's Symg_stab uses.
   The two helpers below are pure view plumbing between x \in 'C[g],
   commute and g ^ x = g; they are what fought, not the mathematics.       *)
Lemma conj_fix_cent (g u : {perm facelet}) : u \in 'C[g] -> g ^ u = g.
Proof. by move=> /cent1P comm; apply/conjg_commute/commute_sym. Qed.

Lemma cent_conj_fix (g u : {perm facelet}) : g ^ u = g -> u \in 'C[g].
Proof. by move=> guEg; apply/cent1P; rewrite /commute [RHS]conjgC guEg. Qed.

(* !inE over-rewrites here and leaves a shape cent_conj_fix cannot see;
   5!inE stops at the three generators.                                     *)
Lemma superflipJ u : u \in Symg -> superflip ^ u = superflip.
Proof.
move=> uS; apply: conj_fix_cent; move: uS; apply: subsetP.
rewrite gen_subG; apply/subsetP => x; rewrite 5!inE.
case/orP=> [/orP[]|] /eqP->; apply: cent_conj_fix.
- by rewrite sftabE SyT ptJ; [congr pt; vm_compute | by vm_compute..].
- by rewrite sftabE SxT ptJ; [congr pt; vm_compute | by vm_compute..].
by rewrite sftabE SmT ptJ; [congr pt; vm_compute | by vm_compute..].
Qed.

(* not solved, and not one move from solved: one and eighteen comparisons of  *)
(* tables, through pt_eq1 of Tsearch.v                                        *)
Lemma superflip_neq1 : superflip != 1.
Proof. by rewrite sftabE pt_eq1 ?sftab_ok //; vm_compute. Qed.

Lemma superflip_move_neq1 m : m \in moves -> superflip * m != 1.
Proof.
move=> mM; have [mt mtM ->] : exists2 mt, mt \in mtabs & m = pt 47 mt.
  by move: mM; rewrite mtabsE => /mapP[mt mtM ->]; exists mt.
have mtok : tab_ok 47 mt by apply: (allP mtabs_ok).
rewrite sftabE (ptM sftab_ok mtok) pt_eq1 ?tab_ok_comp //.
have hall : all (fun mt => comp_tab sftab mt != id_tab 47) mtabs
  by vm_compute.
by apply: (allP hall).
Qed.

(* ---- 3. The 36 prefixes, as arrays ---------------------------------------- *)

(* Indexed by position rather than by membership: arr is not an eqType, so    *)
(* a \in prefixes does not even typecheck, whereas i \in iota 0 18 does.      *)
Definition prefixi (i j : nat) : arr :=
  comp_tabi 47 (comp_tabi 47 sfti (nth sfti mtis i)) (nth sfti mtis j).

Lemma prefixi_ok i j : i < nmoves -> j < nmoves -> tabi_ok 47 (prefixi i j).
Proof.
have hm k : k < nmoves -> tabi_ok 47 (nth sfti mtis k).
  by move=> kL; apply: (all_nthP sfti mtis_ok); rewrite /mtis size_map.
move=> iL jL; rewrite /prefixi.
apply: (tabi_ok_comp n47_small n47_len); last exact: hm.
by apply: (tabi_ok_comp n47_small n47_len); [exact: sfti_ok | exact: hm].
Qed.

(* what the array at (i, j) is, as a permutation: ti2t_comp then ptM, with    *)
(* sftiE and mtisE for the three factors                                      *)
Lemma mtis_ok_nth k : k < nmoves -> tabi_ok 47 (nth sfti mtis k).
Proof. by move=> kL; apply: (all_nthP sfti mtis_ok); rewrite /mtis size_map. Qed.

Lemma nth_movesE k : k < nmoves -> nth 1 moves k = pt 47 (ti2t 47 (nth sfti mtis k)).
Proof.
move=> kL; rewrite mtisE (nth_map (ti2t 47 sfti)) ?size_map ?(nth_map sfti) //;
by rewrite /mtis size_map.
Qed.

Lemma prefixiE i j :
  i < nmoves -> j < nmoves ->
  pt 47 (ti2t 47 (prefixi i j)) = superflip * nth 1 moves i * nth 1 moves j.
Proof.
move=> iL jL; rewrite !nth_movesE // sftiE /prefixi.
rewrite (ti2t_comp n47_small n47_len) ?mtis_ok_nth //;
  last by apply: (tabi_ok_comp n47_small n47_len); [exact: sfti_ok|exact: mtis_ok_nth].
rewrite (ti2t_comp n47_small n47_len) ?sfti_ok ?mtis_ok_nth //.
rewrite -[LHS]ptM //.
- congr (_ * _); rewrite -[LHS]ptM //.
  by apply: mtis_ok_nth.
- apply: tab_ok_comp => //.
  by apply: mtis_ok_nth.
by apply: mtis_ok_nth.
Qed.

(* Sroot is the first two moves, which is why iota 0 nroot is the right index *)
(* range for the first factor.  Both of these are size moves = 18 and one     *)
(* nthP; they are separate lemmas because arr is not an eqType and the        *)
(* indices, not the arrays, are what the computation below is quantified on.  *)
Lemma size_moves : size moves = nmoves.
Proof. by []. Qed.

Lemma SrootE : Sroot = take nroot moves.
Proof. by []. Qed.

Lemma moves_index m : m \in moves -> exists2 j, j < nmoves & nth 1 moves j = m.
Proof.
by move=> /(nthP (1 : {perm facelet}))[j jL jE]; exists j; rewrite // -size_moves.
Qed.

Lemma root_index m : m \in Sroot -> exists2 i, i < nroot & nth 1 moves i = m.
Proof. by rewrite /Sroot !inE => /orP[]/eqP->; [exists 0%N | exists 1%N]. Qed.

(* ---- 4. The computation, and where it lives ------------------------------ *)

(* What is left is 36 searches of depth droot -- two root moves times eighteen
   second moves -- and they are independent.  They are NOT here: one
   generated file per second move proves its own pair, and Farmain.v glues
   the eighteen together and finishes the theorem.  See Farmain.v.

   The split is by second move rather than by pair so that each file is one
   vm_compute over two searches: eighteen files rather than thirty six, and
   each still small enough to check on its own core.                        *)
