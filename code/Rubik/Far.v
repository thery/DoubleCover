(* =========================================================================  *)
(*  Far.v -- superflip \notin ball Sset depth, assembled.                     *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Ball Table Tsearch Tabi Rubik333 Sym Root Coordfs Coordfsi
        Fstab FsTable Diameter Moves Fsmain Searchr Redun Searchir.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* THE ONE LINE TO CHANGE.  Everything below is stated in terms of depth and  *)
(* droot, and the eighteen generated files say droot, so setting depth to 10  *)
(* or 14 restates the theorem and every piece of it.  Only two things do not  *)
(* follow automatically.  First, depth must be at least 2, since ball_root2   *)
(* needs depth = droot.+2.  Second, the pieces are compiled, so after         *)
(* changing this line remove them -- but NOT with make clean, which would     *)
(* also throw away FsData.vo and its six minutes of parsing for nothing.      *)
(* Nothing outside the Far family depends on this file, so                    *)
(*                                                                            *)
(*     ulimit -s unlimited                                                    *)
(*     rm -f Far*.vo Far*.vok Far*.vos Far*.glob .coq-native/NRubik_Far*      *)
(*     make -j18                                                              *)
(*                                                                            *)
(* rebuilds exactly the twenty files that can have changed.                   *)
(*                                                                            *)
(* THE ulimit IS NOT OPTIONAL.  FsData.v is a 2 097 152 element seq int       *)
(* literal, and loading or native compiling a list that deep recurses past    *)
(* the default 8 MB stack; without it the build simply fails.                 *)
(*                                                                            *)
(* On -j: count the jobs, not the cores.  The certificate is sixteen files    *)
(* and the search is eighteen, both just above the twelve physical cores of   *)
(* the old Xeon, so -j12 pays two waves where -j18 pays one.  Drop back to    *)
(* -j12 if memory complains -- every worker loads the table, about a          *)
(* gigabyte each.                                                             *)
Definition depth := 15.
Definition droot := depth.-2.           (* depth = droot.+2                   *)
Definition nroot := 2.                  (* size Sroot                         *)
Definition nmoves := 18.                (* size moves                         *)

(* THE SECOND MOVES A PIECE IS STILL NEEDED FOR.  The first move is on the U  *)
(* face, whose fcpos is 0, and a second move on that same face merges with it *)
(* into one move -- a shorter maneuver, which Searchr.searchr_root2m sends to *)
(* a smaller depth instead of to a piece.  So j = 0, 1, 2 are dropped and     *)
(* fifteen files remain.  The three that turn the D face are NOT dropped:     *)
(* see the header of mkrunp1.sh.                                              *)
Definition jsnd := [seq j <- iota 0 nmoves | fcpos j != 0%N].

(* ---- 1. The heuristic, from the table ------------------------------------ *)

(* Moves.v supplies mtabs, mtis, sftab, sfti and their lemmas.  They used to  *)
(* sit in Toy.v and the real run had to import the toy to reach them; they    *)
(* have their own file now and nothing here depends on Toy.v.                 *)

Definition Dfsd : int -> nat := Dfs fstab.
Definition Dtid : arr -> nat := Dti Dfsd.

(* the two obligations Coordfs.v asks of a table, discharged through Fstab.v  *)
(* by the two boolean checks rather than proved about the table itself        *)
Lemma Dfsd_0 : Dfsd (coordfs 1) = 0.
Proof. by apply: Dfs0_of_check; exact: fstab_check0. Qed.

Lemma Dfsd_step x m : m \in Sset -> Dfsd x <= (Dfsd (actfs x m)).+1.
Proof.
rewrite /Dfsd.
by apply: (DfsStep_of_check fstab_len fstab_def mtabs_ok mtabsE fstab_checkStep).
Qed.

(* ---- 2. What the superflip has to satisfy -------------------------------- *)

(* fixed by the 48 symmetries -- this is what buys the factor of 9.  Sym.v    *)
(* has the conjugation on tables, so this is ptJ plus one comparison of two   *)
(* literal lists per generator of Symg.                                       *)
(* Being fixed by u is a subgroup condition, so it is enough on the three     *)
(* generators of Symg, and each of those is SyT/SxT/SmT then ptJ then one     *)
(* comparison of two literal tables -- the shape Sym.v's Symg_stab uses.      *)
(* The two helpers below are pure view plumbing between x \in 'C[g],          *)
(* commute and g ^ x = g; they are what fought, not the mathematics.          *)
Lemma conj_fix_cent (g u : {perm facelet}) : u \in 'C[g] -> g ^ u = g.
Proof. by move=> /cent1P comm; apply/conjg_commute/commute_sym. Qed.

Lemma cent_conj_fix (g u : {perm facelet}) : g ^ u = g -> u \in 'C[g].
Proof. by move=> guEg; apply/cent1P; rewrite /commute [RHS]conjgC guEg. Qed.

(* !inE over-rewrites here and leaves a shape cent_conj_fix cannot see;       *)
(* 5!inE stops at the three generators.                                       *)
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

(* ---- 3. The 36 prefixes, as arrays ----------------------------------------*)

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

(* What is left is 36 searches of depth droot -- two root moves times         *)
(* eighteen second moves -- and they are independent. They are NOT here: one  *)
(* generated file per second move proves its own pair, and a master file      *)
(* glues the eighteen together and finishes the theorem.                      *)
(*                                                                            *)
(* The split is by second move rather than by pair so that each file is one   *)
(* vm_compute over two searches: eighteen files rather than thirty six, and   *)
(* each still small enough to check on its own core.                          *)

(* ---- 5. The reduced search, and why the guard stops at the prefix ---------*)

(* THE SENTINEL p IS NOT A SHORTCUT, it is forced.  ball_root2 conjugates by  *)
(* the 48 symmetries to push the first move into Sroot, which is worth a      *)
(* factor 9; but conjugation PERMUTES THE FACES, and while the same-face half *)
(* of the guard survives that, the opposite-pair ordering half (smaller face  *)
(* index first) does not.  So the pair (m1, m2) ball_root2 hands back cannot  *)
(* be assumed guard respecting, and the continuation search must start at the *)
(* sentinel -- the guard then applies from the fourth move on.                *)
(* The arithmetic says this is the right trade anyway: symmetry x sentinel is *)
(* 9 x 72 = 648, against 1 x 131 for dropping ball_root2 and using            *)
(* searchr_split2 instead.  Symmetry is worth more than the two levels of     *)
(* guard, by a factor of five.                                                *)
(* ---- 2bis. The symmetry-strengthened heuristic --------------------------- *)

(* Far.v used to prune with ONE lookup in the flip x slice table.  It now     *)
(* prunes with the MAX over five symmetry views of the SAME table.  A max of  *)
(* admissible heuristics is admissible, and it prunes far harder: measured in *)
(* bench/SymHeur.v at depth 9, 94 762 nodes with one view against 4 918 with  *)
(* five, and on the old Xeon at depth 12 the Far phase went from 21m07 CPU to *)
(* 6m40 -- 3.16x.  No new table is involved.                                  *)
(*                                                                            *)
(* Everything is stated over `viewst`, a list of TABLES, and `views` is its   *)
(* image under pt.  Defining views that way rather than as a literal list of  *)
(* permutations is what keeps the proofs short: no lemma ever has to unfold a *)
(* concrete 48 entry table, which is fatal (simpl on these does not return).  *)

Definition conjt (s t : seq nat) : seq nat := comp_tab (inv_tab 47 s) (comp_tab t s).

Definition conji (s : seq nat) (a : arr) : arr :=
  comp_tabi 47 (t2ti 47 (inv_tab 47 s)) (comp_tabi 47 a (t2ti 47 s)).

Definition viewst : seq (seq nat) :=
  [:: id_tab 47; Sytab; Sxtab; comp_tab Sxtab Sytab; comp_tab Sytab Sxtab].

Definition views : seq {perm facelet} := [seq pt 47 s | s <- viewst].

Definition hsymp (g : {perm facelet}) : nat := \max_(u <- views) hfs Dfsd (g ^ u).
Definition Dsymt (t : seq nat)        : nat := \max_(s <- viewst) Dt Dfsd (conjt s t).
(* THE COMPUTATIONAL FORM -- this is what the search actually runs, and what  *)
(* was measured at 6m40 CPU on the Xeon.  The conjugating tables are closed   *)
(* literals so the VM shares them; the \max_(s <- viewst) form (Dsymt) is the *)
(* one the PROOFS are stated over, and DsymdE bridges the two.  Running the   *)
(* search directly over viewst does NOT evaluate -- t2ti (inv_tab s) would be *)
(* rebuilt at every node.                                                     *)
Definition syti     : arr := Eval vm_compute in t2ti 47 Sytab.
Definition sxti     : arr := Eval vm_compute in t2ti 47 Sxtab.
Definition syti_inv : arr := Eval vm_compute in inv_tabi 47 syti.
Definition sxti_inv : arr := Eval vm_compute in inv_tabi 47 sxti.

(* NOTE the bracketing: si . (a . s), matching conji. Written (si . a) . s it *)
(* computes the same thing but every proof below then needs associativity of  *)
(* comp_tab, which is not worth a single lemma.                               *)
Definition conjy (a : arr) : arr := comp_tabi 47 syti_inv (comp_tabi 47 a syti).
Definition conjx (a : arr) : arr := comp_tabi 47 sxti_inv (comp_tabi 47 a sxti).

Definition Dsymd (a : arr) : nat :=
  maxn (maxn (Dtid a) (Dtid (conjy a)))
       (maxn (Dtid (conjx a))
             (maxn (Dtid (conjy (conjx a))) (Dtid (conjx (conjy a))))).

(* ---- the views are symmetries -------------------------------------------  *)

Lemma viewst_ok : all (tab_ok 47) viewst.
Proof.
apply/allP => s; rewrite /viewst !inE.
case/or4P=> [/eqP->|/eqP->|/eqP->|/orP[/eqP->|/eqP->]].
- exact: tab_ok_id.
- exact: okSy.
- exact: okSx.
- by apply: tab_ok_comp; [exact: okSx | exact: okSy].
by apply: tab_ok_comp; [exact: okSy | exact: okSx].
Qed.

Lemma tab_ok_conjt s t : tab_ok 47 s -> tab_ok 47 t -> tab_ok 47 (conjt s t).
Proof.
by move=> sok tok; rewrite /conjt; apply: tab_ok_comp;
   [apply: tab_ok_inv | apply: tab_ok_comp].
Qed.

(* the ptM rewrite has to happen in a SMALL goal. Inline in views_Symg, where *)
(* the goal carries the concrete tables, it does not return.                  *)
Lemma pt_comp_Symg t1 t2 : tab_ok 47 t1 -> tab_ok 47 t2 ->
  pt 47 t1 \in Symg -> pt 47 t2 \in Symg -> pt 47 (comp_tab t1 t2) \in Symg.
Proof. by move=> o1 o2 h1 h2; rewrite -(ptM o1 o2); apply: groupM. Qed.

Lemma pt_Sy_Symg : pt 47 Sytab \in Symg.
Proof. by rewrite -SyT; apply: mem_gen; rewrite !inE eqxx. Qed.

Lemma pt_Sx_Symg : pt 47 Sxtab \in Symg.
Proof. by rewrite -SxT; apply: mem_gen; rewrite !inE eqxx orbT. Qed.

Lemma views_Symg u : u \in views -> u \in Symg.
Proof.
case/mapP => s sV ->.
move: sV; rewrite /viewst !inE.
case/or4P=> [/eqP->|/eqP->|/eqP->|/orP[/eqP->|/eqP->]].
- by rewrite pt1 group1.
- exact: pt_Sy_Symg.
- exact: pt_Sx_Symg.
- by apply: pt_comp_Symg;
     [exact: okSx | exact: okSy | exact: pt_Sx_Symg | exact: pt_Sy_Symg].
by apply: pt_comp_Symg;
   [exact: okSy | exact: okSx | exact: pt_Sy_Symg | exact: pt_Sx_Symg].
Qed.

(* ---- the two certificate obligations, which is the whole mathematics ----- *)

Lemma hsymp0 : hsymp 1 = 0.
Proof.
rewrite /hsymp; apply/eqP; rewrite -leqn0.
apply/bigmax_leqP_seq => u _ _.
by rewrite conj1g (hfs0 Dfsd_0).
Qed.

(* view-wise: (g*m)^u = g^u * m^u, and m^u is again a move because Symg       *)
(* stabilises Sset -- that is Sym.Symg_stab, already proved.  Then max is     *)
(* monotone.  No new mathematics.                                             *)
Lemma hsympS g m : m \in Sset -> hsymp g <= (hsymp (g * m)).+1.
Proof.
move=> mS; rewrite /hsymp.
apply/bigmax_leqP_seq => u uV _.
have uS : u \in Symg by apply: views_Symg.
have muS : m ^ u \in Sset by rewrite -(Symg_stab uS) memJ_conjg.
apply: leq_trans (_ : (hfs Dfsd (g ^ u * m ^ u)).+1 <= _).
  exact: (hfsS Dfsd_step).
rewrite -conjMg ltnS.
exact: (leq_bigmax_seq u uV isT).
Qed.

(* ---- arrays down to tables down to permutations -------------------------- *)

Lemma tabi_ok_conji s a :
  tab_ok 47 s -> tabi_ok 47 a -> tabi_ok 47 (conji s a).
Proof.
move=> sok aok.
have si : tabi_ok 47 (t2ti 47 s) by apply: (tabi_ok_t2ti n47_small n47_len).
have sv : tabi_ok 47 (t2ti 47 (inv_tab 47 s))
  by apply: (tabi_ok_t2ti n47_small n47_len); apply: tab_ok_inv.
by apply: (tabi_ok_comp n47_small n47_len) => //;
   apply: (tabi_ok_comp n47_small n47_len).
Qed.

Lemma ti2t_conji s a :
  tab_ok 47 s -> tabi_ok 47 a -> ti2t 47 (conji s a) = conjt s (ti2t 47 a).
Proof.
move=> sok aok.
have si : tabi_ok 47 (t2ti 47 s) by apply: (tabi_ok_t2ti n47_small n47_len).
have sv : tabi_ok 47 (t2ti 47 (inv_tab 47 s))
  by apply: (tabi_ok_t2ti n47_small n47_len); apply: tab_ok_inv.
have e1 : ti2t 47 (t2ti 47 s) = s by apply: (ti2t_t2ti n47_small n47_len).
have e2 : ti2t 47 (t2ti 47 (inv_tab 47 s)) = inv_tab 47 s
  by apply: (ti2t_t2ti n47_small n47_len); apply: tab_ok_inv.
rewrite /conji /conjt (ti2t_comp n47_small n47_len) //; last first.
  by apply: (tabi_ok_comp n47_small n47_len).
by rewrite (ti2t_comp n47_small n47_len) // e1 e2.
Qed.

Lemma hsympE t : tab_ok 47 t -> hsymp (pt 47 t) = Dsymt t.
Proof.
move=> tok; rewrite /hsymp /Dsymt /views big_map.
apply: eq_big_seq => s sV.
have sok : tab_ok 47 s by apply: (allP viewst_ok).
by rewrite (ptJ tok sok) hfsE // tab_ok_conjt.
Qed.

(* the literal tables, related back to their table forms.  syti and friends   *)
(* are Eval vm_compute in, hence closed literals, so nothing matches them     *)
(* syntactically until these fire.                                            *)
Lemma sytiE     : syti     = t2ti 47 Sytab.               Proof. by vm_compute. Qed.
Lemma sxtiE     : sxti     = t2ti 47 Sxtab.               Proof. by vm_compute. Qed.
Lemma syti_invE : syti_inv = t2ti 47 (inv_tab 47 Sytab).  Proof. by vm_compute. Qed.
Lemma sxti_invE : sxti_inv = t2ti 47 (inv_tab 47 Sxtab).  Proof. by vm_compute. Qed.

Lemma conjyE a : conjy a = conji Sytab a.
Proof. by rewrite /conjy /conji sytiE syti_invE. Qed.

Lemma conjxE a : conjx a = conji Sxtab a.
Proof. by rewrite /conjx /conji sxtiE sxti_invE. Qed.

(* conjugating by the identity, and composing two conjugations.  Both are     *)
(* trivial on PERMUTATIONS (conjg1, conjgM), so transport through pt rather   *)
(* than fight comp_tab and inv_tab directly -- pt_inj_in is what Redun's      *)
(* uniq_moves already uses for exactly this.                                  *)
Lemma conjt_id t : tab_ok 47 t -> conjt (id_tab 47) t = t.
Proof.
move=> tok; apply: pt_inj_in => //; first by apply: tab_ok_conjt (tab_ok_id 47) tok.
by rewrite -(ptJ tok (tab_ok_id 47)) pt1 conjg1.
Qed.

Lemma conjtM s1 s2 t : tab_ok 47 s1 -> tab_ok 47 s2 -> tab_ok 47 t ->
  conjt s2 (conjt s1 t) = conjt (comp_tab s1 s2) t.
Proof.
move=> o1 o2 tok.
have oc1 : tab_ok 47 (conjt s1 t) by apply: tab_ok_conjt.
apply: pt_inj_in.
- by apply: tab_ok_conjt.
- by apply: tab_ok_conjt => //; apply: tab_ok_comp.
rewrite -(ptJ oc1 o2) -(ptJ tok o1) -(ptJ tok (tab_ok_comp o1 o2)).
by rewrite -(ptM o1 o2) conjgM.
Qed.

(* The computational Dsymd equals the \max_(s <- viewst) form the proofs are  *)
(* stated over.  Same five views:                                             *)
(*                                                                            *)
(*   a                <->  s = id_tab 47      ->  g                           *)
(*   conjy a          <->  s = Sytab          ->  g ^ Sy                      *)
(*   conjx a          <->  s = Sxtab          ->  g ^ Sx                      *)
(*   conjy (conjx a)  <->  s = Sxtab * Sytab  ->  g ^ (Sx * Sy)               *)
(*   conjx (conjy a)  <->  s = Sytab * Sxtab  ->  g ^ (Sy * Sx)               *)
(*                                                                            *)
(* THE TACTIC THAT MAKES THIS POSSIBLE IS lock.  Every rewrite here scans the *)
(* whole goal for its pattern, and every subterm it tests against is a conjt  *)
(* or a maxn over concrete 48 entry tables -- so the FAILED matches, not the  *)
(* successful one, are what cost.  Plain `rewrite (conjtM ...)` does not      *)
(* return; locking the other occurrences first makes it 10 ms:                *)
(*                                                                            *)
(*     rewrite {-3 4}[conjt]lock (conjtM okSx okSy aok) -lock.                *)
(*                                                                            *)
(* Same for maxn at the end.  Note also `5!big_cons` with an exact count      *)
(* rather than `!`, and never /= anywhere near these goals.                   *)
Lemma DsymdE a : tabi_ok 47 a -> Dsymd a = Dsymt (ti2t 47 a).
Proof.
move=> aok.
have oky  : tabi_ok 47 (conjy a).
  by rewrite conjyE; apply: tabi_ok_conji; [exact: okSy | exact: aok].
have okx  : tabi_ok 47 (conjx a).
  by rewrite conjxE; apply: tabi_ok_conji; [exact: okSx | exact: aok].
have okxy : tabi_ok 47 (conjx (conjy a)).
  by rewrite conjxE; apply: tabi_ok_conji; [exact: okSx | exact: oky].
have okyx : tabi_ok 47 (conjy (conjx a)).
  by rewrite conjyE; apply: tabi_ok_conji; [exact: okSy | exact: okx].
rewrite /Dsymt /viewst 5!big_cons big_nil.
rewrite {-5}[maxn]lock maxn0 -lock /Dsymd /Dtid.
rewrite !(DtiE Dfsd); [ | done | done | done | done | done].
rewrite (ti2t_conji okSx aok).
rewrite (ti2t_conji okSy aok).
rewrite (ti2t_conji okSy okx) (ti2t_conji okSx oky).
rewrite (ti2t_conji okSx aok) (ti2t_conji okSy aok).
rewrite {-3 4}[conjt]lock (conjtM okSx okSy aok) -lock.
rewrite {-4 5}[conjt]lock (conjtM okSy okSx aok) -lock.
rewrite {-5}[conjt]lock (conjt_id aok) -lock.
rewrite {-5 6}[maxn]lock maxnA -lock.
by [].
Qed.

(* ---- the assembly, exactly as far_of_searchir ---------------------------- *)

Lemma far_of_searchsym d a :
  tabi_ok 47 a ->
  searchir 47 mtis Dsymd nfcube oppf fcpos d a nfcube = false ->
  pt 47 (ti2t 47 a) \notin ball Sset d.
Proof.
move=> aok sE.
have fcE : forall k, k < seq.size [seq ti2t 47 mt | mt <- mtis] ->
    fcube (pt 47 (nth [::] [seq ti2t 47 mt | mt <- mtis] k)) = fcpos k.
  move=> k; rewrite seq.size_map => kL.
  have kL' : k < nmoves by rewrite /mtis seq.size_map in kL.
  by rewrite (nth_map sfti) // -nth_movesE // fcpos_moves.
have mtsok : all (tab_ok 47) [seq ti2t 47 mt | mt <- mtis].
  by rewrite all_map; exact: mtis_ok.
apply: (searchrN Sset_inv hsymp0 hsympS
                 fcube_ltS oppfK fcube_close fcube_comm).
have e1 : searchir 47 mtis Dsymd nfcube oppf fcpos d a nfcube
        = searchtr 47 [seq ti2t 47 mt | mt <- mtis] Dsymt nfcube oppf fcpos
                   d (ti2t 47 a) nfcube.
  by apply: (searchirE n47_small n47_len mtis_ok DsymdE).
have e2 : searchtr 47 [seq ti2t 47 mt | mt <- mtis] Dsymt nfcube oppf fcpos
                   d (ti2t 47 a) nfcube
        = searchr [seq pt 47 mt | mt <- [seq ti2t 47 mt | mt <- mtis]]
                  hsymp nfcube fcube oppf d (pt 47 (ti2t 47 a)) nfcube.
  by apply: (searchtrE mtsok nfcube oppf hsympE fcE).
by rewrite mtisE -e2 -e1.
Qed.

Lemma far_of_searchir d a :
  tabi_ok 47 a ->
  searchir 47 mtis Dtid nfcube oppf fcpos d a nfcube = false ->
  pt 47 (ti2t 47 a) \notin ball Sset d.
Proof.
move=> aok sE.
have fcE : forall k, k < seq.size [seq ti2t 47 mt | mt <- mtis] ->
    fcube (pt 47 (nth [::] [seq ti2t 47 mt | mt <- mtis] k)) = fcpos k.
  move=> k; rewrite seq.size_map => kL.
  have kL' : k < nmoves by rewrite /mtis seq.size_map in kL.
  by rewrite (nth_map sfti) // -nth_movesE // fcpos_moves.
have mtsok : all (tab_ok 47) [seq ti2t 47 mt | mt <- mtis].
  by rewrite all_map; exact: mtis_ok.
apply: (searchrN Sset_inv (hfs0 Dfsd_0) (hfsS Dfsd_step)
                 fcube_ltS oppfK fcube_close fcube_comm).
(* e1 and e2 are stated FULLY INSTANTIATED on purpose.  Written as            *)
(* rewrite -(searchtrE ...) the backward rewrite has to unify                 *)
(* [seq pt 47 mt | mt <- ?mts] against the concrete mtis, which builds        *)
(* eighteen permutations and never returns -- a timeout, not a type error.    *)
(* Given as closed equations both rewrites are syntactic and it takes 1.3 s.  *)
have e1 : searchir 47 mtis Dtid nfcube oppf fcpos d a nfcube
        = searchtr 47 [seq ti2t 47 mt | mt <- mtis] (Dt Dfsd) nfcube oppf fcpos
                   d (ti2t 47 a) nfcube.
  by apply: (searchirE n47_small n47_len mtis_ok (DtiE Dfsd)).
have e2 : searchtr 47 [seq ti2t 47 mt | mt <- mtis] (Dt Dfsd) nfcube oppf fcpos
                   d (ti2t 47 a) nfcube
        = searchr [seq pt 47 mt | mt <- [seq ti2t 47 mt | mt <- mtis]]
                  (hfs Dfsd) nfcube fcube oppf d (pt 47 (ti2t 47 a)) nfcube.
  by apply: (searchtrE mtsok nfcube oppf (hfsE Dfsd) fcE).
by rewrite mtisE -e2 -e1.
Qed.

(* ---- 3ter. The same search, CARRYING the coordinate ---------------------- *)

(* searchir spends ~84% of a node rebuilding the coordinate: comp_tabi        *)
(* composes 48 entries and then Dtid inverts the array and repacks all 24     *)
(* bits from scratch. Measured (fresh coqc, two sizes, differenced) 66.2      *)
(* us/node against 5.4 us for the composition alone; with actf, 19.8 us. actf *)
(* IS the coordinate transition and checkStep already certifies it, so the    *)
(* coordinate can be carried and stepped instead of recomputed. The array is  *)
(* still composed, for the goal test only.                                    *)

(* EVALUATED ONCE. mdataf mtabs is an application of a constant to an         *)
(* argument, so the VM cannot share it: written directly here it is rebuilt   *)
(* on every call -- eighteen mdatf, each a twelve entry array plus a twelve   *)
(* bit pack -- about 13.5 times per node. As a closed Definition it is a      *)
(* literal and costs nothing per node.                                        *)
Definition mdatafd : seq mdatf := Eval vm_compute in mdataf mtabs.

Lemma mdatafdE : mdatafd = mdataf mtabs.
Proof. by vm_cast_no_check (refl_equal mdatafd). Qed.

Definition actcd (x : int) (k : nat) : int :=
  actf x (nth (mdatf_of_tab [::]) mdatafd k).

Lemma DtidE2 a : tabi_ok 47 a -> cubti a -> Dtid a = Dfsd (coordi a).
Proof. by move=> _ ca; rewrite /Dtid /Dti ca; apply: refl_equal. Qed.

Lemma size_mtabs : seq.size mtabs = seq.size mtis.
Proof. by rewrite -ti2t_mtis seq.size_map. Qed.

Lemma ti2t_nth_mtis k : k < seq.size mtis ->
  ti2t 47 (nth (id_tabi 47) mtis k) = nth [::] mtabs k.
Proof. by move=> kL; rewrite -ti2t_mtis (nth_map (id_tabi 47)). Qed.

(* The guard travels: being a cube is closed under composing with a move.     *)
(* Down through cubtiE to tables, cubtE to permutations, where it is cubPM -- *)
(* and the move is a move, by mtisE.  NOTE arr is not an eqType, so the       *)
(* membership cannot be taken in mtis; it goes through mtabs.                 *)
Lemma cubti_comp a k : k < seq.size mtis -> tabi_ok 47 a -> cubti a ->
  cubti (comp_tabi 47 a (nth (id_tabi 47) mtis k)).
Proof.
move=> kL aok ca.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have cok := tabi_ok_comp n47_small n47_len aok mtok.
rewrite (cubtiE cok) (ti2t_comp n47_small n47_len aok mtok).
rewrite -(cubtE (tab_ok_comp aok mtok)) -(ptM aok mtok).
apply: cubPM; first by rewrite (cubtE aok) -(cubtiE aok).
apply: moves_cubP; rewrite inE mtisE; apply/mapP.
exists (ti2t 47 (nth (id_tabi 47) mtis k)) => //.
have -> : ti2t 47 (nth (id_tabi 47) mtis k) = nth [::] mtabs k.
  by rewrite -ti2t_mtis (nth_map (id_tabi 47)).
by rewrite ti2t_mtis mem_nth.
Qed.

(* THE STEP: stepping the coordinate with actf is the same as recomputing it  *)
(* after composing.  This is Coordfs's equivariance coordfsM, carried up      *)
(* through actdE (actfs = actd on a table) and actfE (actd = actf on the      *)
(* packed move data), with coordiE/coordtE moving between the three levels.   *)
(* Every piece was already proved for the certificate; nothing new here.      *)
Lemma actcdE a k : k < seq.size mtis -> tabi_ok 47 a -> cubti a ->
  coordi (comp_tabi 47 a (nth (id_tabi 47) mtis k)) = actcd (coordi a) k.
Proof.
move=> kL aok ca; rewrite /actcd.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have cok := tabi_ok_comp n47_small n47_len aok mtok.
have hmt : ti2t 47 (nth (id_tabi 47) mtis k) = nth [::] mtabs k
  by rewrite -ti2t_mtis (nth_map (id_tabi 47)).
have cA : cubP (pt 47 (ti2t 47 a)) by rewrite (cubtE aok) -(cubtiE aok).
have cM : cubP (pt 47 (ti2t 47 (nth (id_tabi 47) mtis k))).
  apply: moves_cubP; rewrite inE mtisE; apply/mapP.
  exists (ti2t 47 (nth (id_tabi 47) mtis k)) => //.
  by rewrite hmt ti2t_mtis mem_nth // -ti2t_mtis seq.size_map.
rewrite (coordiE cok) (ti2t_comp n47_small n47_len aok mtok).
rewrite -(coordtE (tab_ok_comp aok mtok)) -(ptM aok mtok).
rewrite (coordfsM cA cM) (actdE _ mtok) -actfE.
rewrite (coordtE aok) -(coordiE aok).
congr (actf _ _).
by rewrite mdatafdE /mdataf (nth_map [::]) ?hmt // -ti2t_mtis seq.size_map.
Qed.

Lemma size_mtis : seq.size mtis = nmoves.
Proof. by rewrite /mtis seq.size_map -(seq.size_map (pt 47)) -mtabsE moves_size. Qed.

(* the 36 roots are cubes, so the guard holds where the search starts.        *)
(* NOTE prefixi takes its nth default as sfti and cubti_comp as id_tabi 47;   *)
(* below nmoves they agree, which is what set_nth_default says.               *)
Lemma prefixi_cub i j : i < nmoves -> j < nmoves -> cubti (prefixi i j).
Proof.
move=> iL jL.
have e k : k < nmoves -> nth sfti mtis k = nth (id_tabi 47) mtis k.
  by move=> kL; apply: set_nth_default; rewrite size_mtis.
have csf : cubti sfti by vm_compute.
rewrite /prefixi (e i); last by [].
rewrite e; last by [].
apply: cubti_comp.
- by rewrite size_mtis.
- apply: (tabi_ok_comp n47_small n47_len); first exact: sfti_ok.
  by apply: (all_nthP (id_tabi 47) mtis_ok); rewrite size_mtis.
apply: cubti_comp.
- by rewrite size_mtis.
- exact: sfti_ok.
exact: csf.
Qed.

(* ---- 3quater. searchz: prune the child BEFORE composing ------------------ *)

(* WHY THIS IS WORTH FINISHING. Measured on the real search, single threaded, *)
(* one coqc process, vm_compute, depth 9 from prefixi 0 3:                    *)
(*                                                                            *)
(*     searchir   9.94 s                                                      *)
(*     searchz    2.588 s          -- 3.84x                                   *)
(*                                                                            *)
(* searchir recurses first and tests Dti a <= d INSIDE the call, so every one *)
(* of the ~13.5 children pays a full comp_tabi (48 writes) plus a complete 24 *)
(* bit coordinate rebuild before being thrown away. searchz steps the         *)
(* coordinate with actf, tests the table on it, and composes the array ONLY   *)
(* for children that survive. A pruned child costs one actf and one table     *)
(* read.                                                                      *)
(*                                                                            *)
(* For scale: the same job at depth 12 is 0.2 s in OCaml against 21m07 CPU    *)
(* here, and that ~6300x factors as ~90x per node times ~70x more node        *)
(* visits. This addresses the second factor, which is the larger one.         *)
(*                                                                            *)
(* CONCRETE ON PURPOSE. An earlier attempt (searchic, in Searchir.v,          *)
(* reverted) made the heuristic/coordinate/transition section Variables. It   *)
(* was proved correct but ran SLOWER than searchir -- the higher order        *)
(* parameters appear to defeat whatever specialisation the VM does against a  *)
(* known constant. Do not re-abstract this.                                   *)
(*                                                                            *)
(* mdatafd above is the other half of that lesson: mdataf mtabs is an         *)
(* application, which the VM rebuilds on every call.                          *)

Fixpoint searchz (d : nat) (a : arr) (x : int) (p : nat) : bool :=
  if Dfsd x <= d then
    if eq_tabi 47 a (id_tabi 47) then true
    else if d is d'.+1 then
      (fix go (l : seq nat) : bool :=
         if l is k :: l' then
           (if Dfsd (actcd x k) <= d' then
              (if searchz d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                             (actcd x k) (fcpos k)
               then true else go l')
            else go l')
         else false) (allowedr mtis nfcube oppf fcpos p)
    else false
  else false.

Lemma searchir_gt d a p : (Dtid a <= d) = false ->
  searchir 47 mtis Dtid nfcube oppf fcpos d a p = false.
Proof. by case: d => [|d] h; rewrite {1}/searchir h. Qed.

(* THE LOOP, NAMED.  An anonymous inner fix leaks its whole body into every   *)
(* statement and goal that mentions it, and then congr / case / elim all have *)
(* to match against two copies of it -- which is the only reason this proof   *)
(* ever looked hard.  Named, goals carry the constant goz d a x and every     *)
(* step below is ordinary.                                                    *)
Definition goz (d : nat) (a : arr) (x : int) : seq nat -> bool :=
  fix go (l : seq nat) : bool :=
    if l is k :: l' then
      (if Dfsd (actcd x k) <= d then
         (if searchz d (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                       (actcd x k) (fcpos k)
          then true else go l')
       else go l')
    else false.

Lemma searchzS d a x p :
  searchz d.+1 a x p =
  (Dfsd x <= d.+1) &&
  (eq_tabi 47 a (id_tabi 47) || goz d a x (allowedr mtis nfcube oppf fcpos p)).
Proof. by []. Qed.

Lemma goz_cons d a x k l :
  goz d a x (k :: l) =
  if Dfsd (actcd x k) <= d then
    (if searchz d (comp_tabi 47 a (nth (id_tabi 47) mtis k)) (actcd x k) (fcpos k)
     then true else goz d a x l)
  else goz d a x l.
Proof. by []. Qed.

Lemma hasE (f : nat -> bool) k l : has f (k :: l) = f k || has f l.
Proof. by []. Qed.

(* searchz computes what searchir computes, so it can replace it under the    *)
(* invariant that a is a well formed cube -- which prefixi_cub gives at the   *)
(* roots and cubti_comp carries down.                                         *)
(* TWO TACTIC FACTS, both learned the hard way and both worth keeping:        *)
(* arguments must be EXPLICIT (searchirS and DtidE2 are ~7 ms given           *)
(* explicitly and do not return implicitly), and the two binary operators are *)
(* peeled with f_equal2 rather than congr, which tries to match the whole     *)
(* goal.  Nothing here needs /= : simpl on these goals does not return.       *)
Lemma searchzE d a p : tabi_ok 47 a -> cubti a ->
  searchz d a (coordi a) p = searchir 47 mtis Dtid nfcube oppf fcpos d a p.
Proof.
elim: d a p => [|d IH] a p aok ca.
  rewrite {1}/searchz {1}/searchir (DtidE2 aok ca).
  by case: (Dfsd (coordi a) <= 0); case: (eq_tabi 47 a (id_tabi 47)).
rewrite (searchirS 47 mtis Dtid nfcube oppf fcpos d a p) (DtidE2 aok ca) searchzS.
apply: f_equal2; first by apply: refl_equal.
apply: f_equal2; first by apply: refl_equal.
have hall : all (fun k => k < seq.size mtis) (allowedr mtis nfcube oppf fcpos p).
  by apply/allP => k; rewrite mem_filter mem_iota => /andP[_ /andP[_ h]].
elim: (allowedr mtis nfcube oppf fcpos p) hall => [//|k l IHl /andP[kL hl]].
rewrite goz_cons.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have aok' := tabi_ok_comp n47_small n47_len aok mtok.
have ca' := cubti_comp kL aok ca.
rewrite -(actcdE kL aok ca) (IH _ (fcpos k) aok' ca') -(DtidE2 aok' ca') (IHl hl).
case: ifP => hle; rewrite hasE.
  by case: (searchir 47 mtis Dtid nfcube oppf fcpos d
              (comp_tabi 47 a (nth (id_tabi 47) mtis k)) (fcpos k)).
by rewrite (searchir_gt _ hle).
Qed.

(* ---- 4. Towards carrying FIVE coordinates -----------------------------    *)

(* Dsymd rebuilds five coordinates at every node: five conjugations plus five *)
(* coordi, ~120 us.  Carried and stepped with actf it is five actf, ~10 us.   *)
(* MEASURED at depth 9 from prefixi 0 3, native_compute, same node count      *)
(* (4918): rebuild 2.741 s, carry-and-step 0.437 s -- 6.3x.                   *)
(*                                                                            *)
(* The step is: conjugating then moving = moving by the CONJUGATED move then  *)
(* conjugating.  sigma s k is the index of m_k ^ s, and views_moves is the    *)
(* vm_compute fact that conjugation really does permute the eighteen moves.   *)
(*                                                                            *)
(* These are the supporting lemmas, all proved.  What is still missing is the *)
(* five-tuple search itself and its induction.                                *)

Definition sigma (s : seq nat) (k : nat) : nat :=
  index (conjt s (nth [::] mtabs k)) mtabs.

Lemma conjt_hom s t1 t2 : tab_ok 47 s -> tab_ok 47 t1 -> tab_ok 47 t2 ->
  conjt s (comp_tab t1 t2) = comp_tab (conjt s t1) (conjt s t2).
Proof.
move=> sok o1 o2.
apply: pt_inj_in.
- by apply: tab_ok_conjt => //; apply: tab_ok_comp.
- by apply: tab_ok_comp; apply: tab_ok_conjt.
rewrite -(ptM (tab_ok_conjt sok o1) (tab_ok_conjt sok o2)).
rewrite -(ptJ o1 sok) -(ptJ o2 sok) -conjMg.
by rewrite (ptM o1 o2) (ptJ (tab_ok_comp o1 o2) sok).
Qed.

(* membership, not the equation, is the right hypothesis: it gives both the   *)
(* bound (index_mem) and the value (nth_index).                               *)
Lemma ti2t_step s a k :
  tab_ok 47 s -> tabi_ok 47 a -> k < seq.size mtis ->
  conjt s (nth [::] mtabs k) \in mtabs ->
  ti2t 47 (conji s (comp_tabi 47 a (nth (id_tabi 47) mtis k)))
  = ti2t 47 (comp_tabi 47 (conji s a) (nth (id_tabi 47) mtis (sigma s k))).
Proof.
move=> sok aok kL hm.
have sL : sigma s k < seq.size mtis
  by rewrite /sigma -ti2t_mtis seq.size_map index_mem.
have sg : nth [::] mtabs (sigma s k) = conjt s (nth [::] mtabs k)
  by rewrite /sigma nth_index.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have hk : ti2t 47 (nth (id_tabi 47) mtis k) = nth [::] mtabs k
  by rewrite -ti2t_mtis (nth_map (id_tabi 47)).
have cok := tabi_ok_comp n47_small n47_len aok mtok.
have kM : k < seq.size mtabs by rewrite -ti2t_mtis seq.size_map.
have mok : tab_ok 47 (nth [::] mtabs k) by apply: (all_nthP [::] mtabs_ok).
have sok2 : tabi_ok 47 (conji s a) by apply: tabi_ok_conji.
have mok2 : tabi_ok 47 (nth (id_tabi 47) mtis (sigma s k))
  by apply: (all_nthP (id_tabi 47) mtis_ok).
rewrite (ti2t_conji sok cok) (ti2t_comp n47_small n47_len aok mtok) hk.
rewrite (conjt_hom sok aok mok).
rewrite (ti2t_comp n47_small n47_len sok2 mok2) (ti2t_conji sok aok).
have hs : ti2t 47 (nth (id_tabi 47) mtis (sigma s k)) = nth [::] mtabs (sigma s k)
  by rewrite -ti2t_mtis (nth_map (id_tabi 47)).
by rewrite hs sg.
Qed.

Lemma cubt_conjt s t : tab_ok 47 s -> tab_ok 47 t -> cubt s -> cubt t ->
  cubt (conjt s t).
Proof.
move=> sok tok cs ct.
rewrite -(cubtE (tab_ok_conjt sok tok)) -(ptJ tok sok) conjgE.
apply: cubPM.
- by apply: cubPV; rewrite (cubtE sok).
apply: cubPM.
- by rewrite (cubtE tok).
by rewrite (cubtE sok).
Qed.

Lemma cubt_Sy : cubt Sytab.  Proof. by vm_compute. Qed.
Lemma cubt_Sx : cubt Sxtab.  Proof. by vm_compute. Qed.

Lemma cubti_conji s a : tab_ok 47 s -> cubt s -> tabi_ok 47 a -> cubti a ->
  cubti (conji s a).
Proof.
move=> sok cs aok ca.
have sok2 : tabi_ok 47 (conji s a) by apply: tabi_ok_conji.
rewrite (cubtiE sok2) (ti2t_conji sok aok).
by apply: cubt_conjt => //; rewrite -(cubtiE aok).
Qed.

(* THE PER-VIEW INVARIANT STEP.                                               *)
Lemma coordi_step s a k :
  tab_ok 47 s -> cubt s -> tabi_ok 47 a -> cubti a -> k < seq.size mtis ->
  conjt s (nth [::] mtabs k) \in mtabs ->
  coordi (conji s (comp_tabi 47 a (nth (id_tabi 47) mtis k)))
  = actcd (coordi (conji s a)) (sigma s k).
Proof.
move=> sok cs aok ca kL hm.
have sL : sigma s k < seq.size mtis
  by rewrite /sigma -ti2t_mtis seq.size_map index_mem.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have cok := tabi_ok_comp n47_small n47_len aok mtok.
have sok2 : tabi_ok 47 (conji s a) by apply: tabi_ok_conji.
have mok2 : tabi_ok 47 (nth (id_tabi 47) mtis (sigma s k))
  by apply: (all_nthP (id_tabi 47) mtis_ok).
have h1 : tabi_ok 47 (conji s (comp_tabi 47 a (nth (id_tabi 47) mtis k)))
  by apply: tabi_ok_conji.
rewrite (coordiE h1) (ti2t_step sok aok kL hm).
rewrite -(coordiE (tabi_ok_comp n47_small n47_len sok2 mok2)).
by apply: actcdE => //; apply: cubti_conji.
Qed.

Lemma views_moves :
  all (fun s => all (fun k => conjt s (nth [::] mtabs k) \in mtabs) (iota 0 18))
      viewst.
Proof. by vm_compute. Qed.

Lemma view_move s k : s \in viewst -> k < 18 ->
  conjt s (nth [::] mtabs k) \in mtabs.
Proof.
move=> sV kL.
have := allP views_moves _ sV => /allP; apply.
by rewrite mem_iota add0n leq0n.
Qed.

(* ---- 5. The search carrying FIVE coordinates ----------------------------- *)

(* Dsymd rebuilds five coordinates per node -- five conjugations plus five    *)
(* coordi, ~120 us.  Carried and stepped with actf it is five actf, ~10 us.   *)
(* MEASURED, depth 9 from prefixi 0 3, native_compute, identical node counts  *)
(* (4918): rebuild 2.741 s, carry-and-step 0.437 s -- 6.3x.                   *)

Definition sg0 : seq nat :=
  Eval vm_compute in [seq sigma (nth [::] viewst 0) k | k <- iota 0 18].
Definition sg1 : seq nat :=
  Eval vm_compute in [seq sigma (nth [::] viewst 1) k | k <- iota 0 18].
Definition sg2 : seq nat :=
  Eval vm_compute in [seq sigma (nth [::] viewst 2) k | k <- iota 0 18].
Definition sg3 : seq nat :=
  Eval vm_compute in [seq sigma (nth [::] viewst 3) k | k <- iota 0 18].
Definition sg4 : seq nat :=
  Eval vm_compute in [seq sigma (nth [::] viewst 4) k | k <- iota 0 18].

Definition c5 := (int * int * int * int * int)%type.

Definition step5 (x : c5) (k : nat) : c5 :=
  let: (x0, x1, x2, x3, x4) := x in
  (actcd x0 (nth 0%N sg0 k), actcd x1 (nth 0%N sg1 k), actcd x2 (nth 0%N sg2 k),
   actcd x3 (nth 0%N sg3 k), actcd x4 (nth 0%N sg4 k)).

Definition h5 (x : c5) : nat :=
  let: (x0, x1, x2, x3, x4) := x in
  maxn (maxn (Dfsd x0) (Dfsd x1))
       (maxn (Dfsd x2) (maxn (Dfsd x3) (Dfsd x4))).

(* the five views of the root, in viewst's order                              *)
Definition init5 (a : arr) : c5 :=
  (coordi a, coordi (conjy a), coordi (conjx a),
   coordi (conjy (conjx a)), coordi (conjx (conjy a))).

Fixpoint searchz5 (d : nat) (a : arr) (x : c5) (p : nat) : bool :=
  if h5 x <= d then
    if eq_tabi 47 a (id_tabi 47) then true
    else if d is d'.+1 then
      (fix go (l : seq nat) : bool :=
         if l is k :: l' then
           if searchz5 d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                          (step5 x k) (fcpos k)
           then true else go l'
         else false) (allowedr mtis nfcube oppf fcpos p)
    else false
  else false.

(* the sigma rows, related back to their computable form                      *)
Lemma sg0M : sg0 = [seq sigma (nth [::] viewst 0) k | k <- iota 0 18].
Proof. by vm_compute. Qed.
Lemma sg1M : sg1 = [seq sigma (nth [::] viewst 1) k | k <- iota 0 18].
Proof. by vm_compute. Qed.
Lemma sg2M : sg2 = [seq sigma (nth [::] viewst 2) k | k <- iota 0 18].
Proof. by vm_compute. Qed.
Lemma sg3M : sg3 = [seq sigma (nth [::] viewst 3) k | k <- iota 0 18].
Proof. by vm_compute. Qed.
Lemma sg4M : sg4 = [seq sigma (nth [::] viewst 4) k | k <- iota 0 18].
Proof. by vm_compute. Qed.

(* NOTE: never leave the size side condition to // here -- it wanders into    *)
(* sigma's computation and does not return.                                   *)
Lemma sg0N k : k < 18 -> nth 0%N sg0 k = sigma (nth [::] viewst 0) k.
Proof.
move=> kL; rewrite sg0M (nth_map 0%N).
- by rewrite nth_iota // add0n.
by rewrite size_iota.
Qed.
Lemma sg1N k : k < 18 -> nth 0%N sg1 k = sigma (nth [::] viewst 1) k.
Proof.
move=> kL; rewrite sg1M (nth_map 0%N).
- by rewrite nth_iota // add0n.
by rewrite size_iota.
Qed.
Lemma sg2N k : k < 18 -> nth 0%N sg2 k = sigma (nth [::] viewst 2) k.
Proof.
move=> kL; rewrite sg2M (nth_map 0%N).
- by rewrite nth_iota // add0n.
by rewrite size_iota.
Qed.
Lemma sg3N k : k < 18 -> nth 0%N sg3 k = sigma (nth [::] viewst 3) k.
Proof.
move=> kL; rewrite sg3M (nth_map 0%N).
- by rewrite nth_iota // add0n.
by rewrite size_iota.
Qed.
Lemma sg4N k : k < 18 -> nth 0%N sg4 k = sigma (nth [::] viewst 4) k.
Proof.
move=> kL; rewrite sg4M (nth_map 0%N).
- by rewrite nth_iota // add0n.
by rewrite size_iota.
Qed.

(* FIRST INVARIANT: the carried heuristic is the rebuilt one.                 *)
(* The five DtidE2 rewrites and the final comparison all need lock -- without *)
(* it each one scans a goal full of conjy/conjx over concrete tables.         *)
Lemma h5_init a : tabi_ok 47 a -> cubti a -> h5 (init5 a) = Dsymd a.
Proof.
move=> aok ca.
have oky : tabi_ok 47 (conjy a).
  by rewrite conjyE; apply: tabi_ok_conji; [exact: okSy | exact: aok].
have okx : tabi_ok 47 (conjx a).
  by rewrite conjxE; apply: tabi_ok_conji; [exact: okSx | exact: aok].
have cy : cubti (conjy a).
  by rewrite conjyE; apply: cubti_conji;
     [exact: okSy | exact: cubt_Sy | exact: aok | exact: ca].
have cx : cubti (conjx a).
  by rewrite conjxE; apply: cubti_conji;
     [exact: okSx | exact: cubt_Sx | exact: aok | exact: ca].
have okyx : tabi_ok 47 (conjy (conjx a)).
  by rewrite conjyE; apply: tabi_ok_conji; [exact: okSy | exact: okx].
have okxy : tabi_ok 47 (conjx (conjy a)).
  by rewrite conjxE; apply: tabi_ok_conji; [exact: okSx | exact: oky].
have cyx : cubti (conjy (conjx a)).
  by rewrite conjyE; apply: cubti_conji;
     [exact: okSy | exact: cubt_Sy | exact: okx | exact: cx].
have cxy : cubti (conjx (conjy a)).
  by rewrite conjxE; apply: cubti_conji;
     [exact: okSx | exact: cubt_Sx | exact: oky | exact: cy].
rewrite /h5 /init5 /Dsymd.
rewrite {-1}[Dtid]lock (DtidE2 aok ca) -lock.
rewrite {-1}[Dtid]lock (DtidE2 oky cy) -lock.
rewrite {-1}[Dtid]lock (DtidE2 okx cx) -lock.
rewrite {-1}[Dtid]lock (DtidE2 okyx cyx) -lock.
rewrite (DtidE2 okxy cxy).
by rewrite [Dfsd]lock [coordi]lock.
Qed.

Lemma okv3 : tab_ok 47 (nth [::] viewst 3).
Proof. by apply: tab_ok_comp; [exact: okSx | exact: okSy]. Qed.
Lemma okv4 : tab_ok 47 (nth [::] viewst 4).
Proof. by apply: tab_ok_comp; [exact: okSy | exact: okSx]. Qed.

Lemma ti2t_yx a : tabi_ok 47 a ->
  ti2t 47 (conjy (conjx a)) = ti2t 47 (conji (nth [::] viewst 3) a).
Proof.
move=> aok.
have okx : tabi_ok 47 (conjx a).
  by rewrite conjxE; apply: tabi_ok_conji; [exact: okSx | exact: aok].
rewrite conjyE.
rewrite {2}[conji]lock (ti2t_conji okSy okx) -lock.
rewrite conjxE.
rewrite {2}[conji]lock (ti2t_conji okSx aok) -lock.
by rewrite (conjtM okSx okSy aok) (ti2t_conji okv3 aok).
Qed.

Lemma ti2t_xy a : tabi_ok 47 a ->
  ti2t 47 (conjx (conjy a)) = ti2t 47 (conji (nth [::] viewst 4) a).
Proof.
move=> aok.
have oky : tabi_ok 47 (conjy a).
  by rewrite conjyE; apply: tabi_ok_conji; [exact: okSy | exact: aok].
rewrite conjxE.
rewrite {2}[conji]lock (ti2t_conji okSx oky) -lock.
rewrite conjyE.
rewrite {2}[conji]lock (ti2t_conji okSy aok) -lock.
by rewrite (conjtM okSy okSx aok) (ti2t_conji okv4 aok).
Qed.

Lemma coordi_ti2t X Y : tabi_ok 47 X -> tabi_ok 47 Y ->
  ti2t 47 X = ti2t 47 Y -> coordi X = coordi Y.
Proof. by move=> oX oY e; rewrite (coordiE oX) (coordiE oY) e. Qed.

Lemma sigma_v0 k : k < 18 -> sigma (nth [::] viewst 0) k = k.
Proof.
move=> kL.
have kM : k < seq.size mtabs by rewrite -ti2t_mtis seq.size_map size_mtis.
have mok : tab_ok 47 (nth [::] mtabs k) by apply: (allP mtabs_ok); rewrite mem_nth.
by rewrite /sigma (conjt_id mok) index_uniq // uniq_mtabs.
Qed.

Lemma vV j : j < 5 -> nth [::] viewst j \in viewst.
Proof. by move=> jL; rewrite mem_nth. Qed.

Lemma step_comp s a k : s \in viewst -> tab_ok 47 s -> cubt s ->
  tabi_ok 47 a -> cubti a -> k < 18 ->
  coordi (conji s (comp_tabi 47 a (nth (id_tabi 47) mtis k)))
  = actcd (coordi (conji s a)) (sigma s k).
Proof.
move=> sV sok cs aok ca kL.
by apply: coordi_step => //; last by apply: view_move.
Qed.

(* SECOND INVARIANT: stepping the five agrees with rebuilding them.           *)
Lemma step5_init a k : tabi_ok 47 a -> cubti a -> k < 18 ->
  step5 (init5 a) k = init5 (comp_tabi 47 a (nth (id_tabi 47) mtis k)).
Proof.
move=> aok ca kL.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok); rewrite size_mtis.
have Aok : tabi_ok 47 (comp_tabi 47 a (nth (id_tabi 47) mtis k))
  by apply: (tabi_ok_comp n47_small n47_len).
have cA : cubti (comp_tabi 47 a (nth (id_tabi 47) mtis k))
  by apply: cubti_comp => //; rewrite size_mtis.
have cv3 : cubt (nth [::] viewst 3).
  rewrite -(cubtE okv3) -(ptM okSx okSy); apply: cubPM.
  - by rewrite (cubtE okSx); exact: cubt_Sx.
  by rewrite (cubtE okSy); exact: cubt_Sy.
have cv4 : cubt (nth [::] viewst 4).
  rewrite -(cubtE okv4) -(ptM okSy okSx); apply: cubPM.
  - by rewrite (cubtE okSy); exact: cubt_Sy.
  by rewrite (cubtE okSx); exact: cubt_Sx.
have SyV : Sytab \in viewst by apply: (@vV 1).
have SxV : Sxtab \in viewst by apply: (@vV 2).
rewrite /step5 /init5.
congr (_, _, _, _, _).
- have kM : k < seq.size mtis by rewrite size_mtis.
  by rewrite (@sg0N k kL) (@sigma_v0 k kL) (actcdE kM aok ca).
- rewrite !conjyE (@sg1N k kL); symmetry.
  by apply: step_comp;
     [exact: SyV | exact: okSy | exact: cubt_Sy | exact: aok | exact: ca | exact: kL].
- rewrite !conjxE (@sg2N k kL); symmetry.
  by apply: step_comp;
     [exact: SxV | exact: okSx | exact: cubt_Sx | exact: aok | exact: ca | exact: kL].
- have okxa : tabi_ok 47 (conjx a).
    by rewrite conjxE; apply: tabi_ok_conji; [exact: okSx | exact: aok].
  have okyxa : tabi_ok 47 (conjy (conjx a)).
    by rewrite conjyE; apply: tabi_ok_conji; [exact: okSy | exact: okxa].
  have okxA : tabi_ok 47 (conjx (comp_tabi 47 a (nth (id_tabi 47) mtis k))).
    by rewrite conjxE; apply: tabi_ok_conji; [exact: okSx | exact: Aok].
  have okyxA : tabi_ok 47 (conjy (conjx (comp_tabi 47 a (nth (id_tabi 47) mtis k)))).
    by rewrite conjyE; apply: tabi_ok_conji; [exact: okSy | exact: okxA].
  have e1 : coordi (conjy (conjx a)) = coordi (conji (nth [::] viewst 3) a).
    apply: coordi_ti2t;
      [exact: okyxa | apply: tabi_ok_conji; [exact: okv3 | exact: aok]
       | apply: ti2t_yx; exact: aok].
  have e2 : coordi (conjy (conjx (comp_tabi 47 a (nth (id_tabi 47) mtis k))))
          = coordi (conji (nth [::] viewst 3) (comp_tabi 47 a (nth (id_tabi 47) mtis k))).
    apply: coordi_ti2t;
      [exact: okyxA | apply: tabi_ok_conji; [exact: okv3 | exact: Aok]
       | apply: ti2t_yx; exact: Aok].
  rewrite e1 e2 (@sg3N k kL); symmetry.
  by apply: step_comp;
     [by apply: (@vV 3) | exact: okv3 | exact: cv3 | exact: aok | exact: ca | exact: kL].
have okya : tabi_ok 47 (conjy a).
  by rewrite conjyE; apply: tabi_ok_conji; [exact: okSy | exact: aok].
have okxya : tabi_ok 47 (conjx (conjy a)).
  by rewrite conjxE; apply: tabi_ok_conji; [exact: okSx | exact: okya].
have okyA : tabi_ok 47 (conjy (comp_tabi 47 a (nth (id_tabi 47) mtis k))).
  by rewrite conjyE; apply: tabi_ok_conji; [exact: okSy | exact: Aok].
have okxyA : tabi_ok 47 (conjx (conjy (comp_tabi 47 a (nth (id_tabi 47) mtis k)))).
  by rewrite conjxE; apply: tabi_ok_conji; [exact: okSx | exact: okyA].
have f1 : coordi (conjx (conjy a)) = coordi (conji (nth [::] viewst 4) a).
  apply: coordi_ti2t;
    [exact: okxya | apply: tabi_ok_conji; [exact: okv4 | exact: aok]
     | apply: ti2t_xy; exact: aok].
have f2 : coordi (conjx (conjy (comp_tabi 47 a (nth (id_tabi 47) mtis k))))
        = coordi (conji (nth [::] viewst 4) (comp_tabi 47 a (nth (id_tabi 47) mtis k))).
  apply: coordi_ti2t;
    [exact: okxyA | apply: tabi_ok_conji; [exact: okv4 | exact: Aok]
     | apply: ti2t_xy; exact: Aok].
rewrite f1 f2 (@sg4N k kL); symmetry.
by apply: step_comp;
   [by apply: (@vV 4) | exact: okv4 | exact: cv4 | exact: aok | exact: ca | exact: kL].
Qed.

Lemma searchz5S d a x p :
  searchz5 d.+1 a x p =
  (h5 x <= d.+1) &&
  (eq_tabi 47 a (id_tabi 47) ||
   has (fun k => searchz5 d (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                            (step5 x k) (fcpos k))
       (allowedr mtis nfcube oppf fcpos p)).
Proof.
rewrite {1}/searchz5 -/searchz5.
by case: (h5 x <= d.+1) => //=; case: (eq_tabi 47 a (id_tabi 47)) => //=.
Qed.

(* THE INDUCTION.  f_equal2 rather than congr, which does not return here.    *)
Lemma searchz5E d a p : tabi_ok 47 a -> cubti a ->
  searchz5 d a (init5 a) p = searchir 47 mtis Dsymd nfcube oppf fcpos d a p.
Proof.
elim: d a p => [|d IH] a p aok ca.
  rewrite {1}/searchz5 {1}/searchir (@h5_init a aok ca).
  by case: (Dsymd a <= 0); case: (eq_tabi 47 a (id_tabi 47)).
rewrite searchz5S (searchirS 47 mtis Dsymd nfcube oppf fcpos d a p).
rewrite (@h5_init a aok ca).
apply: f_equal2; first by apply: refl_equal.
apply: f_equal2; first by apply: refl_equal.
apply: eq_in_has => k; rewrite mem_filter mem_iota => /andP[_ /andP[_ kL]].
have kL18 : k < 18 by move: kL; rewrite add0n size_mtis.
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k)
  by apply: (all_nthP (id_tabi 47) mtis_ok); move: kL; rewrite add0n.
have Aok : tabi_ok 47 (comp_tabi 47 a (nth (id_tabi 47) mtis k))
  by apply: (tabi_ok_comp n47_small n47_len).
have cA : cubti (comp_tabi 47 a (nth (id_tabi 47) mtis k))
  by apply: cubti_comp; [move: kL; rewrite add0n | exact: aok | exact: ca].
by rewrite (@step5_init a k aok ca kL18) (IH _ (fcpos k) Aok cA).
Qed.

Lemma far_of_searchz5 d a : tabi_ok 47 a -> cubti a ->
  searchz5 d a (init5 a) nfcube = false ->
  pt 47 (ti2t 47 a) \notin ball Sset d.
Proof.
move=> aok ca hs; apply: far_of_searchsym => //.
by rewrite -(@searchz5E d a nfcube aok ca).
Qed.
