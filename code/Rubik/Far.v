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
        Coordfs Coordfsi Fstab FsTable Diameter Moves Fsmain
        Searchr Redun Searchir.

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

       ulimit -s unlimited
       rm -f Far*.vo Far*.vok Far*.vos Far*.glob .coq-native/NRubik_Far*
       make -j18

   rebuilds exactly the twenty files that can have changed.

   THE ulimit IS NOT OPTIONAL.  FsData.v is a 2 097 152 element seq int
   literal, and loading or native compiling a list that deep recurses past
   the default 8 MB stack; without it the build simply fails.

   On -j: count the jobs, not the cores.  The certificate is sixteen files
   and the search is eighteen, both just above the twelve physical cores of
   the old Xeon, so -j12 pays two waves where -j18 pays one.  Drop back to
   -j12 if memory complains -- every worker loads the table, about a
   gigabyte each.                                                          *)
Definition depth := 12.
Definition droot := depth.-2.           (* depth = droot.+2                   *)
Definition nroot := 2.                  (* size Sroot                         *)
Definition nmoves := 18.                (* size moves                         *)

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


(* ---- 5. The reduced search, and why the guard stops at the prefix --------- *)

(* THE SENTINEL p IS NOT A SHORTCUT, it is forced.  ball_root2 conjugates by
   the 48 symmetries to push the first move into Sroot, which is worth a
   factor 9; but conjugation PERMUTES THE FACES, and while the same-face half
   of the guard survives that, the opposite-pair ordering half (smaller face
   index first) does not.  So the pair (m1, m2) ball_root2 hands back cannot
   be assumed guard respecting, and the continuation search must start at the
   sentinel -- the guard then applies from the fourth move on.
   The arithmetic says this is the right trade anyway: symmetry x sentinel is
   9 x 72 = 648, against 1 x 131 for dropping ball_root2 and using
   searchr_split2 instead.  Symmetry is worth more than the two levels of
   guard, by a factor of five.                                             *)
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
(* e1 and e2 are stated FULLY INSTANTIATED on purpose.  Written as
   rewrite -(searchtrE ...) the backward rewrite has to unify
   [seq pt 47 mt | mt <- ?mts] against the concrete mtis, which builds
   eighteen permutations and never returns -- a timeout, not a type error.
   Given as closed equations both rewrites are syntactic and it takes 1.3 s. *)
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

(* searchir spends ~84% of a node rebuilding the coordinate: comp_tabi
   composes 48 entries and then Dtid inverts the array and repacks all 24 bits
   from scratch.  Measured (fresh coqc, two sizes, differenced) 66.2 us/node
   against 5.4 us for the composition alone; with actf, 19.8 us.  actf IS the
   coordinate transition and checkStep already certifies it, so the coordinate
   can be carried and stepped instead of recomputed.  The array is still
   composed, for the goal test only.                                        *)

(* EVALUATED ONCE.  mdataf mtabs is an application of a constant to an
   argument, so the VM cannot share it: written directly here it is rebuilt on
   every call -- eighteen mdatf, each a twelve entry array plus a twelve bit
   pack -- about 13.5 times per node.  As a closed Definition it is a literal
   and costs nothing per node.                                             *)
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

(* The guard travels: being a cube is closed under composing with a move.
   Down through cubtiE to tables, cubtE to permutations, where it is cubPM --
   and the move is a move, by mtisE.  NOTE arr is not an eqType, so the
   membership cannot be taken in mtis; it goes through mtabs.              *)
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

(* THE STEP: stepping the coordinate with actf is the same as recomputing it
   after composing.  This is Coordfs's equivariance coordfsM, carried up
   through actdE (actfs = actd on a table) and actfE (actd = actf on the
   packed move data), with coordiE/coordtE moving between the three levels.
   Every piece was already proved for the certificate; nothing new here.  *)
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

(* the 36 roots are cubes, so the guard holds where the search starts.
   NOTE prefixi takes its nth default as sfti and cubti_comp as id_tabi 47;
   below nmoves they agree, which is what set_nth_default says.            *)
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

(* WHY THIS IS WORTH FINISHING.  Measured on the real search, single threaded,
   one coqc process, vm_compute, depth 9 from prefixi 0 3:

       searchir   9.94 s
       searchz    2.588 s          -- 3.84x

   searchir recurses first and tests Dti a <= d INSIDE the call, so every one
   of the ~13.5 children pays a full comp_tabi (48 writes) plus a complete 24
   bit coordinate rebuild before being thrown away.  searchz steps the
   coordinate with actf, tests the table on it, and composes the array ONLY
   for children that survive.  A pruned child costs one actf and one table
   read.

   For scale: the same job at depth 12 is 0.2 s in OCaml against 21m07 CPU
   here, and that ~6300x factors as ~90x per node times ~70x more node visits.
   This addresses the second factor, which is the larger one.

   CONCRETE ON PURPOSE.  An earlier attempt (searchic, in Searchir.v, reverted)
   made the heuristic/coordinate/transition section Variables.  It was proved
   correct but ran SLOWER than searchir -- the higher order parameters appear
   to defeat whatever specialisation the VM does against a known constant.  Do
   not re-abstract this.

   mdatafd above is the other half of that lesson: mdataf mtabs is an
   application, which the VM rebuilds on every call.                        *)

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

(* THE LOOP, NAMED.  An anonymous inner fix leaks its whole body into every
   statement and goal that mentions it, and then congr / case / elim all have
   to match against two copies of it -- which is the only reason this proof
   ever looked hard.  Named, goals carry the constant goz d a x and every
   step below is ordinary.                                                 *)
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

(* searchz computes what searchir computes, so it can replace it under the
   invariant that a is a well formed cube -- which prefixi_cub gives at the
   roots and cubti_comp carries down.
   TWO TACTIC FACTS, both learned the hard way and both worth keeping:
   arguments must be EXPLICIT (searchirS and DtidE2 are ~7 ms given
   explicitly and do not return implicitly), and the two binary operators are
   peeled with f_equal2 rather than congr, which tries to match the whole
   goal.  Nothing here needs /= : simpl on these goals does not return.   *)
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
