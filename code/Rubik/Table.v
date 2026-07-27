(* =========================================================================  *)
(*  Table.v                                                                   *)
(*                                                                            *)
(*  Permutations of 'I_n.+1 presented by their image TABLE: a list of n.+1    *)
(*  natural numbers, `pt t` being the permutation sending i to nth 0 t i.     *)
(*                                                                            *)
(*  WHY.  A finite fact about a {perm 'I_48} -- that two products of cycles   *)
(*  are equal, that a turn has order 4, that a conjugate is another turn --   *)
(*  is a computation, but not one the kernel can do on the permutation        *)
(*  itself: `inord` and `enum` do not reduce, and a cyc is a bigop of tperm   *)
(*  over a finfun.  On a table the same fact is an equality of two literal    *)
(*  lists of nat, which vm_compute settles instantly.                         *)
(*                                                                            *)
(*  The bridge is arranged so that NOTHING that gets computed ever mentions   *)
(*  'I_n.+1: tables, their composition, inverse and the cycle tables are all  *)
(*  nat -> nat data, and `inord` occurs only inside the definition of pt and  *)
(*  in the statements, never under a vm_compute.  An equality of two          *)
(*  permutations is reached by `congr pt` and then computing on nat lists.    *)
(*                                                                            *)
(*  Usage.  For a permutation given as a product of cycles with point lists   *)
(*  l1..lk, `cycs_pt` rewrites it to `pt (cycs_tab [:: l1; ..; lk])` (the li  *)
(*  as nat lists); `ptM`, `ptV`, `ptJ` push products, inverses and            *)
(*  conjugates through to the table side; then `congr pt; by vm_compute`.     *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* A list of naturals below n.+1, no repetition, is the image list of a       *)
(* permutation of 'I_n.+1 as soon as it has the right length.                 *)
Lemma uniq_inord n l :
  all (fun i => i < n.+1) l -> uniq l -> uniq ((map inord l) : seq 'I_n.+1).
Proof.
elim: l => //= a l IH /andP[aLn lA] /andP[aNIl lU].
apply/andP; split; last by apply: IH.
apply/negP => aIl; case/negP: aNIl; elim: l {IH lU} lA aIl => //= b l IH.
case/andP=> bLn lA.
rewrite inE => /orP[/val_eqP/val_eqP /=|/IH HH].
  by rewrite !inordK // => /eqP->; rewrite inE eqxx.
by rewrite inE HH ?orbT.
Qed.

Section Table.

Variable n : nat.

Local Notation T := 'I_n.+1.

(* ---- 1. Tables and the permutation they present -------------------------- *)

Definition tab_ok (t : seq nat) :=
  [&& size t == n.+1, all (fun i => i < n.+1) t & uniq t].

(* An entry of a well-formed table, read at any point, is again a point.      *)
Lemma tab_lt t (i : T) : tab_ok t -> nth 0 t i < n.+1.
Proof.
by case/and3P => /eqP tsz /allP tlt _; apply: tlt; rewrite mem_nth // tsz.
Qed.

(* A well-formed table lists every point: it is n.+1 distinct points below    *)
(* n.+1, so it is a permutation of them.                                      *)
Lemma tab_memE t i : tab_ok t -> i < n.+1 -> i \in t.
Proof.
case/and3P => /eqP tsz /allP tlt tu iL.
have sub : {subset t <= iota 0 n.+1} by move=> j /tlt jL; rewrite mem_iota.
have szle : size (iota 0 n.+1) <= size t by rewrite size_iota tsz.
have [_ tE] := uniq_min_size tu sub szle.
by rewrite tE mem_iota.
Qed.

Definition ptf (t : seq nat) (i : T) : T := inord (nth 0 t i).

Lemma ptf_inj t : tab_ok t -> injective (ptf t).
Proof.
move=> tok; have /and3P[/eqP tsz _ tu] := tok => i j.
rewrite /ptf => e.
have e2 : nth 0 t i = nth 0 t j.
  by rewrite -(inordK (tab_lt i tok)) -(inordK (tab_lt j tok)) e.
by apply/val_inj/eqP; rewrite -(nth_uniq 0 _ _ tu) ?tsz ?ltn_ord // e2.
Qed.

(* Made total by falling back on the identity: a table that is not            *)
(* well-formed presents no permutation in particular.  Keeping the            *)
(* definition free of a dependent match is what makes pt easy to reason       *)
(* about -- ptE below is its only interface.                                  *)
Definition ptg (t : seq nat) : T -> T := if tab_ok t then ptf t else id.

Lemma ptg_inj t : injective (ptg t).
Proof.
rewrite /ptg; case: ifP => [h|_]; first exact: (ptf_inj h).
exact: inj_id.
Qed.

Definition pt (t : seq nat) : {perm T} := perm (@ptg_inj t).

Lemma ptE t i : tab_ok t -> pt t i = inord (nth 0 t i).
Proof. by move=> tok; rewrite permE /ptg tok. Qed.

(* ---- 2. The table operations, all on nat ----------------------------------*)

Definition id_tab : seq nat := iota 0 n.+1.

Definition comp_tab (t1 t2 : seq nat) : seq nat := [seq nth 0 t2 i | i <- t1].

Fixpoint exp_tab t m :=
  if m is m1.+1 then comp_tab t (exp_tab t m1) else id_tab.

Definition inv_tab (t : seq nat) : seq nat :=
  [seq index i t | i <- iota 0 n.+1].

Lemma tab_ok_id : tab_ok id_tab.
Proof.
rewrite /tab_ok /id_tab size_iota eqxx iota_uniq andbT /=.
by apply/allP => i; rewrite mem_iota => /andP[].
Qed.

Lemma tab_ok_comp t1 t2 : tab_ok t1 -> tab_ok t2 -> tab_ok (comp_tab t1 t2).
Proof.
move=> t1ok t2ok.
have /and3P[/eqP t1sz /allP t1lt t1u] := t1ok.
have /and3P[/eqP t2sz /allP t2lt t2u] := t2ok.
apply/and3P; split.
- by rewrite /comp_tab size_map t1sz.
- apply/allP => i /mapP[j jt1 ->]; apply: t2lt.
  by rewrite mem_nth // t2sz t1lt.
rewrite /comp_tab map_inj_in_uniq // => a b at1 bt1 e; apply/eqP.
by rewrite -(nth_uniq 0 _ _ t2u) ?t2sz ?t1lt // e.
Qed.

Lemma tab_ok_exp t m : tab_ok t -> tab_ok (exp_tab t m).
Proof.
move=> tT; elim: m => [|m IH] /=; first by apply: tab_ok_id.
by apply: tab_ok_comp.
Qed.

Lemma tab_ok_inv t : tab_ok t -> tab_ok (inv_tab t).
Proof.
move=> tok; have /and3P[/eqP tsz _ tu] := tok.
apply/and3P; split.
- by rewrite /inv_tab size_map size_iota.
- apply/allP => i /mapP[j]; rewrite mem_iota => /andP[_ jL] ->.
  by rewrite -tsz index_mem tab_memE.
rewrite /inv_tab map_inj_in_uniq ?iota_uniq // => a b.
rewrite !mem_iota => /andP[_ aL] /andP[_ bL] e.
by rewrite -(nth_index 0 (tab_memE tok aL)) e nth_index // tab_memE.
Qed.

Lemma pt1 : pt id_tab = 1.
Proof.
apply/permP => i; rewrite ptE ?tab_ok_id // perm1.
by rewrite /id_tab nth_iota ?ltn_ord // add0n inord_val.
Qed.

Lemma ptM t1 t2 : tab_ok t1 -> tab_ok t2 ->
  pt t1 * pt t2 = pt (comp_tab t1 t2).
Proof.
move=> t1ok t2ok; have /and3P[/eqP t1sz _ _] := t1ok.
apply/permP => i; rewrite permM !ptE ?tab_ok_comp //.
rewrite /comp_tab (nth_map 0) ?t1sz ?ltn_ord //.
by congr inord; congr (nth 0 t2 _); rewrite inordK ?tab_lt.
Qed.

Lemma ptX t m : tab_ok t -> pt t ^+ m = pt (exp_tab t m).
Proof.
move=> tT; elim: m => [|m IH] /=; first by rewrite expg0 pt1.
by rewrite expgS // -ptM ?IH // tab_ok_exp.
Qed.

Lemma ptV t : tab_ok t -> (pt t)^-1 = pt (inv_tab t).
Proof.
move=> tok; have /and3P[/eqP tsz _ tu] := tok.
have tiok := tab_ok_inv tok.
apply: (mulgI (pt t)); rewrite mulgV ptM //.
apply/permP => i; rewrite perm1 ptE ?tab_ok_comp //.
rewrite /comp_tab (nth_map 0) ?tsz ?ltn_ord //.
rewrite /inv_tab (nth_map 0) ?size_iota ?tab_lt //.
by rewrite nth_iota ?tab_lt // add0n index_uniq ?tsz ?ltn_ord // inord_val.
Qed.

(* Conjugation, the operation the symmetry facts are stated with.             *)
Lemma ptJ t1 t2 : tab_ok t1 -> tab_ok t2 ->
  (pt t1) ^ (pt t2) = pt (comp_tab (inv_tab t2) (comp_tab t1 t2)).
Proof.
move=> t1ok t2ok.
have t2iok := tab_ok_inv t2ok; have t12ok := tab_ok_comp t1ok t2ok.
by rewrite conjgE ptV // !ptM.
Qed.

(* ---- 3. From cycles to tables -------------------------------------------- *)

(* The table of the cycle on the points of l: each listed point goes to the   *)
(* next one, cyclically; everything else stays.                               *)
Definition cyc_tab (l : seq nat) : seq nat :=
  [seq (if i \in l then nth 0 l ((index i l).+1 %% size l) else i)
  | i <- iota 0 n.+1].

Definition cycs_tab (ll : seq (seq nat)) : seq nat :=
  foldr (fun l t => comp_tab (cyc_tab l) t) id_tab ll.

Lemma tab_ok_cyc l : all (fun i => i < n.+1) l -> uniq l -> tab_ok (cyc_tab l).
Proof.
move=> lA lU; rewrite /tab_ok; rewrite size_map size_iota eqxx andTb.
apply/andP; split.
  apply/allP => /= i /mapP[/= j]; rewrite inE mem_iota add1n => /orP[/eqP->|jL].
    case: (boolP (0 \in _)) => iIl -> //.
    by apply: (allP lA); rewrite mem_nth // ltn_mod //; case: (l) iIl.
  case: (boolP (j \in _)) => jIl -> //.
    by apply: (allP lA); rewrite mem_nth // ltn_mod //; case: (l) jIl.
  by case/andP: jL.
apply/(uniqP 0) => i j; rewrite size_map size_iota //= => iLn jLn.
rewrite !(nth_map 0, size_iota) // !nth_iota // !add0n.
have [iIl|iNIl] := boolP (i \in _); last first.
  have [jIl iE|//] := boolP (j \in _).
  by case/negP : iNIl; rewrite iE mem_nth // ltn_mod; case: (l) jIl.
have [jIl|jNIl jE] := boolP (j \in _); last first.
  by case/negP: jNIl; rewrite -jE mem_nth // ltn_mod; case: (l) iIl.
move=> Hn; suff : index i l = index j l by apply: index_inj.
suff : (index i l).+1 = (index j l).+1 by case.
suff : (index i l).+1  = (index j l).+1  %[mod size l].
  move: iIl jIl; rewrite -!index_mem.
  case : (ltngtP (index i l).+1 (size l)) => // [iLs|->] _.
    rewrite modn_small //.
    case : (ltngtP (index j l).+1 (size l)) => // [jLs|->] _.
      by rewrite modn_small.
    by rewrite modnn => /eqP.
  rewrite modnn.
  case : (ltngtP (index j l).+1 (size l)) => // jLs.
  by rewrite modn_small //; case.
have s_gt0 : 0 < size l by case: (l) iIl.
by apply: (uniqP 0 lU) => //; apply: ltn_pmod.
Qed.

(* THE BRIDGE: a cycle, read off its list of points, is the table cycle.      *)
Lemma cyc_pt l : all (fun i => i < n.+1) l -> uniq l ->
  cyc ((map inord l) : seq T) = pt (cyc_tab l).
Proof.
move=> lA lU.
apply/permP => /= i.
rewrite !permE /ptg tab_ok_cyc // /ptf /cyc_tab.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
have [iIl|iNIl] := boolP ((i :nat) \in l).
  have: @inord n i \in [seq inord i  | i <- l] by apply: map_f.
  rewrite inord_val => /(nth_index ord0) {1}<-.
  rewrite cyc_nth //; last 2 first.
  - by apply: uniq_inord.
  - rewrite index_mem.
    have <- : @inord n i = i by apply: inord_val.
    by apply: map_f.
  rewrite size_map.
  suff -> : index i [seq inord i0  | i0 <- l] = index (i : nat) l.
    by rewrite (nth_map 0) ?inord_val ?ltn_mod //; case: (l) iIl.
  elim: (l) lA iIl => //= a l1 IH /andP[aLi lH].
  rewrite inE => /orP[/eqP<-|/IH-> //]; first by rewrite inord_val !eqxx.
  case: (a =P _) => [->|aDi]; first by rewrite inord_val eqxx.
  case: (_ =P _) => // aE; case: aDi; rewrite -aE.
  by rewrite inordK.
rewrite cyc_notin ?inord_val //.
apply/negP=> /mapP[j jIl iE].
case/negP: iNIl.
suff -> : i = inord j by rewrite inordK //; apply: (allP lA).
by rewrite -iE.
Qed.

Lemma tab_ok_cycs ll :
  all (all (fun i => i < n.+1)) ll -> all uniq ll -> tab_ok (cycs_tab ll).
Proof.
elim: ll => [_ _|l ll IH /andP[lA llA] /andP[lU llU]]; first exact: tab_ok_id.
by apply: tab_ok_comp; [apply: tab_ok_cyc | apply: IH].
Qed.

(* A product of cycles is the composite of their tables.                      *)
Lemma cycs_pt ll :
  all (all (fun i => i < n.+1)) ll -> all uniq ll ->
  \prod_(l <- [seq (map inord l : seq T) | l <- ll]) cyc l = pt (cycs_tab ll).
Proof.
elim: ll => [_ _|l ll IH /andP[lA llA] /andP[lU llU]].
  by rewrite big_nil pt1.
by rewrite map_cons big_cons IH // cyc_pt // ptM ?tab_ok_cyc ?tab_ok_cycs.
Qed.

End Table.
