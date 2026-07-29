(* =========================================================================  *)
(*  Fstab.v                                                                   *)
(*                                                                            *)
(*  The pruning table, and the two checks that make it usable.                *)
(*                                                                            *)
(*  No admits.  Nothing here is computed either: the two computations are     *)
(*  exactly what this file reduces the table's obligations to.                *)
(*                                                                            *)
(*  WHAT THIS FILE IS FOR.  Coordfs.v needs a D with                          *)
(*                                                                            *)
(*      Dfs (coordfs 1) = 0        and      Dfs x <= (Dfs (actfs x m)).+1     *)
(*                                                                            *)
(*  and nothing else -- the table is never proved to be a distance, or even   *)
(*  to be the result of a breadth first search.  It is data that passes two   *)
(*  checks.  So the content of this file is the REDUCTION OF THOSE TWO        *)
(*  PROPOSITIONS TO TWO BOOLEANS, check0 and checkStep, after which a         *)
(*  generated table plus two vm_compute finish the job with no axiom.         *)
(*                                                                            *)
(*  Three things have to be arranged for that reduction to exist.             *)
(*                                                                            *)
(*  x RANGES OVER ALL OF int, not over the 2 ^ 24 summaries.  A loop can only *)
(*  cover the latter, so the table is given default 0: out of range Dfs is 0, *)
(*  and 0 <= _.+1 needs no check.  That is Dfs_oob, and it is why the         *)
(*  generated table must be made with 0 rather than with a cap value.         *)
(*                                                                            *)
(*  m RANGES OVER Sset, whose elements are permutations and do not compute.   *)
(*  actfs x m only ever uses src m and xbit m, twelve numbers and twelve      *)
(*  bits, so the check runs on that data instead -- derived from the move     *)
(*  TABLES by mdat_of_tab, not transcribed.  actdE is the bridge.             *)
(*                                                                            *)
(*  THE LOOP CANNOT COUNT IN nat.  2 ^ 24 as a unary numeral is 16 million    *)
(*  constructors before the loop even starts.  all_pow recurses on the        *)
(*  EXPONENT instead: a term of size 24 that visits 2 ^ 24 values.            *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- 1. A loop over a power of two --------------------------------------- *)

(* all_pow k i f checks f on the 2 ^ k consecutive values from i.  Recursion  *)
(* is on k, so the term is 24 deep for 16 777 216 values; a fuel in nat would *)
(* be the numeral itself.  Both halves are visited, so nothing is skipped.    *)
Fixpoint all_pow (k : nat) (i : int) (f : int -> bool) : bool :=
  if k is k1.+1
  then all_pow k1 i f && all_pow k1 (add i (lsl 1%uint63 (of_nat k1))) f
  else f i.

(* a loop over a predicate that holds everywhere holds *)
Lemma all_pow_all k i (f : int -> bool) : (forall x, f x) -> all_pow k i f.
Proof. by move=> hf; elim: k i => //= k IH i; rewrite !IH. Qed.

(* the completeness lemma.  The induction has to be on a general starting
   point -- the recursive call starts at i + 2 ^ k1, not at 0 -- so the
   statement below is the one to prove and all_powP is its instance at 0. *)

(* the step of the induction: the second half starts 2 ^ k further on, and
   that addition does not wrap                                              *)
Lemma to_nat_addlsl i k :
  k < ndigits -> to_nat i + (2 ^ k)%N < nwB ->
  to_nat (i + lsl 1 (of_nat k))%uint63 = to_nat i + (2 ^ k)%N.
Proof.
move=> kL hb; have h2 : to_nat (lsl 1 (of_nat k)) = (2 ^ k)%N.
  exact: to_nat_lsl1.
by rewrite to_nat_add h2.
Qed.

(* the completeness of the loop, by the get_foldi_in induction: split at the
   midpoint, and to_nat_addlsl for the second half starting 2 ^ k further on *)
Lemma all_pow_gen k i f x :
  k <= ndigits -> to_nat i + (2 ^ k)%N <= nwB -> all_pow k i f ->
  to_nat i <= to_nat x < to_nat i + (2 ^ k)%N -> f x.
Proof.
elim: k i => [|k IH] i kL hb /=.
  (* 2 ^ 0 = 1, so to_nat i <= to_nat x < to_nat i + 1 pins x = i *)
  move=> hf /andP[h1 h2]; rewrite expn0 addn1 ltnS in h2.
  by have -> : x = i by apply: to_nat_inj; apply/eqP; rewrite eqn_leq h1 h2.
move=> /andP[hlo hhi] /andP[h1 h2].
have kL' : k <= ndigits by apply: ltnW.
have hhalf : to_nat i + 2 ^ k <= nwB.
  by apply: leq_trans hb; rewrite leq_add2l leq_exp2l.
have [hlt|hge] := ltnP (to_nat x) (to_nat i + 2 ^ k).
  by apply: (IH i) => //; rewrite h1.                    (* first half *)
have hi2 : to_nat (i + lsl 1 (of_nat k)) = to_nat i + 2 ^ k.
  by apply: to_nat_addlsl => //; apply: leq_trans hb;
    rewrite ltn_add2l ltn_exp2l.
apply: (@IH (i + lsl 1 (of_nat k))%uint63) => //.            (* second half *)
  by rewrite hi2 -addnA addnn -mul2n -expnS.
by rewrite hi2 hge -addnA addnn -mul2n -expnS.
Qed.

Lemma all_powP k f x :
  k <= ndigits -> all_pow k 0%uint63 f -> to_nat x < (2 ^ k)%N -> f x.
Proof.
move=> kL hall hx; apply: (all_pow_gen kL _ hall); rewrite to_nat_0 add0n //.
by rewrite nwB_pow leq_exp2l.
Qed.

(* Reading a table built as a map over iota.  Stated for a general n on
   purpose: with n a literal, rewriting nth_map/nth_iota makes the iota
   compute and the whole list unfold.                                       *)
Lemma nth_map_iota (T : Type) (d : T) (f : nat -> T) n p :
  p < n -> nth d [seq f k | k <- iota 0 n] p = f p.
Proof. by move=> pL; rewrite (nth_map 0%N) ?size_iota // nth_iota. Qed.

(* ---- 2. How the table is packed ------------------------------------------ *)

(* Entries are at most 9, so four bits; eight to a word makes the word index  *)
(* a shift rather than a division, at the price of leaving 31 of the 63 bits  *)
(* empty.  2 ^ 24 entries is then 2 ^ 21 words, 16 MB, one flat PArray --     *)
(* PArray.max_length is 4 194 303, so a two level array is not needed.        *)

Definition nwidth := 4.                 (* bits per entry                     *)
Definition nwidthlog := 2.              (* nwidth = 2 ^ nwidthlog             *)
Definition nperlog := 3.                (* entries per word = 2 ^ nperlog     *)
Definition nper := (2 ^ nperlog)%N.
Definition emask := ((2 ^ nwidth).-1)%N.    (* 15                                 *)
Definition nstates := (2 ^ ncoord)%N.       (* 16 777 216                         *)
Definition nwordslog := (ncoord - nperlog)%N.  (* 21                              *)

(* The array size is an int CONSTANT, not of_nat of a nat one.  nat is unary,
   so of_nat (2 ^ 21) makes the kernel build two million successors the first
   time anything has to convert it -- which unification does, silently, and
   then the file simply never finishes compiling.                             *)
Definition nwordsi : int := lsl 1%uint63 (of_nat nwordslog).

Section Table.

(* The generated table.  A Variable, not a Parameter: this file introduces no *)
(* axiom, and the generated file -- an Eval vm_compute in a Definition, in    *)
(* the style of bench/Store.v -- instantiates it.                             *)
Variable fstab : arr.
Hypothesis fstab_len : PArray.length fstab = nwordsi.
Hypothesis fstab_def : PArray.default fstab = 0%uint63.

(* ---- 3. Reading it ------------------------------------------------------- *)

Definition Dfsi (x : int) : int :=
  (lsr (PArray.get fstab (lsr x (of_nat nperlog)))
       (lsl (x land of_nat nper.-1) (of_nat nwidthlog))
   land of_nat emask)%uint63.

Definition Dfs (x : int) : nat := to_nat (Dfsi x).

(* Out of range the array gives its default, which is why the default has to  *)
(* be 0: it makes the certificate hold there for nothing, so the loop below   *)
(* only has to cover the 2 ^ 24 summaries.                                    *)
Lemma Dfs_oob x : (2 ^ ncoord)%N <= to_nat x -> Dfs x = 0.
Proof.
move=> hx; rewrite /Dfs /Dfsi.
have key : (2 ^ nwordslog)%N <= to_nat x %/ (2 ^ nperlog)%N.
  rewrite leq_divRL; last by rewrite expn_gt0.
  by rewrite -expnD /nwordslog subnK.
have hoob : (lsr x (of_nat nperlog) <? PArray.length fstab)%uint63 = false.
  rewrite fstab_len; apply/negbTE; apply/negP => /nltbP.
  rewrite to_nat_lsr of_natK; last by apply: (@ltn_nwB 6).
  rewrite /nwordsi to_nat_lsl1; last by vm_compute.
  by rewrite ltnNge key.
rewrite (@PArray.get_out_of_bounds int fstab _ hoob) fstab_def.
apply/eqP; rewrite -[0]/(to_nat 0%uint63) (inj_eq to_nat_inj); apply/eqP.
have h0 k : lsr 0%uint63 k = 0%uint63.
  by apply: to_nat_inj; rewrite to_nat_lsr to_nat_0 div0n.
rewrite h0; apply: bit_ext => n; rewrite land_spec.
by rewrite (@bit_false_lt 0%uint63 0 n) ?to_nat_0.
Qed.

(* ---- 4. The move data ---------------------------------------------------- *)

(* actfs x m reads m only through src m and xbit m -- twelve positions and    *)
(* twelve bits.  The check cannot quantify over permutations, so it runs on   *)
(* that data; mdat_of_tab derives it from a move table, so there is no second *)
(* copy of the moves to get wrong.                                            *)

Definition eposn (f : nat) : nat := index f (eprim ++ esec) %% nedge.

Definition mdatum := (seq nat * seq bool)%type.

(* Two named definitions rather than one pair: a projection out of a literal
   pair only reduces under /=, and /= also computes iota 0 nedge and unfolds
   the map over it, after which nth_map_iota has nothing to match.          *)
Definition msrc (mt : seq nat) : seq nat :=
  [seq eposn (nth 0%N (inv_tab 47 mt) (nth 0%N eprim k)) | k <- iota 0 nedge].

Definition mxbit (mt : seq nat) : seq bool :=
  [seq ~~ (nth 0%N (inv_tab 47 mt) (nth 0%N eprim k) \in eprim)
  | k <- iota 0 nedge].

Definition mdat_of_tab (mt : seq nat) : mdatum := (msrc mt, mxbit mt).

Lemma mdat_fst mt : (mdat_of_tab mt).1 = msrc mt. Proof. by []. Qed.
Lemma mdat_snd mt : (mdat_of_tab mt).2 = mxbit mt. Proof. by []. Qed.

Definition actd (x : int) (d : mdatum) : int :=
  packn ncoord
    (fun k => if k < nedge
              then nbit x (nth 0%N d.1 k) (+) nth false d.2 k
              else nbit x (nedge + nth 0%N d.1 (k - nedge))).

(* the bridge, in the shape of coordtE: ptE and ptV turn the permutation      *)
(* reads of src and xbit into the table reads of mdat_of_tab.                 *)
(* the bridge, in the shape of coordtE: ptE and ptV turn the permutation      *)
(* reads of src and xbit into the table reads of msrc and mxbit.              *)
Lemma actdE mt x :
  tab_ok 47 mt -> actfs x (pt 47 mt) = actd x (mdat_of_tab mt).
Proof.
move=> mok; have iok := tab_ok_inv mok.
have ilt p : p < nedge -> nth 0%N (inv_tab 47 mt) (nth 0%N eprim p) < nfacelet.
  move=> pL; have /and3P[/eqP sz /allP hall _] := iok.
  by apply: hall; rewrite mem_nth // sz eprim_lt.
have hval p : p < nedge ->
    (pt 47 mt)^-1 (eprimf p) = inord (nth 0%N (inv_tab 47 mt) (nth 0%N eprim p)).
  by move=> pL; rewrite (ptV mok) ptE // eprimfK.
have hsrc p : p < nedge -> src (pt 47 mt) p = nth 0%N (mdat_of_tab mt).1 p.
  move=> pL; rewrite /src hval // /epos inordK ?ilt //.
  by rewrite mdat_fst /msrc nth_map_iota.
have hxb p : p < nedge -> xbit (pt 47 mt) p = nth false (mdat_of_tab mt).2 p.
  move=> pL; rewrite /xbit hval // /pcol inordK ?ilt //.
  by rewrite mdat_snd /mxbit nth_map_iota.
rewrite /actfs /actd; apply: eq_packn => j jL.
have hsub : nedge <= j -> j - nedge < nedge.
  by move=> jn; rewrite -(ltn_add2l nedge) subnKC.
case: ltnP => jn.
  by rewrite hsrc // hxb.
by rewrite hsrc ?hsub.
Qed.

(* the moves as tables, and the one fact tying them to Rubik333.moves; the    *)
(* assembly file supplies both, as Toy.v does today.                          *)
Variable mtabs : seq (seq nat).
Hypothesis mtabs_ok : all (tab_ok 47) mtabs.
Hypothesis mtabsE : moves = [seq pt 47 mt | mt <- mtabs].

Definition mdata : seq mdatum := [seq mdat_of_tab mt | mt <- mtabs].

(* ---- 5. The two checks --------------------------------------------------- *)

(* coordfs 1 does not compute, being about a permutation; the identity table  *)
(* is its computable form, by pt1 and coordtE.                                *)
Lemma coordfs1E : coordfs 1 = coordt (id_tab 47).
Proof. by rewrite -(coordtE (tab_ok_id 47)) pt1. Qed.

Definition check0 : bool := (Dfsi (coordt (id_tab 47)) =? 0)%uint63.

(* Entries are at most 15, so the successor cannot wrap and the nat           *)
(* inequality can be checked on int.                                          *)
Definition checkStep : bool :=
  all_pow ncoord 0%uint63
    (fun x => all (fun d => (Dfsi x <=? incr (Dfsi (actd x d)))%uint63) mdata).

(* ---- 6. What the two checks buy ------------------------------------------ *)

(* THESE TWO ARE THE POINT OF THE FILE.  Once they are proved, a generated    *)
(* table and two vm_compute discharge Coordfs.v's Dfs0 and DfsStep, and the   *)
(* heuristic has no axiom behind it.                                          *)

Lemma Dfs0_of_check : check0 -> Dfs (coordfs 1) = 0.
Proof. by rewrite /check0 /Dfs coordfs1E => /eqb_correct ->; rewrite to_nat_0. Qed.

(* x outside the summaries is Dfs_oob; inside, all_powP gives the checked     *)
(* instance and actdE turns the move into its data.                           *)
(* the entries are four bits, so the successor on the int side is the
   successor on the nat side -- no wrap to worry about                       *)
Lemma Dfsi_small x : to_nat (Dfsi x) < nwB.-1.
Proof.
rewrite /Dfsi.
set v := (X in (X land _)%uint63); rewrite landC.
apply: ltn_trans (_ : 2 ^ 4 < _); last first.
rewrite -ltnS prednK; last by apply: ltn_trans ndigitsLwB.
apply: ltn_trans ndigitsLwB => //.
by apply: to_nat_land_bound.
Qed.

Lemma leb_incr_le a b :
  (a <=? incr b)%uint63 -> to_nat b < nwB.-1 -> to_nat a <= (to_nat b).+1.
Proof.
move=> aLb bLwB.
rewrite -to_nat_incr; first by apply/nlebP.
by rewrite -[nwB]prednK // (ltn_trans _ ndigitsLwB).
Qed.

(* the routing: out of range is Dfs_oob, in range is all_powP for the checked
   instance and actdE to turn the move into its data.  Note the /checkStep
   has to come before the intros -- unfolding it afterwards is what made this
   look like it diverged.                                                    *)
Lemma DfsStep_of_check :
  checkStep -> forall x m, m \in Sset -> Dfs x <= (Dfs (actfs x m)).+1.
Proof.
rewrite /checkStep.
move=> hcheck x m mS.
have [hx|hx] := ltnP (to_nat x) (2 ^ ncoord); last by rewrite Dfs_oob.
have [mt mtM mE] : exists2 mt, mt \in mtabs & m = pt 47 mt.
  by move: mS; rewrite inE mtabsE => /mapP[mt mtM ->]; exists mt.
have mtok : tab_ok 47 mt by apply: (allP mtabs_ok).
have hd : actfs x m = actd x (mdat_of_tab mt) by rewrite mE actdE.
have hall := all_powP ncoord_dig hcheck hx.
have F := allP hall (mdat_of_tab mt) (map_f _ mtM).
by rewrite hd /Dfs; apply: leb_incr_le; last by exact: Dfsi_small.
Qed.

End Table.
