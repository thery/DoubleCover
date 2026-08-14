(* =========================================================================  *)
(*  Fstab.v -- The pruning table, and the two checks that make it usable.     *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Table Rubik333 Coordfs Coordfsi.

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

(* a loop over a predicate that holds everywhere holds                        *)
Lemma all_pow_all k i (f : int -> bool) : (forall x, f x) -> all_pow k i f.
Proof. by move=> hf; elim: k i => //= k IH i; rewrite !IH. Qed.

(* the completeness lemma.  The induction has to be on a general starting     *)
(* point -- the recursive call starts at i + 2 ^ k1, not at 0 -- so the       *)
(* statement below is the one to prove and all_powP is its instance at 0.     *)

(* the step of the induction: the second half starts 2 ^ k further on, and    *)
(* that addition does not wrap                                                *)
Lemma to_nat_addlsl i k :
  k < ndigits -> to_nat i + (2 ^ k)%N < nwB ->
  to_nat (i + lsl 1 (of_nat k))%uint63 = to_nat i + (2 ^ k)%N.
Proof.
move=> kL hb; have h2 : to_nat (lsl 1 (of_nat k)) = (2 ^ k)%N.
  exact: to_nat_lsl1.
by rewrite to_nat_add h2.
Qed.

(* the completeness of the loop, by the get_foldi_in induction: split at the  *)
(* midpoint, and to_nat_addlsl for the second half starting 2 ^ k further on  *)
Lemma all_pow_gen k i f x :
  k <= ndigits -> to_nat i + (2 ^ k)%N <= nwB -> all_pow k i f ->
  to_nat i <= to_nat x < to_nat i + (2 ^ k)%N -> f x.
Proof.
elim: k i => [|k IH] i kL hb /=.
  (* 2 ^ 0 = 1, so to_nat i <= to_nat x < to_nat i + 1 pins x = i             *)
  move=> hf /andP[h1 h2]; rewrite expn0 addn1 ltnS in h2.
  by have -> : x = i by apply: to_nat_inj; apply/eqP; rewrite eqn_leq h1 h2.
move=> /andP[hlo hhi] /andP[h1 h2].
have kL' : k <= ndigits by apply: ltnW.
have hhalf : to_nat i + 2 ^ k <= nwB.
  by apply: leq_trans hb; rewrite leq_add2l leq_exp2l.
have [hlt|hge] := ltnP (to_nat x) (to_nat i + 2 ^ k).
  by apply: (IH i) => //; rewrite h1.                    (* first half        *)
have hi2 : to_nat (i + lsl 1 (of_nat k)) = to_nat i + 2 ^ k.
  by apply: to_nat_addlsl => //; apply: leq_trans hb;
    rewrite ltn_add2l ltn_exp2l.
apply: (@IH (i + lsl 1 (of_nat k))%uint63) => //.            (* second half   *)
  by rewrite hi2 -addnA addnn -mul2n -expnS.
by rewrite hi2 hge -addnA addnn -mul2n -expnS.
Qed.

Lemma all_powP k f x :
  k <= ndigits -> all_pow k 0%uint63 f -> to_nat x < (2 ^ k)%N -> f x.
Proof.
move=> kL hall hx; apply: (all_pow_gen kL _ hall); rewrite to_nat_0 add0n //.
by rewrite nwB_pow leq_exp2l.
Qed.

(* The same loop, with the offset of the second half carried as an int        *)
(* rather than rebuilt as 1 << of_nat k at each of the 2 ^ k nodes, and with  *)
(* nested ifs in place of &&.  all_powiE says the two agree.                  *)
Fixpoint all_powi (k : nat) (i off : int) (f : int -> bool) : bool :=
  if k is k1.+1 then
    let off' := lsr off 1 in
    if all_powi k1 i off' f then all_powi k1 (add i off') off' f else false
  else f i.

Lemma lsl1S k : k.+1 < ndigits ->
  lsr (lsl 1 (of_nat k.+1)) 1 = lsl 1 (of_nat k).
Proof.
move=> kL; apply: to_nat_inj.
rewrite to_nat_lsr to_nat_lsl1 // to_nat_lsl1; last by apply: ltnW.
by rewrite to_nat_1 expnS mulKn.
Qed.

Lemma all_powiE k i f : k < ndigits ->
  all_powi k i (lsl 1 (of_nat k)) f = all_pow k i f.
Proof.
elim: k i => [|k IH] i //= kL.
have kL' : k < ndigits by apply: ltnW.
by rewrite lsl1S // !IH //; case: all_pow.
Qed.

(* Reading a table built as a map over iota.  Stated for a general n on       *)
(* purpose: with n a literal, rewriting nth_map/nth_iota makes the iota       *)
(* compute and the whole list unfold.                                         *)
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
Definition emask := ((2 ^ nwidth).-1)%N.    (* 15                             *)
Definition nstates := (2 ^ ncoord)%N.       (* 16 777 216                     *)
Definition nwordslog := (ncoord - nperlog)%N.  (* 21                          *)

(* The array size is an int CONSTANT, not of_nat of a nat one.  nat is unary, *)
(* so of_nat (2 ^ 21) makes the kernel build two million successors the first *)
(* time anything has to convert it -- which unification does, silently, and   *)
(* then the file simply never finishes compiling.                             *)
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

(* Two named definitions rather than one pair: a projection out of a literal  *)
(* pair only reduces under /=, and /= also computes iota 0 nedge and unfolds  *)
(* the map over it, after which nth_map_iota has nothing to match.            *)
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

(* ---- 4bis. actf, the same function with no nat inside the loop ------------*)

(* actd is correct but slow: per bit it walks a 12 element nat list for src,  *)
(* a 24 element bool list for xbit, and setbit does an of_nat.  Measured at   *)
(* 79 us per check, which is 6.6 h over the 16 777 216 states.  actf keeps the*)
(* twelve sources in an int array and the twelve xbits in one int, and indexes*)
(* the loop by an int, so nothing in the inner loop is a nat.  Measured at    *)
(* 8.1 us per check, which is 41 min.                                         *)

Definition mdatf := (arr * int)%type.

(* nedge and ncoord as ints, once, so the loop does not redo of_nat per bit   *)
Definition nedgei : int := Eval vm_compute in of_nat nedge.

Definition mk_srci (mt : seq nat) : arr :=
  mkarrn nedgei [seq of_nat v | v <- msrc mt].

Definition mk_xbiti (mt : seq nat) : int :=
  packn nedge (fun k => nth false (mxbit mt) k).

Definition mdatf_of_tab (mt : seq nat) : mdatf := (mk_srci mt, mk_xbiti mt).

(* packn, indexed by an int and built bottom up.  Same word, no of_nat.       *)
Fixpoint packi (k : nat) (i : int) (f : int -> bool) (acc : int) : int :=
  if k is k1.+1 then
    packi k1 (i + 1)%uint63 f (if f i then (acc lor lsl 1 i)%uint63 else acc)
  else acc.

Definition actf (x : int) (dp : mdatf) : int :=
  packi ncoord 0%uint63
    (fun p => if (p <? nedgei)%uint63
              then bit x (PArray.get dp.1 p) (+) bit dp.2 p
              else bit x (PArray.get dp.1 (p - nedgei)%uint63 + nedgei)%uint63)
    0%uint63.

(* ---- 4ter. the obligations that make actf equal to actd -------------------*)

(* (a) the loop.  packi only ors bits in, so every bit of acc survives and the*)
(* bits it adds are exactly i .. i+k-1.  Generalised in i and acc, else the   *)
(* induction has nothing to chew on: packi k.+1 0 f 0 recurses at index 1.    *)
(* setbit with an int index, the one step of the loop                         *)
Lemma nbit_lori (x i : int) (b : bool) j :
  to_nat i < ndigits -> j < ndigits ->
  nbit (if b then (x lor lsl 1 i)%uint63 else x) j
  = nbit x j || ((j == to_nat i) && b).
Proof.
move=> hid hjd; case: b; last by rewrite andbF orbF.
have hjw : j < nwB by apply: ltn_trans hjd ndigitsLwB.
have hi : (i <? digits)%uint63 by apply/nltbP.
have hj : (of_nat j <? digits)%uint63 by apply/nltbP; rewrite of_natK.
rewrite andbT /nbit lor_spec bit_onenn //; congr (_ || _).
apply/idP/idP => [/eqP->|/eqP->]; first by rewrite of_natK.
by rewrite to_natK.
Qed.

Lemma nbit_packi k i f acc j :
  j < ndigits -> to_nat i + k <= ndigits ->
  nbit (packi k i f acc) j
  = nbit acc j || [&& to_nat i <= j, j < to_nat i + k & f (of_nat j)].
Proof.
move=> hjd.
elim: k i acc => [|k IH] i acc hb /=; first by rewrite addn0 leqNgt andbA andNb orbF.
have hid : to_nat i < ndigits.
  by apply: leq_trans hb; rewrite addnS ltnS leq_addr.
have hi1 : to_nat (i + 1)%uint63 = (to_nat i).+1.
  rewrite -[(i+1)%uint63]/(incr _) to_nat_incr //.
  by apply: leq_ltn_trans hid ndigitsLwB.
rewrite IH ?hi1; last by move: hb; rewrite addnS.
rewrite nbit_lori // -orbA; congr (_ || _).
rewrite addnS addSn.
have [->|jne] := eqVneq j (to_nat i).
  by rewrite ltnn leqnn ltnS leq_addr to_natK /= orbF.
by rewrite orFb ltn_neqAle eq_sym (negPf jne).
Qed.

Lemma packi_lt k i f acc :
  to_nat i + k <= ndigits -> to_nat acc < 2 ^ (to_nat i + k) ->
  to_nat (packi k i f acc) < 2 ^ (to_nat i + k).
Proof.
elim: k i acc => [|k IH] i acc hb hacc //=.
have hid : to_nat i < ndigits.
  by apply: leq_trans hb; rewrite addnS ltnS leq_addr.
have hi1 : to_nat (i + 1)%uint63 = (to_nat i).+1.
  rewrite -[(i+1)%uint63]/(incr _) to_nat_incr //.
  by apply: leq_ltn_trans hid ndigitsLwB.
have hsw : to_nat i + k.+1 = to_nat (i + 1)%uint63 + k.
  by rewrite hi1 addSn addnS.
rewrite hsw; apply: IH; first by rewrite -hsw.
rewrite -hsw; case: (f i) => //.
apply: to_nat_lor_bound => //.
rewrite -{1}(to_natK i) to_nat_lsl1 // ltn_exp2l //.
by rewrite addnS ltnS leq_addr.
Qed.

(* (b) the two agree, by packn_eq on the k bits.  This is the payoff of (a).  *)
Lemma packiE k (f : int -> bool) :
  k <= ndigits -> packi k 0%uint63 f 0%uint63 = packn k (fun j => f (of_nat j)).
Proof.
move=> hk; apply: (@packn_eq k).
- have H := @packi_lt k 0%uint63 f 0%uint63.
  by rewrite to_nat_0 add0n in H; apply: H => //; rewrite expn_gt0.
- by apply: packn_lt.
move=> j jk.
have hjd : j < ndigits by apply: leq_trans jk hk.
rewrite nbit_packi ?to_nat_0 ?add0n //.
by rewrite nbit_packn // /nbit bit_0 leq0n jk /=.
Qed.

Lemma nedge_dig : nedge <= ndigits.
Proof. by apply: leq_trans ncoord_dig; rewrite /ncoord leq_addr. Qed.

(* of_nat commutes with the three operations the loop does, below nwB.  These *)
(* are generic int63 facts and would sit better in ssrint63.v; they are here  *)
(* to avoid a rebuild of everything that depends on it.                       *)
Lemma of_nat_ltbE m n : m < nwB -> n < nwB -> (of_nat m <? of_nat n)%uint63 = (m < n).
Proof.
move=> hm hn; apply/idP/idP => H.
  by move/nltbP: H; rewrite !of_natK.
by apply/nltbP; rewrite !of_natK.
Qed.

Lemma of_nat_addE m n : m + n < nwB -> (of_nat m + of_nat n)%uint63 = of_nat (m + n).
Proof.
move=> h.
have hm : m < nwB by apply: leq_ltn_trans h; apply: leq_addr.
have hn : n < nwB by apply: leq_ltn_trans h; apply: leq_addl.
by apply: to_nat_inj; rewrite to_nat_add !of_natK.
Qed.

Lemma of_nat_subE m n : n <= m -> m < nwB -> (of_nat m - of_nat n)%uint63 = of_nat (m - n).
Proof.
move=> hnm hm.
have hn : n < nwB by apply: leq_ltn_trans hm.
have hs : m - n < nwB by apply: leq_ltn_trans hm; apply: leq_subr.
by apply: to_nat_inj; rewrite to_nat_sub !of_natK.
Qed.

Lemma nedgeiE : nedgei = of_nat nedge. Proof. by []. Qed.
Lemma ncoordE : ncoord = nedge + nedge. Proof. by []. Qed.

(* (c) the core: actf = actd whenever the array and the packed word read back *)
(* as the two lists.  Deliberately stated on the READS, not on mk_srci, so it *)
(* needs nothing about mkarrn -- that is isolated in (d).                     *)
Lemma actfE_gen x (dp : mdatf) (d : mdatum) :
  (forall p, p < nedge -> PArray.get dp.1 (of_nat p) = of_nat (nth 0%N d.1 p)) ->
  (forall p, p < nedge -> bit dp.2 (of_nat p) = nth false d.2 p) ->
  (forall p, p < nedge -> nth 0%N d.1 p < nedge) ->
  actf x dp = actd x d.
(* Beware: nwB is 2^63, so a stray // on a `_ < nwB` side goal sends done off *)
(* computing it in unary and the file never compiles -- it looks exactly like *)
(* a diverging tactic.  Every such bound is discharged from hnw below.        *)
Proof.
move=> hget hbit hlt.
have hnw k : k <= ndigits -> k < nwB.
  by move=> kL; apply: leq_ltn_trans kL ndigitsLwB.
have hnedge : nedge < nwB by apply: hnw; exact: nedge_dig.
rewrite /actf packiE ?ncoord_dig // /actd; apply: eq_packn => j jL.
have hjw : j < nwB by apply: hnw; apply: leq_trans (ltnW jL) ncoord_dig.
rewrite nedgeiE of_nat_ltbE //.
case: ltnP => jn; first by rewrite hget // hbit.
have hjs : j - nedge < nedge.
  by rewrite -(ltn_add2r nedge) (subnK jn) -ncoordE; exact: jL.
have h1 : nth 0%N d.1 (j - nedge) + nedge < ncoord.
  by rewrite ncoordE ltn_add2r; exact: hlt _ hjs.
have hb : nth 0%N d.1 (j - nedge) + nedge < nwB.
  by apply: hnw; apply: leq_trans (ltnW h1) ncoord_dig.
rewrite (of_nat_subE jn hjw) (hget _ hjs) (of_nat_addE hb).
by rewrite /nbit addnC.
Qed.

(* (d) reading back a literal built by mkarrn.  epairi and eprimi dodged this *)
(* by being closed terms, so 48 vm_computes did it; mk_srci mt depends on mt, *)
(* so the fold has to be reasoned about for real.                             *)
(* the fold mkarrn is, named so it can be reasoned about.  Convertible with   *)
(* mkarrn's body, hence mkarrnE by [].  Note PArray's axioms need their type  *)
(* given explicitly -- rewrite cannot unify the universe, exact can.          *)
Fixpoint setl (a : arr) (i : int) (l : seq int) : arr :=
  if l is x :: l' then setl (PArray.set a i x) (i + 1)%uint63 l' else a.

Lemma mkarrnE n l : mkarrn n l = setl (PArray.make n 0%uint63) 0%uint63 l.
Proof. by []. Qed.

Lemma length_setl l a i : PArray.length (setl a i l) = PArray.length a.
Proof.
elim: l a i => [|x l IH] a i //=.
rewrite IH; exact: (@PArray.length_set int a i x).
Qed.

(* below the written range the fold changes nothing; this is what lets the    *)
(* head of the list be read back after the tail has been written.             *)
Lemma get_setl_lt l a i j :
  to_nat i + seq.size l < nwB -> to_nat j < to_nat i ->
  PArray.get (setl a i l) j = PArray.get a j.
Proof.
elim: l a i => [|x l IH] a i //= hb hj.
have hi1 : to_nat (i + 1)%uint63 = (to_nat i).+1.
  rewrite -[(i+1)%uint63]/(incr _) to_nat_incr //.
  by apply: leq_ltn_trans hb; rewrite addnS ltnS leq_addr.
have hne : i <> j by move=> e; rewrite e ltnn in hj.
rewrite IH.
- exact: (@PArray.get_set_other int a i j x hne).
- by move: hb; rewrite hi1 addnS addSn.
by rewrite hi1; apply: ltn_trans hj _.
Qed.

Lemma get_setl l a i j :
  to_nat i + seq.size l < nwB ->
  to_nat i <= to_nat j < to_nat i + seq.size l ->
  to_nat i + seq.size l <= to_nat (PArray.length a) ->
  PArray.get (setl a i l) j = nth 0%uint63 l (to_nat j - to_nat i).
Proof.
elim: l a i => [|x l IH] a i /=.
  by rewrite addn0 => _ /andP[h1 h2]; rewrite ltnNge h1 in h2.
move=> hb /andP[hlo hhi] hlen.
have hi1 : to_nat (i + 1)%uint63 = (to_nat i).+1.
  rewrite -[(i+1)%uint63]/(incr _) to_nat_incr //.
  by apply: leq_ltn_trans hb; rewrite addnS ltnS leq_addr.
have hset : PArray.length (PArray.set a i x) = PArray.length a
  := (@PArray.length_set int a i x).
have hbnd : to_nat i < to_nat (PArray.length a).
  by apply: leq_trans hlen; rewrite addnS ltnS leq_addr.
have [e|hne] := eqVneq (to_nat i) (to_nat j).
  have -> : j = i by apply: to_nat_inj; rewrite e.
  rewrite subnn /= get_setl_lt ?hi1 //.
    by apply: (@PArray.get_set_same int a i x); apply/nltbP.
  by move: hb; rewrite addnS addSn.
have hij : to_nat i < to_nat j by rewrite ltn_neqAle hne.
have hk : 0 < to_nat j - to_nat i by rewrite subn_gt0.
rewrite IH ?hi1 ?hset.
- by rewrite subnS; case: (to_nat j - to_nat i) hk => // k _.
- by move: hb; rewrite addnS addSn.
- by rewrite hij /=; move: hhi; rewrite addnS addSn.
by move: hlen; rewrite addnS addSn.
Qed.

Lemma get_mkarrn (n : int) (l : seq int) (j : int) :
  (n <=? PArray.max_length)%uint63 -> seq.size l <= to_nat n ->
  to_nat j < seq.size l ->
  PArray.get (mkarrn n l) j = nth 0%uint63 l (to_nat j).
Proof.
move=> hmax hsz hj.
have hnwb : to_nat n < nwB by exact: to_nat_bounded.
rewrite mkarrnE -[in RHS](subn0 (to_nat j)) -[in X in _ - X](to_nat_0).
apply: get_setl; rewrite ?to_nat_0 ?add0n //.
- by apply: leq_ltn_trans hsz hnwb.
by rewrite length_makeE hmax.
Qed.

(* (e) instantiating (d) at mk_srci / mk_xbiti                                *)
Lemma nedge_small : nedge < nwB.
Proof. by apply: leq_ltn_trans ndigitsLwB; exact: nedge_dig. Qed.

Lemma size_msrc mt : seq.size (msrc mt) = nedge.
Proof. by rewrite /msrc seq.size_map seq.size_iota. Qed.

Lemma get_mk_srci mt p :
  p < nedge ->
  PArray.get (mk_srci mt) (of_nat p) = of_nat (nth 0%N (msrc mt) p).
Proof.
move=> pL.
have hp : to_nat (of_nat p) = p.
  by apply: of_natK; apply: ltn_trans pL nedge_small.
rewrite /mk_srci get_mkarrn ?hp ?seq.size_map ?size_msrc //.
by rewrite (nth_map 0%N) ?size_msrc.
Qed.

Lemma bit_mk_xbiti mt p :
  p < nedge -> bit (mk_xbiti mt) (of_nat p) = nth false (mxbit mt) p.
Proof. by move=> pL; rewrite /mk_xbiti -/(nbit _ p) nbit_packn // nedge_dig. Qed.

(* msrc lands in 0..nedge-1 by construction: eposn is a %% nedge              *)
Lemma msrc_lt mt p : p < nedge -> nth 0%N (msrc mt) p < nedge.
Proof. by move=> pL; rewrite /msrc nth_map_iota // /eposn ltn_mod. Qed.

(* (f) the bridge actually used downstream                                    *)
Lemma actfE mt x : actf x (mdatf_of_tab mt) = actd x (mdat_of_tab mt).
Proof.
apply: actfE_gen.
- by move=> p pL; apply: get_mk_srci.
- by move=> p pL; apply: bit_mk_xbiti.
by move=> p pL; apply: msrc_lt.
Qed.

(* the moves as tables, and the one fact tying them to Rubik333.moves; the    *)
(* assembly file supplies both, as Moves.v does today.                        *)
Variable mtabs : seq (seq nat).
Hypothesis mtabs_ok : all (tab_ok 47) mtabs.
Hypothesis mtabsE : moves = [seq pt 47 mt | mt <- mtabs].

Definition mdata : seq mdatum := [seq mdat_of_tab mt | mt <- mtabs].

(* the same data in the fast shape; checkStep runs on this one                *)
Definition mdataf : seq mdatf := [seq mdatf_of_tab mt | mt <- mtabs].

(* mdatum is an eqType so allP applied to mdata; mdatf holds an arr, which is *)
(* not one, so membership is unavailable and the instance has to be taken by  *)
(* index instead -- all_nthP, then nth_map through index mt mtabs.            *)
Lemma all_mdataf (P : mdatf -> bool) mt :
  all P mdataf -> mt \in mtabs -> P (mdatf_of_tab mt).
Proof.
move=> /(all_nthP (mdatf_of_tab [::])) H hmt.
have hi : index mt mtabs < seq.size mtabs by rewrite index_mem.
have := H (index mt mtabs); rewrite /mdataf seq.size_map => /(_ hi).
by rewrite (nth_map [::]) // nth_index.
Qed.

(* ---- 5. The two checks --------------------------------------------------- *)

(* coordfs 1 does not compute, being about a permutation; the identity table  *)
(* is its computable form, by pt1 and coordtE.                                *)
Lemma coordfs1E : coordfs 1 = coordt (id_tab 47).
Proof. by rewrite -(coordtE (tab_ok_id 47)) pt1. Qed.

Definition check0 : bool := (Dfsi (coordt (id_tab 47)) =? 0)%uint63.

(* Entries are at most 15, so the successor cannot wrap and the nat           *)
(* inequality can be checked on int.                                          *)
(* mdata IS HOISTED, AND THAT IS NOT COSMETIC.  Inside the lambda it is       *)
(* recomputed for every x -- call by value again -- and mdata is eighteen     *)
(* mdat_of_tab, each inverting a 48 entry nat list with index and then        *)
(* scanning a 24 entry list per edge.  Measured: 26 ms per check with it      *)
(* inside, 79 us with it hoisted, over 16 777 216 states times eighteen       *)
(* moves.  That is 90 days against 6.6 hours, for one let.                    *)
(* actd is replaced by actf here, and mdata by mdataf: same booleans by       *)
(* actfE, ten times faster.  See 4bis.                                        *)

(* THE PREDICATE IS NAMED, AND THAT IS NOT COSMETIC EITHER.  With the let     *)
(* written inline under all_pow, splitting the loop for several cores needs   *)
(* an equation between two closed all_pow ncoord terms, and proving it        *)
(* forces conversion to commute the let past all_pow -- which unfolds the     *)
(* loop into 2 ^ 24 conjuncts and never returns.  Named, the split is a       *)
(* delta step: checkStep is all_pow ncoord 0 stepF by definition, and         *)
(* Fspar.v can rewrite /checkStep and work on stepF with the loop still       *)
(* folded.                                                                    *)
Definition stepF : int -> bool :=
  let md := mdataf in
  fun x => all (fun d => (Dfsi x <=? incr (Dfsi (actf x d)))%uint63) md.

Definition checkStep : bool := all_pow ncoord 0%uint63 stepF.

(* ---- 6. What the two checks buy ------------------------------------------ *)

(* THESE TWO ARE THE POINT OF THE FILE, and they are proved.  A table that    *)
(* passes check0 and checkStep therefore discharges Coordfs.v's Dfs0 and      *)
(* DfsStep, and the heuristic has no axiom behind it.                         *)

Lemma Dfs0_of_check : check0 -> Dfs (coordfs 1) = 0.
Proof. by rewrite /check0 /Dfs coordfs1E => /eqb_correct ->; rewrite to_nat_0. Qed.

(* x outside the summaries is Dfs_oob; inside, all_powP gives the checked     *)
(* instance and actdE turns the move into its data.                           *)
(* the entries are four bits, so the successor on the int side is the         *)
(* successor on the nat side -- no wrap to worry about                        *)
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

(* the routing: out of range is Dfs_oob, in range is all_powP for the checked *)
(* instance and actdE to turn the move into its data.  Note the /checkStep    *)
(* has to come before the intros -- unfolding it afterwards is what made this *)
(* look like it diverged.                                                     *)
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
(* actfE turns the checked actf instance back into the actd one               *)
have F := all_mdataf hall mtM; rewrite actfE in F.
by rewrite hd /Dfs; apply: leb_incr_le; last by exact: Dfsi_small.
Qed.

End Table.
