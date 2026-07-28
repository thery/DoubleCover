(* =========================================================================  *)
(*  Fstab.v                                                                   *)
(*                                                                            *)
(*  The pruning table, and the two checks that make it usable.                *)
(*                                                                            *)
(*  SKELETON.  Definitions and statements are meant to be final; the real     *)
(*  proofs are Admitted, each with a note on how it goes.  Nothing here is    *)
(*  computed yet -- the two computations are exactly what this file defers.   *)
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

(* the completeness lemma: this is the only thing the loop is used for, and   *)
(* it is the get_foldi_in pattern -- induct on k, split at the midpoint.      *)
Lemma all_powP k f x :
  k <= ndigits -> all_pow k 0%uint63 f -> to_nat x < (2 ^ k)%N -> f x.
Proof. Admitted.

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
Definition nwords := (nstates %/ nper)%N.   (* 2 097 152                          *)

Section Table.

(* The generated table.  A Variable, not a Parameter: this file introduces no *)
(* axiom, and the generated file -- an Eval vm_compute in a Definition, in    *)
(* the style of bench/Store.v -- instantiates it.                             *)
Variable fstab : arr.
Hypothesis fstab_len : PArray.length fstab = of_nat nwords.
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
Proof. Admitted.

(* ---- 4. The move data ---------------------------------------------------- *)

(* actfs x m reads m only through src m and xbit m -- twelve positions and    *)
(* twelve bits.  The check cannot quantify over permutations, so it runs on   *)
(* that data; mdat_of_tab derives it from a move table, so there is no second *)
(* copy of the moves to get wrong.                                            *)

Definition eposn (f : nat) : nat := index f (eprim ++ esec) %% nedge.

Definition mdatum := (seq nat * seq bool)%type.

Definition mdat_of_tab (mt : seq nat) : mdatum :=
  ([seq eposn (nth 0%N (inv_tab 47 mt) (nth 0%N eprim k)) | k <- iota 0 nedge],
   [seq ~~ (nth 0%N (inv_tab 47 mt) (nth 0%N eprim k) \in eprim)
   | k <- iota 0 nedge]).

Definition actd (x : int) (d : mdatum) : int :=
  packn ncoord
    (fun k => if k < nedge
              then nbit x (nth 0%N d.1 k) (+) nth false d.2 k
              else nbit x (nedge + nth 0%N d.1 (k - nedge))).

(* the bridge, in the shape of coordtE: ptE and ptV turn the permutation      *)
(* reads of src and xbit into the table reads of mdat_of_tab.                 *)
Lemma actdE mt x :
  tab_ok 47 mt -> actfs x (pt 47 mt) = actd x (mdat_of_tab mt).
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.

(* x outside the summaries is Dfs_oob; inside, all_powP gives the checked     *)
(* instance and actdE turns the move into its data.                           *)
Lemma DfsStep_of_check :
  checkStep -> forall x m, m \in Sset -> Dfs x <= (Dfs (actfs x m)).+1.
Proof. Admitted.

End Table.
