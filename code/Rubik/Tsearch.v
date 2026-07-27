(* =========================================================================  *)
(*  Tsearch.v                                                                 *)
(*                                                                            *)
(*  The search of Search.v, run on TABLES.                                    *)
(*                                                                            *)
(*  Nothing about a {perm 'I_n.+1} reduces: inord does not, and a cyc is a    *)
(*  bigop of tperm over a finfun, so the kernel cannot decide g == 1 or       *)
(*  compute g * m.  Table.v exists for exactly that reason, and the search    *)
(*  has to move there too: searcht walks lists of naturals, where comp_tab    *)
(*  is a map and equality is decidable by vm_compute.                         *)
(*                                                                            *)
(*  searchtE is the bridge -- the two searches agree, so a false answer from  *)
(*  the computable one is a false answer from the one Search.v proves sound.  *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball Table Search.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section TSearch.

Variable n : nat.
Local Notation T := 'I_n.+1.

(* ---- 1. A well formed table is determined by the permutation it presents - *)

Lemma pt_inj t1 t2 :
  tab_ok n t1 -> tab_ok n t2 -> pt n t1 = pt n t2 -> t1 = t2.
Proof.
(* both tables have size n.+1 and pt reads them entry by entry, so equal      *)
(* permutations force equal entries.                                          *)
Admitted.

Lemma pt_eq1 t : tab_ok n t -> (pt n t == 1) = (t == id_tab n).
Proof.
(* pt id_tab = 1, and pt is injective on well formed tables.                  *)
Admitted.

(* ---- 2. The search on tables --------------------------------------------- *)

(* the moves, as tables                                                       *)
Variable mts : seq (seq nat).
Hypothesis mtsok : all (tab_ok n) mts.

(* the heuristic, read on tables                                              *)
Variable Dt : seq nat -> nat.

Fixpoint searcht (d : nat) (t : seq nat) : bool :=
  (Dt t <= d) &&
  ((t == id_tab n) ||
   (if d is d'.+1 then has (fun mt => searcht d' (comp_tab t mt)) mts
    else false)).

(* ---- 3. The bridge ------------------------------------------------------- *)

Variable h : {perm T} -> nat.
Hypothesis hE : forall t, tab_ok n t -> h (pt n t) = Dt t.

Lemma searchtE d t :
  tab_ok n t -> searcht d t = search [seq pt n mt | mt <- mts] h d (pt n t).
Proof.
(* induction on d: hE for the cut, pt_eq1 for the solved test, and has_map    *)
(* with ptM for the recursive call, comp_tab t mt presenting pt t * pt mt.    *)
Admitted.

(* A false answer from the computable search is a false answer from the one   *)
(* Search.v proves sound.                                                     *)
Corollary searchtN d t :
  tab_ok n t -> searcht d t = false ->
  search [seq pt n mt | mt <- mts] h d (pt n t) = false.
Proof. by move=> tok; rewrite searchtE. Qed.

End TSearch.
