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
Require Import Table Search.

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
move=> t1ok t2ok /permP pE.
have /and3P[/eqP t1sz _ _] := t1ok; have /and3P[/eqP t2sz _ _] := t2ok.
apply: (@eq_from_nth _ 0) => [|i]; first by rewrite t1sz t2sz.
rewrite t1sz => iL; have := pE (Ordinal iL).
rewrite !ptE // => /=.
have L1 := tab_lt (Ordinal iL) t1ok; have L2 := tab_lt (Ordinal iL) t2ok.
by move=> H; rewrite -(inordK L1) -(inordK L2) H.
Qed.

Lemma pt_eq1 t : tab_ok n t -> (pt n t == 1) = (t == id_tab n).
Proof.
move=> tok; apply/eqP/eqP => [pE|->]; last exact: pt1.
by apply: (pt_inj tok (tab_ok_id n)); rewrite pE pt1.
Qed.

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
elim: d t => [t tok|d IH t tok] /=; rewrite hE // pt_eq1 //.
congr (_ && (_ || _)); rewrite has_map /=.
apply: eq_in_has => mt mtM /=.
have mtok : tab_ok n mt by apply: (allP mtsok).
by rewrite ptM //; apply: IH; apply: tab_ok_comp.
Qed.

(* A false answer from the computable search is a false answer from the one   *)
(* Search.v proves sound.                                                     *)
Corollary searchtN d t :
  tab_ok n t -> searcht d t = false ->
  search [seq pt n mt | mt <- mts] h d (pt n t) = false.
Proof. by move=> tok; rewrite searchtE. Qed.

End TSearch.
