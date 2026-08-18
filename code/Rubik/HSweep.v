(* =========================================================================  *)
(*  HSweep.v -- the sweep obligation D asks for, cut into jobs.               *)
(* =========================================================================  *)

(* HAdmis.hstep is the one thing about the table a machine can check:         *)
(*                                                                            *)
(*   h g <= (h (g * m)).+1   for every position g and every quarter turn m    *)
(*                                                                            *)
(* On cosets that is a sweep of the whole table, 190080 x 70 x 2187 triples   *)
(* and twelve turns each.  This file is that sweep as a boolean, cut into     *)
(* jobs, each of which is its own file.                                       *)
(*                                                                            *)
(* THE LOOP COUNTS IN int63 AND THE FUEL IS THE ONLY nat.  A list of the      *)
(* 190080 coordinates would be 190080 unary numbers of that size -- billions  *)
(* of cells before the first table is read.  iter walks an int63 and counts   *)
(* down a nat, so the only nat built is the number of steps; advn says where  *)
(* the walk has got to, and it is what lets one job start where another       *)
(* stopped without a word of int63 arithmetic.                                *)
(*                                                                            *)
(* WHAT IT IS NOT.  It is a statement about the TABLE, over coset numbers.    *)
(* Reading it as a statement about positions is obligation C, and reading the *)
(* folded table as the flat one is the symmetry argument; neither is here.    *)
(*                                                                            *)
(* ocaml/rubik_h.ml has the same sweep, `make hadmis', in the same order and  *)
(* with the same comparison, so the two are comparable coset for coset.       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Coordfs Phase1 HRoot HCoord HSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

Section Sweep.

(* the same seven tables the search takes                                     *)
Variable mt_e mt_cl mt_ct : arr.
Variable which fam sym_cl sym_ct : arr.
Variable hfold : PArray.array arr.

Local Notation hg v := (hget which fam sym_cl sym_ct hfold v).
Local Notation stp v k := (stepa mt_e mt_cl mt_ct v k).

(* ---- walking a range of int63 ------------------------------------------- *)

Fixpoint iter (n : nat) (x : int) (f : int -> bool) : bool :=
  if n is n1.+1 then f x && iter n1 (Uint63.add x 1%uint63) f else true.

(* where n steps from x get to                                               *)
Fixpoint advn (n : nat) (x : int) : int :=
  if n is n1.+1 then advn n1 (Uint63.add x 1%uint63) else x.

Lemma iterD n m x f : iter (n + m) x f = iter n x f && iter m (advn n x) f.
Proof. by elim: n x => [|n ih] x //=; rewrite ih andbA. Qed.

(* ---- the sweep ----------------------------------------------------------- *)

(* one triple: no turn drops the table by more than one                       *)
Definition adm1 (v : hv) : bool :=
  iter 12 0%uint63
    (fun k => Uint63.leb (hg v) (Uint63.add (hg (stp v k)) 1%uint63)).

(* the two inner coordinates                                                  *)
Definition adm_ct (e cl : int) : bool :=
  iter n_ct 0%uint63 (fun c => adm1 (e, cl, c)).

Definition adm_cl (e : int) : bool :=
  iter n_cl 0%uint63 (fun b => adm_ct e b).

(* n of the e coordinates from x on, which is what one job takes              *)
Definition adm (x : int) (n : nat) : bool := iter n x adm_cl.

(* the whole table                                                            *)
Definition admis : bool := adm 0%uint63 n_e.

(* ---- gluing the jobs ----------------------------------------------------- *)

(* One job stops where the next starts, and advn is what says so -- in a      *)
(* generated file y is the literal the next job was written with, and the     *)
(* premise is a computation.                                                  *)
Lemma adm_split x n m y : advn n x = y -> adm x n -> adm y m -> adm x (n + m).
Proof. by move=> <-; rewrite /adm iterD => -> ->. Qed.

(* ---- what the sweep gives at one triple ---------------------------------- *)

(* iter walks x, x + 1, ... and advn k x is where it stands after k steps, so *)
(* reading a step off the walk needs no arithmetic either.                    *)
Lemma iterP n x f k : (k < n)%N -> iter n x f -> f (advn k x).
Proof.
elim: n x k => [|n ih] x [|k] //= kn /andP[fx it] //.
by apply: ih.
Qed.

(* SAY THE TYPE OF EVERY STEP.  Left to work it out, the unifier meets iter   *)
(* at n_e and expands 190080 into unary; with the type given it does not.     *)
(* The kernel still walks the fuel once at Qed, and that is why this file     *)
(* takes about three minutes to compile where the rest take seconds.  It is   *)
(* paid once, and the sweep jobs themselves never go through this lemma.      *)
Lemma admisP e cl ct : (e < n_e)%N -> (cl < n_cl)%N -> (ct < n_ct)%N ->
  admis -> adm1 (advn e 0%uint63, advn cl 0%uint63, advn ct 0%uint63).
Proof.
move=> eL cL tL ha.
have h1 : adm_cl (advn e 0%uint63) by apply: (iterP eL ha).
have h2 : adm_ct (advn e 0%uint63) (advn cl 0%uint63) by apply: (iterP cL h1).
by apply: (iterP tL h2).
Qed.

End Sweep.
