(** * The words of an array and the coefficients they hold

    Capla passes an array of n words as a [{ffun 'I_n -> int64}].  The
    search sees a flat array of words as k coefficients of l words each,
    the least significant word first: coefficient p is the words
    p l .. p l + l - 1.  [wd B q] is word q (0 past the end), [segv B a l]
    the number of the l words from a, [coefA B l p] coefficient p and
    [coefsA B l k] the coefficients 0 .. k-1: the [coefs] of the VST proof
    (../../../vst/Fdiff.v), on a Capla array. *)

From APaulRocq Require Import HtrDefs.
From compcert Require Import CaplaProof.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Local Open Scope Z_scope.

Section Words.

Context {n : nat}.
Implicit Types B : {ffun 'I_n -> int64}.

(* Word q of B, as an integer; 0 past the end. *)
Definition wd B (q : nat) : Z :=
  nth 0 [seq Int64.unsigned x | x <- tuple.tval (fgraph B)] q.

(* The number of the l words of B from a, the least significant first. *)
Fixpoint segv B (a l : nat) : Z :=
  match l with
  | O => 0
  | S l => wd B a + 2 ^ wbits * segv B a.+1 l
  end.

(* Coefficient p, of l words. *)
Definition coefA B (l p : nat) : Z := segv B (p * l) l.

(* The coefficients 0 .. k-1. *)
Definition coefsA B (l k : nat) : list Z := [seq coefA B l p | p <- iota 0 k].

End Words.
