Require Import BinNums ZArith String List.
(* From compcert *) Require Import Integers Floats Maps.
(* From compcert *) Require Import Types Ops SyntaxCommon L1.

From Flocq Require Import Binary.

Import ListNotations.

Require Import ProofHeader.

Definition __builtin_umulh645 := extract_res (
  make_builtin_or_external "__builtin_umulh64"
    {| sig_args := [u64; u64]; sig_res := u64 |}
    ([VAR 1%positive "a"; VAR 2%positive "x"])
    (PTree.Nodes (PTree.Node110 (PTree.Node010 u64) u64))
    (PTree.Nodes (PTree.Node110 (PTree.Node010 []) []))
    (PTree.Nodes (PTree.Node110 (PTree.Node010 Shared) Shared))) eq_refl.


Definition allocz3 := extract_res (
  make_function {| sig_args := []; sig_res := u64 |} ([])
    ([VAR 7%positive "__tmp__var__"; VAR 6%positive "a1_1_1_";
      VAR 2%positive "x"; VAR 1%positive "a"])
    (Sseq (Sskip) (
     Sseq
     (Sseq
      (Salloc (VAR 1%positive "a") (Econst (Cint64 Unsigned (Int64.repr (1)%Z))))
      (Sskip))
     (
     Sseq (Sskip) (
     Sseq
     (Sseq
      (Sassign (VAR 2%positive "x", [])
         (Eacc (VAR 1%positive "a",
                [Scell [Econst (Cint64 Unsigned (Int64.repr (0)%Z))]])))
      (Sskip))
     (
     Sseq (Sskip) (
     Sseq (Sskip) (
     Sseq (Sfree (VAR 1%positive "a")) (
     Sreturn (Some (Eacc (VAR 2%positive "x", [])))))))))))
    (PTree.Nodes (PTree.Node111 (PTree.Node011 u64 (PTree.Node010 u64))
                    (Tarr u64) (PTree.Node001 (PTree.Node010 u64))))
    (PTree.Empty)
    (PTree.Nodes (PTree.Node111 (PTree.Node011 [] (PTree.Node010 []))
                    [[6%positive]] (PTree.Node001 (PTree.Node010 []))))
    (PTree.Nodes (PTree.Node111 (PTree.Node011 Owned (PTree.Node010 Shared))
                    Owned (PTree.Node001 (PTree.Node010 Owned))))
    (VAR 7%positive "__tmp__var__")) eq_refl.



Definition program := extract_res (make_program
  ([(5%positive, __builtin_umulh645)]) ([(3%positive, Internal allocz3)])
  (4%positive)) eq_refl.
