(* =========================================================================  *)
(*  RowMask.v -- the folded phase one table with the moves, and how it reads. *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  The pruning table is what a search consults to    *)
(* decide where not to go; soundness never looks at it, so nothing here has  *)
(* to be proved.  RowLeaf.v says it in so many words: the table "is then     *)
(* only the pruning table, which soundness never looks at".                  *)
(*                                                                           *)
(* WHAT IS NEW IS THE MOVES.  Fold.v's table gives the distance alone, so a  *)
(* node has to offer all eighteen moves and read the table eighteen times.   *)
(* This one says, beside the distance, which moves bring the state nearer H  *)
(* and which at least do not take it further, and a node then offers three   *)
(* or four.                                                                  *)
(*                                                                           *)
(* AN ENTRY IS TWENTY EIGHT BITS, and that is Rokicki's packing.  Writing    *)
(* the moves out one bit each takes forty one; but a half turn is a quarter  *)
(* turn twice, so two moves of one face cannot differ by more than one step, *)
(* which leaves fifteen of the twenty seven ways a face can go.  Four bits a *)
(* face, six faces, four bits of distance -- two entries to an int63 word.   *)
(*                                                                           *)
(* THE MOVES NAMED ARE THE KEPT STATE'S.  A read folds the rank to its orbit *)
(* and carries the twist through a renaming, so what comes back belongs to   *)
(* the kept state and its moves have to be renamed back.  The renaming rides *)
(* in the bits above the entry, and decoding and renaming are one table read *)
(* a half: three faces at a time, twelve bits in, the eighteen moves of the  *)
(* state itself out.                                                         *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Phase1 Fold.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

(* ---- the widths the generator packs with --------------------------------  *)

(* the entry and its distance are Fold.v's: p1getm and p1getd.  What is here *)
(* is the six faces above the distance.                                      *)
Definition mdbits : int := 4%uint63.        (* bits of distance               *)
Definition mfbits : int := 12%uint63.       (* bits of three faces            *)
Definition mfmask : int := 4095%uint63.     (* twelve bits                    *)
Definition msmask : int := 15%uint63.       (* the renaming, four bits        *)
Definition ndeci  : int := 4096%uint63.     (* a renaming's block of the      *)
                                            (* decoding tables                *)
Definition allmvi : int := 262143%uint63.   (* the eighteen moves             *)

(* the folded read: the same fold, with the renaming kept above the entry    *)
(* because the moves it names are the KEPT state's                          *)
Definition Dfoldm (F : PArray.array arr) (frep fsym : int -> int)
    (twsym : int -> int -> int) (tw r : int) : int :=
  let y := fsym r in
  Uint63.lor (p1getm F (foldi (frep r) (twsym tw y)))
             (Uint63.lsl y mbits).

(* ---- the distance, and the moves worth trying ---------------------------  *)

Definition mdist (w : int) : int := Uint63.land w mdmask.

Section Decode.

(* the four decoding tables, three values to a word at twenty bits: the      *)
(* nearer moves and the not further ones, each in a low and a high half      *)
Variable dnlo dnhi fllo flhi : arr.

(* A move changes the distance by at most one, so a node with s moves to     *)
(* spare beyond its distance may take: any move if s is two or more, one     *)
(* that does not take it further if s is one, and only one that brings it    *)
(* nearer if s is nought.  A mask that offers too much makes the search      *)
(* bigger, never wrong.                                                      *)
Definition mmask (w : int) (s : nat) : int :=
  if (2 <= s)%N then allmvi
  else
    let b := Uint63.mul (Uint63.land (Uint63.lsr w mbits) msmask) ndeci in
    let c := Uint63.lsr w mdbits in
    let lo := Uint63.add b (Uint63.land c mfmask) in
    let hi := Uint63.add b (Uint63.land (Uint63.lsr c mfbits) mfmask) in
    if s is 1%N
    then Uint63.lor (get20 fllo lo) (get20 flhi hi)
    else Uint63.lor (get20 dnlo lo) (get20 dnhi hi).

End Decode.
