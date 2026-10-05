(** * The numbers of exp100

    A number is a list of limbs of 32 bits, the least significant first,
    standing for [valZ].  Pure Z, Stdlib only: no reals, so that the limb
    proofs (ExpLimbs.v) load nothing else. *)

From Stdlib Require Import ZArith List.
Import ListNotations.

Open Scope Z_scope.

Definition limb_bits : Z := 32.  (* bits of a limb          *)
Definition NL : nat := 6.        (* limbs of a number       *)

(** A limb: an integer in [0, 2^32). *)
Definition limb (x : Z) : Prop := 0 <= x < 2 ^ limb_bits.

(** The number a list of limbs stands for, least significant limb first. *)
Fixpoint valZ (ws : list Z) : Z :=
  match ws with
  | [] => 0
  | w :: r => w + 2 ^ limb_bits * valZ r
  end.

(** The weight of limb k, and the bound of a number of k limbs: 2^(32 k). *)
Definition limb_base (k : nat) : Z := 2 ^ (limb_bits * Z.of_nat k).

(** A number of exp100.c: [NL] limbs. *)
Definition num (ws : list Z) : Prop := length ws = NL /\ Forall limb ws.
