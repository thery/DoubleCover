(** * The statement of add: B_ia <- B_ia + B_ib mod 2^(64 l)

    The function [add] of [htr3.c] on a flat array of words, at two
    disjoint offsets [ia] and [ib].  Proved in [Verif_add.v]; used by the
    proof of [tstep]. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.htr3_clight HtrVst.Common.

(** The statement assumed for [_addcarry_u64], the intrinsic of gcc that
    [add] calls (gcc compiles it to [adc]; for VST it is an external
    function, as clightgen only sees its prototype).  With a carry [c] in
    0..1 and two words [a] and [b], it writes [a + b + c] modulo 2^64 at
    [out] and returns the carry, the quotient by 2^64.  This statement is
    trusted, not proved: it is Intel's definition of the instruction. *)
Definition addcarry_spec : ident * funspec :=
 DECLARE __addcarry_u64
 WITH c : Z, a : Z, b : Z, sh : share, out : val
 PRE [ tuchar, tulong, tulong, tptr tulong ]
   PROP (0 <= c <= 1; word a; word b; writable_share sh)
   PARAMS (Vint (Int.repr c); Vlong (Int64.repr a); Vlong (Int64.repr b);
           out)
   SEP (data_at_ sh tulong out)
 POST [ tuchar ]
   PROP ()
   RETURN (Vint (Int.repr ((a + b + c) / 2 ^ wbits)))
   SEP (data_at sh tulong (Vlong (Int64.repr (a + b + c))) out).

Definition add_spec : ident * funspec :=
 DECLARE _add
 WITH sh : share, p : val, xs : list Z, ia : Z, ib : Z, l : Z
 PRE [ tptr tulong, tulong, tulong, tulong ]
   PROP (writable_share sh; Forall word xs;
         0 <= ia; 0 <= ib; 0 <= l;
         ia + l <= Zlength xs; ib + l <= Zlength xs;
         ia + l <= ib \/ ib + l <= ia)
   PARAMS (p; Vlong (Int64.repr ia); Vlong (Int64.repr ib);
           Vlong (Int64.repr l))
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs) p)
 POST [ tvoid ]
   EX xs' : list Z,
   PROP (Zlength xs' = Zlength xs; Forall word xs';
         valZ (sublist ia (ia + l) xs') =
           (valZ (sublist ia (ia + l) xs) + valZ (sublist ib (ib + l) xs))
             mod baseZ l;
         forall q, q < ia \/ ia + l <= q -> Znth q xs' = Znth q xs)
   RETURN ()
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p).
