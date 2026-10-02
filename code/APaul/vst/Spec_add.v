(** * The statement of add: B_ia <- B_ia + B_ib mod 2^(64 l)

    The function [add] of [htr3.c] on a flat array of words, at two
    disjoint offsets [ia] and [ib].  Proved in [Verif_add.v]; used by the
    proof of [tstep]. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.htr3_clight HtrVst.Common.

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
