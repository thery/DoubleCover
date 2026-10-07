(** * The statement of search_filter

    [search_filter] of [htr_filter.c] calls [search] ([Spec_search.v]),
    then walks the first [min(count, cap)] candidates [j] written in
    [out], and keeps (compacted at the start of [out], in order) those for
    which [maybe_hard_bits] of the bits [xb0 + j] ([neg = 0]) or
    [xb0 - j] ([neg <> 0]), taken mod [2^64], answers [1].  It returns the
    number kept.  [maybe_hard_bits] is used through its statement of
    [E.Spec] (the model [maybe_hard_Z] of exp100). *)

Require Import VST.floyd.proofauto.
Require Import HF.htr_filter_clight HF.FCommon.
Require HtrVst.Words HtrVst.Fdiff HtrVst.Common HtrVst.Spec_search.
Require HtrVst.Verif_search E.Common E.Spec.
Require Exp100.ExpModel.

Local Notation vwords := HtrVst.Common.vwords.
Local Notation word := HtrVst.Words.word.
Local Notation coefs := HtrVst.Fdiff.coefs.
Local Notation cands := HtrVst.Spec_search.cands.
Local Notation consts := E.Common.consts.

(** ** What is kept *)

(** The bits of the input [j] of the line: [xb0 + j] or [xb0 - j], as a
    word of 64 bits (what the C computes). *)
Definition xbj (neg xb0 j : Z) : Z :=
  (if Z.eqb neg 0 then xb0 + j else xb0 - j) mod 2 ^ 64.

(** [j] is kept: [maybe_hard_bits] answers [1]. *)
Definition keep (neg xb0 : Z) (j : nat) : bool :=
  Z.eqb (Exp100.ExpModel.maybe_hard_Z (xbj neg xb0 (Z.of_nat j))) 1.

(** The candidates written by [search] in [out] (the first [cap]), then
    those kept. *)
Definition kept_list (l err : Z) (xs : list Z) (k n cap neg xb0 : Z)
  : list nat :=
  filter (keep neg xb0)
    (firstn (Z.to_nat cap) (cands l err (coefs xs l k) (Z.to_nat n))).

(** ** The statement *)

Definition search_filter_spec : ident * funspec :=
 DECLARE _search_filter
 WITH gv : globals, sh : share, p : val, xs : list Z, k : Z, l : Z, n : Z,
      err : Z, sho : share, q : val, os : list val, cap : Z, xb0 : Z,
      neg : Z
 PRE [ tptr tulong, tulong, tulong, tulong, tulong, tulong, tptr tulong,
       tulong, tulong, tint ]
   PROP (writable_share sh; writable_share sho; Forall word xs;
         1 <= k; 1 <= l; k * l <= Zlength xs;
         0 <= n <= Int64.max_unsigned;
         0 <= err; 2 * err <= Int64.max_unsigned;
         0 <= cap <= Int64.max_unsigned; Zlength os = cap;
         0 <= xb0 <= Int64.max_unsigned;
         Int.min_signed <= neg <= Int.max_signed)
   PARAMS (p; Vlong (Int64.repr (Zlength xs)); Vlong (Int64.repr k);
           Vlong (Int64.repr l); Vlong (Int64.repr n);
           Vlong (Int64.repr err); q; Vlong (Int64.repr cap);
           Vlong (Int64.repr xb0); Vint (Int.repr neg))
   GLOBALS (gv)
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs) p;
        data_at sho (tarray tulong cap) os q;
        consts gv)
 POST [ tulong ]
   EX xs' : list Z, EX os' : list val,
   PROP (Zlength xs' = Zlength xs; Forall word xs'; Zlength os' = cap;
         sublist 0 (Zlength (kept_list l err xs k n cap neg xb0)) os' =
         vwords (map Z.of_nat (kept_list l err xs k n cap neg xb0)))
   RETURN (Vlong (Int64.repr
            (Zlength (kept_list l err xs k n cap neg xb0))))
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p;
        data_at sho (tarray tulong cap) os' q;
        consts gv).

(** The statements of the 22 functions: the five of htr3.c, the 16 of
    exp100.c (Spec.v), and search_filter. *)
Definition Gprog : funspecs :=
  HtrVst.Verif_search.Gprog ++ E.Spec.Gprog ++ [search_filter_spec].
