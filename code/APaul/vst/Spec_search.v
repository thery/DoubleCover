(** * The statement of search: the candidates of one line

    The function [search] of [htr3.c]: the array holds the [k] values
    [P(0) .. P(k-1)] of a line, [l] words each; [search] turns them into
    the table of differences, adds [err] to the top word of the first
    coefficient, and walks [j = 0 .. n-1], keeping [j] when that top word
    is at most [2 err].  It returns the number of candidates and writes the
    first [cap] of them in [out].  What is computed is said by [cands],
    copied from [code/APaul/rocq/HtrDefs.v] ([tstepZ] is that of
    [Verif_tstep.v], [fdiff] and [coefs] those of [Fdiff.v]).  Proved in
    [Verif_search.v]. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.Fdiff HtrVst.htr3_clight HtrVst.Common.
Require Import HtrVst.Verif_tstep.

(** ** The search on integers, as in HtrDefs.v *)

(** The top word of [b] seen as [l] words: [(b mod beta^l) / beta^(l-1)]. *)
Definition top (l b : Z) : Z := (b mod baseZ l) / 2 ^ (wbits * (l - 1)).

(** The window: [err] added to the top word of the first coefficient. *)
Definition window (l err : Z) (ds : list Z) : list Z :=
  match ds with
  | a :: r => (a + err * 2 ^ (wbits * (l - 1))) :: r
  | [] => []
  end.

(** The table after [j] steps, from the values [ds = P(0) .. P(k-1)]. *)
Definition table (l err : Z) (ds : list Z) (j : nat) : list Z :=
  Nat.iter j tstepZ (window l err (map (fdiff ds) (seq 0 (length ds)))).

(** [j] is a candidate: the top word of the first coefficient is at most
    [2 err]. *)
Definition cand (l err : Z) (ds : list Z) (j : nat) : bool :=
  top l (nth 0 (table l err ds j) 0) <=? 2 * err.

(** The candidates [j = 0 .. n-1], in increasing order. *)
Definition cands (l err : Z) (ds : list Z) (n : nat) : list nat :=
  filter (cand l err ds) (seq 0 n).

(** ** The statement *)

Definition search_spec : ident * funspec :=
 DECLARE _search
 WITH sh : share, p : val, xs : list Z, k : Z, l : Z, n : Z, err : Z,
      sho : share, q : val, os : list val, cap : Z
 PRE [ tptr tulong, tulong, tulong, tulong, tulong, tulong, tptr tulong,
       tulong ]
   PROP (writable_share sh; writable_share sho; Forall word xs;
         1 <= k; 1 <= l; k * l <= Zlength xs;
         0 <= n <= Int64.max_unsigned;
         0 <= err; 2 * err <= Int64.max_unsigned;
         0 <= cap <= Int64.max_unsigned; Zlength os = cap)
   PARAMS (p; Vlong (Int64.repr (Zlength xs)); Vlong (Int64.repr k);
           Vlong (Int64.repr l); Vlong (Int64.repr n);
           Vlong (Int64.repr err); q; Vlong (Int64.repr cap))
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs) p;
        data_at sho (tarray tulong cap) os q)
 POST [ tulong ]
   EX xs' : list Z, EX os' : list val,
   PROP (Zlength xs' = Zlength xs; Forall word xs'; Zlength os' = cap;
         sublist 0
           (Z.min (Zlength (cands l err (coefs xs l k) (Z.to_nat n))) cap)
           os' =
         vwords
           (map Z.of_nat
              (firstn (Z.to_nat cap)
                 (cands l err (coefs xs l k) (Z.to_nat n)))))
   RETURN (Vlong (Int64.repr
            (Zlength (cands l err (coefs xs l k) (Z.to_nat n)))))
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p;
        data_at sho (tarray tulong cap) os' q).
