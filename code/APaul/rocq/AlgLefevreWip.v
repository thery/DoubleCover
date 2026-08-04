(******************************************************************************)
(*                                                                            *)
(*   Scratch: measuring AlgLefevre.v's invariant                                    *)
(*                                                                            *)
(*   [invw] and the exactness of [d] between the halves are the statements    *)
(*    that can fail for a reason other than bookkeeping, so they are          *)
(*    measured on the states an actual run visits before anything is proved.  *)
(*    That is what refuted the two earlier readings of 4.1 -- AlgFGG's [invd]   *)
(*    at a turn start, and "[inf] drops by [p] across [half1]".               *)
(*                                                                            *)
(*   Verdicts, over all [M <= 20], all [A, B < M], all                        *)
(*    [3 <= N < M %/ gcdn A M], every reachable state:                        *)
(*                                                                            *)
(*      [chk_invw]   0 failures     (turn start: [invw])                      *)
(*      [chk_exact]  0 failures     (after [half1]: [d] is the infimum)       *)
(*      [chk_invd]   FAILS          (AlgFGG's [invd] at a turn start)           *)
(*                                                                            *)
(*   Not part of the development.                                             *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From APaulRocq Require Import Dist Config AlgLefevre.

(*  The states a run of [run1] enters, in order.  The last one can have       *)
(*    [N <= u + v]: the exit test reads the count BETWEEN the halves, so a    *)
(*    turn can begin past [N].                                                *)
Fixpoint states1 (fuel p q d u v N : nat) : seq (nat * nat * nat * nat * nat) :=
  if fuel is fuel1.+1 then
    (p, q, d, u, v) ::
    (if d < p then
       let k := q %/ p in let q1 := q - k * p in let u1 := u + k * v in
       if N <= u1 + v then [::] else states1 fuel1 (p - q1) q1 d u1 (v + u1) N
     else
       let d1 := d - p in let k := p %/ q in let p1 := p - k * q in
       let v1 := v + k * u in
       if N <= u + v1 then [::] else states1 fuel1 p1 (q - p1) d1 (u + v1) v1 N)
  else [::].

Definition sts (M A B N : nat) :=
  states1 M (A %% M) (M - A %% M) (B %% M) 1 1 N.

(*  [invw]: [d] is the infimum plus the [p]-step [half1] has not yet taken.   *)
Definition chk_invw (M A B N : nat) (s : nat * nat * nat * nat * nat) :=
  let: (p, q, d, u, v) := s in
  (d < p + q) &&
  (inf_dst M A B (u + v) == if d < p then d else d - p).

(*  after [half1], [d] is the infimum exactly -- which is where the exit      *)
(*    test reads it.                                                         *)
Definition chk_exact (M A B N : nat) (s : nat * nat * nat * nat * nat) :=
  let: (p, q, d, u, v) := s in
  if d < p then
    let k := q %/ p in d == inf_dst M A B (u + k * v + v)
  else
    let k := p %/ q in d - p == inf_dst M A B (u + (v + k * u)).

(*  AlgFGG's [invd], for contrast: it fails, already at the initial state.      *)
Definition chk_invd (M A B N : nat) (s : nat * nat * nat * nat * nat) :=
  let: (p, q, d, u, v) := s in
  [&& d < maxn p q, d <= inf_dst M A B (u + v) &
      d %% p == inf_dst M A B (u + v) %% p].

Definition cands (Mx : nat) : seq (nat * nat * nat * nat) :=
  flatten [seq flatten [seq flatten [seq [seq (M, A, B, N) | N <- iota 0 M]
    | B <- iota 0 M] | A <- iota 0 M] | M <- iota 1 Mx].

(*  the states, over the whole cube, where [P] fails                          *)
Definition scan P (Mx : nat) :=
  flatten [seq (let: (M, A, B, N) := x in
                if (3 <= N) && (N < M %/ gcdn A M)
                then [seq (M, A, B, N, s) | s <- sts M A B N & ~~ P M A B N s]
                else [::]) | x <- cands Mx].

(*  How the verdicts above were run.  At [Mx = 20] the [size (scan ...)]      *)
(*    form overflows the stack, so count with [all] instead:                  *)
(*                                                                            *)
(*      Eval vm_compute in                                                    *)
(*        all (fun x => let: (M, A, B, N) := x in                             *)
(*          ((3 <= N) && (N < M %/ gcdn A M)) ==>                             *)
(*            all (chk_invw M A B N) (sts M A B N)) (cands 20).               *)
(*                                                                            *)
(*    [chk_invw] and [chk_exact] both come out [true].  For [chk_invd],       *)
(*    [size (scan chk_invd 14)] is 9019, the first failure being              *)
(*    [M=4 A=1 B=1 N=3] at the INITIAL state [(p,q,d,u,v) = (1,3,1,1,1)]:     *)
(*    there [Inf 2] is [0] and [d] is [1], so [invd_le] already fails.        *)
