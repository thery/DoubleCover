(******************************************************************************)
(*                                                                            *)
(*   Scratch: measuring Alg1.v's two open branch equations                    *)
(*                                                                            *)
(*   [half1_inf_lt] and [half1_inf_ge] are the only statements in Alg1.v      *)
(*    that can fail for a reason other than bookkeeping, so they get          *)
(*    measured on reachable states before anyone proves them.  Reachable      *)
(*    is the point: they are stated for any [(p,q,d,u,v)] satisfying the      *)
(*    three invariants, but what matters first is whether they hold along     *)
(*    actual runs.                                                            *)
(*                                                                            *)
(*   Not part of the development.  Delete once the two are settled.           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From APaulRocq Require Import Dist Alg2 Alg1.

(*  Walk a run of [run1] and check, at each turn, the equation the branch     *)
(*    claims for [inf] across [half1]:                                        *)
(*                                                                            *)
(*      [d < p]   : [inf] does not move   -- no point enters [b]'s gap        *)
(*      [p <= d]  : [inf] drops by [p]    -- exactly one point does           *)
Fixpoint chk (fuel p q d u v M A B N : nat) : bool :=
  if fuel is fuel1.+1 then
    if N <= u + v then true else
    if d < p then
      let k  := q %/ p in
      let q1 := q - k * p in
      let u1 := u + k * v in
      (inf_dst M A B (u1 + v) == inf_dst M A B (u + v)) &&
      (if N <= u1 + v then true
       else chk fuel1 (p - q1) q1 d u1 (v + u1) M A B N)
    else
      let k  := p %/ q in
      let p1 := p - k * q in
      let v1 := v + k * u in
      (inf_dst M A B (u + v1) + p == inf_dst M A B (u + v)) &&
      (if N <= u + v1 then true
       else chk fuel1 p1 (q - p1) (d - p) (u + v1) v1 M A B N)
  else true.

Definition chkall (M A B N : nat) : bool :=
  chk M (A %% M) (M - A %% M) (B %% M) 1 1 M A B N.

(*  The same two, separately, so a failure says which one failed.             *)
Fixpoint chk_lt (fuel p q d u v M A B N : nat) : bool :=
  if fuel is fuel1.+1 then
    if N <= u + v then true else
    if d < p then
      let k  := q %/ p in
      let q1 := q - k * p in
      let u1 := u + k * v in
      (inf_dst M A B (u1 + v) == inf_dst M A B (u + v)) &&
      (if N <= u1 + v then true
       else chk_lt fuel1 (p - q1) q1 d u1 (v + u1) M A B N)
    else
      let k  := p %/ q in
      let p1 := p - k * q in
      let v1 := v + k * u in
      (if N <= u + v1 then true
       else chk_lt fuel1 p1 (q - p1) (d - p) (u + v1) v1 M A B N)
  else true.

Fixpoint chk_ge (fuel p q d u v M A B N : nat) : bool :=
  if fuel is fuel1.+1 then
    if N <= u + v then true else
    if d < p then
      let k  := q %/ p in
      let q1 := q - k * p in
      let u1 := u + k * v in
      (if N <= u1 + v then true
       else chk_ge fuel1 (p - q1) q1 d u1 (v + u1) M A B N)
    else
      let k  := p %/ q in
      let p1 := p - k * q in
      let v1 := v + k * u in
      (inf_dst M A B (u + v1) + p == inf_dst M A B (u + v)) &&
      (if N <= u + v1 then true
       else chk_ge fuel1 p1 (q - p1) (d - p) (u + v1) v1 M A B N)
  else true.

Definition sweep (f : nat -> nat -> nat -> nat -> bool) (Mx Nx : nat) : bool :=
  all (fun M => all (fun A => all (fun B => all (fun N =>
    ((3 <= N) && (N < M %/ gcdn A M)) ==> f M A B N)
    (iota 0 Nx)) (iota 0 M)) (iota 0 M)) (iota 1 Mx).
