(******************************************************************************)
(*                                                                            *)
(*   The evaluation the search rests on                                       *)
(*                                                                            *)
(*   The search never asks for [exp] itself.  At the grid point [v] --        *)
(*   standing for the real [v / 2^54] -- it wants the exact answer as an      *)
(*   integer: [exp (v / 2^54)] scaled by [2^vden] with the fraction           *)
(*   dropped.  That integer is [exp_nat v], and it is the only place a real   *)
(*   number occurs here.                                                      *)
(*                                                                            *)
(*   What the search computes instead is [eval_f v].  The one property        *)
(*   assumed of it is that the two are close: [eval_f_spec].  The bound       *)
(*   [errV] is CoqInterval's [2^-tprec] ([Cheb.cheb_valid]) read at scale     *)
(*   [2^vden], plus one for the dropped fraction.                             *)
(*                                                                            *)
(*   So everything downstream is [nat], as in [ScanAll.v]: an abstract        *)
(*   evaluation, an abstract truth, and an integer bound between them.        *)
(*   Discharging [eval_f_spec] for the polynomial the code really runs        *)
(*   ([Search.polyHorner]) is what brings [Cheb.cheb_valid] into play.        *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Reals.
From Flocq Require Import Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*  [Cheb] leaves [R_scope] open; everything below is [nat].                  *)
Open Scope nat_scope.

(*  ** Distance between two integers                                          *)

(*  How far apart two integers are.                                           *)
Definition adist (a b : nat) : nat := (a - b) + (b - a).

(*  It is symmetric...                                                        *)
Lemma adistC a b : adist a b = adist b a.
Proof. by rewrite /adist addnC. Qed.

(*  ...it vanishes exactly on equal arguments...                              *)
Lemma adist_eq0 a b : (adist a b == 0) = (a == b).
Proof.
by rewrite /adist addn_eq0 !subn_eq0 -eqn_leq.
Qed.

(*  Truncated subtraction goes through an intermediate point.                 *)
Lemma leq_subD x y z : x - z <= (x - y) + (y - z).
Proof.
rewrite leq_subLR addnCA.
have h1 : y <= z + (y - z) by rewrite addnC addnCB leq_addr.
by rewrite (leq_trans _ (leq_add (leqnn (x - y)) h1)) // addnCB leq_addr.
Qed.

(*  ...and it satisfies the triangle inequality.                              *)
Lemma adistD a b c : adist a c <= adist a b + adist b c.
Proof.
rewrite /adist addnACA.
by apply: leq_add; [exact: leq_subD | rewrite addnC; exact: leq_subD].
Qed.

(*  ** The scales                                                             *)

(*  The grid: the point [v] stands for the real [v / 2^xden].                 *)
Definition xdenN : nat := 54.

(*  The scale of the integer value: it stands for [exp x * 2^vden].           *)
Definition vdenN : nat := 598.

(*  The accuracy CoqInterval certifies for the polynomial: [2^-tprec].        *)
Definition tprecN : nat := 160.

(*  ** The truth, and what the search computes                                *)

(*  The exact answer as an integer: [exp (v / 2^54) * 2^598], fraction        *)
(*  dropped.  The one real-valued definition in the file.                     *)
Definition exp_nat (v : nat) : nat :=
  Z.to_nat (Zfloor (exp (INR v / 2 ^ xdenN) * 2 ^ vdenN))%R.

(*  What the search evaluates at the grid point [v], in place of it.          *)
Parameter eval_f : nat -> nat.

(*  The ends of the search interval, where that evaluation is good.           *)
Parameter v_lo v_hi : nat.

(*  How far the evaluation may sit from the truth: the certified [2^-tprec]   *)
(*  read at scale [2^vden], plus one for the dropped fraction.                *)
Definition errV : nat := 2 ^ (vdenN - tprecN) + 1.

(*  The one property assumed: on the search interval the evaluation is        *)
(*  within [errV] of the truth.  This is [Cheb.cheb_valid], and it is what    *)
(*  an instantiation by the code's own polynomial has to establish.           *)
Axiom eval_f_spec :
  forall v : nat, v_lo <= v <= v_hi -> adist (eval_f v) (exp_nat v) <= errV.
