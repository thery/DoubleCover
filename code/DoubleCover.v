(** * The Cycle Double Cover Conjecture

    Statement of the Cycle Double Cover conjecture (Tutte, Itai-Rodeh,
    Szekeres, Seymour):

      every finite bridgeless (multi)graph has a collection of cycles
      covering every edge exactly twice.

    We work with finite unlabelled multigraphs [graph unit unit] from the
    GraphTheory library, so that parallel edges and loops are allowed --
    this is essential, since the proof reduces to cubic multigraphs and
    regards two parallel edges as a cycle.

    The main theorem [cycle_double_cover] is stated with an admitted proof. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries mgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CycleDoubleCover.

(** Finite unlabelled multigraph: parallel edges and loops are allowed. *)
Variable G : graph unit unit.

Implicit Types (x y : G) (e : edge G) (C E : {set edge G}).

(** Two vertices are adjacent through the edge set [E] when some edge of
    [E] has them as its two endpoints (in either direction). *)
Definition adj (E : {set edge G}) : rel G :=
  fun x y => [exists e in E,
    ((source e == x) && (target e == y)) || ((source e == y) && (target e == x))].

(** Reachability using only the edges of [E]. *)
Definition econn (E : {set edge G}) : rel G := connect (adj E).

(** Degree of the vertex [x] in the edge set [C]: the number of edge
    endpoints landing on [x]. A loop at [x] contributes 2. *)
Definition deg (C : {set edge G}) x : nat :=
  \sum_(e in C) ((source e == x) + (target e == x)).

(** The vertices actually touched by the edge set [C]. *)
Definition support (C : {set edge G}) : {set G} :=
  [set x | [exists e in C, incident x e]].

(** [C] is a cycle (a circuit): it is nonempty, every vertex it touches
    has degree exactly 2, and all these vertices are connected using the
    edges of [C]. A single loop and a pair of parallel edges are both
    cycles under this definition. *)
Definition is_cycle (C : {set edge G}) : bool :=
  [&& C != set0,
      [forall x in support C, deg C x == 2] &
      [forall x in support C, [forall y in support C, econn C x y]] ].

(** An edge is a bridge when deleting it disconnects its two endpoints.
    Note that a loop is never a bridge. *)
Definition bridge e : bool := ~~ econn (setT :\ e) (source e) (target e).

(** [G] is bridgeless when it has no bridge. *)
Definition bridgeless : bool := [forall e, ~~ bridge e].

End CycleDoubleCover.

Arguments is_cycle {G} C.
Arguments bridgeless : clear implicits.

(** ** Main theorem (Cycle Double Cover Conjecture)

    Every finite bridgeless multigraph admits a multiset of cycles (here a
    [seq] of edge sets, so cycles may be repeated) such that every edge
    belongs to exactly two of them. *)
Theorem cycle_double_cover (G : graph unit unit) :
  bridgeless G ->
  exists s : seq {set edge G},
    all is_cycle s /\ forall e : edge G, count (fun C : {set edge G} => e \in C) s = 2.
Proof.
Admitted.
