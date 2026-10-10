(* AdjointGood.v — the scoping discipline of the adjoint code (milestone M6):
   the statements the adjoint sweeps generate follow `good` (Scoping.v), so
   that simplify_correct_tapes (SimplifyCorrect.v) applies to them.

   The definitions shared by the forward sweep (prim, fwd_value) and the
   reverse sweep (adj, rev_value, rev_loop), in the style of good_k
   (TangentGood.v): a block keeps the discipline when followed by any block
   that keeps it in the scope the block leaves.

   The adjoint code of a body is split: its forward sweep fw is followed, in
   the generated function, by the forward sweeps of nothing else (it is a
   suffix of the whole forward sweep), then by the prologue and the reverse
   sweeps of the enclosing lets (their bar declarations), and only then by
   its reverse sweep rv. So the statement of adj gives fw as a good_k, whose
   final scope sc1 is extended (sc2) before rv runs.

   The variables are numbered by open_pairs. The forward sweep of a body
   opened at c defines, at its top level, the storages of its lets (and
   the tapes of its scalar folds), numbered in [c, c') and in a set F; the
   reverse sweep defines the adjoints of those lets, and loop indices and
   replayed lets numbered in [c, c') but outside F. The scope of the
   reverse sweep holds none of the latter (rev_new).

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform
  Adjoint Simplify Scoping AnfEquiv Correctness TangentCorrect TangentLoops
  TangentGood AdjointCorrect AdjointBranch AdjointFold AdjointFoldy
  AdjointNBody AdjointNesty.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

(* ---------------------------------------------------------------------------
   The numbers of the variables. *)

(* The number a variable is built on, and whether it is an adjoint. *)
Fixpoint dnum (x : dvar W) : option nat :=
  match x with
  | DBound (i, _) => Some i
  | DotOf v | BarOf v | TapeOf v => dnum v
  | ResultVar => None
  end.

Definition is_barv (x : dvar W) : bool :=
  match x with BarOf _ => true | _ => false end.

(* A variable the forward sweep of a body opened at c (ending at c')
   defines at its top level: a storage of its lets, or the tape of a scalar
   fold, numbered in F. *)
Definition fwd_new (F : nat -> Prop) (c c' : nat) (x : dvar W) : Prop :=
  exists j, (c <= j < c')%nat /\ F j /\ dnum x = Some j /\ is_barv x = false.

(* A variable the forward sweep defines that it did not open: the value of
   adjoint-value, or the tape of the array updated in place at the top. *)
Definition out_new (c : nat) (x : dvar W) : Prop :=
  x = ResultVar \/ exists j, (j < c)%nat /\ x = TapeOf (DBound (j, j)).

(* A variable the reverse sweep of the body may define: an adjoint of a
   variable it opened, or a variable it opened outside F. *)
Definition rev_new (F : nat -> Prop) (c c' : nat) (x : dvar W) : Prop :=
  exists j, (c <= j < c')%nat /\ dnum x = Some j /\
    (is_barv x = true \/ ~ F j).

(* The scope after the forward sweep of a body: the scope before, and the
   variables the forward sweep defines. *)
Definition fwd_post (F : nat -> Prop) (c c' : nat) (sc sc1 : list (dvar W)) :
  Prop :=
  forall x, In x sc1 -> In x sc \/ fwd_new F c c' x \/ out_new c x.

Section AGood.
Variable cv : bool.

(* ---------------------------------------------------------------------------
   The forward sweep. *)

(* The scope of a forward sweep, opened before c: the variables whose value
   it reads (rd: the TBR set for adj, the live variables for prim and
   fwd_value) are in scope, the storage updated in place is writable. *)
Definition fscope (L : list pv) (c : nat) (wP : option (atom pv))
  (pp : pplace) (rd : pv -> Prop) (sc wr : list (dvar W)) : Prop :=
  Forall (fun x => below c x /\ consistent x) sc /\ incl wr sc /\
  (forall p, In p L -> rd p -> In (stored p) sc) /\
  (forall o, owner wP pp = Some o -> In (stored o) wr).

(* The tape of the storage updated in place, declared before use. At the
   top, the storage is the written argument (an identity, not recorded),
   whose in-place fold declares the tape: it is not in scope yet. In the
   body of an in-place loop, the storage is the state (no identity), whose
   tape is writable when the body pushes on it: when the state is recorded,
   or a fold of the body records (rr, the records of the body). *)
Definition tape_fwd (wP : option (atom pv)) (pp : pplace) (m : sweep)
  (rr : bool) (sc wr : list (dvar W)) : Prop :=
  forall o, owner wP pp = Some o ->
    (not_in_loop pp ->
     ~ In (TapeOf (stored o)) sc /\ tid (pt o) <> None /\
     trecorded (pt o) = false) /\
    (~ not_in_loop pp ->
     tid (pt o) = None /\
     (sweep_eqb m Forward && (trecorded (pt o) || rr) = true ->
      In (TapeOf (stored o)) wr)).

(* At the top of adjoint-value, the value is defined (a returned real) or
   assigned (a written real). *)
Definition vo_scope (m : sweep) (vo : option (aresult (tvar W)))
  (sc wr : list (dvar W)) : Prop :=
  m = Forward ->
  (forall t, vo = Some (AReturns t) -> ~ In ResultVar sc) /\
  (forall y, vo = Some (AWrites y) -> In (stored_of W y) wr).

(* The state of a fold is recorded (its reverse loop pops it). *)
Definition fold_slive (k : nat) (e : value avar bare) : bool :=
  match e with
  | AFold _ _ _ init b => state_live cv k init b
  | _ => false
  end.

(* prim: the forward sweep of the body of a branch, a map or a fold, that
   computes every let; the value of its tail atom is in scope after it. *)
Definition agood_prim (bP : anf pv bare) : Prop :=
  forall L k c wP pp m m' bA bW bT ty sc wr,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
  sctx L k c wP pp (live_anf k bW) ty ->
  fscope L c wP pp (live_anf k bW) sc wr ->
  tape_fwd wP pp m (records_in cv k bA) sc wr ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  let '((ss, x), c') :=
    open_pairs (prim W (option_map (amap pt) wP) m
                  (rebuild _ bT (annotate_body_t cv m' k bA))) c in
  (c <= c')%nat /\ good_k sc wr c' ss (fun sc' _ => expr_ok sc' x).

(* fwd_value: the forward sweep of a value computed into n (opened before
   c), recorded when rec (then n is the state of an in-place loop, whose
   tape is writable): n is in scope after it, with the tape the in-place
   fold at the top declares. *)
Definition agood_value (eP : value pv bare) : Prop :=
  forall L k c wP pp m tail eA eW eT te n rec ty sc wr,
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> value_eq (gT L) eP eT ->
  sctx L k c wP pp (live_value k eW) ty ->
  fscope L c wP pp (live_value k eW) sc wr ->
  tape_fwd wP pp m (records cv k eA) sc wr ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW =
    (te, Ok) ->
  (tail = true -> te = ty) ->
  (exists j, n = DBound (j, j) /\ (j < c)%nat) ->
  match storage wP tail eP with
  | Some m0 => n = m0
  | None => ~ In n sc /\ ~ In (TapeOf n) sc
  end ->
  (rec = true ->
   ~ not_in_loop pp /\ (sweep_eqb m Forward = true -> In (TapeOf n) wr)) ->
  let '(se, c') :=
    open_pairs (fwd_value W (option_map (amap pt) wP) m
                  (rebuild_value _ eT (annotate_value_t cv k eA)) te n rec)
      c in
  (c <= c')%nat /\
  good_k sc wr c' se (fun sc' wr' =>
    In n sc' /\
    (forall x, In x sc' -> In x sc \/ x = n \/ x = TapeOf n) /\
    (sweep_eqb m Forward && records cv k eA = true -> not_in_loop pp ->
     storage wP tail eP <> None -> In (TapeOf n) wr') /\
    (sweep_eqb m Forward && fold_slive k eA = true ->
     storage wP tail eP = None -> In n wr' /\ In (TapeOf n) wr')).

(* ---------------------------------------------------------------------------
   The reverse sweep. *)

(* The scope of the reverse sweep of a body opened at c (ending at c'),
   extending the scope sc1 its forward sweep leaves: no variable its reverse
   sweep defines is in it. *)
Definition rscope (F : nat -> Prop) (c c' : nat)
  (sc1 wr1 sc2 wr2 : list (dvar W)) : Prop :=
  incl sc1 sc2 /\ incl wr1 wr2 /\ incl wr2 sc2 /\
  Forall (fun x => below c' x /\ consistent x) sc2 /\
  (forall x, In x sc2 -> ~ rev_new F c c' x).

(* The adjoints declared before they are accumulated: the adjoint of every
   varied variable whose adjoint is useful (use), and the storage updated in
   place and its adjoint, are writable. *)
Definition bars_ok (L : list pv) (use : pv -> Prop) (wP : option (atom pv))
  (pp : pplace) (wr : list (dvar W)) : Prop :=
  (forall p, In p L -> use p -> tbar (pt p) = true ->
     In (BarOf (stored p)) wr) /\
  (forall o, owner wP pp = Some o ->
     In (stored o) wr /\ In (BarOf (stored o)) wr).

(* The tape of the storage updated in place, declared before the pops: in
   the body of an in-place loop, when a fold of the body records (rr); at
   the top, the in-place fold declares it in its forward sweep. *)
Definition tape_rev (wP : option (atom pv)) (pp : pplace) (rr : bool)
  (wr : list (dvar W)) : Prop :=
  forall o, owner wP pp = Some o -> ~ not_in_loop pp -> rr = true ->
    In (TapeOf (stored o)) wr.

(* adj: the forward sweep fw, from the scope of the TBR set, keeps the
   discipline and leaves its definitions in scope; the reverse sweep rv
   keeps it from any extension of that scope where the adjoints and the
   tapes it accumulates into are declared and the seed is in scope. *)
Definition agood_body (bP : anf pv bare) : Prop :=
  forall L k c wP pp m vo bA bW bT ty (se : dexpr W),
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
  sctx L k c wP pp (live_anf k bW) ty -> real_or_array ty ->
  (forall p, In p L -> tbar (pt p) = avaried (pa p)) ->
  (m = Forward -> vo <> None -> cv = true) ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  (m = Forward -> pp = PTop) -> (m = Replay -> pp <> PTop) ->
  let '((fw, rv), c') :=
    open_pairs (adj W (option_map (amap pt) wP) vo m
                  (rebuild _ bT (annotate_body_t cv m k bA)) se) c in
  (c <= c')%nat /\
  exists F : nat -> Prop, forall sc wr,
  fscope L c wP pp (tbr cv m k bA) sc wr ->
  tape_fwd wP pp m (records_in cv k bA) sc wr ->
  vo_scope m vo sc wr ->
  good_k sc wr c' fw (fun sc1 wr1 =>
    fwd_post F c c' sc sc1 /\
    (m = Forward -> forall t, vo = Some (AReturns t) -> In ResultVar sc1) /\
    forall sc2 wr2, rscope F c c' sc1 wr1 sc2 wr2 ->
      bars_ok L (useful cv m k bA) wP pp wr2 ->
      tape_rev wP pp (records_in cv k bA) wr2 ->
      expr_ok sc2 se ->
      good_k sc2 wr2 c' rv (fun _ _ => True)).

(* rev_value: the reverse sweep of a value computed into n, from a scope
   opened before c holding the values it reads and the adjoints it
   accumulates into; it defines only variables it opens (loop indices,
   replayed lets, their adjoints), inside its loops and branches. *)
Definition agood_rev (eP : value pv bare) : Prop :=
  forall L k c wP pp vo tail eA eW eT te n ty sc wr,
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> value_eq (gT L) eP eT ->
  sctx L k c wP pp (live_value k eW) ty ->
  (forall p, In p L -> tbar (pt p) = avaried (pa p)) ->
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc ->
  (forall p, In p L -> vreads cv k eA p -> In (stored p) sc) ->
  bars_ok L (vflows cv k eA) wP pp wr ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW =
    (te, Ok) ->
  (tail = true -> te = ty) ->
  (exists j, n = DBound (j, j) /\ (j < c)%nat) ->
  match storage wP tail eP with
  | Some m0 => n = m0
  | None => True
  end ->
  In (BarOf n) wr ->
  (records cv k eA = true -> storage wP tail eP <> None ->
   In (TapeOf n) wr) ->
  (fold_slive k eA = true -> In n wr /\ In (TapeOf n) wr) ->
  let '(re, c') :=
    open_pairs (rev_value W (option_map (amap pt) wP) vo
                  (rebuild_value _ eT (annotate_value_t cv k eA)) te n) c in
  (c <= c')%nat /\ good_k sc wr c' re (fun _ _ => True).

End AGood.
