(* Exec.v — mirrors exec.elpi: the evaluator of L2, executing the programs
   the tool generates, tangents and adjoints, before and after simplification.

   L2 is imperative, so its evaluator threads a store: a list of pairs of a
   variable and its value. Elpi opens the binders of a function with `pi`, as
   fresh Elpi variables; in PHOAS they are instantiated with numbers, allocated
   in order, so that variables compare. The values and the operations are those
   of the evaluator of L0 (Eval.v), in a domain of numbers; a tape is a list of
   reals.

   `exec_dfunction D F Args = Some (Finals, Ret)`: the function F, called with
   Args, one value per parameter in the order of its signature, leaves the
   parameters with the values Finals (a parameter passed by reference returns
   its result there) and returns Ret, [v] for a function that returns v, []
   otherwise. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Derivative Domain Eval.

Import ListNotations.
Open Scope Z_scope.

(* The variables, bound by numbers. *)
Fixpoint dvar_eqb (a b : dvar nat) : bool :=
  match a, b with
  | DBound x, DBound y => Nat.eqb x y
  | DotOf a', DotOf b' => dvar_eqb a' b'
  | BarOf a', BarOf b' => dvar_eqb a' b'
  | TapeOf a', TapeOf b' => dvar_eqb a' b'
  | ResultVar, ResultVar => true
  | _, _ => false
  end.

(* A key of the store: a variable, or where `d-return` leaves the returned
   value (`type returned dvar` in exec.elpi). *)
Inductive key : Type :=
| KVar (v : dvar nat)
| Returned.

Definition key_eqb (a b : key) : bool :=
  match a, b with
  | KVar x, KVar y => dvar_eqb x y
  | Returned, Returned => true
  | _, _ => false
  end.

Section Exec.
Variable N : Type.
Variable D : domain N.

Definition store := list (key * val N).

Fixpoint store_get (s : store) (x : key) : option (val N) :=
  match s with
  | (k, v) :: s' => if key_eqb k x then Some v else store_get s' x
  | [] => None
  end.

Fixpoint store_set (s : store) (x : key) (v : val N) : store :=
  match s with
  | [] => [(x, v)]
  | (k, w) :: s' => if key_eqb k x then (k, v) :: s' else (k, w) :: store_set s'
    x v
  end.

(* Expressions. *)
Fixpoint xeval (s : store) (e : dexpr nat) : option (val N) :=
  match e with
  | DVar x => store_get s (KVar x)
  | DReal l => let* x := dom_lit D l in Some (VReal x)
  | DInt k => Some (VInt k)
  | DAt a i =>
      match xeval s a, xeval s i with
      | Some (VArray l), Some (VInt k) => let* x := nth_z k l in Some (VReal x)
      | _, _ => None
      end
  | DOp1 f a => let* va := xeval s a in eval_op1 D f va
  | DOp2 f a b => let* va := xeval s a in let* vb :=
    xeval s b in eval_op2 D f va vb
  end.

(* assign s l v: the location l, a variable or an element of an array,
   receives v. *)
Definition assign (s : store) (l : dexpr nat) (v : val N) : option store :=
  match l, v with
  | DVar x, _ => Some (store_set s (KVar x) v)
  | DAt (DVar x) i, VReal e =>
      match store_get s (KVar x), xeval s i with
      | Some (VArray l), Some (VInt k) => let* l1 :=
        replace_nth_z k e l in Some (store_set s (KVar x) (VArray l1))
      | _, _ => None
      end
  | _, _ => None
  end.

(* for i in [lo, lo + n), upward, and for i from hi down n indices, downward:
   the body executed with i bound to each index. *)
Fixpoint exec_up (body : store -> option store) (i : dvar nat) (lo : Z)
  (n : nat) (s : store)
  : option store :=
  match n with
  | O => Some s
  | S n' => let* s1 := body (store_set s (KVar i) (VInt lo)) in exec_up body i
    (lo + 1) n' s1
  end.

Fixpoint exec_down (body : store -> option store) (i : dvar nat) (hi : Z)
  (n : nat) (s : store)
  : option store :=
  match n with
  | O => Some s
  | S n' => let* s1 := body (store_set s (KVar i) (VInt hi)) in exec_down body i
    (hi - 1) n' s1
  end.

(* Statements. *)
Fixpoint exec (st : dstmt nat) (s : store) : option store :=
  let exec_stmts := fix exec_stmts (l : list (dstmt nat)) (s : store) : option
    store :=
    match l with
    | [] => Some s
    | st' :: l' => let* s1 := exec st' s in exec_stmts l' s1
    end in
  match st with
  | DDefine _ x e => let* v := xeval s e in Some (store_set s (KVar x) v)
  | DRealVar x => let* z := dom_lit D "0" in Some
    (store_set s (KVar x) (VReal z))   (* T x{}: zero *)
  | DTape x => Some (store_set s (KVar x) (VTape []))
  | DAssign l e => let* v := xeval s e in assign s l v
  | DIncrement l e =>
      match xeval s l, xeval s e with
      | Some (VReal a), Some (VReal b) => let* c :=
        dom_op2 D Add a b in assign s l (VReal c)
      | _, _ => None
      end
  | DBranch c t e =>
      match xeval s c with
      | Some (VBool true) => exec_stmts t s
      | Some (VBool false) => exec_stmts e s
      | _ => None
      end
  | DFor i lo hi b =>
      match xeval s lo, xeval s hi with
      | Some (VInt l), Some (VInt h) => exec_up (exec_stmts b) i l (count l h) s
      | _, _ => None
      end
  | DForBack i lo hi b =>
      match xeval s lo, xeval s hi with
      | Some (VInt l), Some (VInt h) => exec_down (exec_stmts b) i (h - 1)
        (count l h) s
      | _, _ => None
      end
  | DPush t e =>
      match xeval s e, store_get s (KVar t) with
      | Some (VReal x), Some (VTape l) =>
        Some (store_set s (KVar t) (VTape (x :: l)))
      | _, _ => None
      end
  | DPop t l =>
      match store_get s (KVar t) with
      | Some (VTape (x :: xs)) => assign (store_set s (KVar t) (VTape xs)) l
        (VReal x)
      | _ => None
      end
  | DReturn e => let* v := xeval s e in Some (store_set s Returned v)
  end.

Fixpoint exec_stmts (l : list (dstmt nat)) (s : store) : option store :=
  match l with
  | [] => Some s
  | st :: l' => let* s1 := exec st s in exec_stmts l' s1
  end.

(* The variables of the function are opened first, numbered in order. *)
Fixpoint exec_scoped (sc : scoped nat (dbody nat)) (k : nat)
  (args : list (val N))
  : option (list (val N) * list (val N)) :=
  match sc with
  | Named _ f => exec_scoped (f k) (S k) args
  | Fresh _ f => exec_scoped (f k) (S k) args
  | Done (DBody r ps ss) =>
      if negb (Nat.eqb (length ps) (length args)) then None else
      let s0 := map (fun '(DParam _ _ x, a) => (KVar x, a)) (combine ps args) in
      let* s1 := exec_stmts ss s0 in
      let finals := map (fun '(DParam _ _ x) => store_get s1 (KVar x)) ps in
      let* fs := fold_right (fun o acc => let* v := o in let* l :=
        acc in Some (v :: l)) (Some []) finals in
      match r with
      | DReturnsReal => let* v := store_get s1 Returned in Some (fs, [v])
      | DVoid => Some (fs, [])
      end
  end.

Definition exec_dfunction (f : dfunction) (args : list (val N)) : option
  (list (val N) * list (val N)) :=
  exec_scoped (dfbody f nat) 0 args.

End Exec.

Arguments store_get {N}.  Arguments store_set {N}.  Arguments xeval {N}.
  Arguments assign {N}.
Arguments exec {N}.  Arguments exec_stmts {N}.  Arguments exec_scoped {N}.
  Arguments exec_dfunction {N}.
