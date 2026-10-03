(* Lower.v — mirrors lower.elpi: from the derivative IR (L2) to the target
   language (L3), the only pass that names variables and chooses C++ types.

   A variable bound by Named keeps its name; one bound by Fresh gets its
   prefix and a number. Elpi's new-name draws the number from a counter global
   to the run (new_int), so the locals are numbered across the functions of a
   file: here the counter is threaded, lower takes the next number and returns
   the one after, and lower_all lowers the functions of a file in order. In
   PHOAS the binders are instantiated with the names, as Elpi's hypothesis
   `dname v N` gives a bound variable its name. *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Derivative Target Operations Dump.

Import ListNotations.
Open Scope string_scope.

Definition return_type (r : dreturn) : string :=
  match r with DReturnsReal => "T" | DVoid => "void" end.

Definition array_type (k : Z) : string := "std::array<T, " ++ z_to_string k ++ ">".

Definition value_type (t : ty) : string := match t with Real => "const T" | _ => "const auto" end.

Definition pass_string (p : dpass) (t n : string) : string :=
  match p with
  | ByValue => t ++ " " ++ n
  | ByRef => t ++ "& " ++ n
  | ByCref => "const " ++ t ++ "& " ++ n
  | ByRefUnused => t ++ "& /*" ++ n ++ "*/"
  end.

Definition param_string (p : dparam string) : string :=
  let 'DParam pw t v := p in
  match t with
  | Integer => "int " ++ var_name v
  | Real => pass_string pw "T" (var_name v)
  | Array k => pass_string pw (array_type k) (var_name v)
  | Boolean => pass_string pw "bool" (var_name v)
  end.

(* The spelling of an operator: the first row of its table (operations.elpi). *)
Definition spelling1 (f : unary) : string :=
  match operation1 f with Some (_, _, s) => s | None => unary_name f end.

Definition spelling2 (f : binary) : string :=
  match operation2 f with Some (_, _, _, s) => s | None => binary_name f end.

Fixpoint lower_expr (e : dexpr string) : expr :=
  match e with
  | DVar v => Id (var_name v)
  | DReal s => Lit ("T(" ++ s ++ ")")
  | DInt k => Lit (z_to_string k)
  | DAt a i => At (lower_expr a) (lower_expr i)
  | DOp1 f a => Call (spelling1 f) (lower_expr a :: map Lit (extra_arguments f))
  | DOp2 f a b => Call (spelling2 f) [lower_expr a; lower_expr b]
  end.

Fixpoint lower_stmt (s : dstmt string) : stmt :=
  match s with
  | DDefine (DConstant t) v e => Declare (value_type t) (var_name v) (lower_expr e)
  | DDefine DMutable v e => Declare "T" (var_name v) (lower_expr e)
  | DRealVar v => Allocate "T" (var_name v)
  | DTape v => Allocate "std::vector<T>" (var_name v)
  | DAssign a b => Assign (lower_expr a) (lower_expr b)
  | DIncrement a b => Increment (lower_expr a) (lower_expr b)
  | DBranch c t e => Branch (lower_expr c) (map lower_stmt t) (map lower_stmt e)
  | DFor i lo hi b => Loop (var_name i) (lower_expr lo) (lower_expr hi) (map lower_stmt b)
  | DForBack i lo hi b => LoopBack (var_name i) (lower_expr lo) (lower_expr hi) (map lower_stmt b)
  | DPush t e => Push (var_name t) (lower_expr e)
  | DPop t e => Pop (var_name t) (lower_expr e)
  | DReturn e => Return (lower_expr e)
  end.

(* lower-scoped: the binders named in order, the counter threaded. *)
Fixpoint lower_scoped (name : string) (s : scoped string (dbody string)) (k : nat) : cfunction * nat :=
  match s with
  | Named n f => lower_scoped name (f n) k
  | Fresh p f => lower_scoped name (f (p ++ z_to_string (Z.of_nat k))) (S k)
  | Done (DBody r ps ss) => (CFunction (return_type r) name (map param_string ps) (map lower_stmt ss), k)
  end.

Definition lower (f : dfunction) (k : nat) : cfunction * nat := lower_scoped (dfname f) (dfbody f string) k.

(* The functions of a file, lowered in order; Elpi's new_int starts at 1. *)
Fixpoint lower_from (fs : list dfunction) (k : nat) : list cfunction :=
  match fs with
  | [] => []
  | f :: fs' => let '(c, k') := lower f k in c :: lower_from fs' k'
  end.

Definition lower_all (fs : list dfunction) : list cfunction := lower_from fs 1.
