(* Simplify.v — mirrors simplify.elpi: L2′, simplifications of the derivative
   IR, from L2 to L2.

   simplify compares variables (Elpi's X = V in mentions and replace-expr): the
   input is instantiated with pairs of a number and a variable of the output,
   the number allocated when its binder is opened; equality compares the
   numbers, and the simplified statements are converted to the output by
   keeping the variables. fuse restarts on a rearranged block, where Elpi needs
   no termination argument: here the three functions take a fuel, larger than
   the depth of their recursion (twice the number of statements); were it to run
   out, the block would be left as it is. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Derivative.

Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.

Section Simplify.
Variable V : Type.                                (* the variables of the output
  *)
Definition W := (nat * V)%type.                   (* the variables of the input
  *)

Fixpoint dvar_eq (a b : dvar W) : bool :=
  match a, b with
  | DBound (i, _), DBound (j, _) => Nat.eqb i j
  | DotOf a', DotOf b' => dvar_eq a' b'
  | BarOf a', BarOf b' => dvar_eq a' b'
  | TapeOf a', TapeOf b' => dvar_eq a' b'
  | ResultVar, ResultVar => true
  | _, _ => false
  end.

Definition is_lit (s : string) (e : dexpr W) : bool :=
  match e with DReal l => String.eqb l s | _ => false end.

(* Expressions, bottom-up. *)
Definition simplify_op1 (f : unary) (a : dexpr W) : dexpr W :=
  match f, a with
  | Pow 1, _ => a
  | Pow 0, _ => DReal "1"
  | Neg, DOp1 Neg a' => a'
  | _, _ => DOp1 f a
  end.

Definition simplify_op2 (f : binary) (a b : dexpr W) : dexpr W :=
  match f with
  | Mul => if is_lit "0" a then DReal "0" else if is_lit "0" b then DReal "0"
           else if is_lit "1" a then b else if is_lit "1" b then a
           else if is_lit "-1" a then DOp1 Neg b else if is_lit "-1" b then DOp1
             Neg a
           else DOp2 f a b
  | Add => if is_lit "0" a then b else if is_lit "0" b then a else DOp2 f a b
  | Sub => if is_lit "0" b then a else DOp2 f a b
  | _ => DOp2 f a b
  end.

Fixpoint simplify_expr (e : dexpr W) : dexpr W :=
  match e with
  | DOp1 f a => simplify_op1 f (simplify_expr a)
  | DOp2 f a b => simplify_op2 f (simplify_expr a) (simplify_expr b)
  | DAt a i => DAt (simplify_expr a) (simplify_expr i)
  | _ => e
  end.

(* mentions V S: the statement S, or a block nested in it, reads or writes V. *)
Fixpoint mentions_expr (v : dvar W) (e : dexpr W) : bool :=
  match e with
  | DVar x => dvar_eq x v
  | DAt a i => mentions_expr v a || mentions_expr v i
  | DOp1 _ a => mentions_expr v a
  | DOp2 _ a b => mentions_expr v a || mentions_expr v b
  | _ => false
  end.

Fixpoint mentions (v : dvar W) (s : dstmt W) : bool :=
  match s with
  | DDefine _ x e => dvar_eq x v || mentions_expr v e
  | DRealVar x => dvar_eq x v
  | DTape x => dvar_eq x v
  | DAssign a b => mentions_expr v a || mentions_expr v b
  | DIncrement a b => mentions_expr v a || mentions_expr v b
  | DBranch c t e => mentions_expr v c || existsb (mentions v) t ||
    existsb (mentions v) e
  | DFor i lo hi b => dvar_eq i v || mentions_expr v lo || mentions_expr v hi ||
    existsb (mentions v) b
  | DForBack i lo hi b => dvar_eq i v || mentions_expr v lo ||
    mentions_expr v hi || existsb (mentions v) b
  | DPush t e => dvar_eq t v || mentions_expr v e
  | DPop t e => dvar_eq t v || mentions_expr v e
  | DReturn e => mentions_expr v e
  end.

(* writes V S: the statement S, or a block nested in it, assigns or
   accumulates into V, or pushes or pops the tape V. *)
Fixpoint target (v : dvar W) (e : dexpr W) : bool :=
  match e with
  | DVar x => dvar_eq x v
  | DAt a _ => target v a
  | _ => false
  end.

Fixpoint writes (v : dvar W) (s : dstmt W) : bool :=
  match s with
  | DAssign a _ => target v a
  | DIncrement a _ => target v a
  | DPush t _ => dvar_eq t v
  | DPop t a => dvar_eq t v || target v a
  | DBranch _ t e => existsb (writes v) t || existsb (writes v) e
  | DFor _ _ _ b => existsb (writes v) b
  | DForBack _ _ _ b => existsb (writes v) b
  | _ => false
  end.

(* replace-stmt V L S: S with the variable V replaced by the literal L. *)
Fixpoint replace_expr (v : dvar W) (l : dexpr W) (e : dexpr W) : dexpr W :=
  match e with
  | DVar x => if dvar_eq x v then l else e
  | DAt a i => DAt (replace_expr v l a) (replace_expr v l i)
  | DOp1 f a => DOp1 f (replace_expr v l a)
  | DOp2 f a b => DOp2 f (replace_expr v l a) (replace_expr v l b)
  | _ => e
  end.

Fixpoint replace_stmt (v : dvar W) (l : dexpr W) (s : dstmt W) : dstmt W :=
  let re := replace_expr v l in
  match s with
  | DDefine so x e => DDefine so x (re e)
  | DAssign a b => DAssign (re a) (re b)
  | DIncrement a b => DIncrement (re a) (re b)
  | DBranch c t e => DBranch (re c) (map (replace_stmt v l) t)
    (map (replace_stmt v l) e)
  | DFor i lo hi b => DFor i (re lo) (re hi) (map (replace_stmt v l) b)
  | DForBack i lo hi b => DForBack i (re lo) (re hi) (map (replace_stmt v l) b)
  | DPush t e => DPush t (re e)
  | DPop t e => DPop t (re e)
  | DReturn e => DReturn (re e)
  | _ => s
  end.

(* first-mention V Ss: the statements of Ss before the first that mentions V,
   that one, and the rest. *)
Fixpoint first_mention (v : dvar W) (ss : list (dstmt W)) : option
  (list (dstmt W) * dstmt W * list (dstmt W)) :=
  match ss with
  | [] => None
  | s :: ss' => if mentions v s then Some ([], s, ss')
                else match first_mention v ss' with
                     | Some (b, m, a) => Some (s :: b, m, a)
                     | None => None
                     end
  end.

(* Statements: the expressions and the nested blocks first,
   then the block (fuse). *)
Fixpoint simplify_stmts (n : nat) (ss : list (dstmt W)) : list (dstmt W) :=
  match n with
  | O => ss
  | S n' => fuse n' (map (simplify_stmt n') ss)
  end

with simplify_stmt (n : nat) (s : dstmt W) : dstmt W :=
  match n with
  | O => s
  | S n' =>
      match s with
      | DDefine so v e => DDefine so v (simplify_expr e)
      | DAssign a b => DAssign (simplify_expr a) (simplify_expr b)
      | DIncrement a b => DIncrement (simplify_expr a) (simplify_expr b)
      | DBranch c t e => DBranch (simplify_expr c) (simplify_stmts n' t)
        (simplify_stmts n' e)
      | DFor i lo hi b => DFor i (simplify_expr lo) (simplify_expr hi)
        (simplify_stmts n' b)
      | DForBack i lo hi b => DForBack i (simplify_expr lo) (simplify_expr hi)
        (simplify_stmts n' b)
      | DPush t e => DPush t (simplify_expr e)
      | DPop t e => DPop t (simplify_expr e)
      | DReturn e => DReturn (simplify_expr e)
      | _ => s
      end
  end

(* fuse Ss: the accumulations of the block Ss that start at zero, fused. *)
with fuse (n : nat) (ss : list (dstmt W)) : list (dstmt W) :=
  match n with
  | O => ss
  | S n' =>
      match ss with
      | [] => []
      | s :: ss' =>
          match s with
          | DIncrement _ e => if is_lit "0" e then fuse n' ss' else s :: fuse n'
            ss'
          | DDefine DMutable v e0 =>
              if is_lit "0" e0 then
                let fused :=
                  match first_mention v ss' with
                  | Some (before, DIncrement (DVar x) e, after) =>
                      if dvar_eq x v && negb (mentions_expr v e) then
                        let so := if existsb (writes v) after then DMutable else
                          DConstant Real in
                        Some (fuse n' (app before (DDefine so v e :: after)))
                      else None
                  | _ => None
                  end in
                match fused with
                | Some r => r
                | None => if negb (existsb (mentions v) ss') then fuse n' ss'
                  else s :: fuse n' ss'
                end
              else s :: fuse n' ss'
          | DDefine (DConstant t) v e =>
              match e with
              | DReal l => simplify_stmts n'
                (map (replace_stmt v (DReal l)) ss')
              | _ => let r := fuse n' ss' in if existsb (mentions v) r then s ::
                r else r
              end
          | _ => s :: fuse n' ss'
          end
      end
  end.

(* The size of a block, for the fuel. *)
Fixpoint size (s : dstmt W) : nat :=
  match s with
  | DBranch _ t e => S (fold_right (fun x n => size x + n) 0 t + fold_right
    (fun x n => size x + n) 0 e)
  | DFor _ _ _ b | DForBack _ _ _ b => S
    (fold_right (fun x n => size x + n) 0 b)
  | _ => 1
  end.

Definition fuel (ss : list (dstmt W)) : nat :=
  2 * fold_right (fun x n => size x + n) 0 ss + 10.

(* From the input to the output: the variables of the output. *)
Fixpoint out_dvar (v : dvar W) : dvar V :=
  match v with
  | DBound (_, x) => DBound x
  | DotOf v' => DotOf (out_dvar v')
  | BarOf v' => BarOf (out_dvar v')
  | TapeOf v' => TapeOf (out_dvar v')
  | ResultVar => ResultVar
  end.

Fixpoint out_dexpr (e : dexpr W) : dexpr V :=
  match e with
  | DVar v => DVar (out_dvar v)
  | DReal s => DReal s
  | DInt k => DInt k
  | DAt a i => DAt (out_dexpr a) (out_dexpr i)
  | DOp1 f a => DOp1 f (out_dexpr a)
  | DOp2 f a b => DOp2 f (out_dexpr a) (out_dexpr b)
  end.

Fixpoint out_dstmt (s : dstmt W) : dstmt V :=
  match s with
  | DDefine so v e => DDefine so (out_dvar v) (out_dexpr e)
  | DRealVar v => DRealVar (out_dvar v)
  | DTape v => DTape (out_dvar v)
  | DAssign a b => DAssign (out_dexpr a) (out_dexpr b)
  | DIncrement a b => DIncrement (out_dexpr a) (out_dexpr b)
  | DBranch c t e => DBranch (out_dexpr c) (map out_dstmt t) (map out_dstmt e)
  | DFor i lo hi b => DFor (out_dvar i) (out_dexpr lo) (out_dexpr hi)
    (map out_dstmt b)
  | DForBack i lo hi b => DForBack (out_dvar i) (out_dexpr lo) (out_dexpr hi)
    (map out_dstmt b)
  | DPush t e => DPush (out_dvar t) (out_dexpr e)
  | DPop t e => DPop (out_dvar t) (out_dexpr e)
  | DReturn e => DReturn (out_dexpr e)
  end.

Definition out_dparam (p : dparam W) : dparam V :=
  let 'DParam pw t v := p in DParam pw t (out_dvar v).

(* The variables of the function are opened, numbered in order. *)
Fixpoint simplify_scoped (s : scoped W (dbody W)) (k : nat) : scoped V (dbody V)
  :=
  match s with
  | Named n f => Named n (fun v => simplify_scoped (f (k, v)) (S k))
  | Fresh p f => Fresh p (fun v => simplify_scoped (f (k, v)) (S k))
  | Done (DBody r ps ss) =>
      Done (DBody r (map out_dparam ps)
        (map out_dstmt (simplify_stmts (fuel ss) ss)))
  end.

End Simplify.

Definition simplify (f : dfunction) : dfunction :=
  DFunction (dfname f) (fun V => simplify_scoped V (dfbody f (nat * V)) 0).
