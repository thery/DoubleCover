(* Tangent.v — mirrors tangent.elpi: forward mode, the linearization, from
   L1ᵃ into L2.

   The tangent program computes every value together with its tangent. For
   `let x = op F a b`, x_dot is the sum, over the varied operands, of the
   partial derivative times the tangent of the operand. The continuations of
   Elpi (tan-prepend, tan-ite-then, …) are the functions given to sbind. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Anf Derivative Operations Transform.

Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.

Section Tangent.
Variable V : Type.

Notation tvar := (tvar V).
Notation code := (code V).
Definition tangent_code := scoped V (list (dstmt V) * (dexpr V * dexpr V)).
  (* statements, value and tangent of the tail atom *)

Definition tangent_primal (a : decl * dvar V) : dparam V :=
  let '(Decl _ t r, v) := a in
  match t with
  | Integer => DParam ByValue Integer v
  | _ => if written_role r then DParam ByRef t v
         else match t with Real => DParam ByValue Real v | _ =>
           DParam ByCref t v end
  end.

Definition tangent_dot (a : decl * dvar V) : list (dparam V) :=
  let '(Decl _ t r, v) := a in
  match t, r with
  | Integer, _ => []
  | _, Passive => []
  | Real, Independent => [DParam ByValue Real (DotOf v)]
  | _, Independent => [DParam ByCref t (DotOf v)]
  | _, _ => [DParam ByRef t (DotOf v)]
  end.

(* Where the result goes: returned, with its tangent in an argument; stored in
   the written real; an array is written in place, element by element. *)
Definition tangent_result (res : aresult tvar) (v d : dexpr V) : dreturn * list
  (dparam V) * list (dstmt V) :=
  match res with
  | AReturns _ => (DReturnsReal, [DParam ByRef Real (DotOf ResultVar)],
                   [DAssign (DVar (DotOf ResultVar)) d; DReturn v])
  | AWrites (AVar y) =>
      match tty y with
      | Real => (DVoid, [], [DAssign (DVar (tstored y)) v;
        DAssign (DVar (DotOf (tstored y))) d])
      | _ => (DVoid, [], [])
      end
  | AWrites _ => (DVoid, [], [])
  end.

(* tangent-term A P: the partial derivative P times the tangent of the operand
   A, when A is varied. *)
Definition tangent_term (a : atom tvar) (p : pexpr tvar) : list (dexpr V) :=
  if tvaried_atom a then [scale (spell_partial p) (dot a)] else [].

Definition tan_ite (vr : bool) (ec : dexpr V) (n : dvar V)
  (bt be : list (dstmt V) * (dexpr V * dexpr V)) : list (dstmt V) :=
  let '(st, (vt, dt)) := bt in let '(se, (ve, de)) := be in
  if vr then
    [DRealVar n; DRealVar (DotOf n);
     DBranch ec (app st [DAssign (DVar n) vt; DAssign (DVar (DotOf n)) dt])
                (app se [DAssign (DVar n) ve; DAssign (DVar (DotOf n)) de])]
  else
    [DRealVar n; DBranch ec (app st [DAssign (DVar n) vt])
      (app se [DAssign (DVar n) ve])].

Definition tan_map (i : dvar V) (elo ehi : dexpr V) (vr : bool) (n : dvar V)
  (r : list (dstmt V) * (dexpr V * dexpr V)) : list (dstmt V) :=
  let '(sb, (vb, db)) := r in
  if vr then
    [DFor i elo ehi (app sb [DAssign (DAt (DVar n) (DVar i)) vb;
      DAssign (DAt (DVar (DotOf n)) (DVar i)) db])]
  else
    [DFor i elo ehi (app sb [DAssign (DAt (DVar n) (DVar i)) vb;
      DAssign (DAt (DVar (DotOf n)) (DVar i)) (DReal "0")])].

Definition tan_fold (i : dvar V) (elo ehi ei di : dexpr V) (vr : bool)
  (n : dvar V)
  (r : list (dstmt V) * (dexpr V * dexpr V)) : list (dstmt V) :=
  let '(sb, (vb, db)) := r in
  if vr then
    [DDefine DMutable n ei; DDefine DMutable (DotOf n) di;
     DFor i elo ehi (app sb [DAssign (DVar n) vb; DAssign (DVar (DotOf n)) db])]
  else
    [DDefine DMutable n ei; DFor i elo ehi (app sb [DAssign (DVar n) vb])].

Section Tan.
Variable written : option (atom tvar).            (* written Y *)

(* tan T: the statements computing T, with the value and the tangent of its tail
   atom. *)
Fixpoint tan (b : anf tvar ann) : tangent_code :=
  match b with
  | ALet a e b' =>
      let vr := match a with LetAnn v _ _ => v | _ => false end in
      let t := type_of e in
      with_storage written e b' (fun n rec =>
        sbind (tan_value e t vr n) (fun se =>
        sbind (tan (b' (open_let t n vr rec)))
          (fun '(sb, vd) => Done (app se sb, vd))))
  | ARet x => Done ([], (spell x, dot x))
  end

(* tan-value E T Vr N: computes the value E into N, and its tangent when E is
   varied, as Vr says. *)
with tan_value (e : value tvar ann) (t : ty) (vr : bool) (n : dvar V) : code :=
  match e with
  | AOp1 f a =>
      let ee := DOp1 f (spell a) in
      if vr then
        let terms := match partial1 f a with Some p => tangent_term a p |
          None => [] end in
        Done [DDefine (DConstant t) n ee;
          DDefine (DConstant Real) (DotOf n) (sum terms)]
      else Done [DDefine (DConstant t) n ee]
  | AOp2 f a b =>
      let ee := DOp2 f (spell a) (spell b) in
      if vr then
        let terms := match partial2 f a b with
                     | Some (pa, pb) => app (tangent_term a pa)
                       (tangent_term b pb)
                     | None => []
                     end in
        Done [DDefine (DConstant t) n ee;
          DDefine (DConstant Real) (DotOf n) (sum terms)]
      else Done [DDefine (DConstant t) n ee]
  | AGet a i =>
      let ea := spell a in let ei := spell i in
      if tvaried_atom a then
        Done [DDefine (DConstant Real) n (DAt ea ei);
          DDefine (DConstant Real) (DotOf n) (DAt (dot a) ei)]
      else Done [DDefine (DConstant Real) n (DAt ea ei)]
  | ASet _ i v =>
      let ei := spell i in let ev := spell v in
      if vr then Done [DAssign (DAt (DVar n) ei) ev;
        DAssign (DAt (DVar (DotOf n)) ei) (dot v)]
      else Done [DAssign (DAt (DVar n) ei) ev]
  | AIte c th el =>
      sbind (tan th) (fun bt => sbind (tan el)
        (fun be => Done (tan_ite vr (spell c) n bt be)))
  | AMap lo hi b =>
      Fresh "i" (fun i =>
        sbind (tan (b (open_index (DBound i))))
          (fun r => Done (tan_map (DBound i) (spell lo) (spell hi) vr n r)))
  | AFold a lo hi init b =>
      let svr := match a with FoldAnn v _ _ => v | _ => false end in
      match t with
      | Real =>
          let di := if svr then dot init else DReal "0" in
          Fresh "i" (fun i =>
            let '(ix, sx) := open_fold svr Real n (DBound i) false in
            sbind (tan (b ix sx)) (fun r =>
              Done (tan_fold (DBound i) (spell lo) (spell hi) (spell init) di
              svr n r)))
      | Array k =>
          Fresh "i" (fun i =>
            let '(ix, sx) := open_fold svr (Array k) n (DBound i) false in
            sbind (tan (b ix sx)) (fun '(sb, _) =>
              Done [DFor (DBound i) (spell lo) (spell hi) sb]))
      | _ => Done []
      end
  end.

End Tan.

(* The generated signature: the arguments of the primal, then the tangent of
   each argument that has one, then the tangent of a returned value. *)
Definition tangent_body (args : list (decl * dvar V)) (res : aresult tvar)
  (b : anf tvar ann)
  (written : option (atom tvar)) : scoped V (dbody V) :=
  let ps := map tangent_primal args in
  let ds := concat (map tangent_dot args) in
  sbind (tan written b) (fun '(s, (v, d)) =>
    let '(ret, extra, tail) := tangent_result res v d in
    Done (DBody ret (app ps (app ds extra)) (app s tail))).

End Tangent.

Definition tangent (f : afunction ann) : dfunction :=
  DFunction (afname f ++ "_tangent")
    (fun V => with_arguments (afdef f (tvar V)) (tangent_body V)).
