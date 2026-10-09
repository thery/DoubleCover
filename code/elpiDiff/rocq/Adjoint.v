(* Adjoint.v — mirrors adjoint.elpi: reverse mode, the transposition, from L1ᵃ
   into L2.

   The adjoint of `let x = e in body` is the adjoint of body followed by the
   adjoint of e. Guided by the annotations of L1ᵃ, the forward sweep computes
   only the values the reverse sweep reads and records the state of a fold only
   when it is read; inside a reverse loop or branch, the values that are read
   are recomputed (replayed). adj, prim, fwd-value and rev-value call one
   another: here they are one mutually recursive block. Elpi's hypotheses
   become parameters (adjoint-result, written Y) or fields of tvar (recorded N,
   as the flag `rec` of a storage, Transform.v). *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Anf Derivative Operations Transform Tbr.

Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.

Section Adjoint.
Variable V : Type.

Notation tvar := (tvar V).
Notation code := (code V).
Definition sweeps := (list (dstmt V) * list (dstmt V))%type.   (* the forward sweep and the reverse sweep *)

Definition adjoint_primal (cv : bool) (a : decl * dvar V) : dparam V :=
  let '(Decl _ t r, v) := a in
  match t, r with
  | Integer, _ => DParam ByValue Integer v
  | _, Dependent => if cv then DParam ByRef t v else DParam ByRefUnused t v
  | Real, _ => DParam ByValue Real v
  | _, Inout => DParam ByValue t v
  | _, _ => DParam ByCref t v
  end.

Definition adjoint_bar (a : decl * dvar V) : list (dparam V) :=
  let '(Decl _ t r, v) := a in
  match t, r with
  | Integer, _ => []
  | _, Passive => []
  | Real, Dependent => [DParam ByValue Real (BarOf v)]
  | Real, _ => [DParam ByRef Real (BarOf v)]
  | _, Dependent => [DParam ByCref t (BarOf v)]
  | _, _ => [DParam ByRef t (BarOf v)]
  end.

Definition role_of (a : atom tvar) : option role :=
  match a with AVar y => match targ y with Some (_, r) => Some r | None => None end | _ => None end.

Definition stored_of (a : atom tvar) : dvar V :=
  match a with AVar y => tstored y | _ => ResultVar end.

(* The seed, the adjoint of the result: an argument for a returned value; the
   adjoint of the written real, read then reset when that real is also an input;
   none for an array, whose adjoint is read element by element. *)
Definition adjoint_seed (res : aresult tvar) : list (dparam V) * list (dstmt V) * dexpr V :=
  match res with
  | AReturns _ => ([DParam ByValue Real (BarOf ResultVar)], [], DVar (BarOf ResultVar))
  | AWrites y =>
      match tof y, role_of y with
      | Real, Some Dependent => ([], [], DVar (BarOf (stored_of y)))
      | Real, Some Inout =>
          ([], [DDefine (DConstant Real) (BarOf ResultVar) (DVar (BarOf (stored_of y)));
                DAssign (DVar (BarOf (stored_of y))) (DReal "0")],
           DVar (BarOf ResultVar))
      | _, _ => ([], [], DReal "0")
      end
  end.

(* value-output X: at the end of the forward sweep, X, the value of the function,
   sent where it goes, when the adjoint computes it (adjoint-result: vo). *)
Definition value_output (vo : option (aresult tvar)) (x : atom tvar) : list (dstmt V) :=
  match vo with
  | Some (AReturns _) => [DDefine (DConstant Real) ResultVar (spell x)]
  | Some (AWrites y) =>
      match tof y, role_of y with
      | Real, Some Dependent => [DAssign (DVar (stored_of y)) (spell x)]
      | _, _ => []
      end
  | None => []
  end.

Definition bar_declaration (t : ty) (n : dvar V) : list (dstmt V) :=
  match t with Real => [DDefine DMutable (BarOf n) (DReal "0")] | _ => [] end.

(* contribution A P X: `A_bar += P * X`, when the operand A carries an adjoint. *)
Definition contribution (a : atom tvar) (p : pexpr tvar) (x : dvar V) : list (dstmt V) :=
  match bar a with
  | Some ba => [DIncrement ba (scale (spell_partial p) (DVar x))]
  | None => []
  end.

(* The index written by the update that ends the body of an in-place fold. *)
Fixpoint tail_index (b : anf tvar ann) : dexpr V :=
  match b with
  | ALet _ (ASet _ i _) b' => if is_tail b' then spell i else tail_index (b' (probe V))
  | ALet _ _ b' => tail_index (b' (probe V))
  | ARet _ => DInt 0
  end.

(* rev-loop I Lo Hi Pop Mid: the reverse loop: restore, replay, then propagate. *)
Definition rev_loop (i : dvar V) (elo ehi : dexpr V) (pop mid : list (dstmt V)) (sw : sweeps) : list (dstmt V) :=
  let '(f, rv) := sw in [DForBack i elo ehi (app pop (app f (app mid rv)))].

Definition fwd_fold (i : dvar V) (elo ehi ei : dexpr V) (live : bool) (n : dvar V)
  (r : list (dstmt V) * dexpr V) : list (dstmt V) :=
  let '(sb, vb) := r in
  if live then
    [DDefine DMutable n ei; DTape (TapeOf n);
     DFor i elo ehi (app [DPush (TapeOf n) (DVar n)] (app sb [DAssign (DVar n) vb]))]
  else [DDefine DMutable n ei; DFor i elo ehi (app sb [DAssign (DVar n) vb])].

Section Adj.
Variable written : option (atom tvar).            (* written Y *)
Variable vo : option (aresult tvar).              (* adjoint-result, in mode adjoint-value *)

Definition let_ann (a : ann) : bool * bool * bool :=
  match a with LetAnn v ac c => (v, ac, c) | _ => (false, false, false) end.

Definition fold_ann (a : ann) : bool * bool * bool :=
  match a with FoldAnn v l r => (v, l, r) | _ => (false, false, false) end.

(* prim M T: the primal computation of T, recording when M is forward, with the
   value of its tail atom. *)
Fixpoint prim (m : sweep) (b : anf tvar ann) : scoped V (list (dstmt V) * dexpr V) :=
  match b with
  | ALet a e b' =>
      let '(v, _, _) := let_ann a in
      let t := type_of e in
      with_storage written e b' (fun n rec =>
        sbind (fwd_value m e t n rec) (fun se =>
        sbind (prim m (b' (open_let t n v rec))) (fun '(sb, x) => Done (app se sb, x))))
  | ARet x => Done ([], spell x)
  end

(* fwd-value M E T N: computes the value E into N; rec, whether N is recorded. *)
with fwd_value (m : sweep) (e : value tvar ann) (t : ty) (n : dvar V) (rec : bool) : code :=
  match e with
  | AOp1 f a => Done [DDefine (DConstant t) n (DOp1 f (spell a))]
  | AOp2 f a b => Done [DDefine (DConstant t) n (DOp2 f (spell a) (spell b))]
  | AGet a i => Done [DDefine (DConstant Real) n (DAt (spell a) (spell i))]
  | ASet _ i v =>
      let elem := DAt (DVar n) (spell i) in
      if sweep_eqb m Forward && rec then Done [DPush (TapeOf n) elem; DAssign elem (spell v)]
      else Done [DAssign elem (spell v)]
  | AIte c th el =>
      sbind (prim m th) (fun '(st, vt) => sbind (prim m el) (fun '(se, ve) =>
        Done [DRealVar n; DBranch (spell c) (app st [DAssign (DVar n) vt]) (app se [DAssign (DVar n) ve])]))
  | AMap lo hi b =>
      Fresh "i" (fun i =>
        sbind (prim m (b (open_index (DBound i)))) (fun '(sb, vb) =>
          Done [DFor (DBound i) (spell lo) (spell hi) (app sb [DAssign (DAt (DVar n) (DVar (DBound i))) vb])]))
  | AFold a lo hi init b =>
      let '(sv, live0, records) := fold_ann a in
      match t with
      | Real =>
          let live := sweep_eqb m Forward && live0 in
          Fresh "i" (fun i =>
            let '(ix, sx) := open_fold sv Real n (DBound i) false in
            sbind (prim m (b ix sx)) (fun r => Done (fwd_fold (DBound i) (spell lo) (spell hi) (spell init) live n r)))
      | Array k =>
          let rec_state := (sweep_eqb m Forward && live0) || rec in
          let decl := if sweep_eqb m Forward && is_written written init && records then [DTape (TapeOf n)] else [] in
          Fresh "i" (fun i =>
            let '(ix, sx) := open_fold sv (Array k) n (DBound i) rec_state in
            sbind (prim m (b ix sx)) (fun '(sb, _) => Done (app decl [DFor (DBound i) (spell lo) (spell hi) sb])))
      | _ => Done []
      end
  end.

(* adj M T Seed: the forward sweep, computing what the reverse sweep of T needs,
   and the reverse sweep, propagating Seed, the adjoint of T's value, back to
   the atoms of T. A let is computed when its annotation says so, and transposed
   when it is active. *)
Fixpoint adj (m : sweep) (b : anf tvar ann) (seed : dexpr V) : scoped V sweeps :=
  match b with
  | ALet a e b' =>
      let '(v, ac, c) := let_ann a in
      let t := type_of e in
      with_storage written e b' (fun n rec =>
        sbind (adj m (b' (open_let t n v rec)) seed) (fun '(fb, rb) =>
        sbind (if c then fwd_value m e t n rec else Done []) (fun fe =>
        sbind (if ac then rev_value e t n else Done []) (fun re =>
        Done (app fe fb, app (if ac then bar_declaration t n else []) (app rb re))))))
  | ARet x =>
      let fwd := if sweep_eqb m Forward then value_output vo x else [] in
      let rev := match tof x, bar x with
                 | Real, Some bx => [DIncrement bx seed]
                 | _, _ => []
                 end in
      Done (fwd, rev)
  end

(* rev-value E T N: propagates the adjoint of N, the value of E, to the atoms of E. *)
with rev_value (e : value tvar ann) (t : ty) (n : dvar V) : code :=
  match e with
  | AOp1 f a => Done (match partial1 f a with Some p => contribution a p (BarOf n) | None => [] end)
  | AOp2 f a b =>
      Done (match partial2 f a b with
            | Some (pa, pb) => app (contribution a pa (BarOf n)) (contribution b pb (BarOf n))
            | None => []
            end)
  | AGet a i =>
      Done (match bar a with Some ba => [DIncrement (DAt ba (spell i)) (DVar (BarOf n))] | None => [] end)
  | ASet _ i v =>
      let elem := DAt (DVar (BarOf n)) (spell i) in
      Done (match bar v with
            | Some bv => [DIncrement bv elem; DAssign elem (DReal "0")]
            | None => [DAssign elem (DReal "0")]
            end)
  | AIte c th el =>
      sbind (adj Replay th (DVar (BarOf n))) (fun '(ft, rt) =>
      sbind (adj Replay el (DVar (BarOf n))) (fun '(fe, re) =>
        Done [DBranch (spell c) (app ft rt) (app fe re)]))
  | AMap lo hi b =>
      Fresh "i" (fun i =>
        sbind (adj Replay (b (open_index (DBound i))) (DAt (DVar (BarOf n)) (DVar (DBound i)))) (fun sw =>
          Done (rev_loop (DBound i) (spell lo) (spell hi) [] [] sw)))
  | AFold a lo hi init b =>
      let '(sv, live, _) := fold_ann a in
      match t with
      | Real =>
          let pop := if live then [DPop (TapeOf n) (DVar n)] else [] in
          let after := match bar init with Some bi => [DIncrement bi (DVar (BarOf n))] | None => [] end in
          Fresh "i" (fun i => Fresh "r" (fun r =>
            let '(ix, sx) := open_fold sv Real n (DBound i) false in
            sbind (adj Replay (b ix sx) (DVar (BarOf (DBound r)))) (fun sw =>
              Done (app (rev_loop (DBound i) (spell lo) (spell hi) pop
                          [DDefine (DConstant Real) (BarOf (DBound r)) (DVar (BarOf n));
                           DAssign (DVar (BarOf n)) (DReal "0")] sw)
                        after))))
      | Array k =>
          Fresh "i" (fun i =>
            let '(ix, sx) := open_fold sv (Array k) n (DBound i) false in
            let pop := if live then [DPop (TapeOf n) (DAt (DVar n) (tail_index (b ix sx)))] else [] in
            sbind (adj Replay (b ix sx) (DReal "0")) (fun sw =>
              Done (rev_loop (DBound i) (spell lo) (spell hi) pop [] sw)))
      | _ => Done []
      end
  end.

End Adj.

(* The forward sweep, then the reverse sweep, then the returned value. *)
Definition adjoint_finish (cv : bool) (res : aresult tvar) (params : list (dparam V))
  (prologue : list (dstmt V)) (sw : sweeps) : dbody V :=
  let '(fwd, rev) := sw in
  match cv, res with
  | true, AReturns _ => DBody DReturnsReal params (app fwd (app prologue (app rev [DReturn (DVar ResultVar)])))
  | _, _ => DBody DVoid params (app fwd (app prologue rev))
  end.

(* The function writes an inout argument: adjoint-value does not give it back. *)
Definition inout_result (res : aresult tvar) : bool :=
  match res with AWrites y => match role_of y with Some Inout => true | _ => false end | _ => false end.

(* The generated signature: the arguments of the primal, then the adjoint of
   each argument that has one, then the adjoint of a returned value. *)
Definition adjoint_body (cv : bool) (args : list (decl * dvar V)) (res : aresult tvar) (b : anf tvar ann)
  (written : option (atom tvar)) : scoped V (dbody V) :=
  let ps := map (adjoint_primal cv) args in
  let bs := concat (map adjoint_bar args) in
  let '(extra, prologue, seed) := adjoint_seed res in
  let vo := if cv && negb (inout_result res) then Some res else None in
  sbind (adj written vo Forward b seed) (fun sw =>
    Done (adjoint_finish cv res (app ps (app bs extra)) prologue sw)).

End Adjoint.

(* adjoint Value F: the adjoint of F, computing its value as well when Value is true. *)
Definition adjoint (cv : bool) (f : afunction ann) : dfunction :=
  DFunction (afname f ++ (if cv then "_adjoint_value" else "_adjoint"))
            (fun V => with_arguments (afdef f (tvar V)) (adjoint_body V cv)).
