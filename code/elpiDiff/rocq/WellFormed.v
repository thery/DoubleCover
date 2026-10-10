(* WellFormed.v — mirrors well-formed.elpi: the supported language, as a
   judgment that returns a diagnostic.

   Elpi opens a binder with hypotheses on its variable: its type (`of x T`)
   and, for an argument, its name and role (`argument x N R`). In PHOAS the
   variables are instantiated with the record of that information, `vinfo`,
   whose `vid`, numbered in order, is the identity of the variable that Elpi's
   same_term and occurs compare. The hypothesis `written Y` becomes an argument,
   and Elpi's diagnostic, ok or error M, an inductive. Where Elpi leaves the
   type of a refused body unbound, the type here is Real: it is never read when
   the diagnostic is an error. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Anf Operations Normalize.

Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.

Inductive diagnostic : Type :=
| Ok
| Error (m : string).

(* What a typing judgment knows of a variable. *)
Record vinfo : Type := VInfo {
  vid : nat;                                      (* its identity *)
  vty : ty;                                       (* of x T *)
  varg : option (string * role)                   (* argument x N R,
    for an argument *)
}.

(* A variable opened without information,
   to look into a binder: as Elpi's pi. *)
Definition anon (k : nat) : vinfo := VInfo k Real None.

(* Typing: `of A Ty`. *)
Definition of_atom (a : atom vinfo) : ty :=
  match a with
  | ANum _ => Real
  | ANat _ => Integer
  | AVar v => vty v
  end.

(* same_term on atoms: the same variable. *)
Definition same_atom (a b : atom vinfo) : bool :=
  match a, b with
  | AVar x, AVar y => Nat.eqb (vid x) (vid y)
  | _, _ => false
  end.

(* occurs Y T: the variable y occurs in T; the binders of T are opened with
   identities from k on, beyond those of the variables in scope. *)
Definition occurs_atom (y : nat) (a : atom vinfo) : bool :=
  match a with AVar v => Nat.eqb (vid v) y | _ => false end.

Fixpoint occurs_anf {I : Type} (y : nat) (k : nat) (b : anf vinfo I) : bool :=
  match b with
  | ALet _ e b' => occurs_value y k e || occurs_anf y (S k) (b' (anon k))
  | ARet x => occurs_atom y x
  end
with occurs_value {I : Type} (y : nat) (k : nat) (e : value vinfo I) : bool :=
  match e with
  | AOp1 _ a => occurs_atom y a
  | AOp2 _ a b => occurs_atom y a || occurs_atom y b
  | AGet a i => occurs_atom y a || occurs_atom y i
  | ASet a i v => occurs_atom y a || occurs_atom y i || occurs_atom y v
  | AIte c t e => occurs_atom y c || occurs_anf y k t || occurs_anf y k e
  | AMap lo hi b => occurs_atom y lo || occurs_atom y hi ||
    occurs_anf y (S k) (b (anon k))
  | AFold _ lo hi init b =>
      occurs_atom y lo || occurs_atom y hi || occurs_atom y init
      || occurs_anf y (S (S k)) (b (anon k) (anon (S k)))
  end.

(* B = (x\ a-ret x): the body only returns the variable it binds. *)
Definition is_tail {I : Type} (b : vinfo -> anf vinfo I) (k : nat) : bool :=
  match b (anon k) with
  | ARet (AVar v) => Nat.eqb (vid v) k
  | _ => false
  end.

(* Where a body sits, since some constructs are only supported in some places.
   *)
Inductive place : Type :=
| Top                                             (* the body of the function *)
| InBranch                                        (* a branch of an ite *)
| ScalarBody                                      (* the body of a map or of a
  scalar fold *)
| ArrayBody (index state : atom vinfo).
  (* the body of an in-place fold: its index and its state *)

Definition written_decl (d : decl) : bool := let 'Decl _ _ r :=
  d in written_role r.

Definition ty_is_array (t : ty) : bool := match t with Array _ => true | _ =>
  false end.

(* An in-place fold starts from the written argument at the end of the function,
   or from the state of the enclosing in-place fold at the end of its body. *)
Definition in_place_init (written : option (atom vinfo)) (p : place)
  (tail : bool) (init : atom vinfo) : bool :=
  match p, tail with
  | Top, true => match written with Some y => same_atom init y | None =>
    false end
  | ArrayBody _ state, true => same_atom init state
  | _, _ => false
  end.

(* reads-around-inner-loop S B: B ends with an inner in-place loop,
   and reads the
   state S before it. *)
Fixpoint ends_with_fold (k : nat) (b : anf vinfo bare) : bool :=
  match b with
  | ALet _ (AFold _ _ _ _ _) b' => is_tail b' k ||
    ends_with_fold (S k) (b' (anon k))
  | ALet _ _ b' => ends_with_fold (S k) (b' (anon k))
  | ARet _ => false
  end.

Fixpoint reads_before_tail (s : nat) (k : nat) (b : anf vinfo bare) : bool :=
  match b with
  | ALet _ e b' => if is_tail b' k then false
                   else occurs_value s k e ||
                     reads_before_tail s (S k) (b' (anon k))
  | ARet _ => false
  end.

Definition reads_around_inner_loop (s : nat) (k : nat) (b : anf vinfo bare) :
  bool :=
  ends_with_fold k b && reads_before_tail s k b.

Definition is_ok (d : diagnostic) : bool := match d with Ok => true | _ =>
  false end.

Definition q (s : string) : string := "`" ++ s ++ "`".

Section Typecheck.
Variable written : option (atom vinfo).
  (* the argument a `writes` function stores into *)

(* typecheck p b k = (T, D): in place p, the body b has type T, or D explains
   why not; its binders are numbered from k. *)
Fixpoint typecheck (p : place) (k : nat) (b : anf vinfo bare) : ty * diagnostic
  :=
  match b with
  | ALet _ e b' =>
      let tail := is_tail b' k in
      let '(te, d0) := typecheck_value p tail k e in
      if is_ok d0 then typecheck p (S k) (b' (VInfo k te None)) else (Real, d0)
  | ARet x =>
      (* a body that computes an array does not end with another array argument
         *)
      match x with
      | AVar v =>
          let other := match written with Some y => negb (same_atom x y) |
            None => true end in
          match varg v with
          | Some (nx, _) =>
              if ty_is_array (vty v) && other
              then (vty v, Error (q nx ++
                " is an argument: an array the function computes must be built, by a map or an in-place loop, not taken from another argument"))
              else (of_atom x, Ok)
          | None => (of_atom x, Ok)
          end
      | _ => (of_atom x, Ok)
      end
  end
with typecheck_value (p : place) (tail : bool) (k : nat) (e : value vinfo bare)
  : ty * diagnostic :=
  match e with
  | AOp1 f a =>
      let s := unary_name f in
      match operation1 f with
      | None => (Real, Error (q s ++
        " is not an elementary operation: no partial derivative is known for it"))
      | Some (ta, t0, _) =>
          if ty_eqb (of_atom a) ta then (t0, Ok)
          else (Real, Error (q s ++
            " is applied to an operand of the wrong type"))
      end
  | AOp2 f a b =>
      let s := binary_name f in
      match operation2 f with
      | None => (Real, Error (q s ++
        " is not an elementary operation: no partial derivative is known for it"))
      | Some _ =>
          match operation2_typed f (of_atom a) (of_atom b) with
          | Some (t0, _) => (t0, Ok)
          | None => (Real, Error (q s ++
            " is applied to operands of the wrong types"))
          end
      end
  | AGet a i =>
      if ty_is_array (of_atom a) && ty_eqb (of_atom i) Integer then (Real, Ok)
      else (Real, Error "a[i] needs an array and an integer index")
  | ASet a i v =>
      let ok_set :=
        match p, of_atom a with
        | ArrayBody index state, Array n =>
            if tail && same_atom a state && ty_eqb (of_atom v) Real
               && (same_atom i index || match i with ANat _ => true | _ =>
                 false end)
            then Some n else None
        | _, _ => None
        end in
      match ok_set with
      | Some n => (Array n, Ok)
      | None =>
        (Real, Error
        "an array update must end the body of a fold on that array, at the loop index")
      end
  | AIte c t e =>
      match p with
      | ArrayBody _ _ => (Real, Error
        "a branch inside an in-place loop is not supported")
      | _ =>
          if ty_eqb (of_atom c) Boolean then
            let '(t1, d1) := typecheck InBranch k t in
            let '(t2, d2) := typecheck InBranch k e in
            if is_ok d1 then
              if is_ok d2 then
                if ty_eqb t1 Real && ty_eqb t2 Real then (Real, Ok)
                else (Real, Error "both branches must compute a real")
              else (Real, d2)
            else (Real, d1)
          else (Real, Error "a branch condition must be a comparison")
      end
  | AMap lo hi b =>
      match p, tail, lo, hi with
      | Top, true, ANat l, ANat h =>
          let n := (h - l)%Z in
          if negb (l =? 0)%Z then (Array n, Error "a map starts at index 0")
            else
          match written with
          | Some (AVar y) as w =>
              match varg y with
              | Some (ny, Inout) =>
                  (Array n, Error (q ny ++
                    " is inout: a map computes the whole array, so the argument it writes is dependent"))
              | _ =>
              if occurs_anf (vid y) (S k) (b (anon k)) then
                let ny := match varg y with Some (nm, _) => nm | None =>
                  "" end in
                (Array n, Error (q ny ++
                  " is the array the loop writes: a map cannot read it"))
              else
                let '(t, d0) := typecheck ScalarBody (S k)
                  (b (VInfo k Integer None)) in
                if is_ok d0 then if ty_eqb t Real then (Array n, Ok) else
                  (Array n, Error "a map must compute reals")
                else (Array n, d0)
              end
          | _ =>
              let '(t, d0) := typecheck ScalarBody (S k)
                (b (VInfo k Integer None)) in
              if is_ok d0 then if ty_eqb t Real then (Array n, Ok) else
                (Array n, Error "a map must compute reals")
              else (Array n, d0)
          end
      | _, _, _, _ =>
        (Real, Error
        "a map must end the function, with integer literal bounds, writing its output")
      end
  | AFold _ lo hi init b =>
      if ty_eqb (of_atom lo) Integer && ty_eqb (of_atom hi) Integer then
        if ty_eqb (of_atom init) Real then
          match p with
          | Top =>
              let '(t1, d0) := typecheck ScalarBody (S (S k))
                (b (VInfo k Integer None) (VInfo (S k) Real None)) in
              if is_ok d0 then if ty_eqb t1 Real then (Real, Ok)
                               else
                                 (Real, Error
                                 "a scalar recurrence must compute a real")
              else (Real, d0)
          | _ =>
            (Real, Error
            "a scalar recurrence inside a loop body or a branch is not supported")
          end
        else
          match of_atom init with
          | Array n =>
              if in_place_init written p tail init then
                (* the loop does not read the array before it: the written
                   argument, or the state of the enclosing in-place loop *)
                let reads_before :=
                  match init with
                  | AVar y => if occurs_anf (vid y) (S (S k))
                    (b (anon k) (anon (S k))) then Some y else None
                  | _ => None
                  end in
                match reads_before with
                | Some y =>
                    match varg y with
                    | Some (ny, _) =>
                        (Array n, Error (q ny ++
                          " is the array before the loop that updates it in place: inside that loop, read its current version, the loop state"))
                    | None =>
                        (Array n, Error
                          "an in-place loop nested in another cannot read the state of the outer one: read its own state")
                    end
                | None =>
                    let i := VInfo k Integer None in
                    let s := VInfo (S k) (Array n) None in
                    let '(t1, d0) := typecheck (ArrayBody (AVar i) (AVar s))
                      (S (S k)) (b i s) in
                    if is_ok d0 then
                      if ty_eqb t1 (Array n) then
                        if reads_around_inner_loop (S k) (S (S k))
                          (b (anon k) (anon (S k)))
                        then (Array n, Error
                          "an in-place loop that contains another one cannot read the array itself")
                        else (Array n, Ok)
                      else (Array n, Error
                        "an in-place loop must compute the next version of its array")
                    else (Array n, d0)
                end
              else
                (Real, Error
                "a fold carries a real, or updates in place the array the function writes")
          | _ =>
            (Real, Error
            "a fold carries a real, or updates in place the array the function writes")
          end
      else (Real, Error "loop bounds must be integers")
  end.

End Typecheck.

(* well-formed-result: where the result goes,
   checked against the declarations. *)
Definition well_formed_result (decls : list decl) (r : aresult vinfo)
  (b : anf vinfo bare) (k : nat) : diagnostic :=
  match r with
  | AReturns Real =>
      if existsb written_decl decls
      then Error
        "a function that returns a real cannot declare a dependent or inout argument"
      else let '(t, d0) := typecheck None Top k b in
           if is_ok d0 then if ty_eqb t Real then Ok else Error
             "the body must compute a real" else d0
  | AReturns _ => Error "a function can only return a real"
  | AWrites y =>
      match y with
      | AVar v =>
          match varg v with
          | Some (n, role) =>
              if written_role role then
                let ty := vty v in
                if negb (Nat.eqb (length (filter written_decl decls)) 1)
                then Error
                  "a function writes a single dependent or inout argument"
                else if negb (ty_eqb ty Real || ty_is_array ty) then Error
                  "only a real or an array of reals can be written"
                else
                  let '(t, d0) := typecheck (Some y) Top k b in
                  if is_ok d0 then
                    if negb (ty_eqb t ty) then Error
                      "the body must compute the argument it writes"
                    else match role with
                         | Dependent => if occurs_anf (vid v) k b then
                                          Error
                                            (q n ++
                                            " is declared dependent but the body reads it: an argument read then written is inout")
                                        else Ok
                         | Inout => if negb (occurs_anf (vid v) k b) then
                                      Error
                                        (q n ++
                                        " is declared inout but the body never reads it: an argument only written is dependent")
                                    else Ok
                         | _ => Ok
                         end
                  else d0
              else Error
                "a function can only write a dependent or inout argument"
          | None => Error
            "a function can only write a dependent or inout argument"
          end
      | _ => Error "a function can only write a dependent or inout argument"
      end
  end.

(* Opening the definition: an argument has a type,
   and a name and a role for the diagnostics. *)
Fixpoint well_formed_definition (decls : list decl) (k : nat)
  (d : adefinition vinfo bare) : diagnostic :=
  match d with
  | AArg n t r f => well_formed_definition decls (S k)
    (f (VInfo k t (Some (n, r))))
  | ABody r b => well_formed_result decls r b k
  end.

(* non-real-varied: the first argument that is independent or inout but
   neither a real nor an array: it would carry no derivative. *)
Fixpoint non_real_varied (ds : list decl) : option string :=
  match ds with
  | [] => None
  | Decl n t r :: ds' =>
      if varied_role r && negb (ty_eqb t Real || ty_is_array t) then Some n else
        non_real_varied ds'
  end.

Definition well_formed (f : afunction bare) : diagnostic :=
  let decls := declarations (afdef f unit) in
  match non_real_varied decls with
  | Some n => Error
    (q n ++
    " is independent or inout: only a real or an array of reals carries a derivative")
  | None => well_formed_definition decls 0 (afdef f vinfo)
  end.

(* type-of E T: the type of a value in a well-formed body, annotated or not. *)
Definition type_of {I : Type} (e : value vinfo I) : option ty :=
  match e with
  | AOp1 f a => match operation1 f with
                | Some (ta, t, _) => if ty_eqb (of_atom a) ta then Some t else
                  None
                | None => None
                end
  | AOp2 f a b => match operation2_typed f (of_atom a) (of_atom b) with
                  | Some (t, _) => Some t
                  | None => None
                  end
  | AGet _ _ => Some Real
  | ASet a _ _ => Some (of_atom a)
  | AIte _ _ _ => Some Real
  | AMap (ANat l) (ANat h) _ => Some (Array (h - l))
  | AMap _ _ _ => None
  | AFold _ _ _ init _ => Some (of_atom init)
  end.
