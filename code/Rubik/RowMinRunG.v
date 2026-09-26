(* =========================================================================  *)
(*  RowMinRunG.v -- the folded run with its search over globals, timed        *)
(*  beside the one over section variables.                                    *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  native_compute makes every `if' and      *)
(* every match of a function into an OCaml function of its own, and hands it *)
(* every variable in scope.  RowFoldN's search is written in a section, so   *)
(* its twenty odd section variables -- the tables, cstep, xstep, okmv ...    *)
(* -- are in scope everywhere: one move tried passes 22, 20, 19 and 16        *)
(* arguments through four nested tests (.coq-native/NRubik_RowMin.native,    *)
(* case_iwsrchL_80 .. 72).                                                   *)
(*                                                                            *)
(* Here the counting search, its leaf, the level and the run name the tables *)
(* and the step functions as global constants, so a test carries only the    *)
(* search's own variables.  THE BODIES ARE RowFoldN's, word for word, with   *)
(* each section variable replaced by the constant RowMinInst.rowmapiD hands  *)
(* it.  The stopping level and the prepass are called as before.             *)
(*                                                                            *)
(* Both runs to thirteen, alternated: 14 731 320 all four.                   *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMin RowMinTab RowMinInst.
Require Import P1Fdec P1FTable.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope uint63_scope.

(* ---- the section's variables, as globals ---------------------------------- *)

(* RowInst.cstep at RowMinInst.actfsri                                        *)
Definition cstepG (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (ctw c) k) nfsi) (actfsri (cfs c) k).

(* RowFoldSrch.fp1g at p1ftab frepi fsymi twsymi, Dfoldm written out          *)
Definition p1gG (c : int) : int :=
  let tw := Uint63.div c nfsi in
  let r := Uint63.sub c (Uint63.mul tw nfsi) in
  let y := fsymi r in
  Uint63.lor (p1getm p1ftab (foldi (frepi r) (twsymi tw y)))
             (Uint63.lsl y mbits).

(* RowMask.mmask at the four decoding tables                                  *)
Definition wmaskG (w : int) (s : nat) : int :=
  mmask dnlo_data dnhi_data fllo_data flhi_data w s.

(* RowFoldN.fmarknw at fpg fsgr fsbt forb                                     *)
Definition fmarknwG (mn : rmap * int) (pg gr bt : int) : rmap * int :=
  fmarknw fpg_m fsgr_m fsbt_m forb_m mn pg gr bt.

(* ---- RowFoldN's search, over the globals ---------------------------------- *)

(* RowFoldN.wleaf                                                             *)
Definition wleafG (c : int) (x : cpos) (a : rmap * int) : rmap * int :=
  if ycsolvedd c
  then let '(pg, gr, bt) := place24 e8num_m e4bit_m (cmemb x) in
       fmarknwG a pg gr bt
  else a.

(* RowFoldN.iwsrchL                                                           *)
Fixpoint iwsrchLG (cut : bool) (togo : nat) (togoi : int) (c : int) (x : cpos)
                  (msk pv : int) (a : rmap * int) : rmap * int :=
  match togo with
  | S togo' =>
    match togo' with
    | O =>
      ifold nmvn 0
        (fun k a' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
           else if negb (okmvvd pv k) then a'
           else if andb cut
                  (negb (Uint63.eqb (Uint63.land ishmi (Uint63.lsl 1 k)) 0))
           then a'
           else wleafG (cstepG c k) (cstepx x k) a')
        a
    | _ =>
    let togoi' := Uint63.sub togoi 1 in
    ifold nmvn 0
      (fun k a' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
         else if negb (okmvvd pv k) then a'
         else if (if cut
                  then (if eqn togo' O
                        then negb (Uint63.eqb (Uint63.land ishmi
                                                 (Uint63.lsl 1 k)) 0)
                        else false)
                  else false)
         then a'
         else
           let c' := cstepG c k in
           let w := p1gG c' in
           let nd := mdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then iwsrchLG cut togo' togoi' c' (cstepx x k)
                         (wmaskG w (fsslack (Uint63.sub togoi' nd))) k a'
           else a')
      a
    end
  | O => wleafG c x a
  end.

(* RowFoldN.wslv; the stopping level is isrchskL as before                    *)
Definition wslvG (cut : bool) (d : nat) (m' : rmap) (nb : int) : rmap * int :=
  if leq d srchd then
    let w := p1gG croot in
    let di := of_nat d in
    if (mdist w <=? di) then
      let msk := wmaskG w (fsslack (Uint63.sub di (mdist w))) in
      if eqn d srchd then
        let e := Uint63.add enoughb (Uint63.div nb enoughd) in
        isrchskL e8num_m e4bit_m fpg_m fsgr_m fsbt_m
          p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
          (cstep actfsri) cstepx cmemb okmvvd ycsolvedd ishmi
          cut d di croot crootD msk 18 e (m', nb)
      else iwsrchLG cut d di croot crootD msk 18 (m', nb)
    else (m', nb)
  else (m', nb).

(* RowFoldN.wrun; the prepass is flevel as before                             *)
Fixpoint wrunG (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  match n with
  | S n1 =>
    if Uint63.ltb ncutb n0 then
      let m1 := flevel fsrc_m fsrc2_m ffull_m fsgr_m fslo_m fshi_m
                       mgr_m msw_m mlo_m mhi_m m dst in
      let a := wslvG true (S d) m1 (fcount forb_m fpop_m m1) in
      wrunG n1 (S d) (snd a) (fst a) m
    else
      let a := wslvG false (S d) m n0 in
      wrunG n1 (S d) (snd a) (fst a) dst
  | O => m
  end.

Definition rowmapiDG (n : nat) : rmap := wrunG n 0 0 (mkempty tt) (mkempty tt).

(* ---- the bench ------------------------------------------------------------ *)

(* thrown away: the tables arriving, and the four numbers' tables built       *)
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (mkempty tt).
Time Eval native_compute in
  Uint63.add (Uint63.add (PArray.get ctab 5) (PArray.get etab 5))
    (Uint63.add (PArray.get e8rT 5) (Uint63.add (PArray.get e4rT 5) ishmi)).

(* over globals, then over the section's variables, twice: 14 731 320 all    *)
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (rowmapiDG 13).
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (rowmapiD 13).
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (rowmapiDG 13).
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (rowmapiD 13).
