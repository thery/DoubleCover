(* =========================================================================  *)
(*  RowMinRun.v -- RowFoldCubDefD's run to thirteen, with Stdlib only loaded. *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowMin.v's run over RowMinTab.v's tables *)
(* and the generated ones, which need Stdlib only already: P1Fsm, P1Fold,    *)
(* P1Fdec, P1FTable and its chunks.  What the development computes -- the    *)
(* tables of the four numbers, ishmi -- is computed here by the same bodies; *)
(* the four values it reads off deeper files (ymvpi, yrooti, croot and       *)
(* csolvedci) are written in, as RowTransConsts.v prints them.                *)
(*                                                                            *)
(* Run it where the development was built (roquableu), beside                 *)
(* RowBenchCountF.v: fcount48 (rowmapiD 13) must be 14 731 320.              *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Stdlib Require Import List.
Require Import RowMin RowMinTab.
Require Import P1Fsm P1Fold P1Fdec P1FTable.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope uint63_scope.

(* ---- the four values read off Rocq (RowTransConsts.v) --------------------- *)

Definition ymvpi : arr :=
  [| 3; 0; 1; 2; 4; 5; 6; 7; 11; 8; 9; 10; 12; 13; 14; 15; 16; 17; 18; 19;
  2; 3; 0; 1; 4; 5; 6; 7; 10; 11; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19;
  1; 2; 3; 0; 4; 5; 6; 7; 9; 10; 11; 8; 12; 13; 14; 15; 16; 17; 18; 19;
  4; 1; 2; 0; 7; 5; 6; 3; 16; 9; 10; 11; 19; 13; 14; 15; 12; 17; 18; 8;
  7; 1; 2; 4; 3; 5; 6; 0; 12; 9; 10; 11; 8; 13; 14; 15; 19; 17; 18; 16;
  3; 1; 2; 7; 0; 5; 6; 4; 19; 9; 10; 11; 16; 13; 14; 15; 8; 17; 18; 12;
  1; 5; 2; 3; 0; 4; 6; 7; 8; 17; 10; 11; 12; 16; 14; 15; 9; 13; 18; 19;
  5; 4; 2; 3; 1; 0; 6; 7; 8; 13; 10; 11; 12; 9; 14; 15; 17; 16; 18; 19;
  4; 0; 2; 3; 5; 1; 6; 7; 8; 16; 10; 11; 12; 17; 14; 15; 13; 9; 18; 19;
  0; 1; 2; 3; 5; 6; 7; 4; 8; 9; 10; 11; 13; 14; 15; 12; 16; 17; 18; 19;
  0; 1; 2; 3; 6; 7; 4; 5; 8; 9; 10; 11; 14; 15; 12; 13; 16; 17; 18; 19;
  0; 1; 2; 3; 7; 4; 5; 6; 8; 9; 10; 11; 15; 12; 13; 14; 16; 17; 18; 19;
  0; 2; 6; 3; 4; 1; 5; 7; 8; 9; 18; 11; 12; 13; 17; 15; 16; 10; 14; 19;
  0; 6; 5; 3; 4; 2; 1; 7; 8; 9; 14; 11; 12; 13; 10; 15; 16; 18; 17; 19;
  0; 5; 1; 3; 4; 6; 2; 7; 8; 9; 17; 11; 12; 13; 18; 15; 16; 14; 10; 19;
  0; 1; 3; 7; 4; 5; 2; 6; 8; 9; 10; 19; 12; 13; 14; 18; 16; 17; 11; 15;
  0; 1; 7; 6; 4; 5; 3; 2; 8; 9; 10; 15; 12; 13; 14; 11; 16; 17; 19; 18;
  0; 1; 6; 2; 4; 5; 7; 3; 8; 9; 10; 18; 12; 13; 14; 19; 16; 17; 15; 11 | 0 |].

Definition yrooti : arr :=
  [| 0; 3; 6; 9; 12; 15; 18; 21; 1; 3; 5; 7; 9; 11; 13; 15; 17; 19; 21; 23 | 0 |].

Definition croot : int := 1013759.           (* RowInst.croot                 *)
Definition csolvedci : int := 494.           (* RowInst.csolvedci             *)

(* ---- Phase1, Farp1: the coordinate's step --------------------------------- *)

(* Phase1.twmove, acttwii                                                     *)
Definition twmove : arr := twmove_m.
Definition acttwii (x k : int) : int :=
  PArray.get twmove (Uint63.add (Uint63.mul x 18) k).

(* Farp1.fsmtabs, actfsri                                                     *)
Definition fsmtabs : PArray.array arr :=
  let a := PArray.make 3 (PArray.make 1 0) in
  let a := PArray.set a 0 fsm_chunk_00 in
  let a := PArray.set a 1 fsm_chunk_01 in
  let a := PArray.set a 2 fsm_chunk_02 in
  a.
Definition fcwlogi : int := 21.
Definition fcwmaski : int := 2097151.
Definition actfsri (r k : int) : int :=
  let i := Uint63.add (Uint63.mul r 18) k in
  let w := Uint63.div i 3 in
  let j := Uint63.sub i (Uint63.mul w 3) in
  let c := Uint63.lsr w fcwlogi in
  let o := Uint63.land w fcwmaski in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get fsmtabs c) o) (Uint63.mul j 20))
    1048575.

(* RowInst.cstep, over its section's fsstep                                   *)
Section Inst.
Variable fsstep : int -> int -> int.
Definition ctw (c : int) : int := Uint63.div c nfsi.
Definition cfs (c : int) : int := Uint63.mod c nfsi.
Definition cstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (ctw c) k) nfsi) (fsstep (cfs c) k).
End Inst.

(* ---- RowFoldCubDef ------------------------------------------------------- *)

(* RowFoldCubDef.fstep, ishmi                                                 *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).
Definition ishmi : int :=
  Eval vm_compute in
  ifold nmvn 0
    (fun k a =>
       if Uint63.eqb (fstep csolvedci k) csolvedci
       then Uint63.lor a (Uint63.lsl 1 k) else a)
    0.

(* RowFoldCubDef.ycsolvedd, okmvvd, srchd                                     *)
Definition ycsolvedd (c : int) : bool := Uint63.eqb c csolvedci.
Definition okmvvd (pv k : int) : bool :=
  if (18 <=? pv) then true
  else let fp := (pv / 3) in
       let fk := (k / 3) in
       negb (orb (fp =? fk) (fp =? fk + 3)).
Definition srchd : nat := 16%nat.

(* ---- FoldTables ----------------------------------------------------------- *)

Definition repa : arr := Eval vm_compute in rep_data.
Definition syma : arr := Eval vm_compute in sym_data.
Definition twsyma : arr := Eval vm_compute in twsym_data.
Definition frepi (r : int) : int := get20 repa r.
Definition fsymi (r : int) : int := get4 syma r.
Definition twsymi (tw s : int) : int :=
  get20 twsyma (Uint63.add (Uint63.mul tw nsymi) s).

(* ---- RowLeafFast: the rank ------------------------------------------------ *)

(* RowLeafFast.lbpop, lbcq, lbeq: the same values                             *)
Definition popc8 (s : int) : int :=
  ifold 8%nat 0 (fun b c => Uint63.add c (Uint63.land (Uint63.lsr s b) 1)) 0.
Definition lbpop : arr := Eval vm_compute in
  ifold 256%nat 0 (fun s a => PArray.set a s (popc8 s)) (PArray.make 256 0).
Definition lbcq : arr := Eval vm_compute in
  ifold 24%nat 0 (fun v a => PArray.set a v (Uint63.div v 3)) (PArray.make 24 0).
Definition lbeq : arr := Eval vm_compute in
  ifold 24%nat 0 (fun v a => PArray.set a v (Uint63.div v 2)) (PArray.make 24 0).

(* ssrint63.decr                                                              *)
Definition decr s := Uint63.sub s 1.

(* RowLeafFast.lbstep, lbrank                                                 *)
Definition lbstep (ni : int) (v : int -> int) (i st : int) : int :=
  let x := v i in
  let bx := Uint63.lsl 1 x in
  let seen := Uint63.land st 255 in
  let c := Uint63.sub x (PArray.get lbpop (Uint63.land seen (decr bx))) in
  Uint63.add (Uint63.lsl (Uint63.add (Uint63.mul (Uint63.lsr st 8) (Uint63.sub ni i)) c) 8)
             (Uint63.add seen bx).
Definition lbrank (v : int -> int) (nn : nat) (ni : int) : int :=
  Uint63.lsr (ifold nn 0 (lbstep ni v) 0) 8.

(* ---- RowCoord: the four numbers ------------------------------------------- *)

(* RowCoord.mkT                                                               *)
Definition mkT (sz : nat) (f : int -> int) : arr :=
  ifold sz 0 (fun i a => PArray.set a i (f i)) (PArray.make (of_nat sz) 0).

(* RowCoord.factA, nthfree, cunrank                                           *)
Definition factA : arr := mkT 8 (fun i => ifold (to_nat i) 1 Uint63.mul 1).
Definition nthfree (s c : int) : int :=
  fst (ifold 8%nat 0
     (fun v (st : int * int) =>
        let '(res, cnt) := st in
        if Uint63.eqb (Uint63.land s (Uint63.lsl 1 v)) 0
        then (if Uint63.eqb cnt c then v else res, Uint63.add cnt 1)
        else st)
     (0, 0)).
Definition cunrank (r : int) : arr :=
  let '(a, _, _) :=
    ifold 8%nat 0
      (fun i (st : arr * int * int) =>
         let '(a, r, s) := st in
         let f := PArray.get factA (Uint63.sub 7 i) in
         let c := Uint63.div r f in
         let v := nthfree s c in
         (PArray.set a i v, Uint63.sub r (Uint63.mul c f),
          Uint63.lor s (Uint63.lsl 1 v)))
      (PArray.make 8 0, r, 0) in a.

(* RowCoord.ctab                                                              *)
Definition ctab : arr :=
  mkT (40320 * 18)
    (fun i =>
       let r := Uint63.div i 18 in
       let k := Uint63.sub i (Uint63.mul r 18) in
       let a := cunrank r in
       lbrank (fun j => PArray.get a (PArray.get ymvpi (Uint63.add (Uint63.mul k 20) j)))
              8 8).

(* RowCoord.einvT                                                             *)
Definition einvT : arr :=
  ifold (18 * 12) 0
    (fun i a =>
       let k := Uint63.div i 12 in
       let j := Uint63.sub i (Uint63.mul k 12) in
       PArray.set a
         (Uint63.add (Uint63.mul k 12)
            (Uint63.sub (PArray.get ymvpi (Uint63.add (Uint63.mul k 20)
                                                      (Uint63.add 8 j))) 8))
         j)
    (PArray.make (18 * 12) 0).

(* RowCoord.enc, tp0 .. tp3, etab                                             *)
Definition ntup : nat := 20736%nat.
Definition enc (p0 p1 p2 p3 : int) : int :=
  Uint63.add (Uint63.mul (Uint63.add (Uint63.mul (Uint63.add (Uint63.mul p0 12) p1)
                                                 12) p2) 12) p3.
Definition tp0 (t : int) : int := Uint63.div t 1728.
Definition tp1 (t : int) : int := Uint63.mod (Uint63.div t 144) 12.
Definition tp2 (t : int) : int := Uint63.mod (Uint63.div t 12) 12.
Definition tp3 (t : int) : int := Uint63.mod t 12.
Definition etab : arr :=
  mkT (ntup * 18)
    (fun i =>
       let t := Uint63.div i 18 in
       let k := Uint63.sub i (Uint63.mul t 18) in
       let inv q := PArray.get einvT (Uint63.add (Uint63.mul k 12) q) in
       enc (inv (tp0 t)) (inv (tp1 t)) (inv (tp2 t)) (inv (tp3 t))).

(* RowCoord.all4, dist4, sub8tup, sub8, tup8                                  *)
Definition all4 (f : int -> bool) (t : int) : bool :=
  andb (f (tp0 t)) (andb (f (tp1 t)) (andb (f (tp2 t)) (f (tp3 t)))).
Definition dist4 (t : int) : bool :=
  let a := tp0 t in let b := tp1 t in let c := tp2 t in let d := tp3 t in
  negb (orb (a =? b) (orb (a =? c) (orb (a =? d) (orb (b =? c) (orb (b =? d) (c =? d)))))).
Definition n8t : int := 1680.
Definition sub8tup : arr * arr :=
  let '(s, u, _) :=
    ifold ntup 0
      (fun t (st : arr * arr * int) =>
         let '(s, u, n) := st in
         if andb (all4 (fun p => p <? 8) t) (dist4 t)
         then (PArray.set s t n, PArray.set u n t, Uint63.add n 1)
         else st)
      (PArray.make (of_nat ntup) 0, PArray.make n8t 0, 0) in (s, u).
Definition sub8 : arr := fst sub8tup.
Definition tup8 : arr := snd sub8tup.

(* RowCoord.cstepx                                                            *)
Definition cpos := (int * int * int * int)%type.
Definition cstepx (x : cpos) (k : int) : cpos :=
  let '(c, u, d, m) := x in
  (PArray.get ctab (Uint63.add (Uint63.mul c 18) k),
   PArray.get etab (Uint63.add (Uint63.mul u 18) k),
   PArray.get etab (Uint63.add (Uint63.mul d 18) k),
   PArray.get etab (Uint63.add (Uint63.mul m 18) k)).

(* RowCoord.eplace, cofy                                                      *)
Definition eplace (y : arr) (b : int) : int :=
  ifold 12%nat 0
    (fun p r => if Uint63.eqb (PArray.get lbeq (PArray.get y (Uint63.add 8 p))) b
                then p else r) 0.
Definition cofy (y : arr) : cpos :=
  let tup b := enc (eplace y b) (eplace y (Uint63.add b 1))
                   (eplace y (Uint63.add b 2)) (eplace y (Uint63.add b 3)) in
  (lbrank (fun p => PArray.get lbcq (PArray.get y p)) 8 8, tup 0, tup 4, tup 8).

(* ---- RowCoordLeaf: the member --------------------------------------------- *)

(* mathcomp's index, over int                                                 *)
Fixpoint index (p : int) (l : list int) : nat :=
  match l with
  | nil => O
  | x :: l' => if Uint63.eqb x p then O else S (index p l')
  end.

(* RowCoordLeaf.l8, ecub, e8rT, l4, mcub, e4rT, cmemb                          *)
Definition l8 (u v : int) : list int :=
  tp0 u :: tp1 u :: tp2 u :: tp3 u :: tp0 v :: tp1 v :: tp2 v :: tp3 v :: nil.
Definition ecub (u v p : int) : int := of_nat (index p (l8 u v)).
Definition e8rT : arr :=
  mkT (1680 * 1680)
    (fun i =>
       let a := Uint63.div i n8t in
       let b := Uint63.sub i (Uint63.mul a n8t) in
       lbrank (ecub (PArray.get tup8 a) (PArray.get tup8 b)) 8 8).
Definition l4 (m : int) : list int := tp0 m :: tp1 m :: tp2 m :: tp3 m :: nil.
Definition mcub (m p : int) : int := of_nat (index (Uint63.add p 8) (l4 m)).
Definition e4rT : arr := mkT ntup (fun t => lbrank (mcub t) 4 4).
Definition cmemb (x : cpos) : memb :=
  let '(c, u, d, m) := x in
  (c, PArray.get e8rT (Uint63.add (Uint63.mul (PArray.get sub8 u) n8t)
                                   (PArray.get sub8 d)),
   PArray.get e4rT m).

(* ---- RowFoldCubDefD.rowmapiD ---------------------------------------------- *)

Definition crootD : cpos := cofy yrooti.

Definition rowmapiD (n : nat) : rmap :=
  wrun e8num_m e4bit_m fpg_m fsrc_m fsrc2_m ffull_m fsgr_m fslo_m fshi_m fsbt_m
       mgr_m msw_m mlo_m mhi_m
       p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
       (cstep actfsri) cstepx cmemb okmvvd ycsolvedd
       croot crootD srchd forb_m fpop_m ishmi
       n 0 0 (mkempty tt) (mkempty tt).

(* ---- the bench ------------------------------------------------------------ *)

(* thrown away: the tables arriving, and the four numbers' tables built       *)
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (mkempty tt).
Time Eval native_compute in
  Uint63.add (Uint63.add (PArray.get ctab 5) (PArray.get etab 5))
    (Uint63.add (PArray.get e8rT 5) (Uint63.add (PArray.get e4rT 5) ishmi)).

(* the run to thirteen: 14 731 320, twice                                     *)
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (rowmapiD 13).
Time Eval native_compute in fcount48 ffull_m forb_m fpop_m (rowmapiD 13).
