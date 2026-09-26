(* =========================================================================  *)
(*  RowOpt.v -- what the row search computes at every node, done faster, and *)
(*  each proved equal to what it replaces.                                   *)
(* =========================================================================  *)

(* perf on roquableu (RowMinRun.v, native_compute, depth 13) put 14.5 % of   *)
(* the cycles in Uint63.div and Uint63.rem, which native code calls out of   *)
(* line as real 64 bit divisions, and about 9.7 % in the type argument a     *)
(* polymorphic ifold is handed at every call.  Here:                         *)
(*   - a division by a constant is a multiplication and a shift, and a mod   *)
(*     is a subtraction;                                                     *)
(*   - the flip and slice step is two small tables, where it was one of      *)
(*     48 MB: the flip x slice rank is flip * 495 + slice;                   *)
(*   - fsgr is four fifteen bit entries a word, 1.3 MB where it was 5 MB;    *)
(*   - ifoldM is ifold at the one type the searches use it at.               *)
(*                                                                            *)
(* EVERY FAST FORM FIRST ASKS WHETHER ITS ARGUMENT IS IN THE RANGE IT WAS    *)
(* CHECKED ON, and computes the original otherwise.  A comparison is far     *)
(* cheaper than a division, and each equation then holds for every int, so  *)
(* nothing about ranges reaches the searches that use them.  The ranges are  *)
(* checked by vm_compute, over the whole of each.                            *)
(*                                                                            *)
(* THE RANGE IS ASKED OF THE BLOCK, i lsr 12 <? 4455 and not i <? 18247680:  *)
(* the proofs then meet no number bigger than a block count.  Eighteen       *)
(* million in unary, which vm_compute builds as a term, does not fit in      *)
(* memory.                                                                   *)

From Stdlib Require Import ZArith Lia.
From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Phase1 Row RowMap RowInst RowTab Fold FoldTables P1FTable.
Require Import P1Fdec RowMask Farp1 RowFold RowFoldTab RowFoldSrch RowSrch.
Require Import RowFoldCubDef RowFoldN.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- a check over every int below na * nb --------------------------------- *)

(* A walk of eighteen million ints recurses eighteen million deep; this one  *)
(* walks na blocks of nb and recurses na + nb deep.                          *)
Definition iter2 (na nb : nat) (b : int) (f : int -> bool) : bool :=
  iter na 0 (fun a => iter nb 0 (fun c => f (Uint63.add (Uint63.mul a b) c))).

Lemma iter2_at na nb b f x :
  iter2 na nb b f -> to_nat b = nb -> (0 < nb)%N ->
  (to_nat (x / b) < na)%N -> f x.
Proof.
move=> hi hb nbP ha.
have hc : (to_nat (x mod b) < nb)%N by rewrite to_nat_mod hb ltn_pmod.
have h := iter_at (iter_at hi ha) hc.
by rewrite [x in f x](int_add_mod x b).
Qed.

(* ---- a mod is a subtraction, a halving a shift ---------------------------- *)

Lemma modE i j : i - i / j * j = i mod j.
Proof.
apply: to_nat_inj; rewrite to_nat_mod.
have iB := to_nat_bounded i.
have hle : (to_nat (i / j) * to_nat j <= to_nat i)%N.
  by rewrite to_nat_div leq_divM.
have hmul : to_nat (i / j * j) = (to_nat (i / j) * to_nat j)%N.
  by apply: to_nat_mul; apply: leq_ltn_trans hle iB.
have h1 : (to_nat (i / j * j) <= to_nat i)%N by rewrite hmul.
rewrite (@to_nat_sub i (i / j * j) h1 iB) hmul to_nat_div.
by rewrite {1}(divn_eq (to_nat i) (to_nat j)) addKn.
Qed.

(* a shift by k is a division by b = 2 ^ k                                  *)
Lemma lsrE x k b : to_nat b = (2 ^ to_nat k)%N -> Uint63.lsr x k = x / b.
Proof. by move=> hb; apply: to_nat_inj; rewrite to_nat_lsr to_nat_div hb. Qed.

Lemma lsr1E x : Uint63.lsr x 1 = x / 2.
Proof.
apply: to_nat_inj; rewrite to_nat_lsr to_nat_div to_nat_1 expn1.
by have -> : to_nat 2 = 2%N by [].
Qed.

Lemma land1E x : Uint63.land x 1 = x mod 2.
Proof.
have h := @land_power2 x 1 (erefl true).
have e1 : decr (lsl one 1) = 1 by [].
have e2 : lsl one 1 = 2 by [].
by rewrite e1 e2 in h.
Qed.

(* ---- division by a constant ----------------------------------------------- *)

(* i / 3 below 4455 * 4096 = 18 247 680 = 1 013 760 * 18: every index of a   *)
(* three to a word table the search reads, and of the move table             *)
Definition div3m (i : int) : int := Uint63.lsr (Uint63.mul i 11184811) 25.
Definition div3o (i : int) : int :=
  if Uint63.lsr i 12 <? 4455 then div3m i else i / 3.

(* stated unfolded: matching iter2_at against a name makes Rocq evaluate it *)
Lemma div3chkT : iter2 4455 4096 4096 (fun i => div3m i =? i / 3).
Proof. by vm_compute. Qed.

Lemma div3oE i : div3o i = i / 3.
Proof.
rewrite /div3o; case: nltbP => h //.
have e : Uint63.lsr i 12 = i / 4096 by apply: lsrE.
have hn : to_nat 4455 = 4455%N by [].
rewrite e hn in h.
by move: (iter2_at div3chkT (erefl _) (erefl _) h) => /neqbP/to_nat_inj.
Qed.

(* i / 15 below 495 * 2048 = 1 013 760: every index of a fifteen to a word   *)
(* table the search reads                                                     *)
Definition div15m (i : int) : int := Uint63.lsr (Uint63.mul i 559241) 23.
Definition div15o (i : int) : int :=
  if Uint63.lsr i 11 <? 495 then div15m i else i / 15.

Lemma div15chkT : iter2 495 2048 2048 (fun i => div15m i =? i / 15).
Proof. by vm_compute. Qed.

Lemma div15oE i : div15o i = i / 15.
Proof.
rewrite /div15o; case: nltbP => h //.
have e : Uint63.lsr i 11 = i / 2048 by apply: lsrE.
have hn : to_nat 495 = 495%N by [].
rewrite e hn in h.
by move: (iter2_at div15chkT (erefl _) (erefl _) h) => /neqbP/to_nat_inj.
Qed.

(* x / 495 below 529 * 2048 = 1 083 392: every coordinate shifted by eleven *)
(* (under 2187 * 495 = 1 082 565), and every flip and slice rank             *)
Definition div495m (x : int) : int := Uint63.lsr (Uint63.mul x 271147) 27.
Definition div495o (x : int) : int :=
  if Uint63.lsr x 11 <? 529 then div495m x else x / 495.

Lemma div495chkT : iter2 529 2048 2048 (fun x => div495m x =? x / 495).
Proof. by vm_compute. Qed.

Lemma div495oE x : div495o x = x / 495.
Proof.
rewrite /div495o; case: nltbP => h //.
have e : Uint63.lsr x 11 = x / 2048 by apply: lsrE.
have hn : to_nat 529 = 529%N by [].
rewrite e hn in h.
by move: (iter2_at div495chkT (erefl _) (erefl _) h) => /neqbP/to_nat_inj.
Qed.

(* c / nfsi, nfsi = 2 ^ 11 * 495, as (c lsr 11) / 495: exact for every c     *)
Definition divnfs (c : int) : int := div495o (Uint63.lsr c 11).

(* in Z, where nfsi is not a million nested successors                     *)
Lemma divnfsE c : divnfs c = c / nfsi.
Proof.
rewrite /divnfs div495oE; apply: to_Z_inj.
have e11 : to_Z 11 = 11%Z by [].
have e495 : to_Z 495 = 495%Z by [].
have enfs : to_Z nfsi = (2 ^ 11 * 495)%Z by [].
rewrite !div_spec lsr_spec e11 e495 enfs Z.div_div //.
Qed.

(* ---- the reads of the phase one table ------------------------------------- *)

(* Fold.get20, get4                                                           *)
Definition get20O (a : arr) (i : int) : int :=
  let w := div3o i in
  let j := Uint63.sub i (Uint63.mul w nwide) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j wbits)) wmaski.

Lemma get20OE a i : get20O a i = get20 a i.
Proof. by rewrite /get20O /get20 /nwide div3oE. Qed.

Definition get4O (a : arr) (i : int) : int :=
  let w := div15o i in
  let j := Uint63.sub i (Uint63.mul w nnarrow) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j nbits)) nmask4.

Lemma get4OE a i : get4O a i = get4 a i.
Proof. by rewrite /get4O /get4 /nnarrow div15oE. Qed.

(* Phase1.p1getm at p1ftab                                                    *)
Definition p1getmO (i : int) : int :=
  let w := Uint63.lsr i 1 in
  let r := Uint63.sub i (Uint63.mul w mper) in
  let c := Uint63.lsr w cwlogi in
  let o := Uint63.land w cwmaski in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get p1ftab c) o) (Uint63.mul r mbits))
    mmaski.

Lemma p1getmOE i : p1getmO i = p1getm p1ftab i.
Proof. by rewrite /p1getmO /p1getm /mper lsr1E. Qed.

(* RowFoldSrch.fp1g and RowSrch.sp1g at the folded table                      *)
Definition p1gO (c : int) : int :=
  let tw := divnfs c in
  let r := Uint63.sub c (Uint63.mul tw nfsi) in
  let y := get4O syma r in
  Uint63.lor
    (p1getmO (foldi (get20O repa r)
                    (get20O twsyma (Uint63.add (Uint63.mul tw Fold.nsymi) y))))
    (Uint63.lsl y mbits).

Lemma p1gOE c : p1gO c = fp1g p1ftab frepi fsymi twsymi c.
Proof.
rewrite /p1gO /fp1g /Dfoldm /frepi /fsymi /twsymi divnfsE; cbv beta zeta.
by rewrite get4OE !get20OE p1getmOE.
Qed.

Lemma p1gOEs c : p1gO c = sp1g p1ftab frepi fsymi twsymi c.
Proof. by rewrite p1gOE /fp1g /sp1g. Qed.

(* RowMask.mmask at the four decoding tables                                  *)
Definition mmaskO (w : int) (s : nat) : int :=
  if (2 <= s)%N then allmvi
  else
    let b := Uint63.mul (Uint63.land (Uint63.lsr w mbits) msmask) ndeci in
    let c := Uint63.lsr w mdbits in
    let lo := Uint63.add b (Uint63.land c mfmask) in
    let hi := Uint63.add b (Uint63.land (Uint63.lsr c mfbits) mfmask) in
    if s is 1%N
    then Uint63.lor (get20O fllo_data lo) (get20O flhi_data hi)
    else Uint63.lor (get20O dnlo_data lo) (get20O dnhi_data hi).

Lemma mmaskOE w s :
  mmaskO w s = mmask dnlo_data dnhi_data fllo_data flhi_data w s.
Proof. by rewrite /mmaskO /mmask; cbv zeta; rewrite !get20OE. Qed.

(* ---- the step of the phase one coordinate ---------------------------------- *)

(* the flip part of the flip x slice move, and the slice part                 *)
Definition nflipmv : int := 36864.            (* 2048 flips by 18 moves      *)
Definition nslicemv : int := 8910.            (* 495 slices by 18 moves      *)

Definition fmO : arr := Eval vm_compute in
  ifold (2048 * 18) 0
    (fun i a =>
       let f := i / 18 in
       let k := Uint63.sub i (Uint63.mul f 18) in
       PArray.set a i (actfsri (Uint63.mul f 495) k / 495))
    (PArray.make nflipmv 0).

Definition smO : arr := Eval vm_compute in
  ifold (495 * 18) 0
    (fun i a =>
       let s := i / 18 in
       let k := Uint63.sub i (Uint63.mul s 18) in
       PArray.set a i (actfsri s k mod 495))
    (PArray.make nslicemv 0).

(* the move of a flip x slice rank, from the two, and as the check reads it  *)
Definition fsstepO (fs k : int) : int :=
  let f := div495o fs in
  let s := fs - f * 495 in
  Uint63.add (Uint63.mul (PArray.get fmO (Uint63.add (Uint63.mul f 18) k)) 495)
             (PArray.get smO (Uint63.add (Uint63.mul s 18) k)).

Definition fsstepR (fs k : int) : int :=
  let f := fs / 495 in
  let s := fs mod 495 in
  Uint63.add (Uint63.mul (PArray.get fmO (Uint63.add (Uint63.mul f 18) k)) 495)
             (PArray.get smO (Uint63.add (Uint63.mul s 18) k)).

Lemma fsstepOE fs k : fsstepO fs k = fsstepR fs k.
Proof. by rewrite /fsstepO /fsstepR; cbv zeta; rewrite div495oE modE. Qed.

(* every rank and every move: the two tables are the move table            *)
Lemma fschkT :
  iter2 495 2048 2048
    (fun fs => iter 18 0 (fun k => fsstepR fs k =? actfsri fs k)).
Proof. by vm_compute. Qed.

(* RowInst.cstep at actfsri                                                   *)
Definition cstepO (c k : int) : int :=
  let tw := divnfs c in
  let fs := c - tw * nfsi in
  if k <? 18 then
    if Uint63.lsr fs 11 <? 495 then
      Uint63.add (Uint63.mul (acttwii tw k) nfsi) (fsstepO fs k)
    else RowInst.cstep actfsri c k
  else RowInst.cstep actfsri c k.

Lemma cstepOE c k : cstepO c k = RowInst.cstep actfsri c k.
Proof.
rewrite /cstepO; cbv zeta; case: nltbP => hk //; case: nltbP => hf //.
rewrite divnfsE modE in hf *.
rewrite fsstepOE /RowInst.cstep /ctw /cfs.
have e : Uint63.lsr (c mod nfsi) 11 = c mod nfsi / 2048 by apply: lsrE.
have hn : to_nat 495 = 495%N by [].
rewrite e hn in hf.
have hk18 : (to_nat k < 18)%N by move: hk; have -> : to_nat 18 = 18%N by [].
have := iter_at (iter2_at fschkT (erefl _) (erefl _) hf) hk18.
by move=> /neqbP/to_nat_inj ->.
Qed.

(* ---- the moves a node may take --------------------------------------------- *)

(* RowFoldCubDef.okmvvd, RowReal.okmvv: the face of a move                    *)
Definition okmvO (pv k : int) : bool :=
  if (18 <=? pv) then true
  else let fp := div3o pv in
       let fk := div3o k in
       ~~ ((fp =? fk) || (fp =? fk + 3)).

Lemma okmvOE pv k : okmvO pv k = okmvvd pv k.
Proof. by rewrite /okmvO /okmvvd !div3oE. Qed.

(* ---- the place of a member -------------------------------------------------- *)

(* Row.place24 at the layout tables                                           *)
Definition place24O (x : memb) : int * int * int :=
  (mcp x, Uint63.lsr (PArray.get e8numi (mud x)) 1, PArray.get e4biti (mmp x)).

Lemma place24OE x : place24O x = place24 e8numi e4biti x.
Proof. by rewrite /place24O /place24 lsr1E. Qed.

(* Row.place at the layout tables                                             *)
Definition placeO (x : memb) : int * int * int :=
  (Uint63.lsr (PArray.get e8numi (mcp x)) 1,
   Uint63.lsr (PArray.get e8numi (mud x)) 1,
   Uint63.add (Uint63.mul (Uint63.land (PArray.get e8numi (mcp x)) 1) nbiti)
              (PArray.get e4biti (mmp x))).

Lemma placeOE x : placeO x = place e8numi e4biti x.
Proof. by rewrite /placeO /place !lsr1E land1E. Qed.

(* ---- fsgr, four entries of fifteen bits a word ----------------------------- *)

Definition nfsgrw : int := 161280.            (* 645 120 entries, four a word *)

Definition fsgrP : arr := Eval vm_compute in
  ifold 161280 0
    (fun w a =>
       let g j := PArray.get fsgri (Uint63.add (Uint63.mul w 4) j) in
       PArray.set a w
         (Uint63.lor (Uint63.lor (g 0) (Uint63.lsl (g 1) 15))
                     (Uint63.lor (Uint63.lsl (g 2) 30) (Uint63.lsl (g 3) 45))))
    (PArray.make nfsgrw 0).

(* entry i                                                                    *)
Definition gt4 (i : int) : int :=
  Uint63.land (Uint63.lsr (PArray.get fsgrP (Uint63.lsr i 2))
                          (Uint63.mul (Uint63.land i 3) 15)) 32767.

(* every entry reads back                                                     *)
Lemma fsgrchkT : iter2 315 2048 2048 (fun i => gt4 i =? PArray.get fsgri i).
Proof. by vm_compute. Qed.

(* RowFold.sgrmv at fsgri                                                     *)
Definition sgrmvO (u pty g : int) : int :=
  let i := Uint63.add (Uint63.mul (Uint63.add (Uint63.mul u 2) pty) ngroupi) g in
  if Uint63.lsr i 11 <? 315 then gt4 i else PArray.get fsgri i.

Lemma sgrmvOE u pty g : sgrmvO u pty g = sgrmv fsgri u pty g.
Proof.
rewrite /sgrmvO /sgrmv; cbv zeta; case: nltbP => h //.
set i := Uint63.add _ _ in h *.
have e : Uint63.lsr i 11 = i / 2048 by apply: lsrE.
have hn : to_nat 315 = 315%N by [].
rewrite e hn in h.
by move: (iter2_at fsgrchkT (erefl _) (erefl _) h) => /neqbP/to_nat_inj.
Qed.

(* RowFoldN.fmarknw at the folded tables, reading the packed fsgr            *)
Definition fmarknwO (mn : rmap * int) (pg gr bt : int) : rmap * int :=
  let: (m, n) := mn in
  let w := PArray.get fpgi pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12) then 0 else 1) in
  let r := fkpt w in
  let g := sgrmvO u pty gr in
  let v := bitof (fbit (fhlf w) (sbtmv fsbti u bt)) in
  let c := pchk r in
  let i := Uint63.add (poff r) g in
  let a := PArray.get m c in
  let old := PArray.get a i in
  let w' := Uint63.lor old v in
  if Uint63.eqb w' old then mn
  else (PArray.set m c (PArray.set a i w'),
        if Uint63.eqb (fhlf w) 0 then Uint63.add n (PArray.get forbi r) else n).

Lemma fmarknwOE mn pg gr bt :
  fmarknwO mn pg gr bt = fmarknw fpgi fsgri fsbti forbi mn pg gr bt.
Proof.
case: mn => m n; rewrite /fmarknwO /fmarknw; cbv beta iota zeta.
by rewrite sgrmvOE.
Qed.

(* ---- ifold at the searches' type ------------------------------------------- *)

(* RowMap.ifold with its type fixed, so no type argument is passed           *)
Fixpoint ifoldM (n : nat) (x : int) (f : int -> rmap * int -> rmap * int)
                (a : rmap * int) : rmap * int :=
  if n is n1.+1 then ifoldM n1 (Uint63.add x 1) f (f x a) else a.

Lemma ifoldME n x f a : ifoldM n x f a = ifold n x f a.
Proof. by elim: n x a => [|n ih] x a //=; rewrite ih. Qed.
