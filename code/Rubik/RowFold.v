(* =========================================================================  *)
(*  RowFold.v -- a row, folded by the sixteen symmetries.                     *)
(* =========================================================================  *)

(* The map is 40320 pages, one for each corner permutation, of 20160 groups.  *)
(* The sixteen symmetries that fix the U/D axis send H to H and fix the       *)
(* superflip, so keeping one page of each orbit of sixteen is enough: fifteen *)
(* times less memory, and as much less work, one level being one pass over    *)
(* the map.                                                                   *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowPrep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- the folded map ------------------------------------------------------ *)

Definition nsymi : int := 16.               (* renamings that keep U/D        *)

(* A CELL IS A PAIR OF KEPT PAGES, and forty eight bits.  The pairing is the  *)
(* relabelling tau = (0 2)(1 3)(4 6)(5 7) of the corner cubies.  Relabelling  *)
(* commutes with permuting places, so every MOVE carries a tau pair to a tau  *)
(* pair; and tau is one of the three non trivial involutions that commute     *)
(* with all sixteen RENAMINGS, which is what `(0 1)' -- the plain map's       *)
(* pairing -- does not do.  Both facts are walked in the prototype,           *)
(* `./rubik_row_nofold central': nought of ten moves and nought of sixteen    *)
(* renamings break the pair.                                                  *)
(*                                                                            *)
(* TAU SENDS AN ORBIT TO AN ORBIT, so it pairs the kept pages -- but not all  *)
(* of them.  It fixes 224 of the 2768: those orbits already hold both a page  *)
(* and its partner, so the fold had identified them and the pairing adds      *)
(* nothing there.  The other 2544 pair off.  2544 / 2 + 224 = 1496 cells.     *)
(* THE 224 USE THE LOW HALF ONLY, which is why the map is not asked to be     *)
(* full of forty eight bits everywhere but of what `ffull' reads off a mask.  *)
Definition nrepi : int := 1496.             (* cells, of the 2768 kept pages  *)
Definition nrepn : nat := to_nat nrepi.

(* A half is Row's own twenty four bits and a cell its forty eight, so the    *)
(* arithmetic of a place inside a cell is the arithmetic the plain map        *)
(* already has: nbiti and nbit48i, and the lemmas that go with them.          *)

(* ---- A CHUNK HOLDS WHOLE PAGES ------------------------------------------- *)

(* RowMap.v cuts the map into chunks of two million words and finds a word by *)
(* splitting its number, which costs a shift, a mask AND A SECOND ARRAY READ  *)
(* at every single word: the chunk first, then the word inside it.            *)
(*                                                                            *)
(* Here a chunk holds sixty four kept pages exactly, so a page never straddles*)
(* two chunks.  The level then reads the chunk ONCE a page and walks inside   *)
(* it, and the second read is gone from the inner loop.  Sixty four is a      *)
(* power of two, so which chunk and where in it are a shift and a mask.       *)

Definition ppcshft : int := 6.                 (* 64 pages a chunk            *)
Definition ppcmask : int := 63.
Definition csizef  : int := 1290240.           (* 64 * 20160                  *)
Definition nchunkf : int := 24.                (* 1496 cells, 64 at a time    *)

(* EVERY CHUNK ITS OWN ARRAY.  `PArray.make nchunkf (PArray.make csizef 0)'   *)
(* runs the inner make ONCE and hands the same array to all forty four slots,  *)
(* so a write to any chunk chains a difference onto that one array -- and it   *)
(* is a global, which nothing ever collects.  Built chunk by chunk instead,    *)
(* each make is under a lambda and runs afresh.                               *)
Definition nchunkn : nat := 24.

Definition mkempty (u : unit) : rmap :=
  ifold nchunkn 0
    (fun c a => PArray.set a c (PArray.make csizef 0))
    (PArray.make nchunkf (PArray.make 1 0)).

(* NEVER START A RUN FROM THIS ONE.  A persistent array keeps its whole       *)
(* history behind any pointer that is still held, and a global is held for    *)
(* ever: every map written from memptyf would keep every difference ever made *)
(* to it alive.  Runs call mkempty tt, which nothing holds.  This one is for  *)
(* reading -- mfullf memptyf and the like -- and for nothing that writes.     *)
Definition memptyf : rmap := mkempty tt.

(* the chunk a kept page lives in, and where the page starts inside it        *)
Definition pchk (r : int) : int := Uint63.lsr r ppcshft.
Definition poff (r : int) : int :=
  Uint63.mul (Uint63.land r ppcmask) ngroupi.

(* one word, for the marking: the level does not go through these            *)
Definition fget (m : rmap) (r g : int) : int :=
  PArray.get (PArray.get m (pchk r)) (Uint63.add (poff r) g).

Definition fset (m : rmap) (r g v : int) : rmap :=
  let c := pchk r in
  PArray.set m c (PArray.set (PArray.get m c) (Uint63.add (poff r) g) v).

(* ONE READ OF THE CHUNK TABLE, ONE OF THE CHUNK, AND NO WRITE UNLESS THE     *)
(* WORD CHANGES.  This is RowMap's gor, at the folded map.  The search        *)
(* reaches the same member by many different words, so most of its marks were *)
(* setting a bit that was already set, and a persistent array keeps a small   *)
(* record of every write.  fmarkn -- the counting mark, used at the stopping  *)
(* level -- has had the test all along; fmark, used at every other level,     *)
(* had not.                                                                   *)
Definition ffor (m : rmap) (r g v : int) : rmap :=
  let c := pchk r in
  let i := Uint63.add (poff r) g in
  let a := PArray.get m c in
  let old := PArray.get a i in
  let w := Uint63.lor old v in
  if Uint63.eqb w old then m else PArray.set m c (PArray.set a i w).

(* THE MAP IS FULL WHEN EVERY CELL HAS THE BITS IT IS OWED, AND THAT IS NOT   *)
(* THE SAME NUMBER FOR EVERY CELL.  A cell holds a pair of kept pages and     *)
(* forty eight bits -- except the 224 cells whose two pages are the same      *)
(* page, which hold twenty four.  `fful' is that mask, one word a cell.  A    *)
(* cell asked for too few bits can only make the run finish early, never let  *)
(* a member through, so nothing here has to trust the mask.                   *)
Definition mfullf (fful : arr) (m : rmap) : bool :=
  iter nrepn 0
    (fun r =>
       let a := PArray.get m (pchk r) in
       let o := poff r in
       let w := PArray.get fful r in
       iter ngroupn 0
         (fun g => Uint63.eqb (PArray.get a (Uint63.add o g)) w)).

Section PreF.

(* ---- what the fold reads ------------------------------------------------- *)

(* fpg  : a page -- where it is kept, the renaming that folds it, its parity  *)
(* fsrc : a kept page and a move -- the kept page it gathers from, the        *)
(*        renaming to read that page through, and that page's parity          *)
(* fsgr : a renaming on a group, the two parities apart                       *)
(* fslo : a renaming on the twelve bits of the low half, fshi the high        *)
(* fsbt : a renaming on one of the twenty four bits                           *)
(*                                                                            *)
(* A PAGE AND ITS RENAMING ARE ONE NUMBER, and so are a source and its        *)
(* parity: the level reads one word where it would otherwise read three.      *)
Variable fpg : arr.                 (* 40320                                  *)
Variable fsrc : arr.                (* 1496 * 10                              *)

(* THE SECOND RENAMING.  A cell's half nought is gathered from the source     *)
(* cell's half h0 through u0, which fsrc carries; its half one from h1        *)
(* through u1, which this does.  The source CELL is the same for both -- so   *)
(* one read of the source word serves both halves -- but the two renamings    *)
(* need not be, and in 836 of the 14960 cell-and-move pairs they are not.     *)
Variable fsrc2 : arr.               (* 1496 * 10, u1 * 2 + h1                 *)

(* and the mask, which is also how the level knows whether a cell has a       *)
(* second half at all: NOTHING MAY BE WRITTEN OUTSIDE IT, since mfullf is an  *)
(* equality and a stray high bit would keep the map from ever being full.     *)
Variable fful : arr.                (* 1496                                   *)
Variable fsgr : arr.                (* 16 * 2 * 20160                         *)
Variable fslo fshi : arr.           (* 16 * 4096                              *)
Variable fsbt : arr.                (* 16 * 24                                *)

(* and what RowMap.v's level reads: the move on groups, halves and bits       *)
Variable mgr msw mlo mhi : arr.

(* forb : a kept page -- how many pages its orbit has                         *)
(* fpop : the bits of a half, counted                                         *)
Variable forb fpop : arr.           (* 2768, 4096                             *)

(* the four fields of a folded word.  fhlf is new: which half of its cell a   *)
(* page is, nought or one.                                                    *)
Definition fpar (w : int) : int := Uint63.land w 1.
Definition fren (w : int) : int := Uint63.land (Uint63.lsr w 1) 15.
Definition fhlf (w : int) : int := Uint63.land (Uint63.lsr w 5) 1.
Definition fkpt (w : int) : int := Uint63.lsr w 6.

(* WHERE A BIT SITS IN A CELL: the half, then the bit inside it.  A TEST AND  *)
(* AN ADD, not a multiplication -- there are only two halves, so there is     *)
(* nothing to multiply by.                                                    *)
Definition fbit (h b : int) : int :=
  if Uint63.eqb h 0 then b else Uint63.add nbiti b.

(* AND IT IS THE PLAIN MAP'S PLACE, written as a test.  There are two halves, *)
(* so there is nothing to multiply by; but saying so lets every lemma Row.v   *)
(* proves about `24 * h + b' be read here.                                    *)
Lemma fbitE h b : (to_nat h < 2)%N ->
  fbit h b = Uint63.add (Uint63.mul h nbiti) b.
Proof.
move=> hh; rewrite /fbit; case: (int_lt2 hh) => ->.
  by rewrite eqb_refl RowPrep.mul0_nbiti ladd0n.
by rewrite RowPrep.mul1_nbiti; have -> : (1 =? 0)%uint63 = false by vm_compute.
Qed.

(* the half is one bit, so it is nought or one                                *)
Lemma fhlf_lt2 w : (to_nat (fhlf w) < 2)%N.
Proof.
rewrite /fhlf landC.
have -> : (2 = 2 ^ 1)%N by [].
by apply: to_nat_land_bound; rewrite to_nat_1.
Qed.

(* a place in a cell is a place in a cell                                     *)
Lemma fbit_lt h b : (to_nat h < 2)%N -> (b <? nbiti)%uint63 ->
  (fbit h b <? nbit48i)%uint63.
Proof.
move=> hh hb; rewrite fbitE //; apply: bit48_lt => //; exact/nltbP.
Qed.

(* AND IT SAYS BOTH THINGS: which half, and which bit of it.  The two halves  *)
(* are the numbers below twenty four and those from twenty four up, and       *)
(* nothing is in both -- so two places that agree agree on the half and on    *)
(* the bit.  It is Row's own division, read through fbitE.                    *)
Lemma fbit_inj h1 b1 h2 b2 : (to_nat h1 < 2)%N -> (to_nat h2 < 2)%N ->
  (b1 <? nbiti)%uint63 -> (b2 <? nbiti)%uint63 ->
  fbit h1 b1 = fbit h2 b2 -> h1 = h2 /\ b1 = b2.
Proof.
move=> hh1 hh2 hb1 hb2.
have hn1 : (to_nat b1 < to_nat nbiti)%N by apply/nltbP.
have hn2 : (to_nat b2 < to_nat nbiti)%N by apply/nltbP.
rewrite !fbitE // => he; split.
  by rewrite -(div_mulD hn1 (bit48_bound hh1 hn1)) he
             (div_mulD hn2 (bit48_bound hh2 hn2)).
by rewrite -(mod_mulD hn1 (bit48_bound hh1 hn1)) he
           (mod_mulD hn2 (bit48_bound hh2 hn2)).
Qed.

(* ---- and a word ored into one half is read only in that half ------------- *)

(* The level takes a twenty four bit word and ors it into one half of a cell. *)
(* A member that reads a bit of what it wrote therefore reads THAT half -- no *)
(* bit is in both -- and reads it at the bit the word had before the shift.   *)
(* twenty four plus a bit is a place, and nothing wraps.  NWB IS NEVER LEFT   *)
(* TO THE UNIFIER: it is two to the sixty third and a nat is unary, so the    *)
(* bound is reached through ltn_nwB at a small power and never by evaluating. *)
Lemma to_nat_nbiti_add i : (i <? nbiti)%uint63 ->
  to_nat (Uint63.add nbiti i) = (to_nat nbiti + to_nat i)%N.
Proof.
move=> hi.
have hin : (to_nat i < to_nat nbiti)%N by apply/nltbP.
have hsum : (to_nat nbiti + to_nat i < nwB)%N.
  move: hin; rewrite nbitiE => hi24.
  apply: (@ltn_nwB 6); first by vm_compute.
  have -> : (2 ^ 6 = 24 + 40)%N by [].
  by rewrite ltn_add2l; apply: leq_trans hi24 _.
by rewrite to_nat_add // addnC.
Qed.

(* ---- and reading one half of a cell is reading the cell at that half ----- *)

(* The level reads the half of a source cell the page names, masked back down *)
(* to twenty four bits.  A bit of what it read is the cell's own bit, at the  *)
(* place that half puts it.                                                   *)
Lemma bit_fhalf v sh i : (to_nat sh < 2)%N -> (i <? nbiti)%uint63 ->
  bit (if Uint63.eqb sh 0 then Uint63.land v allbits24
       else Uint63.land (Uint63.lsr v nbiti) allbits24) i
  = bit v (fbit sh i).
Proof.
move=> hs hi.
have h10 : (1 =? 0)%uint63 = false by vm_compute.
have h00 : (0 =? 0)%uint63 = true by vm_compute.
have hin : (to_nat i < to_nat nbiti)%N by apply/nltbP.
have h1L : (to_nat 1%uint63 < 2)%N by rewrite to_nat_1.
case: (int_lt2 hs) => -> ; rewrite /fbit ?h00 ?h10.
  by rewrite bit_lo24.
have h48 : (Uint63.add nbiti i <? nbit48i)%uint63.
  by have := fbit_lt h1L hi; rewrite /fbit h10.
have hadd := to_nat_nbiti_add hi.
have hle : (nbiti <=? Uint63.add nbiti i)%uint63 by apply/nlebP; rewrite hadd leq_addr.
have hsub : Uint63.sub (Uint63.add nbiti i) nbiti = i.
  apply: to_nat_inj; rewrite to_nat_sub ?hadd ?addKn //.
  by rewrite -hadd; apply: to_nat_bounded.
by rewrite -{1}hsub (bit_hi24 v hle h48).
Qed.

Lemma fbit_half w dh h j :
  (w <? Uint63.lsl one nbiti)%uint63 ->
  (to_nat dh < 2)%N -> (to_nat h < 2)%N -> (j <? nbiti)%uint63 ->
  ~~ (Uint63.land (if Uint63.eqb h 0 then w else Uint63.lsl w nbiti)
        (bitof (fbit dh j)) =? 0)%uint63 ->
  dh = h /\ ~~ (Uint63.land w (bitof j) =? 0)%uint63.
Proof.
move=> hw hdh hh hj.
have h10 : (1 =? 0)%uint63 = false by vm_compute.
have h00 : (0 =? 0)%uint63 = true by vm_compute.
have hnd : (to_nat nbiti < ndigits)%N by rewrite nbitiE /ndigits; vm_compute.
have hjn : (to_nat j < to_nat nbiti)%N by apply/nltbP.
(* THE EXPONENT STAYS SYMBOLIC.  Two to the twenty fourth is sixteen million  *)
(* and a nat is unary, so it must never be evaluated: nbitiE is used on the   *)
(* small ends of the arithmetic and nowhere else.                             *)
have hwn : (to_nat w < 2 ^ to_nat nbiti)%N.
  by rewrite -(to_nat_lsl_one nbiti hnd); apply/nltbP.
have hadd := to_nat_nbiti_add hj.
have hjd := lt_digits24 hj.
have hfd : (fbit dh j <? digits)%uint63 by apply: lt_digits; apply: fbit_lt.
rewrite (test_bit _ hfd) /fbit.
case: (int_lt2 hdh) => -> ; rewrite ?h00 ?h10.
- (* the destination bit is in the low half *)
  case: (int_lt2 hh) => -> ; rewrite ?h00 ?h10.
    by move=> hb; split=> //; rewrite (test_bit _ hjd).
  by rewrite bit_lsl hj.
(* and here it is in the high half *)
case: (int_lt2 hh) => -> ; rewrite ?h00 ?h10; last first.
  rewrite bit_lsl.
  have -> : (Uint63.add nbiti j <? nbiti)%uint63 = false.
    by apply/negbTE; apply/negP => /nltbP; rewrite hadd ltnNge leq_addr.
  have -> : (digits <=? Uint63.add nbiti j)%uint63 = false.
    apply/negbTE; apply/negP => /nlebP; rewrite hadd nbitiE => hle.
    have h63 : to_nat digits = 63%N by vm_compute.
    move: hle; rewrite h63 => hle63.
    have : (to_nat j < 24)%N by move: hjn; rewrite nbitiE.
    by move=> hj24; move: hle63; rewrite ltnNge => /negP[]; rewrite -ltnS;
       apply: leq_ltn_trans (leq_add (leqnn 24) (ltnW hj24)) _.
  have -> : Uint63.sub (Uint63.add nbiti j) nbiti = j.
    apply: to_nat_inj; rewrite to_nat_sub ?hadd ?addKn //.
    by rewrite -hadd; apply: to_nat_bounded.
  by move=> hb; split=> //; rewrite (test_bit _ hjd).
by rewrite (@bit_false_lt _ (to_nat nbiti) _ _ hwn) // hadd leq_addr.
Qed.


Definition sgrmv (u pty g : int) : int :=
  PArray.get fsgr
    (Uint63.add (Uint63.mul (Uint63.add (Uint63.mul u 2) pty) ngroupi) g).

Definition slomv (u v : int) : int :=
  PArray.get fslo (Uint63.add (Uint63.lsl u 12) v).
Definition shimv (u v : int) : int :=
  PArray.get fshi (Uint63.add (Uint63.lsl u 12) v).

Definition sbtmv (u bt : int) : int :=
  PArray.get fsbt (Uint63.add (Uint63.mul u nbiti) bt).

(* ---- where a member stands ----------------------------------------------- *)

(* The page is folded to the kept page of its orbit and the renaming that      *)
(* folds it is played on the rest of the member.  WHICH PARITY THE GROUP IS    *)
(* READ AT is the page's parity turned over by the bit's: the low half of a    *)
(* word is the even middle permutations and the high half the odd ones.        *)
Definition fmark (m : rmap) (pg gr bt : int) : rmap :=
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12)%uint63 then 0 else 1) in
  ffor m (fkpt w) (sgrmv u pty gr) (bitof (fbit (fhlf w) (sbtmv u bt))).

(* THE SAME MARK, AND A COUNT OF WHAT IT PUTS IN.  The early stop has to know *)
(* how full the map is, and a bit already set is not new.  It also does not   *)
(* write a word that is already right, which is what flevelg does for the     *)
(* level.                                                                    *)
Definition fmarkn (mn : rmap * int) (pg gr bt : int) : rmap * int :=
  let: (m, n) := mn in
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12)%uint63 then 0 else 1) in
  let r := fkpt w in
  let g := sgrmv u pty gr in
  let v := bitof (fbit (fhlf w) (sbtmv u bt)) in
  let c := pchk r in
  let i := Uint63.add (poff r) g in
  let a := PArray.get m c in
  let old := PArray.get a i in
  let w := Uint63.lor old v in
  if Uint63.eqb w old then mn
  else (PArray.set m c (PArray.set a i w), Uint63.add n 1%uint63).

Definition ftest (m : rmap) (pg gr bt : int) : bool :=
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12)%uint63 then 0 else 1) in
  negb (Uint63.eqb
          (Uint63.land (fget m (fkpt w) (sgrmv u pty gr))
                       (bitof (fbit (fhlf w) (sbtmv u bt)))) 0).

(* ---- one level ----------------------------------------------------------- *)

(* THE DESTINATION IS A MAP OF ITS OWN, which is the prototype's blit: the    *)
(* level reads the map of the last level and writes the map of this one, and  *)
(* no array is read that is also being written.                               *)
(*                                                                            *)
(* A KEPT PAGE IS FILLED IN ONE GO.  Every write this level makes to a page   *)
(* is made here, so the page's chunk is read ONCE, the carry and the ten      *)
(* moves are poured into it, and it is put back once.  The inner loop then    *)
(* holds one array and reaches a word by adding, where RowMap.v's level reads *)
(* the chunk again at every word.                                             *)
(*                                                                            *)
(* The low half of a word and the high half are two outer edge permutations   *)
(* that a renaming sends to two different pairs, so the two halves go to two  *)
(* different words.  Each is twelve bits moved as a block, twice: once for    *)
(* the renaming and once for the move.                                        *)

(* one move of H, gathered into the page being filled                         *)
(* where a twelve bit field lands: the offset inside a half, and twenty four  *)
(* more when it is the high half.  A TEST, NOT A MULTIPLICATION.              *)
Definition fofs (dh o : int) : int :=
  if Uint63.eqb dh 0 then o else Uint63.add o nbiti.

(* one half of a cell, moved, WRITING WHATEVER IT IS HANDED.  flevmvh below   *)
(* is this with the test that skips a write which changes nothing; the two    *)
(* are kept side by side so the guard can be priced.                          *)
Definition flevmvu (mgr fsgr' : arr) (v dh doff glo ghi ub kb k : int)
                   (sw : bool) (b : arr) : arr :=
  if Uint63.eqb v 0 then b
  else
    let lo := Uint63.land v lo12 in
    let hi := Uint63.land (Uint63.lsr v 12) lo12 in
    let b1 :=
      if Uint63.eqb lo 0 then b
      else
        let l := PArray.get mlo
                   (Uint63.add kb (PArray.get fslo (Uint63.add ub lo))) in
        let j := Uint63.add doff
                   (PArray.get mgr
                      (Uint63.add
                         (Uint63.mul
                            (PArray.get fsgr' glo) nhi) k)) in
        PArray.set b j
          (Uint63.lor (PArray.get b j)
             (Uint63.lsl l (fofs dh (if sw then 0 else 12)))) in
    if Uint63.eqb hi 0 then b1
    else
      let h := PArray.get mhi
                 (Uint63.add kb (PArray.get fshi (Uint63.add ub hi))) in
      let j := Uint63.add doff
                 (PArray.get mgr
                    (Uint63.add
                       (Uint63.mul
                          (PArray.get fsgr' ghi) nhi) k)) in
      PArray.set b1 j
        (Uint63.lor (PArray.get b1 j)
           (Uint63.lsl h (fofs dh (if sw then 12 else 0)))).

Definition flevmv (src : rmap) (r k doff : int) (a : arr) : arr :=
  let w := PArray.get fsrc (Uint63.add (Uint63.mul r nhi) k) in
  let w2 := PArray.get fsrc2 (Uint63.add (Uint63.mul r nhi) k) in
  let u0 := fren w in
  let h0 := fhlf w in
  let u1 := Uint63.lsr w2 1 in
  let h1 := Uint63.land w2 1 in
  let pc := fpar w in
  let p := fkpt w in
  let two := ~~ Uint63.eqb (PArray.get fful r) allbits24 in
  let sa := PArray.get src (pchk p) in
  let soff := poff p in
  let gl u := Uint63.mul (Uint63.add (Uint63.mul u 2) pc) ngroupi in
  let gh u :=
    Uint63.mul (Uint63.add (Uint63.mul u 2) (Uint63.sub 1 pc)) ngroupi in
  let kb := Uint63.lsl k 12 in
  let sw := Uint63.eqb (PArray.get msw k) 0 in
  ifold ngroupn 0
    (fun g b =>
       let v := PArray.get sa (Uint63.add soff g) in
       if Uint63.eqb v 0 then b
       else
         let vof h :=
           if Uint63.eqb h 0 then Uint63.land v allbits24
           else Uint63.land (Uint63.lsr v nbiti) allbits24 in
         let b0 :=
           flevmvu mgr fsgr (vof h0) 0 doff
             (Uint63.add (gl u0) g) (Uint63.add (gh u0) g)
             (Uint63.lsl u0 12) kb k sw b in
         if two then
           flevmvu mgr fsgr (vof h1) 1 doff
             (Uint63.add (gl u1) g) (Uint63.add (gh u1) g)
             (Uint63.lsl u1 12) kb k sw b0
         else b0)
    a.

(* one kept page: the carry, then the ten moves, then the chunk put back      *)
(* THE CARRY OVERWRITES.  The destination is a map of two levels ago, so its  *)
(* words are stale and every one of them is written, nought or not.  That is  *)
(* what lets the two maps be reused instead of a new one being made a level:  *)
(* a map made a level is 454 MB, and the old ones are held long enough to     *)
(* pile up.                                                                   *)
Definition flevpg (src : rmap) (r : int) (d : rmap) : rmap :=
  let c := pchk r in
  let doff := poff r in
  let sa := PArray.get src c in
  let a0 := PArray.get d c in
  let a1 :=
    ifold ngroupn 0
      (fun g b =>
         let j := Uint63.add doff g in
         PArray.set b j (PArray.get sa j))
      a0 in
  let a2 := ifold nhn 0 (fun k b => flevmv src r k doff b) a1 in
  PArray.set d c a2.

(* THE TWO MAPS ARE HANDED IN AND HANDED BACK.  Nothing is allocated a level: *)
(* the level reads one and fills the other, and the caller swaps them.        *)
Definition flevel (src : rmap) (dst : rmap) : rmap :=
  ifold nrepn 0 (fun r d => flevpg src r d) dst.

(* ---- the same level, but never writing a word that is already right ----- *)

(* PArray.set allocates a difference whatever it is handed, and the old
   version chains forward through every one of them: on a sparse map nearly
   every word of a level is nought written over nought, 613 million of them,
   and they are all reachable until the level returns.  Filliatre's own
   persistent array tests for an equal value and skips; Rocq's does not, so
   it is tested here.  Same answers, and nothing allocated for a word that
   does not change.

   flevel above is left exactly as it was, so the two can be run side by
   side. *)

(* one move of H, gathered into the cell being filled                         *)

(* A CELL IS TWO KEPT PAGES AND FOUR TWELVE BIT FIELDS.  The twenty four bit  *)
(* work below is exactly what it was -- the renaming on a half, then the      *)
(* move -- and it is run once for each half of the source word.  The two      *)
(* differ in ONE thing: where the answer lands.  Which half of the            *)
(* destination a source half goes to is fixed for the cell and the move, and  *)
(* `fswp' is that bit, read off the same word as the source.                  *)
(*                                                                            *)
(* AND THE PARITY IS SHARED.  tau is even -- four transpositions -- so the    *)
(* two pages of a cell have the SAME corner parity, and `glo' and `ghi', the  *)
(* two parity tables the group is read at, are the same for both halves.      *)
(* With an odd pairing they would not be, and this would be twice the work.   *)

Definition flevmvh (mgr fsgr' : arr) (v dh doff glo ghi ub kb k : int)
                   (sw : bool) (b : arr) : arr :=
  if Uint63.eqb v 0 then b
  else
    let lo := Uint63.land v lo12 in
    let hi := Uint63.land (Uint63.lsr v 12) lo12 in
    let b1 :=
      if Uint63.eqb lo 0 then b
      else
        let l := PArray.get mlo
                   (Uint63.add kb (PArray.get fslo (Uint63.add ub lo))) in
        let j := Uint63.add doff
                   (PArray.get mgr
                      (Uint63.add
                         (Uint63.mul
                            (PArray.get fsgr' glo) nhi) k)) in
        let w := PArray.get b j in
        let w' := Uint63.lor w
                    (Uint63.lsl l (fofs dh (if sw then 0 else 12))) in
        if Uint63.eqb w w' then b else PArray.set b j w' in
    if Uint63.eqb hi 0 then b1
    else
      let h := PArray.get mhi
                 (Uint63.add kb (PArray.get fshi (Uint63.add ub hi))) in
      let j := Uint63.add doff
                 (PArray.get mgr
                    (Uint63.add
                       (Uint63.mul
                          (PArray.get fsgr' ghi) nhi) k)) in
      let w := PArray.get b1 j in
      let w' := Uint63.lor w
                  (Uint63.lsl h (fofs dh (if sw then 12 else 0))) in
      if Uint63.eqb w w' then b1 else PArray.set b1 j w'.

Definition flevmvg (src : rmap) (r k doff : int) (a : arr) : arr :=
  let w := PArray.get fsrc (Uint63.add (Uint63.mul r nhi) k) in
  let w2 := PArray.get fsrc2 (Uint63.add (Uint63.mul r nhi) k) in
  let u0 := fren w in
  let h0 := fhlf w in
  let u1 := Uint63.lsr w2 1 in
  let h1 := Uint63.land w2 1 in
  let pc := fpar w in
  let p := fkpt w in
  let two := ~~ Uint63.eqb (PArray.get fful r) allbits24 in
  let sa := PArray.get src (pchk p) in
  let soff := poff p in
  let gl u := Uint63.mul (Uint63.add (Uint63.mul u 2) pc) ngroupi in
  let gh u :=
    Uint63.mul (Uint63.add (Uint63.mul u 2) (Uint63.sub 1 pc)) ngroupi in
  let kb := Uint63.lsl k 12 in
  let sw := Uint63.eqb (PArray.get msw k) 0 in
  ifold ngroupn 0
    (fun g b =>
       let v := PArray.get sa (Uint63.add soff g) in
       if Uint63.eqb v 0 then b
       else
         (* the source half a destination half reads: a test, not a shift by  *)
         (* a computed amount                                                 *)
         let vof h :=
           if Uint63.eqb h 0 then Uint63.land v allbits24
           else Uint63.land (Uint63.lsr v nbiti) allbits24 in
         let b0 :=
           flevmvh mgr fsgr (vof h0) 0 doff
             (Uint63.add (gl u0) g) (Uint63.add (gh u0) g)
             (Uint63.lsl u0 12) kb k sw b in
         if two then
           flevmvh mgr fsgr (vof h1) 1 doff
             (Uint63.add (gl u1) g) (Uint63.add (gh u1) g)
             (Uint63.lsl u1 12) kb k sw b0
         else b0)
    a.

(* one kept page: the carry, then the ten moves, then the chunk put back      *)
(* THE CARRY OVERWRITES.  The destination is a map of two levels ago, so its  *)
(* words are stale and every one of them is written, nought or not.  That is  *)
(* what lets the two maps be reused instead of a new one being made a level:  *)
(* a map made a level is 454 MB, and the old ones are held long enough to     *)
(* pile up.                                                                   *)
Definition flevpgg (src : rmap) (r : int) (d : rmap) : rmap :=
  let c := pchk r in
  let doff := poff r in
  let sa := PArray.get src c in
  let a0 := PArray.get d c in
  (* NEVER WRITE A WORD THAT IS ALREADY RIGHT.  PArray.set allocates a
     difference whatever it is handed, and on a sparse map nearly every word
     of the carry is nought over nought: 613 million writes a level, all of
     them kept until the map dies.  Filliatre's own persistent array tests
     this and skips; Rocq's does not, so it is tested here. *)
  let a1 :=
    ifold ngroupn 0
      (fun g b =>
         let j := Uint63.add doff g in
         let v := PArray.get sa j in
         if Uint63.eqb (PArray.get b j) v then b else PArray.set b j v)
      a0 in
  let a2 := ifold nhn 0 (fun k b => flevmvg src r k doff b) a1 in
  PArray.set d c a2.

(* THE TWO MAPS ARE HANDED IN AND HANDED BACK.  Nothing is allocated a level: *)
(* the level reads one and fills the other, and the caller swaps them.        *)
Definition flevelg (src : rmap) (dst : rmap) : rmap :=
  ifold nrepn 0 (fun r d => flevpgg src r d) dst.

(* n levels, the two maps swapping at each one                                *)
Fixpoint flevn (n : nat) (m d : rmap) : rmap :=
  if n is n1.+1 then flevn n1 (flevel m d) m else m.

Fixpoint flevng (n : nat) (m d : rmap) : rmap :=
  if n is n1.+1 then flevng n1 (flevelg m d) m else m.

(* ---- the members, counted ------------------------------------------------ *)

(* NOT PART OF THE ROW, which only ever asks whether the map is full.  This   *)
(* is what the prototype's own numbers can be compared with, level by level:  *)
(* a bit of a kept page stands for as many members as its orbit has pages.    *)
Definition fcount (m : rmap) : int :=
  ifold nrepn 0
    (fun r acc =>
       let orb := PArray.get forb r in
       let ca := PArray.get m (pchk r) in
       let co := poff r in
       ifold ngroupn 0
         (fun g b =>
            let v := PArray.get ca (Uint63.add co g) in
            if Uint63.eqb v 0 then b
            else
              Uint63.add b
                (Uint63.mul orb
                   (Uint63.add (PArray.get fpop (Uint63.land v lo12))
                      (PArray.get fpop
                         (Uint63.land (Uint63.lsr v 12) lo12)))))
         acc)
    0.

End PreF.
