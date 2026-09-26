(* =========================================================================  *)
(*  RowMin.v -- the folded run's code with Stdlib only, and not one proof.    *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowFoldCubDefD's run needs mathcomp and  *)
(* the whole development loaded; this is the same code with nothing else, so *)
(* native_compute can be timed at its smallest footprint, beside its OCaml   *)
(* translation (ocaml/rubik_row_rocq.ml).                                    *)
(*                                                                            *)
(* EVERY BODY IS THE ORIGINAL'S, in the original's section, so each closed   *)
(* function takes the same arguments in the same order.  Only the syntax     *)
(* changes: match for `if .. is', negb for ~~, andb for &&, fst and snd for  *)
(* .1 and .2, and mathcomp's leq and eqn written out with their bodies.       *)
(* Each definition names the one it copies.                                   *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.

Set Implicit Arguments.
Unset Strict Implicit.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- mathcomp's nat ------------------------------------------------------ *)

(* ssrnat.eqn                                                                 *)
Fixpoint eqn (m n : nat) {struct m} : bool :=
  match m, n with
  | O, O => true
  | S m', S n' => eqn m' n'
  | _, _ => false
  end.

(* ssrnat.leq: m - n == 0, and subn is Nat.sub                               *)
Definition leq (m n : nat) : bool := eqn (Nat.sub m n) O.

(* ---- RowMap -------------------------------------------------------------- *)

(* RowMap.ifold                                                               *)
Fixpoint ifold (A : Type) (n : nat) (x : int) (f : int -> A -> A) (a : A) : A :=
  match n with
  | O => a
  | S n1 => ifold n1 (Uint63.add x 1) f (f x a)
  end.

(* RowRun.nmvn                                                                *)
Definition nmvn : nat := 18%nat.

(* Row.v, RowMap.v                                                            *)
Definition ngroupi : int := 20160.
Definition ngroupn : nat := 20160%nat.
Definition nbiti   : int := 24.
Definition nhi     : int := 10.
Definition nhn     : nat := 10%nat.
Definition lo12    : int := 4095.
Definition allbits24 : int := 16777215.

(* RowMap.bitof                                                               *)
Definition bitof (bt : int) : int := Uint63.lsl 1 bt.

(* ---- Row: a member and its place ----------------------------------------- *)

Definition memb := (int * int * int)%type.

Definition mcp (x : memb) : int := let '(c, _, _) := x in c.
Definition mud (x : memb) : int := let '(_, u, _) := x in u.
Definition mmp (x : memb) : int := let '(_, _, m) := x in m.

(* Row.place24                                                                *)
Definition place24 (e8num e4bit : arr) (x : memb) : int * int * int :=
  (mcp x,
   Uint63.div (PArray.get e8num (mud x)) 2,
   PArray.get e4bit (mmp x)).

(* ---- RowFold: the folded map --------------------------------------------- *)

Definition nrepi : int := 1496.
Definition nrepn : nat := 1496%nat.
Definition ppcshft : int := 6.
Definition ppcmask : int := 63.
Definition csizef  : int := 1290240.
Definition nchunkf : int := 24.
Definition nchunkn : nat := 24%nat.

(* RowFold.mkempty                                                            *)
Definition mkempty (u : unit) : rmap :=
  ifold nchunkn 0
    (fun c a => PArray.set a c (PArray.make csizef 0))
    (PArray.make nchunkf (PArray.make 1 0)).

(* RowFold.pchk, poff                                                         *)
Definition pchk (r : int) : int := Uint63.lsr r ppcshft.
Definition poff (r : int) : int :=
  Uint63.mul (Uint63.land r ppcmask) ngroupi.

(* RowFold.ffor                                                               *)
Definition ffor (m : rmap) (r g v : int) : rmap :=
  let c := pchk r in
  let i := Uint63.add (poff r) g in
  let a := PArray.get m c in
  let old := PArray.get a i in
  let w := Uint63.lor old v in
  if Uint63.eqb w old then m else PArray.set m c (PArray.set a i w).

Section PreF.

Variable fpg : arr.
Variable fsrc : arr.
Variable fsrc2 : arr.
Variable fful : arr.
Variable fsgr : arr.
Variable fslo fshi : arr.
Variable fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable forb fpop : arr.

(* RowFold: the four fields of a folded word                                  *)
Definition fpar (w : int) : int := Uint63.land w 1.
Definition fren (w : int) : int := Uint63.land (Uint63.lsr w 1) 15.
Definition fhlf (w : int) : int := Uint63.land (Uint63.lsr w 5) 1.
Definition fkpt (w : int) : int := Uint63.lsr w 6.

(* RowFold.fbit                                                               *)
Definition fbit (h b : int) : int :=
  if Uint63.eqb h 0 then b else Uint63.add nbiti b.

(* RowFold.sgrmv, slomv, shimv, sbtmv                                         *)
Definition sgrmv (u pty g : int) : int :=
  PArray.get fsgr
    (Uint63.add (Uint63.mul (Uint63.add (Uint63.mul u 2) pty) ngroupi) g).
Definition slomv (u v : int) : int :=
  PArray.get fslo (Uint63.add (Uint63.lsl u 12) v).
Definition shimv (u v : int) : int :=
  PArray.get fshi (Uint63.add (Uint63.lsl u 12) v).
Definition sbtmv (u bt : int) : int :=
  PArray.get fsbt (Uint63.add (Uint63.mul u nbiti) bt).

(* RowFold.fmark                                                              *)
Definition fmark (m : rmap) (pg gr bt : int) : rmap :=
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12) then 0 else 1) in
  ffor m (fkpt w) (sgrmv u pty gr) (bitof (fbit (fhlf w) (sbtmv u bt))).

(* RowFold.fmarkn                                                             *)
Definition fmarkn (mn : rmap * int) (pg gr bt : int) : rmap * int :=
  let '(m, n) := mn in
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12) then 0 else 1) in
  let r := fkpt w in
  let g := sgrmv u pty gr in
  let v := bitof (fbit (fhlf w) (sbtmv u bt)) in
  let c := pchk r in
  let i := Uint63.add (poff r) g in
  let a := PArray.get m c in
  let old := PArray.get a i in
  let w := Uint63.lor old v in
  if Uint63.eqb w old then mn
  else (PArray.set m c (PArray.set a i w), Uint63.add n 1).

(* RowFold.fofs                                                               *)
Definition fofs (dh o : int) : int :=
  if Uint63.eqb dh 0 then o else Uint63.add o nbiti.

(* RowFold.flevmvu                                                            *)
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

(* RowFold.flevmv                                                             *)
Definition flevmv (src : rmap) (r k doff : int) (a : arr) : arr :=
  let w := PArray.get fsrc (Uint63.add (Uint63.mul r nhi) k) in
  let w2 := PArray.get fsrc2 (Uint63.add (Uint63.mul r nhi) k) in
  let u0 := fren w in
  let h0 := fhlf w in
  let u1 := Uint63.lsr w2 1 in
  let h1 := Uint63.land w2 1 in
  let pc := fpar w in
  let p := fkpt w in
  let two := negb (Uint63.eqb (PArray.get fful r) allbits24) in
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

(* RowFold.flevpg                                                             *)
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

(* RowFold.flevel                                                             *)
Definition flevel (src : rmap) (dst : rmap) : rmap :=
  ifold nrepn 0 (fun r d => flevpg src r d) dst.

(* RowFold.fcount48                                                           *)
Definition fcount48 (m : rmap) : int :=
  ifold nrepn 0
    (fun r acc =>
       let orb := PArray.get forb r in
       let w := if Uint63.eqb (PArray.get fful r) allbits24
                then orb else Uint63.div orb 2 in
       let ca := PArray.get m (pchk r) in
       let co := poff r in
       ifold ngroupn 0
         (fun g b =>
            let v := PArray.get ca (Uint63.add co g) in
            if Uint63.eqb v 0 then b
            else
              Uint63.add b
                (Uint63.mul w
                   (Uint63.add
                      (Uint63.add
                         (PArray.get fpop (Uint63.land v lo12))
                         (PArray.get fpop
                            (Uint63.land (Uint63.lsr v 12) lo12)))
                      (Uint63.add
                         (PArray.get fpop
                            (Uint63.land (Uint63.lsr v nbiti) lo12))
                         (PArray.get fpop
                            (Uint63.land
                               (Uint63.lsr v (Uint63.add nbiti 12)) lo12))))))
         acc)
    0.

(* RowFold.fcount                                                             *)
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

(* RowFoldN.fmarknw                                                           *)
Definition fmarknw (fpg fsgr fsbt forb : arr) (mn : rmap * int)
                   (pg gr bt : int) : rmap * int :=
  let '(m, n) := mn in
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12) then 0 else 1) in
  let r := fkpt w in
  let g := sgrmv fsgr u pty gr in
  let v := bitof (fbit (fhlf w) (sbtmv fsbt u bt)) in
  let c := pchk r in
  let i := Uint63.add (poff r) g in
  let a := PArray.get m c in
  let old := PArray.get a i in
  let w' := Uint63.lor old v in
  if Uint63.eqb w' old then mn
  else (PArray.set m c (PArray.set a i w'),
        if Uint63.eqb (fhlf w) 0 then Uint63.add n (PArray.get forb r) else n).

(* ---- Phase1, Fold, RowMask: the folded phase one table ------------------- *)

(* Phase1                                                                     *)
Definition cwlogi : int := 21.
Definition cwmaski : int := 2097151.
Definition mbits  : int := 28.
Definition mper   : int := 2.
Definition mmaski : int := 268435455.
Definition nfsi    : int := 1013760.
Definition ntwisti : int := 2187.

Section P1.
Variable p1ftabs : PArray.array arr.

(* Phase1.p1getm                                                              *)
Definition p1getm (i : int) : int :=
  let w := Uint63.div i mper in
  let r := Uint63.sub i (Uint63.mul w mper) in
  let c := Uint63.lsr w cwlogi in
  let o := Uint63.land w cwmaski in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get p1ftabs c) o) (Uint63.mul r mbits))
    mmaski.
End P1.

(* Fold                                                                       *)
Definition nsymi   : int := 16.
Definition nwide   : int := 3.
Definition wbits   : int := 20.
Definition wmaski  : int := 1048575.
Definition nnarrow : int := 15.
Definition nbits   : int := 4.
Definition nmask4  : int := 15.

(* Fold.foldi                                                                 *)
Definition foldi (rep tw : int) : int :=
  Uint63.add (Uint63.mul rep ntwisti) tw.

(* Fold.get20, get4                                                           *)
Definition get20 (a : arr) (i : int) : int :=
  let w := Uint63.div i nwide in
  let j := Uint63.sub i (Uint63.mul w nwide) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j wbits)) wmaski.

Definition get4 (a : arr) (i : int) : int :=
  let w := Uint63.div i nnarrow in
  let j := Uint63.sub i (Uint63.mul w nnarrow) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j nbits)) nmask4.

(* RowMask                                                                    *)
Definition mdbits : int := 4.
Definition mdmask : int := 15.
Definition mfbits : int := 12.
Definition mfmask : int := 4095.
Definition msmask : int := 15.
Definition ndeci  : int := 4096.
Definition allmvi : int := 262143.

(* RowMask.Dfoldm                                                             *)
Definition Dfoldm (F : PArray.array arr) (frep fsym : int -> int)
    (twsym : int -> int -> int) (tw r : int) : int :=
  let y := fsym r in
  Uint63.lor (p1getm F (foldi (frep r) (twsym tw y)))
             (Uint63.lsl y mbits).

(* RowMask.mdist                                                              *)
Definition mdist (w : int) : int := Uint63.land w mdmask.

Section Decode.
Variable dnlo dnhi fllo flhi : arr.

(* RowMask.mmask                                                              *)
Definition mmask (w : int) (s : nat) : int :=
  if leq 2 s then allmvi
  else
    let b := Uint63.mul (Uint63.land (Uint63.lsr w mbits) msmask) ndeci in
    let c := Uint63.lsr w mdbits in
    let lo := Uint63.add b (Uint63.land c mfmask) in
    let hi := Uint63.add b (Uint63.land (Uint63.lsr c mfbits) mfmask) in
    match s with
    | S O => Uint63.lor (get20 fllo lo) (get20 flhi hi)
    | _ => Uint63.lor (get20 dnlo lo) (get20 dnhi hi)
    end.
End Decode.

(* ---- RowFoldSrch, RowFoldSrchI: the numbers ------------------------------ *)

(* RowFoldSrch.fp1g                                                           *)
Definition fp1g (F : PArray.array arr) (frep fsym : int -> int)
    (twsym : int -> int -> int) (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm F frep fsym twsym tw (Uint63.sub c (Uint63.mul tw nfsi)).

(* RowFoldSrch                                                                *)
Definition enoughb : int := 167000000.
Definition enoughd : int := 3.
Definition ncutb : int := 6000000.

(* RowFoldSrchI                                                               *)
Definition frcutii : int := 5.
Definition fsslack (s : int) : nat :=
  if (2 <=? s) then 2%nat else if (s =? 1) then 1%nat else 0%nat.

(* ---- RowFoldSrchI, RowFoldSrchIC: the stopping search --------------------- *)

Section FSrchI.

Variable e8num e4bit : arr.
Variable fpg fsgr fsbt : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation plc := (place24 e8num e4bit).
Local Notation fmkn := (fmarkn fpg fsgr fsbt).
Local Notation p1g := (fp1g F frep fsym twsym).
Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.
Variable ishm : int.

(* RowFoldSrchI.fsrchski                                                      *)
Fixpoint fsrchski (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                  (msk pv : int) (enough : int) (mn : rmap * int)
                  : rmap * int :=
  if Uint63.leb enough (snd mn) then mn
  else match togo with
  | S togo' =>
    let togoi' := Uint63.sub togoi 1 in
    ifold nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if negb (okmv pv k) then a
         else if (if cut
                  then (if eqn togo' O
                        then negb (Uint63.eqb (Uint63.land ishm
                                                 (Uint63.lsl 1 k)) 0)
                        else false)
                  else false)
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then fsrchski cut togo' togoi' c' (xstep x k)
                         (wmask w (fsslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  | O =>
    if csolved c
    then let '(pg, gr, bt) := plc (tomemb x) in fmkn mn pg gr bt
    else mn
  end.

End FSrchI.

Section FSrchIC.

Variable e8num e4bit : arr.
Variable fpg fsgr fsbt : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation p1g := (fp1g F frep fsym twsym).
Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.
Variable ishm : int.

Local Notation fsrski :=
  (fsrchski e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).

(* RowFoldSrchIC.isrchskL                                                     *)
Fixpoint isrchskL (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                  (msk pv : int) (enough : int) (mn : rmap * int)
                  : rmap * int :=
  if Uint63.leb enough (snd mn) then mn
  else match togo with
  | S togo' =>
    match togo' with
    | O =>
      ifold nmvn 0
        (fun k a =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
           else if negb (okmv pv k) then a
           else if andb cut
                  (negb (Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0))
           then a
           else fsrski cut 0 0 (cstep c k) (xstep x k) 0 k enough a)
        mn
    | _ =>
    let togoi' := Uint63.sub togoi 1 in
    ifold nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if negb (okmv pv k) then a
         else if (if cut
                  then (if eqn togo' O
                        then negb (Uint63.eqb (Uint63.land ishm
                                                 (Uint63.lsl 1 k)) 0)
                        else false)
                  else false)
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then isrchskL cut togo' togoi' c' (xstep x k)
                         (wmask w (fsslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
    end
  | O => fsrski cut 0 togoi c x msk pv enough mn
  end.

End FSrchIC.

(* ---- RowFoldN: the counting search, the level and the run ---------------- *)

Section FN.

Variable e8num e4bit : arr.
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation plc := (place24 e8num e4bit).
Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Local Notation p1g := (fp1g F frep fsym twsym).
Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

Variables forb fpop : arr.
Variable ishm : int.

Local Notation fmknw := (fmarknw fpg fsgr fsbt forb).
Local Notation isrskL :=
  (isrchskL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).

(* RowFoldN.wleaf                                                             *)
Definition wleaf (c : int) (x : pst) (a : rmap * int) : rmap * int :=
  if csolved c then let '(pg, gr, bt) := plc (tomemb x) in fmknw a pg gr bt
  else a.

(* RowFoldN.iwsrchL                                                           *)
Fixpoint iwsrchL (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                 (msk pv : int) (a : rmap * int) : rmap * int :=
  match togo with
  | S togo' =>
    match togo' with
    | O =>
      ifold nmvn 0
        (fun k a' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
           else if negb (okmv pv k) then a'
           else if andb cut
                  (negb (Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0))
           then a'
           else wleaf (cstep c k) (xstep x k) a')
        a
    | _ =>
    let togoi' := Uint63.sub togoi 1 in
    ifold nmvn 0
      (fun k a' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
         else if negb (okmv pv k) then a'
         else if (if cut
                  then (if eqn togo' O
                        then negb (Uint63.eqb (Uint63.land ishm
                                                 (Uint63.lsl 1 k)) 0)
                        else false)
                  else false)
         then a'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then iwsrchL cut togo' togoi' c' (xstep x k)
                        (wmask w (fsslack (Uint63.sub togoi' nd))) k a'
           else a')
      a
    end
  | O => wleaf c x a
  end.

(* RowFoldN.wslv                                                              *)
Definition wslv (cut : bool) (d : nat) (m' : rmap) (nb : int) : rmap * int :=
  if leq d dsrch then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (fsslack (Uint63.sub di (wdist w))) in
      if eqn d dsrch then
        let e := Uint63.add enoughb (Uint63.div nb enoughd) in
        isrskL cut d di croot sroot msk 18 e (m', nb)
      else iwsrchL cut d di croot sroot msk 18 (m', nb)
    else (m', nb)
  else (m', nb).

(* RowFoldN.wrun                                                              *)
Fixpoint wrun (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  match n with
  | S n1 =>
    if Uint63.ltb ncutb n0 then
      let m1 := flev m dst in
      let a := wslv true (S d) m1 (fcount forb fpop m1) in
      wrun n1 (S d) (snd a) (fst a) m
    else
      let a := wslv false (S d) m n0 in
      wrun n1 (S d) (snd a) (fst a) dst
  | O => m
  end.

End FN.
