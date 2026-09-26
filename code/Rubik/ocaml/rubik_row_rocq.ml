(* =========================================================================
   rubik_row_rocq.ml -- the Rocq plain run, RowCubDefD.rowmappiD, written
   out again in OCaml, to see where its time goes.

   FAITHFUL, NOT FAST.  Nothing is improved here; it is a reference.
     - an int of Rocq (Uint63) is an OCaml int
     - a nat is the unary type below, and every ifold counts one down
     - a PArray is Rocq's own, kernel/parray.ml of 9.1.1, copied below
     - a pair is a pair, and a triple is a pair of a pair
     - ~~, || and && are functions, so both sides are evaluated, as
       native_compute evaluates them
     - a section's variables are arguments: the search calls cstep, xstep,
       okmv, tomemb and csolved through closures
     - the GC is set as rocq sets its own (sysinit/coqinit.ml)
   Each function names the Rocq definition it copies.

   The tables are read from the same .v files Rocq loads.  Those Rocq builds
   by computation (ctab, etab, e8rT ...) are built by the same computation.
   Four values come from RowTransConsts.v, run under Rocq.  None of the
   building is timed.

   usage: rubik_row_rocq plain|fold DIR GEN CONSTS [n]
     DIR     code/Rubik, for the tables in the repo
     GEN     where p1gen wrote the generated ones, looked in first
     CONSTS  what `rocq compile RowTransConsts.v' prints
     n       the depth, 13 by default: mcount (rowmappiD n) or
             fcount48 (rowmapiD n), as RowBenchCountN.v and
             RowBenchCountF.v time them
   ========================================================================= *)

(* ---- Rocq's persistent arrays: kernel/parray.ml, 9.1.1 ------------------- *)

(* Copied as it is, with Uint63 the kernel's own compare on 63 bits. *)
module Uint63 = struct
  let zero = 0
  let of_int x = x
  let to_int2 x = (0, x)
  let lt (x : int) (y : int) =
    (x lxor 0x4000000000000000) < (y lxor 0x4000000000000000)
  let le (x : int) (y : int) =
    (x lxor 0x4000000000000000) <= (y lxor 0x4000000000000000)
end

module Parray = struct
  module UArray :
  sig
    type 'a t
    val unsafe_get : 'a t -> int -> 'a
    val unsafe_set : 'a t -> int -> 'a -> unit
    val length : 'a t -> int
    val make : int -> 'a -> 'a t
    val of_array : 'a array -> 'a t
  end =
  struct
    type 'a t = Obj.t array
    let length (v : 'a t) = Array.length v
    let of_array v =
      if (Obj.tag (Obj.repr v) == Obj.double_array_tag) then begin
        let n = Array.length v in
        let ans = Array.make n (Obj.repr ()) in
        for i = 0 to n - 1 do
          Array.unsafe_set ans i (Obj.repr (Array.unsafe_get v i))
        done;
        ans
      end else
        (Obj.magic (Array.copy v))
    let unsafe_get = Obj.magic Array.unsafe_get
    let unsafe_set = Obj.magic Array.unsafe_set
    let make (type a) n (x : a) : a t =
      let ans = Array.make n (Obj.repr ()) in
      let () = Array.fill ans 0 n (Obj.repr x) in
      ans
  end

  let max_array_length32 = 4194303

  let length_to_int i = snd (Uint63.to_int2 i)

  let trunc_size n =
    if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int max_array_length32)
    then length_to_int n
    else max_array_length32

  type 'a t = ('a kind) ref
  and 'a kind =
    | Array of 'a UArray.t * 'a
    | Updated of int * 'a * 'a t

  let of_array t def = ref (Array (UArray.of_array t, def))

  let rec rerootk t k =
    match !t with
    | Array (a, _) -> k a
    | Updated (i, v, p) ->
        let k' a =
          let v' = UArray.unsafe_get a i in
          UArray.unsafe_set a i v;
          t := !p;
          p := Updated (i, v', t);
          k a in
        rerootk p k'

  let reroot t = rerootk t (fun a -> a)

  let length_int p = UArray.length (reroot p)

  let length p = Uint63.of_int @@ length_int p

  let get p n =
    let t = reroot p in
    let l = UArray.length t in
    if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l) then
      UArray.unsafe_get t (length_to_int n)
    else
      match !p with
      | Array (_, def) -> def
      | Updated _ -> assert false

  let set p n e =
    let a = reroot p in
    let l = Uint63.of_int (UArray.length a) in
    if Uint63.le Uint63.zero n && Uint63.lt n l then
      let i = length_to_int n in
      let v' = UArray.unsafe_get a i in
      UArray.unsafe_set a i e;
      let t = ref !p in
      p := Updated (i, v', t);
      t
    else p

  let make_int n def = ref (Array (UArray.make n def, def))

  let make n def = make_int (trunc_size n) def
end

type arr = int Parray.t
type rmap = arr Parray.t

(* ---- nat, and mathcomp's arithmetic on it -------------------------------- *)

type nat = O | S of nat

(* building a nat, for the constants; never inside the run *)
let nat_of_int n =
  let rec go k acc = if k = 0 then acc else go (k - 1) (S acc) in go n O

(* Nat.sub, which is mathcomp's subn *)
let rec subn m n = match m, n with S k, S l -> subn k l | _, _ -> m

(* mathcomp's eqn *)
let rec eqn m n =
  match m, n with O, O -> true | S m', S n' -> eqn m' n' | _, _ -> false

(* mathcomp's leq: m - n == 0 *)
let leq m n = eqn (subn m n) O

(* Uint63.of_nat, read as a count *)
let rec of_nat n = match n with O -> 0 | S n' -> of_nat n' + 1

(* the boolean functions, strict in both arguments *)
let negb b = if b then false else true
let orb a b = if a then true else b
let andb a b = if a then b else false

(* ---- RowMap: the walk, the map ------------------------------------------- *)

(* RowMap.ifold *)
let rec ifold : 'a. nat -> int -> (int -> 'a -> 'a) -> 'a -> 'a =
  fun n x f a -> match n with O -> a | S n1 -> ifold n1 (x + 1) f (f x a)

let ngroupi = 20160                     (* Row.v *)
let nclsi = 20160
let nbiti = 24
let npagei = 40320
let nclsn = nat_of_int nclsi            (* Row.v: to_nat nclsi *)
let ngroupn = nat_of_int ngroupi

let cshft = 21
let cmskw = 2097151
let csize = 2097152
let nchunk = 194
let nchunkn = nat_of_int 194

(* RowMap.gget *)
let gget (m : rmap) g =
  Parray.get (Parray.get m (g lsr cshft)) (g land cmskw)

(* RowMap.gor *)
let gor (m : rmap) g v =
  let c = g lsr cshft in
  let i = g land cmskw in
  let a = Parray.get m c in
  let old = Parray.get a i in
  let w = old lor v in
  if w = old then m else Parray.set m c (Parray.set a i w)

(* RowMap.mkempty *)
let mkempty () : rmap =
  ifold nchunkn 0
    (fun c a -> Parray.set a c (Parray.make csize 0))
    (Parray.make nchunk (Parray.make 1 0))

(* RowMap.grpof, bitof *)
let grpof pg gr = pg * ngroupi + gr
let bitof bt = 1 lsl bt

(* RowMap: the moves of H on the map *)
let nhi = 10
let nhn = nat_of_int 10
let pgmv cpg k pg = Parray.get cpg (pg * nhi + k)
let grmv mgr k gr = Parray.get mgr (gr * nhi + k)
let lomv mlo k v = Parray.get mlo ((k lsl 12) + v)
let himv mhi k v = Parray.get mhi ((k lsl 12) + v)
let lo12 = 4095
let allbits24 = 16777215

(* RowMap.grpmv24 *)
let grpmv24 msw mlo mhi k v =
  let l = lomv mlo k (v land lo12) in
  let h = himv mhi k ((v lsr 12) land lo12) in
  if Parray.get msw k = 0
  then l lor (h lsl 12)
  else h lor (l lsl 12)

(* RowMap.grpmv *)
let grpmv cfl msw mlo mhi k v =
  let a = (grpmv24 msw mlo mhi k (v land allbits24)) land allbits24 in
  let b = (grpmv24 msw mlo mhi k ((v lsr nbiti) land allbits24))
          land allbits24 in
  if Parray.get cfl k = 0
  then a lor (b lsl nbiti)
  else b lor (a lsl nbiti)

(* ---- RowLvl: the prepass ------------------------------------------------- *)

let pgbase pg = grpof pg 0
let pgchk pg = pgbase pg / csize
let pgoff pg = pgbase pg mod csize

(* RowLvl.pgfits *)
let pgfits pg =
  andb (pgoff pg + ngroupi <= csize) (pgoff pg <= pgoff pg + ngroupi)

(* RowLvl.prepmv0S *)
let prepmv0S cpg cfl mgr msw mlo mhi k (src : rmap) (dst : rmap) : rmap =
  ifold nclsn 0
    (fun pg d ->
       let pg' = pgmv cpg k pg in
       if pgfits pg then
         let sa = Parray.get src (pgchk pg) in
         let o = pgoff pg in
         ifold ngroupn 0
           (fun gr d' ->
              let g = grpof pg gr in
              let v = Parray.get sa (o + gr) in
              if v = 0 then d'
              else gor (gor d' g v) (grpof pg' (grmv mgr k gr))
                       (grpmv cfl msw mlo mhi k v))
           d
       else
         ifold ngroupn 0
           (fun gr d' ->
              let g = grpof pg gr in
              let v = gget src g in
              if v = 0 then d'
              else gor (gor d' g v) (grpof pg' (grmv mgr k gr))
                       (grpmv cfl msw mlo mhi k v))
           d)
    dst

(* RowLvl.prepmvD *)
let prepmvD cpg cfl mgr msw mlo mhi k (src : rmap) (dst : rmap) : rmap =
  ifold nclsn 0
    (fun pg d ->
       let pg' = pgmv cpg k pg in
       if andb (pgfits pg)
            (andb (pgfits pg') (pgchk pg' < Parray.length d)) then
         let sa = Parray.get src (pgchk pg) in
         let o = pgoff pg in
         let c' = pgchk pg' in
         let o' = pgoff pg' in
         Parray.set d c'
           (ifold ngroupn 0
              (fun gr b ->
                 let v = Parray.get sa (o + gr) in
                 if v = 0 then b
                 else
                   let j = o' + grmv mgr k gr in
                   let old = Parray.get b j in
                   let w = old lor (grpmv cfl msw mlo mhi k v) in
                   if w = old then b else Parray.set b j w)
              (Parray.get d c'))
       else if pgfits pg then
         let sa = Parray.get src (pgchk pg) in
         let o = pgoff pg in
         ifold ngroupn 0
           (fun gr d' ->
              let v = Parray.get sa (o + gr) in
              if v = 0 then d'
              else gor d' (grpof pg' (grmv mgr k gr))
                       (grpmv cfl msw mlo mhi k v))
           d
       else
         ifold ngroupn 0
           (fun gr d' ->
              let v = gget src (grpof pg gr) in
              if v = 0 then d'
              else gor d' (grpof pg' (grmv mgr k gr))
                       (grpmv cfl msw mlo mhi k v))
           d)
    dst

(* RowLvl.prepassD *)
let prepassD cpg cfl mgr msw mlo mhi (src : rmap) (dst : rmap) : rmap =
  ifold nhn 0
    (fun k d ->
       if k = 0 then prepmv0S cpg cfl mgr msw mlo mhi k src d
       else prepmvD cpg cfl mgr msw mlo mhi k src d)
    dst

(* ---- Phase1, Fold, RowMask: the folded phase one table ------------------- *)

let nfsi = 1013760
let ntwisti = 2187
let nsymi = 16
let cwlogi = 21
let cwmaski = (1 lsl cwlogi) - 1
let mbits = 28
let mper = 2
let mmaski = (1 lsl mbits) - 1

(* Phase1.p1getm *)
let p1getm (f : arr Parray.t) i =
  let w = i / mper in
  let r = i - w * mper in
  let c = w lsr cwlogi in
  let o = w land cwmaski in
  ((Parray.get (Parray.get f c) o) lsr (r * mbits)) land mmaski

(* Fold.foldi *)
let foldi rep tw = rep * ntwisti + tw

(* RowMask.Dfoldm *)
let dfoldm f frep fsym twsym tw r =
  let y = fsym r in
  (p1getm f (foldi (frep r) (twsym tw y))) lor (y lsl mbits)

(* RowMask *)
let mdmask = 15
let mfbits = 12
let mfmask = 4095
let msmask = 15
let ndeci = 4096
let allmvi = 262143
let mdbits = 4

(* Fold.get20, get4 *)
let get20 (a : arr) i =
  let w = i / 3 in
  let j = i - w * 3 in
  ((Parray.get a w) lsr (j * 20)) land 1048575

let get4 (a : arr) i =
  let w = i / 15 in
  let j = i - w * 15 in
  ((Parray.get a w) lsr (j * 4)) land 15

(* RowMask.mdist *)
let mdist w = w land mdmask

let two = S (S O)

(* RowMask.mmask *)
let mmask dnlo dnhi fllo flhi w s =
  if leq two s then allmvi
  else
    let b = ((w lsr mbits) land msmask) * ndeci in
    let c = w lsr mdbits in
    let lo = b + (c land mfmask) in
    let hi = b + ((c lsr mfbits) land mfmask) in
    match s with
    | S O -> (get20 fllo lo) lor (get20 flhi hi)
    | _ -> (get20 dnlo lo) lor (get20 dnhi hi)

(* RowSrch.sp1g *)
let sp1g f frep fsym twsym c =
  let tw = c / nfsi in
  dfoldm f frep fsym twsym tw (c - tw * nfsi)

(* ---- Row: the place of a member ------------------------------------------ *)

let mcp ((c, _), _) = c
let mud ((_, u), _) = u
let mmp (_, m) = m

(* Row.place *)
let place e8num e4bit x =
  ((Parray.get e8num (mcp x) / 2,
    Parray.get e8num (mud x) / 2),
   (Parray.get e8num (mcp x) mod 2) * nbiti + Parray.get e4bit (mmp x))

(* ---- RowSrch: the count, and the mark that counts ------------------------ *)

let nlo12 = 4096

(* RowSrch.popof, popi *)
let popof v = ifold (nat_of_int 12) 0 (fun i a -> a + ((v lsr i) land 1)) 0
let popi : arr =
  ifold (nat_of_int nlo12) 0 (fun i a -> Parray.set a i (popof i))
    (Parray.make nlo12 0)

(* RowSrch.mcount *)
let mcount (m : rmap) =
  ifold nclsn 0
    (fun pg acc ->
       ifold ngroupn 0
         (fun gr b ->
            let v = gget m (grpof pg gr) in
            if v = 0 then b
            else
              b +
                ((Parray.get popi (v land lo12) +
                  Parray.get popi ((v lsr 12) land lo12)) +
                 (Parray.get popi ((v lsr 24) land lo12) +
                  Parray.get popi ((v lsr 36) land lo12))))
         acc)
    0

(* RowSrch.mmarkn *)
let mmarkn (mn : rmap * int) pg gr bt =
  let (m, n) = mn in
  let g = grpof pg gr in
  let c = g lsr cshft in
  let i = g land cmskw in
  let a = Parray.get m c in
  let old = Parray.get a i in
  let v = bitof bt in
  let w = old lor v in
  if w = old then mn
  else (Parray.set m c (Parray.set a i w), n + 1)

let enoughb = 167000000
let enoughd = 3
let ncutb = 6000000
let rcutii = 5
let nmvn = nat_of_int 18                (* RowRun.nmvn *)

(* RowSrchN.nbig is 2 ^ 62, which Uint63.leb reads unsigned and no count
   reaches.  As a signed OCaml int 2 ^ 62 is min_int, below every count, so
   it is max_int here: the one place the sign of a compare matters. *)
let nbig = max_int

(* RowSrch.sslack *)
let one = S O
let sslack s = if 2 <= s then two else if s = 1 then one else O

(* RowSrch.srchski: its section's variables first *)
let srchski e8num e4bit f frep fsym twsym dnlo dnhi fllo flhi
            cstep xstep tomemb okmv csolved ishm =
  let rec srchski cut togo togoi c x msk pv enough (mn : rmap * int) =
    if enough <= snd mn then mn
    else match togo with
    | S togo' ->
        let togoi' = togoi - 1 in
        ifold nmvn 0
          (fun k a ->
             if msk land (1 lsl k) = 0 then a
             else if negb (okmv pv k) then a
             else if (if cut
                      then (if eqn togo' O
                            then negb (ishm land (1 lsl k) = 0)
                            else false)
                      else false)
             then a
             else
               let c' = cstep c k in
               let w = sp1g f frep fsym twsym c' in
               let nd = mdist w in
               if (if nd <= togoi'
                   then (if cut
                         then (if nd = togoi' then true
                               else rcutii <= togoi' + nd)
                         else true)
                   else false)
               then srchski cut togo' togoi' c' (xstep x k)
                      (mmask dnlo dnhi fllo flhi w (sslack (togoi' - nd)))
                      k enough a
               else a)
          mn
    | O ->
        if csolved c
        then let ((pg, gr), bt) = place e8num e4bit (tomemb x) in
             mmarkn mn pg gr bt
        else mn in
  srchski

(* RowSrchC.srchskiL: hcoset's last level *)
let srchskiL e8num e4bit f frep fsym twsym dnlo dnhi fllo flhi
             cstep xstep tomemb okmv csolved ishm =
  let rec srchskiL cut togo togoi c x msk pv enough (mn : rmap * int) =
    if enough <= snd mn then mn
    else match togo with
    | S togo' ->
        (match togo' with
         | O ->
             ifold nmvn 0
               (fun k a ->
                  if msk land (1 lsl k) = 0 then a
                  else if negb (okmv pv k) then a
                  else if (if cut then negb (ishm land (1 lsl k) = 0)
                           else false)
                  then a
                  else srchski e8num e4bit f frep fsym twsym
                         dnlo dnhi fllo flhi cstep xstep tomemb okmv
                         csolved ishm
                         cut O 0 (cstep c k) (xstep x k) 0 k enough a)
               mn
         | _ ->
             let togoi' = togoi - 1 in
             ifold nmvn 0
               (fun k a ->
                  if msk land (1 lsl k) = 0 then a
                  else if negb (okmv pv k) then a
                  else if (if cut
                           then (if eqn togo' O
                                 then negb (ishm land (1 lsl k) = 0)
                                 else false)
                           else false)
                  then a
                  else
                    let c' = cstep c k in
                    let w = sp1g f frep fsym twsym c' in
                    let nd = mdist w in
                    if (if nd <= togoi'
                        then (if cut
                              then (if nd = togoi' then true
                                    else rcutii <= togoi' + nd)
                              else true)
                        else false)
                    then srchskiL cut togo' togoi' c' (xstep x k)
                           (mmask dnlo dnhi fllo flhi w
                              (sslack (togoi' - nd)))
                           k enough a
                    else a)
               mn)
    | O ->
        srchski e8num e4bit f frep fsym twsym dnlo dnhi fllo flhi
          cstep xstep tomemb okmv csolved ishm
          cut O togoi c x msk pv enough mn in
  srchskiL

(* ---- RowSrchN: the level and the run ------------------------------------- *)

(* RowSrchN.slvlskni *)
let slvlskni e8num e4bit f frep fsym twsym dnlo dnhi fllo flhi
             cstep xstep tomemb okmv csolved croot sroot dsrch ishm
             cut d (m' : rmap) nb : rmap * int =
  if leq d dsrch then
    let w = sp1g f frep fsym twsym croot in
    let di = of_nat d in
    if mdist w <= di then
      let msk = mmask dnlo dnhi fllo flhi w (sslack (di - mdist w)) in
      let e = if eqn d dsrch then enoughb + nb / enoughd else nbig in
      srchskiL e8num e4bit f frep fsym twsym dnlo dnhi fllo flhi
        cstep xstep tomemb okmv csolved ishm
        cut d di croot sroot msk 18 e (m', nb)
    else (m', nb)
  else (m', nb)

(* RowSrchN.runskni *)
let runskni e8num e4bit prep f frep fsym twsym dnlo dnhi fllo flhi
            cstep xstep tomemb okmv csolved croot sroot dsrch ishm =
  let rec runskni n d n0 (m : rmap) (dst : rmap) : rmap =
    match n with
    | S n1 ->
        if ncutb < n0 then
          let m1 = prep m dst in
          let mn = slvlskni e8num e4bit f frep fsym twsym dnlo dnhi fllo flhi
                     cstep xstep tomemb okmv csolved croot sroot dsrch ishm
                     true (S d) m1 (mcount m1) in
          runskni n1 (S d) (snd mn) (fst mn) m
        else
          let mn = slvlskni e8num e4bit f frep fsym twsym dnlo dnhi fllo flhi
                     cstep xstep tomemb okmv csolved croot sroot dsrch ishm
                     false (S d) m n0 in
          runskni n1 (S d) (snd mn) (fst mn) dst
    | O -> m in
  runskni

(* ---- reading the tables from the .v files -------------------------------- *)

(* The numbers of `Definition NAME ... := [:: ... ]' or `[| ... | def |]',
   in order. *)
let read_def file name : int array =
  let ic = open_in file in
  let key = "Definition " ^ name ^ " " in
  let kl = String.length key in
  let rec find () =
    let l = input_line ic in
    if String.length l >= kl && String.sub l 0 kl = key then l else find () in
  let first = (try find () with End_of_file ->
    failwith (Printf.sprintf "%s: no %s" file name)) in
  let buf = ref (Array.make 1024 0) and len = ref 0 in
  let push v =
    if !len = Array.length !buf then begin
      let b = Array.make (2 * !len) 0 in
      Array.blit !buf 0 b 0 !len; buf := b
    end;
    !buf.(!len) <- v; incr len in
  let started = ref false and stop = ref false in
  let cur = ref 0 and indig = ref false in
  let scan l =
    let n = String.length l in
    let i = ref 0 in
    while not !stop && !i < n do
      let ch = l.[!i] in
      if not !started then begin
        if ch = '[' && !i + 1 < n && (l.[!i + 1] = '|' || l.[!i + 1] = ':')
        then begin
          started := true;
          i := !i + (if l.[!i + 1] = '|' then 1 else 2)
        end
      end else if ch >= '0' && ch <= '9' then begin
        cur := !cur * 10 + (Char.code ch - 48); indig := true
      end else begin
        if !indig then (push !cur; cur := 0; indig := false);
        if ch = ']' || ch = '|' then stop := true
      end;
      incr i
    done;
    if !started && !indig && not !stop then (push !cur; cur := 0; indig := false)
  in
  scan first;
  (try while not !stop do scan (input_line ic) done
   with End_of_file -> ());
  close_in ic;
  Array.sub !buf 0 !len

(* Phase1.mkarr n d l: an array of n, the list written from 0 *)
let mkarr n d (l : int array) : arr =
  let a = Array.make n d in
  Array.blit l 0 a 0 (min n (Array.length l));
  Parray.of_array a d

(* an array literal: its default is 0 in every generated file *)
let lit (l : int array) : arr = Parray.of_array l 0

(* ---- the four values read off Rocq --------------------------------------- *)

(* The values printed by RowTransConsts.v, in its order: ymvpi, yrooti,
   RowInst.croot, RowInst.csolvedci.  An array prints as [| a; b | def : int |]. *)
let read_consts file =
  let ic = open_in file in
  let txt = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let vals = ref [] in
  let n = String.length txt in
  let i = ref 0 in
  let ints s =
    List.filter_map (fun t ->
        let t = String.trim t in
        let t = match String.index_opt t '%' with
          | Some j -> String.sub t 0 j | None -> t in
        if t = "" then None else Some (int_of_string t))
      (String.split_on_char ';' s) in
  while !i < n do
    (* a value starts at `= ' after a newline and spaces *)
    if txt.[!i] = '=' && !i + 1 < n && txt.[!i + 1] = ' ' then begin
      let j = (try String.index_from txt !i ':' with Not_found -> n) in
      let body = String.sub txt (!i + 2) (j - !i - 2) in
      (match String.index_opt body '[' with
       | Some _ ->
           (* [| a; b; ... | def : int |] : the ':' found is the default's *)
           let parts = String.split_on_char '|' body in
           vals := `A (Array.of_list (ints (List.nth parts 1))) :: !vals
       | None -> vals := `I (List.hd (ints body)) :: !vals);
      i := j
    end else incr i
  done;
  List.rev !vals

(* ---- RowCoord, RowCoordLeaf, RowLeafFast: the tables Rocq computes ------- *)

(* RowCoord.mkT *)
let mkT sz f : arr =
  let szn = nat_of_int sz in
  ifold szn 0 (fun i a -> Parray.set a i (f i)) (Parray.make (of_nat szn) 0)

(* RowLeafFast.lbpop, lbcq, lbeq *)
let popn s =
  let rec go s = if s = 0 then 0 else (s land 1) + go (s lsr 1) in go s
let lbpop : arr =
  ifold (nat_of_int 256) 0 (fun s a -> Parray.set a s (popn s))
    (Parray.make 256 0)
let lbcq : arr =
  ifold (nat_of_int 24) 0 (fun v a -> Parray.set a v (v / 3)) (Parray.make 24 0)
let lbeq : arr =
  ifold (nat_of_int 24) 0 (fun v a -> Parray.set a v (v / 2)) (Parray.make 24 0)

(* RowLeafFast.lbstep, lbrank *)
let lbstep ni v i st =
  let x = v i in
  let bx = 1 lsl x in
  let seen = st land 255 in
  let c = x - Parray.get lbpop (seen land (bx - 1)) in
  ((((st lsr 8) * (ni - i)) + c) lsl 8) + (seen + bx)

let lbrank v nn ni = (ifold nn 0 (lbstep ni v) 0) lsr 8

let eight = nat_of_int 8
let four = nat_of_int 4

(* RowCoord.factA, nthfree, cunrank *)
let factA = mkT 8 (fun i -> ifold (nat_of_int i) 1 (fun x a -> x * a) 1)

let nthfree s c =
  fst (ifold eight 0
         (fun v (res, cnt) ->
            if s land (1 lsl v) = 0
            then ((if cnt = c then v else res), cnt + 1)
            else (res, cnt))
         (0, 0))

let cunrank r : arr =
  let (a, _, _) =
    ifold eight 0
      (fun i (a, r, s) ->
         let f = Parray.get factA (7 - i) in
         let c = r / f in
         let v = nthfree s c in
         (Parray.set a i v, r - c * f, s lor (1 lsl v)))
      (Parray.make 8 0, r, 0) in a

(* RowCoord.ctab *)
let mk_ctab ymvpi =
  mkT (40320 * 18)
    (fun i ->
       let r = i / 18 in
       let k = i - r * 18 in
       let a = cunrank r in
       lbrank (fun j -> Parray.get a (Parray.get ymvpi (k * 20 + j))) eight 8)

(* RowCoord.einvT *)
let mk_einvT ymvpi : arr =
  ifold (nat_of_int (18 * 12)) 0
    (fun i a ->
       let k = i / 12 in
       let j = i - k * 12 in
       Parray.set a
         (k * 12 + (Parray.get ymvpi (k * 20 + (8 + j)) - 8))
         j)
    (Parray.make (18 * 12) 0)

let ntup = 20736
let enc p0 p1 p2 p3 = ((p0 * 12 + p1) * 12 + p2) * 12 + p3
let tp0 t = t / 1728
let tp1 t = (t / 144) mod 12
let tp2 t = (t / 12) mod 12
let tp3 t = t mod 12

(* RowCoord.etab *)
let mk_etab einvT =
  mkT (ntup * 18)
    (fun i ->
       let t = i / 18 in
       let k = i - t * 18 in
       let inv q = Parray.get einvT (k * 12 + q) in
       enc (inv (tp0 t)) (inv (tp1 t)) (inv (tp2 t)) (inv (tp3 t)))

(* RowCoord.all4, dist4, sub8tup *)
let all4 f t = andb (andb (andb (f (tp0 t)) (f (tp1 t))) (f (tp2 t))) (f (tp3 t))
let dist4 t =
  let a = tp0 t and b = tp1 t and c = tp2 t and d = tp3 t in
  negb (a = b || a = c || a = d || b = c || b = d || c = d)

let n8t = 1680
let (sub8, tup8) =
  let (s, u, _) =
    ifold (nat_of_int ntup) 0
      (fun t ((s, u, n) as st) ->
         if andb (all4 (fun p -> p < 8) t) (dist4 t)
         then (Parray.set s t n, Parray.set u n t, n + 1)
         else st)
      (Parray.make ntup 0, Parray.make n8t 0, 0) in (s, u)

(* mathcomp's index *)
let index p l =
  let rec go i = function [] -> i | x :: l -> if x = p then i else go (i + 1) l in
  go 0 l

(* RowCoordLeaf.l8, ecub, e8rT, l4, mcub, e4rT *)
let l8 u v = [tp0 u; tp1 u; tp2 u; tp3 u; tp0 v; tp1 v; tp2 v; tp3 v]
let ecub u v p = index p (l8 u v)
let e8rT =
  mkT (1680 * 1680)
    (fun i ->
       let a = i / n8t in
       let b = i - a * n8t in
       lbrank (ecub (Parray.get tup8 a) (Parray.get tup8 b)) eight 8)
let l4 m = [tp0 m; tp1 m; tp2 m; tp3 m]
let mcub m p = index (p + 8) (l4 m)
let e4rT = mkT ntup (fun t -> lbrank (mcub t) four 4)

(* ---- the position: RowCoord.cstepx, cofy; RowCoordLeaf.cmemb ------------- *)

(* RowCoord.cstepx *)
let cstepx ctab etab x k =
  let (((c, u), d), m) = x in
  (((Parray.get ctab (c * 18 + k),
     Parray.get etab (u * 18 + k)),
    Parray.get etab (d * 18 + k)),
   Parray.get etab (m * 18 + k))

(* RowCoordLeaf.cmemb *)
let cmemb x =
  let (((c, u), d), m) = x in
  ((c, Parray.get e8rT (Parray.get sub8 u * n8t + Parray.get sub8 d)),
   Parray.get e4rT m)

(* RowCoord.eplace, cofy *)
let eplace (y : arr) b =
  ifold (nat_of_int 12) 0
    (fun p r -> if Parray.get lbeq (Parray.get y (8 + p)) = b then p else r) 0

let cofy (y : arr) =
  let tup b = enc (eplace y b) (eplace y (b + 1))
                  (eplace y (b + 2)) (eplace y (b + 3)) in
  (((lbrank (fun p -> Parray.get lbcq (Parray.get y p)) eight 8, tup 0),
    tup 4), tup 8)

(* ---- RowInst, Farp1, Phase1: the phase one coordinate --------------------- *)

(* Phase1.acttwii *)
let acttwii twmove x k = Parray.get twmove (x * 18 + k)

(* Farp1.actfsri *)
let fcwlogi = 21
let fcwmaski = (1 lsl fcwlogi) - 1
let actfsri (fsmtabs : arr Parray.t) r k =
  let i = r * 18 + k in
  let w = i / 3 in
  let j = i - w * 3 in
  let c = w lsr fcwlogi in
  let o = w land fcwmaski in
  ((Parray.get (Parray.get fsmtabs c) o) lsr (j * 20)) land 1048575

(* RowInst.cstep: ctw is Uint63.div, cfs Uint63.mod *)
let cstep twmove fsstep c k =
  (acttwii twmove (c / nfsi) k) * nfsi + fsstep (c mod nfsi) k

(* RowReal.okmvv *)
let okmvv pv k =
  if 18 <= pv then true
  else let fp = pv / 3 in
       let fk = k / 3 in
       negb (orb (fp = fk) (fp = fk + 3))

(* RowCubDef.fstep, ishmi *)
let fstep twmove fsmtabs c k =
  (acttwii twmove (c / nfsi) k) * nfsi + actfsri fsmtabs (c mod nfsi) k

let mk_ishmi twmove fsmtabs csolvedci =
  ifold nmvn 0
    (fun k a ->
       if fstep twmove fsmtabs csolvedci k = csolvedci
       then a lor (1 lsl k) else a)
    0

(* ========================================================================= *)
(*  THE FOLDED RUN: RowFoldCubDefD.rowmapiD                                   *)
(* ========================================================================= *)

(* ---- RowFold: the folded map --------------------------------------------- *)

let nrepi = 1496
let nrepn = nat_of_int nrepi
let ppcshft = 6
let ppcmask = 63
let csizef = 1290240
let nchunkf = 24
let nchunkfn = nat_of_int 24

(* RowFold.mkempty *)
let mkemptyf () : rmap =
  ifold nchunkfn 0
    (fun c a -> Parray.set a c (Parray.make csizef 0))
    (Parray.make nchunkf (Parray.make 1 0))

(* RowFold.pchk, poff *)
let pchk r = r lsr ppcshft
let poff r = (r land ppcmask) * ngroupi

(* RowFold.ffor *)
let ffor (m : rmap) r g v =
  let c = pchk r in
  let i = poff r + g in
  let a = Parray.get m c in
  let old = Parray.get a i in
  let w = old lor v in
  if w = old then m else Parray.set m c (Parray.set a i w)

(* RowFold: the four fields of a folded word *)
let fpar w = w land 1
let fren w = (w lsr 1) land 15
let fhlf w = (w lsr 5) land 1
let fkpt w = w lsr 6

(* RowFold.fbit *)
let fbit h b = if h = 0 then b else nbiti + b

(* RowFold.sgrmv, sbtmv *)
let sgrmv fsgr u pty g = Parray.get fsgr ((u * 2 + pty) * ngroupi + g)
let sbtmv fsbt u bt = Parray.get fsbt (u * nbiti + bt)

(* RowFold.fmark *)
let fmark fpg fsgr fsbt (m : rmap) pg gr bt =
  let w = Parray.get fpg pg in
  let u = fren w in
  let pty = (fpar w) lxor (if bt < 12 then 0 else 1) in
  ffor m (fkpt w) (sgrmv fsgr u pty gr) (bitof (fbit (fhlf w) (sbtmv fsbt u bt)))

(* RowFold.fmarkn *)
let fmarkn fpg fsgr fsbt (mn : rmap * int) pg gr bt =
  let (m, n) = mn in
  let w = Parray.get fpg pg in
  let u = fren w in
  let pty = (fpar w) lxor (if bt < 12 then 0 else 1) in
  let r = fkpt w in
  let g = sgrmv fsgr u pty gr in
  let v = bitof (fbit (fhlf w) (sbtmv fsbt u bt)) in
  let c = pchk r in
  let i = poff r + g in
  let a = Parray.get m c in
  let old = Parray.get a i in
  let w = old lor v in
  if w = old then mn
  else (Parray.set m c (Parray.set a i w), n + 1)

(* RowFoldN.fmarknw *)
let fmarknw fpg fsgr fsbt forb (mn : rmap * int) pg gr bt =
  let (m, n) = mn in
  let w = Parray.get fpg pg in
  let u = fren w in
  let pty = (fpar w) lxor (if bt < 12 then 0 else 1) in
  let r = fkpt w in
  let g = sgrmv fsgr u pty gr in
  let v = bitof (fbit (fhlf w) (sbtmv fsbt u bt)) in
  let c = pchk r in
  let i = poff r + g in
  let a = Parray.get m c in
  let old = Parray.get a i in
  let w' = old lor v in
  if w' = old then mn
  else (Parray.set m c (Parray.set a i w'),
        if fhlf w = 0 then n + Parray.get forb r else n)

(* Row.place24 *)
let place24 e8num e4bit x =
  ((mcp x, Parray.get e8num (mud x) / 2), Parray.get e4bit (mmp x))

(* ---- RowFold: the level -------------------------------------------------- *)

(* RowFold.fofs *)
let fofs dh o = if dh = 0 then o else o + nbiti

(* RowFold.flevmvu; mlo mhi fslo fshi are its section's *)
let flevmvu fslo fshi mlo mhi (mgr : arr) (fsgr' : arr)
            v dh doff glo ghi ub kb k sw (b : arr) : arr =
  if v = 0 then b
  else
    let lo = v land lo12 in
    let hi = (v lsr 12) land lo12 in
    let b1 =
      if lo = 0 then b
      else
        let l = Parray.get mlo (kb + Parray.get fslo (ub + lo)) in
        let j = doff + Parray.get mgr ((Parray.get fsgr' glo) * nhi + k) in
        Parray.set b j
          ((Parray.get b j) lor (l lsl (fofs dh (if sw then 0 else 12)))) in
    if hi = 0 then b1
    else
      let h = Parray.get mhi (kb + Parray.get fshi (ub + hi)) in
      let j = doff + Parray.get mgr ((Parray.get fsgr' ghi) * nhi + k) in
      Parray.set b1 j
        ((Parray.get b1 j) lor (h lsl (fofs dh (if sw then 12 else 0))))

(* RowFold.flevmv *)
let flevmv fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi
           (src : rmap) r k doff (a : arr) : arr =
  let w = Parray.get fsrc (r * nhi + k) in
  let w2 = Parray.get fsrc2 (r * nhi + k) in
  let u0 = fren w in
  let h0 = fhlf w in
  let u1 = w2 lsr 1 in
  let h1 = w2 land 1 in
  let pc = fpar w in
  let p = fkpt w in
  let two = negb (Parray.get fful r = allbits24) in
  let sa = Parray.get src (pchk p) in
  let soff = poff p in
  let gl u = (u * 2 + pc) * ngroupi in
  let gh u = (u * 2 + (1 - pc)) * ngroupi in
  let kb = k lsl 12 in
  let sw = Parray.get msw k = 0 in
  ifold ngroupn 0
    (fun g b ->
       let v = Parray.get sa (soff + g) in
       if v = 0 then b
       else
         let vof h =
           if h = 0 then v land allbits24
           else (v lsr nbiti) land allbits24 in
         let b0 =
           flevmvu fslo fshi mlo mhi mgr fsgr (vof h0) 0 doff
             (gl u0 + g) (gh u0 + g) (u0 lsl 12) kb k sw b in
         if two then
           flevmvu fslo fshi mlo mhi mgr fsgr (vof h1) 1 doff
             (gl u1 + g) (gh u1 + g) (u1 lsl 12) kb k sw b0
         else b0)
    a

(* RowFold.flevpg *)
let flevpg fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi
           (src : rmap) r (d : rmap) : rmap =
  let c = pchk r in
  let doff = poff r in
  let sa = Parray.get src c in
  let a0 = Parray.get d c in
  let a1 =
    ifold ngroupn 0
      (fun g b ->
         let j = doff + g in
         Parray.set b j (Parray.get sa j))
      a0 in
  let a2 = ifold nhn 0
      (fun k b -> flevmv fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi
                    src r k doff b) a1 in
  Parray.set d c a2

(* RowFold.flevel *)
let flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi
           (src : rmap) (dst : rmap) : rmap =
  ifold nrepn 0
    (fun r d -> flevpg fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi src r d)
    dst

(* ---- RowFold: the count -------------------------------------------------- *)

(* RowFold.fcount *)
let fcount forb fpop (m : rmap) =
  ifold nrepn 0
    (fun r acc ->
       let orb = Parray.get forb r in
       let ca = Parray.get m (pchk r) in
       let co = poff r in
       ifold ngroupn 0
         (fun g b ->
            let v = Parray.get ca (co + g) in
            if v = 0 then b
            else
              b + orb * (Parray.get fpop (v land lo12) +
                         Parray.get fpop ((v lsr 12) land lo12)))
         acc)
    0

(* RowFold.fcount48 *)
let fcount48 fful forb fpop (m : rmap) =
  ifold nrepn 0
    (fun r acc ->
       let orb = Parray.get forb r in
       let w = if Parray.get fful r = allbits24 then orb else orb / 2 in
       let ca = Parray.get m (pchk r) in
       let co = poff r in
       ifold ngroupn 0
         (fun g b ->
            let v = Parray.get ca (co + g) in
            if v = 0 then b
            else
              b + w * ((Parray.get fpop (v land lo12) +
                        Parray.get fpop ((v lsr 12) land lo12)) +
                       (Parray.get fpop ((v lsr nbiti) land lo12) +
                        Parray.get fpop ((v lsr (nbiti + 12)) land lo12))))
         acc)
    0

(* ---- RowFoldSrchI: the searches, and RowFoldSrchIC: the last level ------- *)

let frcutii = 5
let fsslack = sslack

(* RowFoldSrchI.fsrchki, the leaf fmark *)
let fsrchki e8num e4bit fpg fsgr fsbt f frep fsym twsym dnlo dnhi fllo flhi
            cstep xstep tomemb okmv csolved ishm =
  let rec fsrchki cut togo togoi c x msk pv (m : rmap) : rmap =
    match togo with
    | S togo' ->
        let togoi' = togoi - 1 in
        ifold nmvn 0
          (fun k m' ->
             if msk land (1 lsl k) = 0 then m'
             else if negb (okmv pv k) then m'
             else if (if cut
                      then (if eqn togo' O
                            then negb (ishm land (1 lsl k) = 0)
                            else false)
                      else false)
             then m'
             else
               let c' = cstep c k in
               let w = sp1g f frep fsym twsym c' in
               let nd = mdist w in
               if (if nd <= togoi'
                   then (if cut
                         then (if nd = togoi' then true
                               else frcutii <= togoi' + nd)
                         else true)
                   else false)
               then fsrchki cut togo' togoi' c' (xstep x k)
                      (mmask dnlo dnhi fllo flhi w (fsslack (togoi' - nd)))
                      k m'
               else m')
          m
    | O ->
        if csolved c
        then let ((pg, gr), bt) = place24 e8num e4bit (tomemb x) in
             fmark fpg fsgr fsbt m pg gr bt
        else m in
  fsrchki

(* RowFoldSrchI.fsrchski, the leaf fmarkn *)
let fsrchski e8num e4bit fpg fsgr fsbt f frep fsym twsym dnlo dnhi fllo flhi
             cstep xstep tomemb okmv csolved ishm =
  let rec fsrchski cut togo togoi c x msk pv enough (mn : rmap * int) =
    if enough <= snd mn then mn
    else match togo with
    | S togo' ->
        let togoi' = togoi - 1 in
        ifold nmvn 0
          (fun k a ->
             if msk land (1 lsl k) = 0 then a
             else if negb (okmv pv k) then a
             else if (if cut
                      then (if eqn togo' O
                            then negb (ishm land (1 lsl k) = 0)
                            else false)
                      else false)
             then a
             else
               let c' = cstep c k in
               let w = sp1g f frep fsym twsym c' in
               let nd = mdist w in
               if (if nd <= togoi'
                   then (if cut
                         then (if nd = togoi' then true
                               else frcutii <= togoi' + nd)
                         else true)
                   else false)
               then fsrchski cut togo' togoi' c' (xstep x k)
                      (mmask dnlo dnhi fllo flhi w (fsslack (togoi' - nd)))
                      k enough a
               else a)
          mn
    | O ->
        if csolved c
        then let ((pg, gr), bt) = place24 e8num e4bit (tomemb x) in
             fmarkn fpg fsgr fsbt mn pg gr bt
        else mn in
  fsrchski

(* RowFoldSrchIC.isrchskL *)
let isrchskL e8num e4bit fpg fsgr fsbt f frep fsym twsym dnlo dnhi fllo flhi
             cstep xstep tomemb okmv csolved ishm =
  let rec isrchskL cut togo togoi c x msk pv enough (mn : rmap * int) =
    if enough <= snd mn then mn
    else match togo with
    | S togo' ->
        (match togo' with
         | O ->
             ifold nmvn 0
               (fun k a ->
                  if msk land (1 lsl k) = 0 then a
                  else if negb (okmv pv k) then a
                  else if andb cut (negb (ishm land (1 lsl k) = 0))
                  then a
                  else fsrchski e8num e4bit fpg fsgr fsbt f frep fsym twsym
                         dnlo dnhi fllo flhi cstep xstep tomemb okmv csolved
                         ishm cut O 0 (cstep c k) (xstep x k) 0 k enough a)
               mn
         | _ ->
             let togoi' = togoi - 1 in
             ifold nmvn 0
               (fun k a ->
                  if msk land (1 lsl k) = 0 then a
                  else if negb (okmv pv k) then a
                  else if (if cut
                           then (if eqn togo' O
                                 then negb (ishm land (1 lsl k) = 0)
                                 else false)
                           else false)
                  then a
                  else
                    let c' = cstep c k in
                    let w = sp1g f frep fsym twsym c' in
                    let nd = mdist w in
                    if (if nd <= togoi'
                        then (if cut
                              then (if nd = togoi' then true
                                    else frcutii <= togoi' + nd)
                              else true)
                        else false)
                    then isrchskL cut togo' togoi' c' (xstep x k)
                           (mmask dnlo dnhi fllo flhi w
                              (fsslack (togoi' - nd)))
                           k enough a
                    else a)
               mn)
    | O ->
        fsrchski e8num e4bit fpg fsgr fsbt f frep fsym twsym dnlo dnhi fllo flhi
          cstep xstep tomemb okmv csolved ishm
          cut O togoi c x msk pv enough mn in
  isrchskL

(* ---- RowFoldN: the counting search, the level and the run ---------------- *)

(* RowFoldN.wleaf *)
let wleaf e8num e4bit fpg fsgr fsbt forb tomemb csolved c x a =
  if csolved c then
    let ((pg, gr), bt) = place24 e8num e4bit (tomemb x) in
    fmarknw fpg fsgr fsbt forb a pg gr bt
  else a

(* RowFoldN.iwsrchL *)
let iwsrchL e8num e4bit fpg fsgr fsbt f frep fsym twsym dnlo dnhi fllo flhi
            cstep xstep tomemb okmv csolved forb ishm =
  let rec iwsrchL cut togo togoi c x msk pv (a : rmap * int) =
    match togo with
    | S togo' ->
        (match togo' with
         | O ->
             ifold nmvn 0
               (fun k a' ->
                  if msk land (1 lsl k) = 0 then a'
                  else if negb (okmv pv k) then a'
                  else if andb cut (negb (ishm land (1 lsl k) = 0))
                  then a'
                  else wleaf e8num e4bit fpg fsgr fsbt forb tomemb csolved
                         (cstep c k) (xstep x k) a')
               a
         | _ ->
             let togoi' = togoi - 1 in
             ifold nmvn 0
               (fun k a' ->
                  if msk land (1 lsl k) = 0 then a'
                  else if negb (okmv pv k) then a'
                  else if (if cut
                           then (if eqn togo' O
                                 then negb (ishm land (1 lsl k) = 0)
                                 else false)
                           else false)
                  then a'
                  else
                    let c' = cstep c k in
                    let w = sp1g f frep fsym twsym c' in
                    let nd = mdist w in
                    if (if nd <= togoi'
                        then (if cut
                              then (if nd = togoi' then true
                                    else frcutii <= togoi' + nd)
                              else true)
                        else false)
                    then iwsrchL cut togo' togoi' c' (xstep x k)
                           (mmask dnlo dnhi fllo flhi w
                              (fsslack (togoi' - nd)))
                           k a'
                    else a')
               a)
    | O -> wleaf e8num e4bit fpg fsgr fsbt forb tomemb csolved c x a in
  iwsrchL

(* RowFoldN.wslv *)
let wslv e8num e4bit fpg fsgr fsbt f frep fsym twsym dnlo dnhi fllo flhi
         cstep xstep tomemb okmv csolved croot sroot dsrch forb ishm
         cut d (m' : rmap) nb : rmap * int =
  if leq d dsrch then
    let w = sp1g f frep fsym twsym croot in
    let di = of_nat d in
    if mdist w <= di then
      let msk = mmask dnlo dnhi fllo flhi w (fsslack (di - mdist w)) in
      if eqn d dsrch then
        let e = enoughb + nb / enoughd in
        isrchskL e8num e4bit fpg fsgr fsbt f frep fsym twsym
          dnlo dnhi fllo flhi cstep xstep tomemb okmv csolved ishm
          cut d di croot sroot msk 18 e (m', nb)
      else
        iwsrchL e8num e4bit fpg fsgr fsbt f frep fsym twsym
          dnlo dnhi fllo flhi cstep xstep tomemb okmv csolved forb ishm
          cut d di croot sroot msk 18 (m', nb)
    else (m', nb)
  else (m', nb)

(* RowFoldN.wrun *)
let wrun e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
         f frep fsym twsym dnlo dnhi fllo flhi
         cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm =
  let rec wrun n d n0 (m : rmap) (dst : rmap) : rmap =
    match n with
    | S n1 ->
        if ncutb < n0 then
          let m1 = flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi m dst in
          let a = wslv e8num e4bit fpg fsgr fsbt f frep fsym twsym
                    dnlo dnhi fllo flhi cstep xstep tomemb okmv csolved
                    croot sroot dsrch forb ishm
                    true (S d) m1 (fcount forb fpop m1) in
          wrun n1 (S d) (snd a) (fst a) m
        else
          let a = wslv e8num e4bit fpg fsgr fsbt f frep fsym twsym
                    dnlo dnhi fllo flhi cstep xstep tomemb okmv csolved
                    croot sroot dsrch forb ishm
                    false (S d) m n0 in
          wrun n1 (S d) (snd a) (fst a) dst
    | O -> m in
  wrun

(* ---- main ---------------------------------------------------------------- *)

let () =
  (* rocq's own GC policy, sysinit/coqinit.ml *)
  Gc.set { (Gc.get ()) with
           Gc.minor_heap_size = 32 * 1024 * 1024;
           Gc.space_overhead = 120 };
  let mode = Sys.argv.(1) in
  let dir = Sys.argv.(2) in
  let gen = Sys.argv.(3) in
  let consts = Sys.argv.(4) in
  let depth = if Array.length Sys.argv > 5 then int_of_string Sys.argv.(5)
              else 13 in
  if mode <> "plain" && mode <> "fold" then failwith "mode: plain or fold";
  let t0 = Unix.gettimeofday () in
  (* a generated file is looked for in GEN first *)
  let v file =
    let g = Filename.concat gen file in
    if Sys.file_exists g then g else Filename.concat dir file in
  let (ymvpi, yrooti, croot, csolvedci) =
    match read_consts consts with
    | [`A a; `A b; `I c; `I d] -> (Parray.of_array a 0, Parray.of_array b 0, c, d)
    | l -> failwith (Printf.sprintf "%s: %d values, four expected"
                       consts (List.length l)) in
  (* RowTab: the layout and the prepass *)
  let e8numi = mkarr npagei 0 (read_def (v "RowTabL.v") "e8num_data") in
  let e4biti = mkarr nbiti 0 (read_def (v "RowTabL.v") "e4bit_data") in
  let mgri = mkarr 201600 0 (read_def (v "RowTabP.v") "mgr_data") in
  let mswi = mkarr 10 0 (read_def (v "RowTabP.v") "msw_data") in
  let mloi = mkarr 40960 0 (read_def (v "RowTabP.v") "mlo_data") in
  let mhii = mkarr 40960 0 (read_def (v "RowTabP.v") "mhi_data") in
  (* Phase1.twmove, Farp1.fsmtabs *)
  let twmove = mkarr 39366 0 (read_def (v "P1Small.v") "twmove_data") in
  let fsmtabs : arr Parray.t =
    let a = Parray.make 3 (Parray.make 1 0) in
    let a = Parray.set a 0 (lit (read_def (v "P1Fsm.v") "fsm_chunk_00")) in
    let a = Parray.set a 1 (lit (read_def (v "P1Fsm.v") "fsm_chunk_01")) in
    let a = Parray.set a 2 (lit (read_def (v "P1Fsm.v") "fsm_chunk_02")) in
    a in
  (* P1Fold, P1Fdec, FoldTables *)
  let rep_data = lit (read_def (v "P1Fold.v") "rep_data") in
  let sym_data = lit (read_def (v "P1Fold.v") "sym_data") in
  let twsym_data = lit (read_def (v "P1Fold.v") "twsym_data") in
  let dnlo = lit (read_def (v "P1Fdec.v") "dnlo_data") in
  let dnhi = lit (read_def (v "P1Fdec.v") "dnhi_data") in
  let fllo = lit (read_def (v "P1Fdec.v") "fllo_data") in
  let flhi = lit (read_def (v "P1Fdec.v") "flhi_data") in
  let frepi r = get20 rep_data r in
  let fsymi r = get4 sym_data r in
  let twsymi tw s = get20 twsym_data (tw * nsymi + s) in
  (* P1FTable.p1ftab: as many chunks as the file names, then the three *)
  let p1ftab : arr Parray.t =
    let ic = open_in (v "P1FTable.v") in
    let lines = ref [] in
    (try while true do lines := input_line ic :: !lines done
     with End_of_file -> ());
    close_in ic;
    let lines = List.rev !lines in
    let size = ref 0 in
    List.iter (fun l ->
        try Scanf.sscanf l "  let a := PArray.make %d" (fun n -> size := n)
        with _ -> ()) lines;
    let a = ref (Parray.make !size (Parray.make 1 0)) in
    List.iter (fun l ->
        try Scanf.sscanf l "  let a := PArray.set a %d %s@ in"
              (fun i name ->
                 let tab =
                   if name = "rep_data" then rep_data
                   else if name = "sym_data" then sym_data
                   else if name = "twsym_data" then twsym_data
                   else
                     let c = String.sub name (String.length name - 2) 2 in
                     lit (read_def (v ("P1F_" ^ c ^ ".v")) name) in
                 a := Parray.set !a i tab)
        with Scanf.Scan_failure _ | End_of_file | Failure _ -> ()) lines;
    !a in
  (* RowCoord *)
  let ctab = mk_ctab ymvpi in
  let einvT = mk_einvT ymvpi in
  let etab = mk_etab einvT in
  let ishmi = mk_ishmi twmove fsmtabs csolvedci in
  let sroot = cofy yrooti in
  let ycsolved c = c = csolvedci in
  let srch = nat_of_int 16 in
  let cstepi = cstep twmove (actfsri fsmtabs) in
  let xstepi = cstepx ctab etab in
  let t1 = Unix.gettimeofday () in
  Printf.printf "tables built in %.1f s  (length p1ftab %d, ishmi %d, \
                 croot %d, csolved %d)\n%!"
    (t1 -. t0) (Parray.length p1ftab) ishmi croot csolvedci;
  if mode = "plain" then begin
    let cpgi = mkarr 201600 0 (read_def (v "RowTabC.v") "cpg_data") in
    let cfli = mkarr 10 0 (read_def (v "RowTabC.v") "cfl_data") in
    (* RowCubDefD.rowmappiD *)
    let rowmappiD n =
      runskni e8numi e4biti (prepassD cpgi cfli mgri mswi mloi mhii)
        p1ftab frepi fsymi twsymi dnlo dnhi fllo flhi
        cstepi xstepi cmemb okmvv ycsolved croot sroot srch ishmi
        n O 0 (mkempty ()) (mkempty ()) in
    let t2 = Unix.gettimeofday () in
    let m = rowmappiD (nat_of_int depth) in
    let t3 = Unix.gettimeofday () in
    let c = mcount m in
    let t4 = Unix.gettimeofday () in
    Printf.printf "mcount (rowmappiD %d) = %d\n" depth c;
    Printf.printf "  run %.2f s, count %.2f s, total %.2f s\n%!"
      (t3 -. t2) (t4 -. t3) (t4 -. t2)
  end else begin
    (* RowFoldTab, over RowTabF48 *)
    let tf = v "RowTabF48.v" in
    let fpgi = mkarr 40320 0 (read_def tf "fpg_data") in
    let fsrci = mkarr 14960 0 (read_def tf "fsrc_data") in
    let fsrc2i = mkarr 14960 0 (read_def tf "fsrc2_data") in
    let ffuli = mkarr nrepi 0 (read_def tf "ffull_data") in
    let fsgri = mkarr 645120 0 (read_def tf "fsgr_data") in
    let fsloi = mkarr 65536 0 (read_def tf "fslo_data") in
    let fshii = mkarr 65536 0 (read_def tf "fshi_data") in
    let fsbti = mkarr 384 0 (read_def tf "fsbt_data") in
    let forbi = mkarr nrepi 0 (read_def tf "forb_data") in
    let fpopi = mkarr 4096 0 (read_def tf "fpop_data") in
    (* RowFoldCubDefD.rowmapiD, with RowFoldCubDef's okmvvd, ycsolvedd,
       srchd and ishmi: the same bodies as the plain run's *)
    let rowmapiD n =
      wrun e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
        mgri mswi mloi mhii
        p1ftab frepi fsymi twsymi dnlo dnhi fllo flhi
        cstepi xstepi cmemb okmvv ycsolved croot sroot srch forbi fpopi ishmi
        n O 0 (mkemptyf ()) (mkemptyf ()) in
    let t2 = Unix.gettimeofday () in
    let m = rowmapiD (nat_of_int depth) in
    let t3 = Unix.gettimeofday () in
    let c = fcount48 ffuli forbi fpopi m in
    let t4 = Unix.gettimeofday () in
    Printf.printf "fcount48 (rowmapiD %d) = %d\n" depth c;
    Printf.printf "  run %.2f s, count %.2f s, total %.2f s\n%!"
      (t3 -. t2) (t4 -. t3) (t4 -. t2)
  end
