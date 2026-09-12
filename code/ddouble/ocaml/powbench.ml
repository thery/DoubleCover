(* x^100 computed two ways, on the machine Rocq runs on.                    *)
(*                                                                          *)
(* "2 floats" is a double word: the definitions are the ones of dwarith.v,  *)
(* copied over.  In particular the product of two floats is split by        *)
(* Dekker's method, because a primitive float has no fused multiply add.    *)
(*                                                                          *)
(* "3 ints" is a mantissa of 120 bits held in two integers of 60 bits, and  *)
(* an exponent.  Sixty rather than the sixty three an OCaml integer holds:  *)
(* that is a choice, it leaves room to add a few of them without watching   *)
(* the sign bit, and it costs no multiplication.  The product is taken in   *)
(* both shapes, one that throws away the half that does not fit and one     *)
(* that rounds to nearest.                                                  *)

let pow = 100                       (* the power, so 99 multiplications     *)
let rep = 200_000                   (* how many powers a run computes       *)

(* ---------------------------------------------------------------------- *)
(* 2 floats                                                               *)
(* ---------------------------------------------------------------------- *)

type dw = { h : float; l : float }

let c_const = 134217729.            (* 2^27 + 1                             *)

(* splitC, dekker and fastTwoSum written out inside timesDwDw rather than   *)
(* called: a float held in a local name stays in a register, one returned   *)
(* from a function is put in a box.  Both sides then build exactly one      *)
(* record per multiplication, which is what makes the two times comparable. *)
let times_dw_dw x y =
  let xh = x.h and xl = x.l and yh = y.h and yl = y.l in
  (* splitC xh *)
  let gx = c_const *. xh in
  let dx = xh -. gx in
  let xhh = gx +. dx in
  let xhl = xh -. xhh in
  (* splitC yh *)
  let gy = c_const *. yh in
  let dy = yh -. gy in
  let yhh = gy +. dy in
  let yhl = yh -. yhh in
  (* dekker xh yh *)
  let ch = xh *. yh in
  let t1 = -. ch +. xhh *. yhh in
  let t2 = t1 +. xhh *. yhl in
  let t3 = t2 +. xhl *. yhh in
  let cl1 = t3 +. xhl *. yhl in
  (* the three remaining products, then fastTwoSum *)
  let cl2 = xh *. yl +. xl *. yh in
  let cl3 = cl1 +. cl2 in
  let s = ch +. cl3 in
  let z = s -. ch in
  { h = s; l = cl3 -. z }

(* ---------------------------------------------------------------------- *)
(* 3 ints: the value is (hi * 2^60 + lo) * 2^(e - 120), and the mantissa   *)
(* is kept between a half and one, so bit 59 of hi is set                  *)
(* ---------------------------------------------------------------------- *)

let mask30 = (1 lsl 30) - 1
let mask60 = (1 lsl 60) - 1

type ti = { hi : int; lo : int; e : int }

(* The low 60 bits of a product are just a * b: OCaml keeps the low bits    *)
(* exactly.  The high 60 need the schoolbook split, which is where the      *)
(* work is, since no integer here can hold a product of two whole words.    *)
let mulh a b =
  let al = a land mask30 and ah = a lsr 30 in
  let bl = b land mask30 and bh = b lsr 30 in
  let t = al * bl and m = ah * bl and n = al * bh in
  let acc = (t lsr 30) + (m land mask30) + (n land mask30) in
  ah * bh + (m lsr 30) + (n lsr 30) + (acc lsr 30)

(* the three digits of the product that reach the answer, the fourth being  *)
(* too small to carry anything                                              *)
let ti_mul a b =
  let p11h = mulh a.hi b.hi and p11l = a.hi * b.hi land mask60 in
  let p10h = mulh a.hi b.lo and p10l = a.hi * b.lo land mask60 in
  let p01h = mulh a.lo b.hi and p01l = a.lo * b.hi land mask60 in
  let p00h = mulh a.lo b.lo in
  let d1 = p10l + p01l + p00h in
  let d2 = p11l + p10h + p01h + (d1 lsr 60) in
  let d3 = p11h + (d2 lsr 60) in
  let r0 = d2 land mask60 and g = d1 land mask60 in
  if d3 lsr 59 = 1 then { hi = d3; lo = r0; e = a.e + b.e }
  else { hi = (d3 lsl 1) lor (r0 lsr 59);
         lo = ((r0 lsl 1) lor (g lsr 59)) land mask60;
         e = a.e + b.e - 1 }

let ti_mulr a b =
  let p11h = mulh a.hi b.hi and p11l = a.hi * b.hi land mask60 in
  let p10h = mulh a.hi b.lo and p10l = a.hi * b.lo land mask60 in
  let p01h = mulh a.lo b.hi and p01l = a.lo * b.hi land mask60 in
  let p00h = mulh a.lo b.lo in
  let d1 = p10l + p01l + p00h in
  let d2 = p11l + p10h + p01h + (d1 lsr 60) in
  let d3 = p11h + (d2 lsr 60) in
  let r0 = d2 land mask60 and g = d1 land mask60 in
  let sh = 1 - (d3 lsr 59) in       (* one shift, or none                   *)
  let n1 = if sh = 1 then (d3 lsl 1) lor (r0 lsr 59) else d3 in
  let n0 =
    if sh = 1 then ((r0 lsl 1) lor (g lsr 59)) land mask60 else r0 in
  let rb =                          (* the first bit that does not fit      *)
    if sh = 1 then (g lsr 58) land 1 else g lsr 59 in
  let n0 = n0 + rb in
  let n1 = n1 + (n0 lsr 60) in
  let n0 = n0 land mask60 in
  if n1 lsr 60 = 1 then { hi = 1 lsl 59; lo = 0; e = a.e + b.e - sh + 1 }
  else { hi = n1; lo = n0; e = a.e + b.e - sh }

let ti_of_float x =
  let f, e = Float.frexp x in
  { hi = int_of_float (Float.ldexp f 53) lsl 7; lo = 0; e }

(* ---------------------------------------------------------------------- *)

let base k = 3.14159265358979311600 +. 1e-12 *. float_of_int k

(* one power function each, rather than one taking the multiplication as an *)
(* argument, which would put a call through a pointer on every step         *)
let rec ti_pow r x n = if n = 0 then r else ti_pow (ti_mul r x) x (n - 1)
let rec tr_pow r x n = if n = 0 then r else tr_pow (ti_mulr r x) x (n - 1)
let rec dw_pow r x n = if n = 0 then r else dw_pow (times_dw_dw r x) x (n - 1)
let rec fl_pow r x n = if n = 0 then r else fl_pow (r *. x) x (n - 1)

let run_ti () =
  let t = Sys.time () in
  let rec go k acc last =
    if k = rep then (Sys.time () -. t, acc, last)
    else
      let x = ti_of_float (base k) in
      let r = ti_pow x x (pow - 1) in
      go (k + 1) (acc + r.hi) r
  in
  go 0 0 { hi = 0; lo = 0; e = 0 }

let run_tr () =
  let t = Sys.time () in
  let rec go k acc last =
    if k = rep then (Sys.time () -. t, acc, last)
    else
      let x = ti_of_float (base k) in
      let r = tr_pow x x (pow - 1) in
      go (k + 1) (acc + r.hi) r
  in
  go 0 0 { hi = 0; lo = 0; e = 0 }

let run_dw () =
  let t = Sys.time () in
  let rec go k acc last =
    if k = rep then (Sys.time () -. t, acc, last)
    else
      let x = { h = base k; l = 0. } in
      let r = dw_pow x x (pow - 1) in
      go (k + 1) (acc +. r.h) r
  in
  go 0 0. { h = 0.; l = 0. }

let run_fl () =
  let t = Sys.time () in
  let rec go k acc last =
    if k = rep then (Sys.time () -. t, acc, last)
    else
      let x = base k in
      let r = fl_pow x x (pow - 1) in
      go (k + 1) (acc +. r) r
  in
  go 0 0. 0.

let () =
  let w0 = Gc.minor_words () in
  let tt, at, rt = run_ti () in
  let w1 = Gc.minor_words () in
  let tr, ar, rr = run_tr () in
  let w2 = Gc.minor_words () in
  let td, ad, rd = run_dw () in
  let w3 = Gc.minor_words () in
  let tf, af, rf = run_fl () in
  let n = float_of_int rep *. float_of_int (pow - 1) in
  Printf.printf "pi^%d, %d times, %d multiplications each\n\n" pow rep (pow - 1);
  Printf.printf "  3 ints    %6.2f ns/mul   the low half thrown away\n"
    (1e9 *. tt /. n);
  Printf.printf "  3 ints    %6.2f ns/mul   rounded to nearest\n"
    (1e9 *. tr /. n);
  Printf.printf "  2 floats  %6.2f ns/mul\n" (1e9 *. td /. n);
  Printf.printf "  1 float   %6.2f ns/mul\n" (1e9 *. tf /. n);
  Printf.printf "\n  3 ints / 2 floats   %.2f thrown away   %.2f rounded\n"
    (tt /. td) (tr /. td);
  Printf.printf "\nthe last power, mantissa of 120 bits and exponent\n";
  Printf.printf "  3 ints    %015x%015x  2^%d  thrown away\n" rt.hi rt.lo rt.e;
  Printf.printf "  3 ints    %015x%015x  2^%d  rounded\n" rr.hi rr.lo rr.e;
  Printf.printf "  2 floats  %h %h\n" rd.h rd.l;
  Printf.printf "  1 float   %.17e\n" rf;
  Printf.printf "\nwords put in the heap per multiplication  %.1f %.1f %.1f\n"
    ((w1 -. w0) /. n) ((w2 -. w1) /. n) ((w3 -. w2) /. n);
  Printf.printf "\nchecksums %d %d %.17e %.17e\n" at ar ad af
