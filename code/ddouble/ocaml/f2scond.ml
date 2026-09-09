(* The same two conditions, hunted where they can actually fail: high words
   that nearly cancel, low words as large as a double word allows.  The
   known |c| > |sh| example is run first, as a check on the harness. *)

let two_sum a b =
  let s = a +. b in
  let a' = s -. b in
  let b' = s -. a' in
  (s, (a -. a') +. (b -. b'))

let fast_two_sum a b =
  let s = a +. b in
  let z = s -. a in
  (s, b -. z)

let ce x =
  if x = 0.0 then min_int / 2
  else let (_, k) = Float.frexp x in max (k - 53) (-1074)

let ulp x = if x = 0.0 then Float.min_float
            else let (_, k) = Float.frexp x in Float.ldexp 1.0 (k - 53)

let well_formed h l = h +. l = h

let bad_abs1 = ref 0 and bad_ce1 = ref 0
let bad_abs2 = ref 0 and bad_ce2 = ref 0
let bad_exact = ref 0
let seen = ref 0
let bad_ce1_nz = ref 0
let worst = ref 0
let ex_abs = ref None and ex_ce = ref None

let trial xh xl yh yl =
  if well_formed xh xl && well_formed yh yl
     && Float.is_finite xh && Float.is_finite yh then begin
    incr seen;
    let (sh, sl) = two_sum xh yh in
    let (th, tl) = two_sum xl yl in
    let c = sl +. th in
    let (vh, vl) = fast_two_sum sh c in
    let w = tl +. vl in
    let (zh, zl) = fast_two_sum vh w in
    if abs_float c > abs_float sh then begin
      incr bad_abs1;
      if !ex_abs = None then ex_abs := Some (xh, xl, yh, yl, sh, c)
    end;
    if ce c > ce sh then begin
      incr bad_ce1;
      if sh <> 0.0 then begin
        incr bad_ce1_nz;
        if ce c - ce sh > !worst then worst := ce c - ce sh;
        if !ex_ce = None then ex_ce := Some (xh, xl, yh, yl, sh, c)
      end
    end;
    if abs_float w > abs_float vh then incr bad_abs2;
    if ce w > ce vh then incr bad_ce2;
    if vh +. vl <> sh +. c then incr bad_exact;
    if zh +. zl <> vh +. w then incr bad_exact
  end

let () =
  (* the harness check: this pair is known to break |c| <= |sh| *)
  trial 4503599627370496.0 0.5 (-4503599627370495.5) 0.125;
  Printf.printf "self test, |c| > |sh| seen: %d (want 1)\n" !bad_abs1;
  bad_abs1 := 0; bad_ce1 := 0; bad_abs2 := 0; bad_ce2 := 0;
  bad_exact := 0; seen := 0; ex_abs := None; ex_ce := None;
  bad_ce1_nz := 0; worst := 0;
  Random.self_init ();
  let lows x = [ ulp x /. 2.; -. (ulp x) /. 2.; ulp x /. 4.; -. (ulp x) /. 4.;
                 ulp x /. 8.; -. (ulp x) /. 8.; 0.0 ] in
  for _ = 1 to 40000 do
    let e = Random.int 120 - 60 in
    let xh = Float.ldexp (1.0 +. Random.float 1.0) e in
    let u = ulp xh in
    List.iter (fun xl ->
      for k = -8 to 8 do
        List.iter (fun step ->
          let yh = -. xh +. float_of_int k *. step in
          List.iter (fun yl -> trial xh xl yh yl) (lows yh))
          [ u; u /. 2.; u /. 4. ]
      done) (lows xh)
  done;
  Printf.printf "well formed pairs tried %d\n" !seen;
  Printf.printf "|c| > |sh|         %d\n" !bad_abs1;
  Printf.printf "ce c > ce sh       %d (of which sh <> 0: %d)\n"
    !bad_ce1 !bad_ce1_nz;
  Printf.printf "worst ce c - ce sh with sh <> 0: %d\n" !worst;
  Printf.printf "|w| > |vh|         %d\n" !bad_abs2;
  Printf.printf "ce w > ce vh       %d\n" !bad_ce2;
  Printf.printf "fastTwoSum inexact %d\n" !bad_exact;
  let show name = function
    | None -> Printf.printf "%s: none\n" name
    | Some (xh, xl, yh, yl, sh, c) ->
      Printf.printf "%s: xh=%h xl=%h yh=%h yl=%h sh=%h c=%h\n"
        name xh xl yh yl sh c in
  show "first |c| > |sh|" !ex_abs;
  show "first ce failure " !ex_ce
