(* Can add_UP return minus infinity as its high word?  If it can, valid_ub is
   false on that result and the FloatOps obligation fails.  This mirrors
   dwarith.v and dw_updn.v step for step and hunts at the top of the range,
   where the last Fast2Sum can overflow while everything before it is finite. *)

let u = ldexp 1.0 (-53)

let two_sum a b =
  let s = a +. b in
  let a' = s -. b in
  let b' = s -. a' in
  (s, (a -. a') +. (b -. b'))

let fast_two_sum a b =
  let s = a +. b in
  let z = s -. a in
  (s, b -. z)

let add_up_fp a b = Float.succ (a +. b)
let mul_up_fp a b = Float.succ (a *. b)

(* plusDwDwErr *)
let plus_dw_dw_err (xh, xl) (yh, yl) =
  let (sh, sl) = two_sum xh yh in
  let (th, tl) = two_sum xl yl in
  let c = sl +. th in
  let (vh, vl) = fast_two_sum sh c in
  let w = tl +. vl in
  let e = mul_up_fp u (add_up_fp (abs_float c) (abs_float w)) in
  (fast_two_sum vh w, e)

let widen_up (zh, zl) f = fast_two_sum zh (add_up_fp zl f)

let add_dw_up x y = let (d, e) = plus_dw_dw_err x y in widen_up d e

let well_formed (h, l) = h +. l = h

(* the high word decides the class, and minus infinity there is the failure *)
let fails x y =
  let (h, _) = add_dw_up x y in h = neg_infinity

let () =
  Random.self_init ();
  let found = ref None and tried = ref 0 in
  let try_pair x y =
    if well_formed x && well_formed y then begin
      incr tried;
      if fails x y && !found = None then found := Some (x, y)
    end in
  (* both words as large in magnitude as a double word allows, near the top *)
  for _ = 1 to 200000 do
    let e = 1023 - Random.int 3 in
    let xh = -. Float.ldexp (1.0 +. Random.float 1.0) e in
    let yh = -. Float.ldexp (1.0 +. Random.float 1.0) e in
    let ulp v = let (_, k) = Float.frexp v in Float.ldexp 1.0 (k - 53) in
    let lows v = [ ulp v /. 2.; -. (ulp v) /. 2.; ulp v /. 4.;
                   -. (ulp v) /. 4.; 0.0 ] in
    List.iter (fun xl ->
      List.iter (fun yl -> try_pair (xh, xl) (yh, yl)) (lows yh)) (lows xh)
  done;
  (* and the extreme corner, spelled out *)
  let m = max_float in
  List.iter (fun xl -> List.iter (fun yl ->
      try_pair (-. m, xl) (-. m, yl))
      [ 0.0; -. Float.ldexp 1.0 970; Float.ldexp 1.0 970 ])
    [ 0.0; -. Float.ldexp 1.0 970; Float.ldexp 1.0 970 ];
  Printf.printf "well formed pairs tried %d\n" !tried;
  match !found with
  | None -> print_endline "no result with minus infinity as high word"
  | Some ((xh, xl), (yh, yl)) ->
    Printf.printf "FAILS: xh=%h xl=%h yh=%h yl=%h\n" xh xl yh yl
