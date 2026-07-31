(* V0 .. V4 : bare skeleton -> real search shape, one ingredient at a time,
   at the SAME depth throughout.  Mirrors steps.v exactly and uses Rocq's own
   move tables (cubedata.ml, generated from mtis / sfti / eprim / masks), so
   the trees are identical and the node counts must agree. *)

open Cubedata

let nfacelet = 48
let nmoves = 18
let nfcube = 6
let nedge = 12
let ncoord = 24

let fcpos k = k / 3
let oppf f = (f + 3) mod nfcube
let okfc0 p f = if p < nfcube then f <> p && not (f = oppf p && p < f) else true

(* rebuilt per node, exactly as Rocq's allowedr is *)
let allow p =
  let r = ref [] in
  for k = nmoves - 1 downto 0 do
    if okfc0 p (fcpos k) then r := k :: !r
  done; !r

(* comp_tabi : c.(i) = b.(a.(i)), into a fresh array *)
let comp a b =
  let c = Array.make nfacelet 0 in
  for i = 0 to nfacelet - 1 do c.(i) <- b.(a.(i)) done; c

(* inv_tabi *)
let inv a =
  let c = Array.make nfacelet 0 in
  for i = 0 to nfacelet - 1 do c.(a.(i)) <- i done; c

let bit m i = (m lsr i) land 1 = 1

(* ecoordi : packn over 24 positions *)
let ecoordi u =
  let acc = ref 0 in
  for k = 0 to ncoord - 1 do
    let b =
      if k < nedge then not (bit pmask u.(eprim.(k)))
      else bit smask u.(eprim.(k - nedge))
    in
    if b then acc := !acc lor (1 lsl k)
  done; !acc

let coordi a = ecoordi (inv a)

let hsyn x = x land 3

let eq_ident a =
  let r = ref true in
  for i = 0 to nfacelet - 1 do if a.(i) <> i then r := false done; !r

(* ---- V0 : the skeleton -------------------------------------------------- *)
let rec v0 d p =
  if d = 0 then 1
  else List.fold_left (fun acc k -> acc + v0 (d-1) (fcpos k)) 1 (allow p)

(* ---- V1 : + carry and compose the cube ---------------------------------- *)
let rec v1 d a p =
  if d = 0 then 1
  else List.fold_left (fun acc k -> acc + v1 (d-1) (comp a moves.(k)) (fcpos k))
         1 (allow p)

(* ---- V2 : + the goal test ----------------------------------------------- *)
let rec v2 d a p =
  if eq_ident a then 1
  else if d = 0 then 1
  else List.fold_left (fun acc k -> acc + v2 (d-1) (comp a moves.(k)) (fcpos k))
         1 (allow p)

(* ---- V3 : + coordinate and heuristic, computed but NOT used ------------- *)
let rec v3 d a p =
  if eq_ident a then 1
  else if d = 0 then 1
  else List.fold_left
         (fun acc k -> (if hsyn (coordi a) = 99 then 1 else 0)
                       + acc + v3 (d-1) (comp a moves.(k)) (fcpos k))
         1 (allow p)

(* ---- V4 : + prune on it -- the real search shape ------------------------ *)
let rec v4 d a p =
  if hsyn (coordi a) <= d then
    (if eq_ident a then 1
     else if d = 0 then 1
     else List.fold_left (fun acc k -> acc + v4 (d-1) (comp a moves.(k)) (fcpos k))
            1 (allow p))
  else 1

(* ---- V5 : V4 with PREALLOCATED per-depth arrays (no allocation) --------- *)
let buf  = Array.init 40 (fun _ -> Array.make nfacelet 0)
let ibuf = Array.init 40 (fun _ -> Array.make nfacelet 0)

let comp_into dst a b =
  for i = 0 to nfacelet - 1 do dst.(i) <- b.(a.(i)) done

let coordi_into iv a =
  for i = 0 to nfacelet - 1 do iv.(a.(i)) <- i done;
  let acc = ref 0 in
  for k = 0 to ncoord - 1 do
    let b =
      if k < nedge then not (bit pmask iv.(eprim.(k)))
      else bit smask iv.(eprim.(k - nedge))
    in
    if b then acc := !acc lor (1 lsl k)
  done; !acc

let rec v5 d a p =
  if hsyn (coordi_into ibuf.(d) a) <= d then
    (if eq_ident a then 1
     else if d = 0 then 1
     else List.fold_left (fun acc k ->
            let nx = buf.(d) in
            comp_into nx a moves.(k);
            acc + v5 (d-1) nx (fcpos k)) 1 (allow p))
  else 1

(* ---- V6 : V5 but the coordinate is LOOKED UP, not rebuilt --------------- *)
let memo : (int * int, int) Hashtbl.t = Hashtbl.create 1000003

let rec v6 d a x p =
  if hsyn x <= d then
    (if eq_ident a then 1
     else if d = 0 then 1
     else List.fold_left (fun acc k ->
            let nx = buf.(d) in
            comp_into nx a moves.(k);
            let x' =
              match Hashtbl.find_opt memo (x, k) with
              | Some v -> v
              | None -> let v = coordi_into ibuf.(d) nx in
                        Hashtbl.add memo (x, k) v; v
            in
            acc + v6 (d-1) nx x' (fcpos k)) 1 (allow p))
  else 1

let bench name f =
  Gc.full_major ();
  let w0 = Gc.minor_words () +. (Gc.quick_stat ()).Gc.major_words in
  let t0 = Unix.gettimeofday () in
  let n = f () in
  let t1 = Unix.gettimeofday () in
  let w1 = Gc.minor_words () +. (Gc.quick_stat ()).Gc.major_words in
  let dt = t1 -. t0 in
  Printf.printf "%-3s nodes=%-9d %9.5f s  %12.0f nodes/s  %7.1f words/node\n%!"
    name n dt (float_of_int n /. dt) ((w1 -. w0) /. float_of_int n)

let () =
  let d = try int_of_string Sys.argv.(1) with _ -> 5 in
  Printf.printf "depth %d\n%!" d;
  bench "V0" (fun () -> v0 d nfcube);
  bench "V1" (fun () -> v1 d sfti nfcube);
  bench "V2" (fun () -> v2 d sfti nfcube);
  bench "V3" (fun () -> v3 d sfti nfcube);
  bench "V4" (fun () -> v4 d sfti nfcube);
  bench "V5" (fun () -> v5 d sfti nfcube);
  Hashtbl.reset memo;
  bench "V6" (fun () -> v6 d sfti (coordi sfti) nfcube);
  bench "V6b" (fun () -> v6 d sfti (coordi sfti) nfcube)
