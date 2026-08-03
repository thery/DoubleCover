(* The phase 1 table -- twist x flip x slice, 2 217 093 120 states -- built in
   the ROCQ coordinate, so it can be emitted as Rocq literals directly.

   ocaml/rubik_par.ml builds the same table from a corner/edge cube model.  The
   values must agree; only the slot numbering differs.  The check that costs
   nothing and needs no bridge is the DEPTH HISTOGRAM: how many states sit at
   each BFS level.  Two programs on two cube models must produce the same
   counts, level for level.

   usage: p1gen [cap] [mode]   cap defaults to 9, as rubik_par's does
     (none)     the depth histogram
     search N   rubik_par's search, in the Rocq coordinate
     corner     the corner laws, measured on random walks
     acttwi     Phase1.v's acttwiE, checked before it is proved
     small      emit ../P1Small.v: srank and the twist move table
     emit [a b] emit ../P1_00.v .. ../P1_70.v and ../P1Table.v: the table
                itself, 2.9 GB.  a and b bound the chunk range, so the
                emission can be split over several cores.  See ../mkp1.sh *)

open Cubedata

let nfacelet = 48
let nmoves = 18
let ntwist = 2187
let nslice = 495
let nfs = 1013760                       (* 2048 flip x 495 slice *)

(* ---- the shape of the emitted table, all of it constant ------------------ *)
(* Four bits per entry, fifteen per int63 word -- the true distance 0 .. cap+1,
   never clamped from below.  Storing d - base and clamping the underflow to 0
   would report base for a state that is really nearer, which OVERSTATES the
   distance and is not admissible.  Clamping from above is the safe direction
   and is what cap already does. *)

let nper = 15                           (* entries per int63 word            *)
let nwidth = 4                          (* bits per entry                    *)
let n_all_c = ntwist * nfs
let words = (n_all_c + nper - 1) / nper
let cwlog = 21                          (* Phase1.v's cwlog                  *)
let cwords = 1 lsl cwlog
let nchunk = (words + cwords - 1) / cwords

let time name f =
  let t = Unix.gettimeofday () in
  let r = f () in
  Printf.printf "  %-38s %7.2f s\n%!" name (Unix.gettimeofday () -. t); r

(* ---- permutations, exactly as gen.ml and Rocq's comp_tabi / inv_tabi ----- *)

let comp a b = Array.init nfacelet (fun i -> b.(a.(i)))
let comp_into dst a b = for i = 0 to nfacelet - 1 do dst.(i) <- b.(a.(i)) done
let inv_into dst a = for i = 0 to nfacelet - 1 do dst.(a.(i)) <- i done
let ident = Array.init nfacelet (fun i -> i)
let bit m i = (m lsr i) land 1 = 1

(* ---- the flip x slice coordinate, Coordfs's packn over 24 positions ------ *)

let ecoordi u =
  let acc = ref 0 in
  for k = 0 to 23 do
    let b = if k < 12 then not (bit pmask u.(eprim.(k)))
            else bit smask u.(eprim.(k - 12)) in
    if b then acc := !acc lor (1 lsl k)
  done; !acc

(* ---- the twist coordinate, over corner data DERIVED from the moves ------- *)

(* A facelet is a corner facelet iff f mod 8 is in {0,2,5,7}; two of them sit
   on the same cubie iff exactly the same face turns move them.

   The U/D axis is NOT a free choice.  It must be the axis the flip x slice
   coordinate already uses -- the two faces whose turns leave the slice alone.
   Phase1.v's cprim/ctrip put it on a different axis, which makes twist and
   flip x slice quotients along different axes; their product is then not
   Kociemba's phase 1 coordinate at all, and every BFS level comes out too
   large.  Hence: derive, do not transcribe. *)

let is_corner f = let m = f mod 8 in m = 0 || m = 2 || m = 5 || m = 7
let moved_by x = Array.init 6 (fun f -> moves.(3 * f).(x) <> x)

(* Move group k/3 and facelet block f/8 are DIFFERENT numberings: moves.(9) is
   group 3 but it is block 5 that spins in place under it.  The block of a
   group is the one the turn permutes within itself. *)
let block_of_group g =
  let b = ref (-1) in
  for k = 0 to 5 do
    let inside = ref true in
    for i = 8 * k to 8 * k + 7 do
      if moves.(3 * g).(i) / 8 <> k then inside := false
    done;
    if !inside && moves.(3 * g).(8 * k) <> 8 * k then b := k
  done;
  if !b < 0 then (Printf.eprintf "no block spins under group %d\n" g; exit 1);
  !b

let ctrip = Array.make 8 (0, 0, 0)
let is_cprim = Array.make nfacelet false

(* udf : the two MOVE GROUPS of the U/D axis; their blocks carry the stickers *)
let derive_corners udf =
  let b1 = block_of_group (fst udf) and b2 = block_of_group (snd udf) in
  Printf.printf "U/D facelet blocks: %d and %d\n%!" b1 b2;
  let onud f = f / 8 = b1 || f / 8 = b2 in
  let corners = ref [] in
  for x = 0 to nfacelet - 1 do
    if is_corner x && onud x then corners := x :: !corners
  done;
  let corners = List.sort compare !corners in
  if List.length corners <> 8 then
    (Printf.eprintf "expected 8 U/D corner stickers, got %d\n"
       (List.length corners); exit 1);
  List.iteri (fun i c0 ->
    let m0 = moved_by c0 in
    let others = ref [] in
    for x = 0 to nfacelet - 1 do
      if x <> c0 && is_corner x && moved_by x = m0 then others := x :: !others
    done;
    match List.sort compare !others with
    | [c1; c2] -> ctrip.(i) <- (c0, c1, c2); is_cprim.(c0) <- true
    | l -> Printf.eprintf "corner %d has %d partners\n" c0 (List.length l);
           exit 1)
    corners;
  (* The cyclic order is NOT free.  Sorting the other two stickers gives a
     different sense per corner, and then corner orientation is not an action
     at all.  A coherent order is exactly one for which the 3-cycle rotating
     every corner in place COMMUTES with every move -- Phase1.v's cubcP.
     Exactly two of the 2 ^ 8 choices qualify (the two chiralities); take the
     smaller mask. *)
  let coherent mask =
    let tri = Array.mapi (fun i (a, b, c) ->
      if (mask lsr i) land 1 = 1 then (a, c, b) else (a, b, c)) ctrip in
    let cc = Array.init nfacelet (fun x -> x) in
    Array.iter (fun (a, b, c) -> cc.(a) <- b; cc.(b) <- c; cc.(c) <- a) tri;
    let ok = ref true in
    for k = 0 to nmoves - 1 do
      for x = 0 to nfacelet - 1 do
        if cc.(moves.(k).(x)) <> moves.(k).(cc.(x)) then ok := false
      done
    done; !ok in
  let m = ref (-1) in
  for mask = 255 downto 0 do if coherent mask then m := mask done;
  if !m < 0 then (prerr_endline "no coherent cyclic order"; exit 1);
  Printf.printf "coherent cyclic order: mask %d\n%!" !m;
  Array.iteri (fun i (a, b, c) ->
    if (!m lsr i) land 1 = 1 then ctrip.(i) <- (a, c, b)) (Array.copy ctrip)

(* foldr (fun t x -> x * 3 + corient u t) 0 (take 7 ctrip) *)
let ectwist u =
  let acc = ref 0 in
  for i = 6 downto 0 do
    let (c0, c1, _) = ctrip.(i) in
    let o = if is_cprim.(u.(c0)) then 0 else if is_cprim.(u.(c1)) then 1 else 2 in
    acc := !acc * 3 + o
  done; !acc

(* ---- emitting Rocq literals --------------------------------------------- *)
(* top level, because two modes emit: `small`, which stops after the move
   tables, and `emit`, which needs the whole BFS behind it *)

let emit_seq oc name n f =
  Printf.fprintf oc "Definition %s : seq int := [::\n" name;
  for i = 0 to n - 1 do
    Printf.fprintf oc "%d%s" (f i)
      (if i = n - 1 then "" else if i mod 8 = 7 then ";\n" else "; ")
  done;
  Printf.fprintf oc "]%%uint63.\n\n"

let header oc what =
  Printf.fprintf oc
    "(* GENERATED by bench/p1gen.ml -- do not edit.                    *)\n\
     (* %s *)\n\n\
     From Stdlib Require Import Uint63.\n\
     From mathcomp Require Import all_ssreflect.\n\n" what

(* ---- the glue file, which depends on nothing but the constants ---------- *)
(* Each chunk becomes an array of its own length, and the default 0 is what an
   index past the end reads -- a distance of 0, which UNDERstates and so stays
   admissible.  Valid indices never reach it.

   Written by its own mode as well as by `emit', so the text can be iterated on
   without paying the two minute BFS again. *)

let emit_table () =
  let oc = open_out "../P1Table.v" in
  Printf.fprintf oc
    "(* GENERATED by bench/p1gen.ml -- do not edit.                     *)\n\
     (* The phase 1 table: %d chunks of at most %d words, glued.  *)\n\
     (*                                                                 *)\n\
     (* This file costs about %0.1f GB of .vo.  Phase1.v does NOT        *)\n\
     (* require it: the table is a Section variable there, and p1dummy   *)\n\
     (* is what the development uses until the certificate is actually   *)\n\
     (* being checked.  Build it with ../mkp1.sh, on roquableu.          *)\n\n\
     From Stdlib Require Import Uint63.\n\
     From Stdlib Require Import -(notations) PArray.\n\
     From mathcomp Require Import all_ssreflect.\n\
     From Rubik Require Import ssrint63.\n\
     Require Import Phase1"
    nchunk cwords (float_of_int nchunk *. 0.063);
  for i = 0 to nchunk - 1 do Printf.fprintf oc "\n        P1_%02d" i done;
  Printf.fprintf oc ".\n\n";
  Printf.fprintf oc "Definition p1tab : PArray.array (PArray.array int) :=\n";
  Printf.fprintf oc
    "  let a := PArray.make %d%%uint63 (PArray.make 1%%uint63 0%%uint63) in\n"
    nchunk;
  for i = 0 to nchunk - 1 do
    let lo = i * cwords in
    let hi = min (lo + cwords) words in
    Printf.fprintf oc
      "  let a := PArray.set a %d%%uint63 (mkarr %d%%uint63 0%%uint63 \
       p1_chunk_%02d) in\n" i (hi - lo) i
  done;
  Printf.fprintf oc "  a.\n";
  close_out oc;
  Printf.printf "wrote ../P1Table.v: %d chunks\n%!" nchunk

let () =
  let cap = try int_of_string Sys.argv.(1) with _ -> 9 in
  Printf.printf "phase 1 generator, Rocq coordinate, cap %d\n%!" cap;

  (* the glue file alone: no BFS, no table, milliseconds *)
  if Array.length Sys.argv > 2 && Sys.argv.(2) = "table" then
    (emit_table (); exit 0);

  (* ---- srank : 12 bit slice mask -> rank among the 495 with 4 bits set --- *)
  let srank = Array.make 4096 nslice in
  let r = ref 0 in
  for m = 0 to 4095 do
    let p = ref 0 in
    for i = 0 to 11 do if bit m i then incr p done;
    if !p = 4 then (srank.(m) <- !r; incr r)
  done;
  Printf.printf "srank: %d masks with four bits set\n%!" !r;
  let fsidx c = (c land 2047) * nslice + srank.(c lsr 12) in

  let iv = Array.make nfacelet 0 in
  let coordi a = inv_into iv a; ecoordi iv in

  (* the U/D axis, read off the flip x slice coordinate itself: the two faces
     whose quarter turn leaves the slice alone *)
  let slice_of a = srank.((coordi a) lsr 12) in
  let s0 = slice_of ident in
  let udl = ref [] in
  for f = 0 to 5 do
    if slice_of moves.(3 * f) = s0 then udl := f :: !udl
  done;
  let udf = match List.sort compare !udl with
    | [a; b] -> (a, b)
    | l -> Printf.eprintf "U/D axis: expected 2 faces, got %d\n"
             (List.length l); exit 1 in
  Printf.printf "U/D axis: faces %d and %d\n%!" (fst udf) (snd udf);
  derive_corners udf;
  Printf.printf "cprim = [%s]\n"
    (String.concat "; "
       (Array.to_list (Array.map (fun (c, _, _) -> string_of_int c) ctrip)));
  Printf.printf "ctrip = [%s]\n%!"
    (String.concat "; "
       (Array.to_list (Array.map (fun (a, b, c) ->
          Printf.sprintf "(%d,%d,%d)" a b c) ctrip)));

  let ctwist a = inv_into iv a; ectwist iv in

  (* ---- BFS the two coordinate spaces, keeping a representative ----------- *)

  let bfs_reps size idx =
    let rep = Array.make size [||] and seen = Array.make size false in
    let cnt = ref 0 and q = Queue.create () in
    let i0 = idx ident in
    rep.(i0) <- ident; seen.(i0) <- true; incr cnt; Queue.add ident q;
    while not (Queue.is_empty q) do
      let a = Queue.pop q in
      for k = 0 to nmoves - 1 do
        let b = comp a moves.(k) in
        let i = idx b in
        if not seen.(i) then
          (rep.(i) <- b; seen.(i) <- true; incr cnt; Queue.add b q)
      done
    done;
    (rep, !cnt) in

  let twrep, twcnt =
    time "BFS the twist space" (fun () -> bfs_reps ntwist ctwist) in
  Printf.printf "twist: reached %d of %d\n%!" twcnt ntwist;
  let fsrep, fscnt =
    time "BFS the flip x slice space" (fun () ->
      bfs_reps nfs (fun a -> fsidx (coordi a))) in
  Printf.printf "flip x slice: reached %d of %d\n%!" fscnt nfs;

  (* ---- the coordinate move tables --------------------------------------- *)

  let scratch = Array.make nfacelet 0 in
  let twmove = Array.make (ntwist * nmoves) 0 in
  time "twist move table" (fun () ->
    for i = 0 to ntwist - 1 do
      for k = 0 to nmoves - 1 do
        comp_into scratch twrep.(i) moves.(k);
        twmove.(i * nmoves + k) <- ctwist scratch
      done
    done);
  let fsmove = Array.make (nfs * nmoves) 0 in
  time "flip x slice move table" (fun () ->
    for i = 0 to nfs - 1 do
      for k = 0 to nmoves - 1 do
        comp_into scratch fsrep.(i) moves.(k);
        fsmove.(i * nmoves + k) <- fsidx (coordi scratch)
      done
    done);

  (* ---- are they well defined?  step a random walk both ways -------------- *)
  (* the move tables are read off ONE representative per coordinate; they are
     only meaningful if every other cube with the same coordinate steps to the
     same place.  Walk at random and compare cube level against table level. *)

  let viol = ref 0 in
  time "move tables vs cube composition" (fun () ->
    let a = ref ident and st = Random.State.make [|20260801|] in
    for _ = 0 to 2_000_000 do
      let k = Random.State.int st nmoves in
      let b = comp !a moves.(k) in
      let t = ctwist !a and f = fsidx (coordi !a) in
      if twmove.(t * nmoves + k) <> ctwist b then incr viol;
      if fsmove.(f * nmoves + k) <> fsidx (coordi b) then incr viol;
      a := b
    done);
  Printf.printf "move table violations: %d\n%!" !viol;
  if !viol > 0 then (prerr_endline "MOVE TABLES ARE NOT WELL DEFINED"; exit 1);

  (* ---- the two SMALL tables, emitted before the big BFS ------------------ *)
  (* srank is 4096 numbers and twmove is 39 366: a quarter of a megabyte, so
     they are checked in and Phase1.v requires them unconditionally.  The
     phase 1 table itself is 2.9 GB of literals and is not.  Nothing after
     this point is needed, so the mode stops here. *)

  if Array.length Sys.argv > 2 && Sys.argv.(2) = "small" then begin
    let oc = open_out "../P1Small.v" in
    header oc "srank, and the twist move table.";
    emit_seq oc "srank_data" 4096 (fun i -> srank.(i));
    emit_seq oc "twmove_data" (ntwist * nmoves) (fun i -> twmove.(i));
    close_out oc;
    let sz = (Unix.stat "../P1Small.v").Unix.st_size in
    Printf.printf "wrote ../P1Small.v: %.2f MB\n%!"
      (float_of_int sz /. 1048576.0);
    exit 0
  end;

  (* ---- twist x slice, rubik_par's second table -------------------------- *)
  (* the slice moves on its own: fsidx is flip * nslice + slice, and the slice
     part of a move depends only on the slice part *)

  let slmove = Array.make (nslice * nmoves) 0 in
  for s = 0 to nslice - 1 do
    for k = 0 to nmoves - 1 do
      slmove.(s * nmoves + k) <- fsmove.(s * nmoves + k) mod nslice
    done
  done;
  (* flip x slice on its own, rubik_par's first table *)
  let pfs = Bytes.make nfs '\255' in
  Bytes.set pfs (fsidx (coordi ident)) '\000';
  time "BFS flip x slice distance" (fun () ->
    let cur = ref 0 and go = ref true in
    while !go do
      let added = ref 0 in
      for i = 0 to nfs - 1 do
        if Char.code (Bytes.unsafe_get pfs i) = !cur then
          for k = 0 to nmoves - 1 do
            let j = fsmove.(i * nmoves + k) in
            if Char.code (Bytes.unsafe_get pfs j) = 255 then
              (Bytes.unsafe_set pfs j (Char.unsafe_chr (!cur + 1)); incr added)
          done
      done;
      if !added = 0 then go := false else incr cur
    done);
  let fsmax = ref 0 and fsfill = ref 0 in
  Bytes.iter (fun c -> let v = Char.code c in
    if v < 255 then (incr fsfill; if v > !fsmax then fsmax := v)) pfs;
  Printf.printf "flip x slice: %d of %d filled, max depth %d\n%!"
    !fsfill nfs !fsmax;

  let nts = ntwist * nslice in
  let pts = Bytes.make nts '\255' in
  Bytes.set pts (ctwist ident * nslice + slice_of ident) '\000';
  time "BFS twist x slice" (fun () ->
    let cur = ref 0 and go = ref true in
    while !go do
      let added = ref 0 in
      for i = 0 to nts - 1 do
        if Char.code (Bytes.unsafe_get pts i) = !cur then begin
          let t = i / nslice and s = i mod nslice in
          for k = 0 to nmoves - 1 do
            let j = twmove.(t * nmoves + k) * nslice
                    + slmove.(s * nmoves + k) in
            if Char.code (Bytes.unsafe_get pts j) = 255 then
              (Bytes.unsafe_set pts j (Char.unsafe_chr (!cur + 1)); incr added)
          done
        end
      done;
      if !added = 0 then go := false else incr cur
    done);
  let tsmax = ref 0 and tsfill = ref 0 in
  Bytes.iter (fun c -> let v = Char.code c in
    if v < 255 then (incr tsfill; if v > !tsmax then tsmax := v)) pts;
  Printf.printf "twist x slice: %d of %d filled, max depth %d\n%!"
    !tsfill nts !tsmax;

  (* ---- the phase 1 BFS, index = twist * nfs + fsidx ---------------------- *)

  let n_all = ntwist * nfs in
  Printf.printf "phase 1 space: %d states (%.2f GB as bytes)\n%!"
    n_all (float_of_int n_all /. 1073741824.0);
  let p = Bytes.make n_all (Char.chr (cap + 1)) in
  let i0 = ctwist ident * nfs + fsidx (coordi ident) in
  Bytes.set p i0 '\000';
  let hist = Array.make (cap + 2) 0 in
  hist.(0) <- 1;
  let t0 = Unix.gettimeofday () in
  for cur = 0 to cap - 1 do
    let added = ref 0 in
    for t = 0 to ntwist - 1 do
      let tb = t * nmoves and base = t * nfs in
      for f = 0 to nfs - 1 do
        if Char.code (Bytes.unsafe_get p (base + f)) = cur then begin
          let fb = f * nmoves in
          for k = 0 to nmoves - 1 do
            let j = Array.unsafe_get twmove (tb + k) * nfs
                    + Array.unsafe_get fsmove (fb + k) in
            if Char.code (Bytes.unsafe_get p j) > cur + 1 then begin
              Bytes.unsafe_set p j (Char.unsafe_chr (cur + 1)); incr added
            end
          done
        end
      done
    done;
    hist.(cur + 1) <- !added;
    Printf.printf "   depth %2d -> %12d states (%.0f s)\n%!"
      (cur + 1) !added (Unix.gettimeofday () -. t0)
  done;

  (* ---- the three axis views, DERIVED ------------------------------------ *)
  (* rubik_par takes h as the max over three axis rotations -- conjugation by
     the 120 degree turn about a corner, which permutes the six faces in two
     3-cycles.  Which Rocq move groups those are is not guessable, so find the
     rotation: an order 3 element of the symmetry group that permutes the move
     set.  {1, r, r^2} are then the three views. *)

  let sy = [|2;4;7;1;6;0;3;5;32;33;34;35;36;37;38;39;8;9;10;11;12;13;14;15;
             16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;
             45;43;40;46;41;47;44;42|] in
  let sx = [|39;38;37;36;35;34;33;32;13;11;8;14;9;15;12;10;0;1;2;3;4;5;6;7;
             26;28;31;25;30;24;27;29;47;46;45;44;43;42;41;40;
             16;17;18;19;20;21;22;23|] in
  let sm = [|2;1;0;4;3;7;6;5;26;25;24;28;27;31;30;29;18;17;16;20;19;23;22;21;
             10;9;8;12;11;15;14;13;34;33;32;36;35;39;38;37;
             42;41;40;44;43;47;46;45|] in
  let inv a = let c = Array.make nfacelet 0 in
              for i = 0 to nfacelet - 1 do c.(a.(i)) <- i done; c in
  let group gens =
    let seen = Hashtbl.create 64 in
    let rec add a = let k = Array.to_list a in
      if not (Hashtbl.mem seen k) then begin
        Hashtbl.add seen k a; List.iter (fun g -> add (comp a g)) gens end in
    add ident; Hashtbl.fold (fun _ v acc -> v :: acc) seen [] in
  let syms = group [sy; sx; sm] in
  (* r is usable iff order 3 and conjugation sends every move to a move *)
  let permutes_moves r =
    let ri = inv r in
    let idx = Array.make nmoves (-1) in
    (try
       for k = 0 to nmoves - 1 do
         let c = comp ri (comp moves.(k) r) in
         let j = ref (-1) in
         for m = 0 to nmoves - 1 do if moves.(m) = c then j := m done;
         if !j < 0 then raise Exit; idx.(k) <- !j
       done; Some idx
     with Exit -> None) in
  let order3 = List.filter (fun r ->
    r <> ident && comp r (comp r r) = ident) syms in
  let rot = List.find_opt (fun r -> permutes_moves r <> None) order3 in
  let mv = match rot with
    | None -> Printf.eprintf "no order 3 rotation permutes the moves\n"; exit 1
    | Some r ->
      let i1 = match permutes_moves r with Some x -> x | None -> assert false in
      let r2 = comp r r in
      let i2 = match permutes_moves r2 with Some x -> x | None -> assert false in
      [| Array.init nmoves (fun m -> m); i1; i2 |] in
  Printf.printf "three views: move relabellings %s / %s\n%!"
    (String.concat "," (Array.to_list (Array.map string_of_int mv.(1))))
    (String.concat "," (Array.to_list (Array.map string_of_int mv.(2))));

  (* the rotation itself, as a facelet table, so Rocq is GIVEN it rather than
     guessing which product of Sy and Sx it is.  Printed in Rocq syntax. *)
  if Array.length Sys.argv > 2 && Sys.argv.(2) = "views" then begin
    let rot = match rot with Some r -> r | None -> assert false in
    let pr name a =
      Printf.printf "Definition %s : seq nat :=\n  [:: %s]%%N.\n\n" name
        (String.concat "; " (Array.to_list (Array.map string_of_int a))) in
    pr "rot3t" rot;
    pr "mv3a" mv.(1);
    pr "mv3b" mv.(2);
    (* and the check Rocq will have to reproduce: conjugation by rot sends
       move k to move mv1 k, and by rot^2 to mv2 k *)
    let ri = inv rot in
    let bad = ref 0 in
    for k = 0 to nmoves - 1 do
      if comp ri (comp moves.(k) rot) <> moves.(mv.(1).(k)) then incr bad;
      let r2 = comp rot rot in
      if comp (inv r2) (comp moves.(k) r2) <> moves.(mv.(2).(k)) then incr bad
    done;
    Printf.printf "(* relabelling check: %d mismatches of %d *)\n%!"
      !bad (2 * nmoves);
    exit 0
  end;

  (* ---- the search, mimicking rubik_par's dfs ----------------------------- *)

  if Array.length Sys.argv > 2 && Sys.argv.(2) = "search" then begin
    let target = try int_of_string Sys.argv.(3) with _ -> 14 in
    let maxd = 24 in
    let cube = Array.init maxd (fun _ -> Array.make nfacelet 0) in
    let tw = Array.make_matrix maxd 3 0 in
    let fs = Array.make_matrix maxd 3 0 in
    let nodes = ref 0L in
    let heur d =
      let h = ref 0 in
      for k = 0 to 2 do
        let t = tw.(d).(k) and f = fs.(d).(k) in
        let a = Char.code (Bytes.unsafe_get pfs f) in
        let b = Char.code (Bytes.unsafe_get pts (t * nslice + f mod nslice)) in
        let c = Char.code (Bytes.unsafe_get p (t * nfs + f)) in
        if a > !h then h := a;
        if b > !h then h := b;
        if c > !h then h := c
      done; !h in
    let opp f = (f + 3) mod 6 in
    let step d m =
      let d' = d + 1 in
      comp_into cube.(d') cube.(d) moves.(m);
      for k = 0 to 2 do
        let mk = mv.(k).(m) in
        tw.(d').(k) <- twmove.(tw.(d).(k) * nmoves + mk);
        fs.(d').(k) <- fsmove.(fs.(d).(k) * nmoves + mk)
      done in
    let rec dfs d rem prev =
      nodes := Int64.add !nodes 1L;
      let h = heur d in
      if h = 0 && cube.(d) = ident then true
      else if h > rem || rem = 0 then false
      else begin
        let found = ref false and m = ref 0 in
        while not !found && !m < nmoves do
          let f = !m / 3 in
          if not (f = prev || (f = opp prev && f > prev)) then begin
            step d !m;
            if dfs (d + 1) (rem - 1) f then found := true
          end;
          incr m
        done; !found
      end in
    for t = 1 to target do
      Array.blit sfti 0 cube.(0) 0 nfacelet;
      for k = 0 to 2 do
        tw.(0).(k) <- ctwist sfti; fs.(0).(k) <- fsidx (coordi sfti) done;
      nodes := 0L;
      let t0 = Unix.gettimeofday () in
      let found = ref false in
      List.iter (fun m ->
        if not !found then begin
          step 0 m;
          if dfs 1 (t - 1) 0 then found := true
        end) [0; 1];
      Printf.printf "depth %2d : %14Ld nodes, %8.1f s, solution %b\n%!"
        t !nodes (Unix.gettimeofday () -. t0) !found
    done;
    exit 0
  end;

  (* ---- does corientgM hold?  test before proving ------------------------ *)
  (* Rocq: corientg (g * m) p = (dign (coordtw g) (csrc m p) + cdelta m p) mod 3
     with (g * m) x = m (g x), and g^-1 y = the i with g i = y. *)

  if Array.length Sys.argv > 2 && Sys.argv.(2) = "corner" then begin
    let cflat = Array.make 24 0 in
    Array.iteri (fun i (a, b, c) ->
      cflat.(3*i) <- a; cflat.(3*i+1) <- b; cflat.(3*i+2) <- c) ctrip;
    let idx = Array.make nfacelet (-1) in
    Array.iteri (fun i f -> idx.(f) <- i) cflat;
    let cpos f = idx.(f) / 3 and cslot f = idx.(f) mod 3 in
    let cprimf p = let (a, _, _) = ctrip.(p) in a in
    let pinv = Array.make nfacelet 0 in
    let inv_of a = for i = 0 to nfacelet - 1 do pinv.(a.(i)) <- i done; pinv in
    let corientg a p =                     (* a is the permutation g *)
      let gi = inv_of a in
      let (c0, c1, _) = ctrip.(p) in
      if is_cprim.(gi.(c0)) then 0 else if is_cprim.(gi.(c1)) then 1 else 2 in
    let coordtw_of a =
      let acc = ref 0 in
      for p = 6 downto 0 do acc := !acc * 3 + corientg a p done; !acc in
    let dig x p = (x / (int_of_float (3.0 ** float_of_int p))) mod 3 in
    let dign x p =
      if p = 7 then
        let s = ref 0 in for q = 0 to 6 do s := !s + dig x q done;
        (3 - !s mod 3) mod 3
      else dig x p in
    (* foundation: is corientg g p the slot of the sticker now at p's U/D
       slot, or its negation? *)
    let c1 = ref 0 and c2 = ref 0 and n = ref 0 in
    let st = Random.State.make [|20260801|] in
    let a = ref ident in
    for _ = 0 to 100_000 do
      a := comp !a moves.(Random.State.int st nmoves);
      let gi = Array.copy (inv_of !a) in
      for p = 0 to 7 do
        let want = corientg !a p and s = cslot gi.(cprimf p) in
        incr n;
        if want <> s then incr c1;
        if want <> (3 - s) mod 3 then incr c2
      done
    done;
    Printf.printf "corientg vs cslot      : %d of %d\n" !c1 !n;
    Printf.printf "corientg vs (3-cslot)%%3: %d of %d\n%!" !c2 !n;
    (* and the composition law, four conventions *)
    let variants = Array.make 8 0 and tested = ref 0 in
    let b = ref ident in
    for _ = 0 to 200_000 do
      let k = Random.State.int st nmoves in
      let m = moves.(k) in
      let gm = comp !b m in
      let mi = Array.copy (inv_of m) in
      let cg = coordtw_of !b in
      for p = 0 to 6 do
        let want = corientg gm p in
        let try_one v f =
          let cs = cpos f and cd = cslot f in
          want <> (match v with
            | 0 -> (dign cg cs + cd) mod 3
            | 1 -> (dign cg cs + 3 - cd) mod 3
            | 2 -> (3 - dign cg cs + cd) mod 3
            | _ -> (6 - dign cg cs - cd) mod 3) in
        for v = 0 to 3 do
          if try_one v mi.(cprimf p) then variants.(v) <- variants.(v) + 1;
          if try_one v m.(cprimf p) then variants.(4+v) <- variants.(4+v) + 1
        done;
        incr tested
      done;
      b := gm
    done;
    Array.iteri (fun v c ->
      Printf.printf "  %s cdelta %-5s : %d of %d\n"
        (if v < 4 then "m^-1" else "m   ")
        [|"+"; "-"; "neg+"; "neg-"|].(v mod 4) c !tested) variants;
    exit 0
  end;

  (* ---- does acttwiE hold?  the table action vs the digit formula --------- *)
  (* Rocq: acttwi x k = acttw x (pt 47 mtabs_k), i.e. the emitted 2187 x 18
     table agrees with the computed corner action.  Test before proving. *)

  if Array.length Sys.argv > 2 && Sys.argv.(2) = "acttwi" then begin
    let cflat = Array.make 24 0 in
    Array.iteri (fun i (a, b, c) ->
      cflat.(3*i) <- a; cflat.(3*i+1) <- b; cflat.(3*i+2) <- c) ctrip;
    let idx = Array.make nfacelet (-1) in
    Array.iteri (fun i f -> idx.(f) <- i) cflat;
    let cpos f = idx.(f) / 3 and cslot f = idx.(f) mod 3 in
    let cprimf p = let (a, _, _) = ctrip.(p) in a in
    let pw3 = [|1;3;9;27;81;243;729|] in
    let dign x p =
      if p = 7 then
        (let s = ref 0 in
         for q = 0 to 6 do s := !s + (x / pw3.(q)) mod 3 done;
         (3 - !s mod 3) mod 3)
      else (x / pw3.(p)) mod 3 in
    let bad = ref 0 in
    let mi = Array.make nfacelet 0 in
    for k = 0 to nmoves - 1 do
      inv_into mi moves.(k);
      for x = 0 to ntwist - 1 do
        (* the digit formula, exactly acttw *)
        let got = ref 0 in
        for p = 6 downto 0 do
          let f = mi.(cprimf p) in
          got := !got * 3 + (dign x (cpos f) + 3 - cslot f) mod 3
        done;
        if !got <> twmove.(x * nmoves + k) then incr bad
      done
    done;
    Printf.printf "acttwiE: %d mismatches out of %d\n%!" !bad (ntwist * nmoves);
    exit 0
  end;

  (* ---- emission ---------------------------------------------------------- *)
  (* Four bits per entry, fifteen per int63 word -- the true distance 0..cap+1,
     never clamped from below.  Storing d - base and clamping the underflow to
     0 would report base for a state that is really nearer, which OVERSTATES
     the distance and is not an admissible heuristic.  Clamping from above is
     the safe direction and is what cap already does. *)

  Printf.printf "\nemission: %d words of %d entries, %d chunks of %d\n%!"
    words nper nchunk cwords;

  let word w =
    let v = ref 0 in
    for j = nper - 1 downto 0 do
      let i = w * nper + j in
      let d = if i < n_all then Char.code (Bytes.unsafe_get p i) else 0 in
      v := (!v lsl nwidth) lor d
    done; !v in

  (* one file per chunk, P1_00.v .. P1_70.v, plus P1Table.v which glues them.
     A range may be given -- `emit 3 7' does chunks 3 to 7 -- so the emission
     can be split over several cores; P1Table.v is rewritten either way, since
     it depends only on the chunk COUNT and is a few hundred bytes. *)

  if Array.length Sys.argv > 2 && Sys.argv.(2) = "emit" then begin
    let first = try int_of_string Sys.argv.(3) with _ -> 0 in
    let last = try int_of_string Sys.argv.(4) with _ -> nchunk - 1 in

    (* THE PACKING HAS TO INVERT, and this is the only place it is checked:
       Phase1.p1get reads entry i as nibble i mod 15 of word i / 15, out of
       chunk w >> 21 at offset w land (2 ^ 21 - 1).  Sample it before writing
       gigabytes.  (The Rocq side of the same arithmetic is checked against a
       toy two-chunk array, so both ends are pinned.) *)
    let bad = ref 0 and st = Random.State.make [|20260803|] in
    for _ = 1 to 500_000 do
      (* full_int, not int: Random.int's bound caps at 2 ^ 30 and n_all is
         2 217 093 120 -- it raises Invalid_argument rather than truncating *)
      let i = Random.State.full_int st n_all in
      let w = i / nper and r = i mod nper in
      let c = w lsr 21 and o = w land ((1 lsl 21) - 1) in
      if c * cwords + o <> w then incr bad;
      if (word w lsr (r * nwidth)) land 15
         <> Char.code (Bytes.unsafe_get p i) then incr bad
    done;
    Printf.printf "packing self check: %d mismatches of 500000\n%!" !bad;
    if !bad > 0 then (prerr_endline "PACKING IS WRONG"; exit 1);

    let total = ref 0.0 in
    for i = first to min last (nchunk - 1) do
      let lo = i * cwords in
      let hi = min (lo + cwords) words in
      let fn = Printf.sprintf "../P1_%02d.v" i in
      let oc = open_out fn in
      header oc (Printf.sprintf
        "The phase 1 table, chunk %d of %d: words %d .. %d." i nchunk lo (hi-1));
      emit_seq oc (Printf.sprintf "p1_chunk_%02d" i) (hi - lo)
        (fun j -> word (lo + j));
      close_out oc;
      let sz = float_of_int (Unix.stat fn).Unix.st_size in
      total := !total +. sz;
      Printf.printf "  %s  %6d words  %.1f MB\n%!" fn (hi - lo) (sz /. 1048576.0)
    done;
    Printf.printf "wrote chunks %d .. %d, %.2f GB\n%!"
      first (min last (nchunk - 1)) (!total /. 1073741824.0);

    emit_table ()
  end;

  (* ---- the histogram, which is what rubik_par must reproduce ------------- *)

  let acc = ref 0 in
  Printf.printf "\ndepth histogram (compare against rubik_par):\n";
  for d = 0 to cap do
    acc := !acc + hist.(d);
    Printf.printf "  %2d %14d\n" d hist.(d)
  done;
  Printf.printf "  %2d %14d  (unreached, >= %d)\n" (cap + 1) (n_all - !acc)
    (cap + 1);
  Printf.printf "  total %12d\n%!" n_all
