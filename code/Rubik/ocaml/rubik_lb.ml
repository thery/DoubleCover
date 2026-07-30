(* Prototype for the superflip lower bound: IDA* with admissible pruning
   tables, written the way the Rocq version would be, to measure node counts.

   corners: URF=0 UFL=1 ULB=2 UBR=3 DFR=4 DLF=5 DBL=6 DRB=7
   edges:   UR=0 UF=1 UL=2 UB=3 DR=4 DF=5 DL=6 DB=7 FR=8 FL=9 BL=10 BR=11
   move index = face*3 + t,  face U=0 R=1 F=2 D=3 L=4 B=5,  t: 0=cw 1=half 2=ccw *)

type cube = { cp : int array; co : int array; ep : int array; eo : int array }

let solved () =
  { cp = Array.init 8 (fun i -> i); co = Array.make 8 0;
    ep = Array.init 12 (fun i -> i); eo = Array.make 12 0 }

let mult a b =                      (* a * b : first a, then b *)
  let r = solved () in
  for i = 0 to 7 do
    r.cp.(i) <- a.cp.(b.cp.(i));
    r.co.(i) <- (a.co.(b.cp.(i)) + b.co.(i)) mod 3
  done;
  for i = 0 to 11 do
    r.ep.(i) <- a.ep.(b.ep.(i));
    r.eo.(i) <- (a.eo.(b.ep.(i)) + b.eo.(i)) land 1
  done;
  r

let basic = [|
  (* U *) { cp = [|3;0;1;2;4;5;6;7|]; co = Array.make 8 0;
            ep = [|3;0;1;2;4;5;6;7;8;9;10;11|]; eo = Array.make 12 0 };
  (* R *) { cp = [|4;1;2;0;7;5;6;3|]; co = [|2;0;0;1;1;0;0;2|];
            ep = [|8;1;2;3;11;5;6;7;4;9;10;0|]; eo = Array.make 12 0 };
  (* F *) { cp = [|1;5;2;3;0;4;6;7|]; co = [|1;2;0;0;2;1;0;0|];
            ep = [|0;9;2;3;4;8;6;7;1;5;10;11|]; eo = [|0;1;0;0;0;1;0;0;1;1;0;0|] };
  (* D *) { cp = [|0;1;2;3;5;6;7;4|]; co = Array.make 8 0;
            ep = [|0;1;2;3;5;6;7;4;8;9;10;11|]; eo = Array.make 12 0 };
  (* L *) { cp = [|0;2;6;3;4;1;5;7|]; co = [|0;1;2;0;0;2;1;0|];
            ep = [|0;1;10;3;4;5;9;7;8;2;6;11|]; eo = Array.make 12 0 };
  (* B *) { cp = [|0;1;3;7;4;5;2;6|]; co = [|0;0;1;2;0;0;2;1|];
            ep = [|0;1;2;11;4;5;6;10;8;9;3;7|]; eo = [|0;0;0;1;0;0;0;1;0;0;1;1|] };
|]

let moves =
  Array.init 18 (fun m ->
    let b = basic.(m / 3) in
    match m mod 3 with
    | 0 -> b
    | 1 -> mult b b
    | _ -> mult (mult b b) b)

(* ---- coordinates ------------------------------------------------------- *)

let n_twist = 2187 and n_flip = 2048 and n_slice = 495

let twist c = let s = ref 0 in for i = 6 downto 0 do s := 3 * !s + c.co.(i) done; !s
let flip  c = let s = ref 0 in for i = 10 downto 0 do s := 2 * !s + c.eo.(i) done; !s

let cnk = Array.make_matrix 13 5 0
let () =
  for n = 0 to 12 do
    cnk.(n).(0) <- 1;
    for k = 1 to 4 do
      cnk.(n).(k) <- (if n = 0 then 0 else cnk.(n-1).(k-1) + cnk.(n-1).(k))
    done
  done

let slice c =                       (* rank of the set of UD-slice positions *)
  let a = ref 0 and x = ref 0 in
  for j = 11 downto 0 do
    if c.ep.(j) >= 8 then begin a := !a + cnk.(11 - j).(!x + 1); incr x end
  done;
  !a

(* inverse coordinates, to build the move tables *)
let cube_of_twist t =
  let c = solved () and t = ref t and s = ref 0 in
  for i = 0 to 6 do c.co.(i) <- !t mod 3; s := !s + c.co.(i); t := !t / 3 done;
  c.co.(7) <- (3 - !s mod 3) mod 3; c

let cube_of_flip f =
  let c = solved () and f = ref f and s = ref 0 in
  for i = 0 to 10 do c.eo.(i) <- !f land 1; s := !s + c.eo.(i); f := !f lsr 1 done;
  c.eo.(11) <- !s land 1; c

let cube_of_slice s =
  let c = solved () in
  (* place the four slice edges on the positions whose rank is s *)
  let a = ref s and x = ref 4 in
  let pos = Array.make 12 0 in
  for j = 0 to 11 do
    if !x > 0 && !a >= cnk.(11 - j).(!x) then begin
      a := !a - cnk.(11 - j).(!x); decr x; pos.(j) <- 1
    end
  done;
  let nslice = ref 8 and nother = ref 0 in
  for j = 0 to 11 do
    if pos.(j) = 1 then begin c.ep.(j) <- !nslice; incr nslice end
    else begin c.ep.(j) <- !nother; incr nother end
  done;
  c

let mk_move_table n of_coord coord =
  let t = Array.make_matrix n 18 0 in
  for i = 0 to n - 1 do
    let c = of_coord i in
    for m = 0 to 17 do t.(i).(m) <- coord (mult c moves.(m)) done
  done;
  t

(* ---- pruning tables ----------------------------------------------------- *)

let bfs size succ start =
  let d = Bytes.make size '\255' in
  Bytes.set d start '\000';
  let cur = ref 0 and total = ref 1 in
  (try while true do
    let added = ref 0 in
    for i = 0 to size - 1 do
      if Char.code (Bytes.get d i) = !cur then
        succ i (fun j ->
          if Char.code (Bytes.get d j) = 255 then begin
            Bytes.set d j (Char.chr (!cur + 1)); incr added
          end)
    done;
    total := !total + !added;
    if !added = 0 then raise Exit;
    incr cur
  done with Exit -> ());
  Printf.printf "  table %d entries, filled %d, max depth %d\n%!" size !total !cur;
  d

(* ---- main --------------------------------------------------------------- *)

(* ---- the flip x slice table, in the form Fstab.v reads ------------------- *)

(* The Rocq summary is 24 bits: bit p (p < 12) is the orientation of the edge
   at position p, bit 12 + p says the edge there is a slice edge.  Position
   order is Coordfs.v's eprim, which is this file's edge numbering
   UR UF UL UB DR DF DL DB FR FL BL BR.  A move sends position p's content to
   what was at ep.(p), flipping by eo.(p) -- so src is ep and xbit is eo,
   which is exactly Fstab.v's mdat_of_tab.

   Nothing here is trusted: the table only has to pass check0 and checkStep. *)

let nfs = 1 lsl 24                     (* summaries: 2 ^ 24                   *)
let fs_solved = 0xF lsl 20             (* eo all 0, the four slice edges home *)

let fs_succ x m =
  let ep = moves.(m).ep and eo = moves.(m).eo in
  let r = ref 0 in
  for p = 0 to 11 do
    let q = ep.(p) in
    let fb = ((x lsr q) land 1) lxor eo.(p) in
    let sb = (x lsr (12 + q)) land 1 in
    r := !r lor (fb lsl p) lor (sb lsl (12 + p))
  done;
  !r

(* Truncated at cap: everything not reached by then is given cap + 1, which
   keeps the local check true -- a state at depth cap has a neighbour at
   cap + 1 at worst, and cap <= (cap + 1) + 1.  Unreachable junk keeps
   cap + 1 too, and its neighbours are junk, so it checks as well. *)
let fs_build cap =
  let d = Bytes.make nfs (Char.chr (cap + 1)) in
  Bytes.set d fs_solved '\000';
  let t0 = Unix.gettimeofday () in
  for cur = 0 to cap - 1 do
    let added = ref 0 in
    for i = 0 to nfs - 1 do
      if Char.code (Bytes.get d i) = cur then
        for m = 0 to 17 do
          let j = fs_succ i m in
          if Char.code (Bytes.get d j) > cur + 1 then begin
            Bytes.set d j (Char.chr (cur + 1)); incr added
          end
        done
    done;
    Printf.eprintf "   depth %d -> %d states (%.0f s)\n%!"
      (cur + 1) !added (Unix.gettimeofday () -. t0)
  done;
  d

(* Eight four bit entries to a word, so the word index is a shift. *)
let fs_dump cap =
  let d = fs_build cap in
  let nwords = nfs / 8 in
  Printf.eprintf "packing %d words...\n%!" nwords;
  let buf = Buffer.create (1 lsl 24) in
  Buffer.add_string buf
    "(* GENERATED by rubik_lb dumpfs -- do not edit.                              *)\n\
     (* The flip x slice pruning table, breadth first from the solved summary,    *)\n\
     (* truncated, eight four bit entries per int63 word.                         *)\n\n\
     From Stdlib Require Import Uint63.\n\
     From mathcomp Require Import all_ssreflect.\n\n\
     Definition fsdata : seq int := [::\n";
  for w = 0 to nwords - 1 do
    let v = ref 0 in
    for k = 0 to 7 do
      v := !v lor (Char.code (Bytes.get d (w * 8 + k)) lsl (4 * k))
    done;
    Buffer.add_string buf (string_of_int !v);
    if w < nwords - 1 then Buffer.add_char buf ';';
    if w mod 16 = 15 then Buffer.add_char buf '\n'
    else Buffer.add_char buf ' '
  done;
  Buffer.add_string buf "]%uint63.\n";
  print_string (Buffer.contents buf)

let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "dumpfs" then begin
    let cap = try int_of_string Sys.argv.(2) with _ -> 9 in
    fs_dump cap; exit 0
  end

let () =
  (* validation: the classical 20-move maneuver must produce the superflip *)
  let man = [|0;4;6;15;3;16;3;1;12;16;3;2;11;4;6;5;12;16;1;7|] in
  let c = ref (solved ()) in
  Array.iter (fun m -> c := mult !c moves.(m)) man;
  let sf = !c in
  let ok = ref true in
  for i = 0 to 7 do if sf.cp.(i) <> i || sf.co.(i) <> 0 then ok := false done;
  for i = 0 to 11 do if sf.ep.(i) <> i || sf.eo.(i) <> 1 then ok := false done;
  Printf.printf "20-move maneuver gives the superflip: %b\n%!" !ok;
  if not !ok then exit 1;

  (* validation: every coordinate must survive a decode/encode round trip *)
  let check name n of_coord coord =
    let bad = ref (-1) in
    for i = n - 1 downto 0 do if coord (of_coord i) <> i then bad := i done;
    Printf.printf "%s round trip over %d values: %s\n%!" name n
      (if !bad < 0 then "ok" else Printf.sprintf "FAILS at %d" !bad);
    if !bad >= 0 then exit 1 in
  check "twist" n_twist cube_of_twist twist;
  check "flip"  n_flip  cube_of_flip  flip;
  check "slice" n_slice cube_of_slice slice;

  Printf.printf "building move tables...\n%!";
  let mt_twist = mk_move_table n_twist cube_of_twist twist in
  let mt_flip  = mk_move_table n_flip  cube_of_flip  flip  in
  let mt_slice = mk_move_table n_slice cube_of_slice slice in

  (* Which quotients the heuristic reads.  "all" is the real thing; the other
     two exist to measure what each table is worth, and they also skip the
     build of the tables they do not use -- "fs" never allocates the 2.2 GB. *)
  let mode = try Sys.argv.(3) with _ -> "all" in
  let use_ts = mode <> "fs" and use_all = mode = "all" in
  Printf.printf "heuristic: %s\n%!"
    (match mode with
     | "fs" -> "flip x slice only"
     | "pairs" -> "flip x slice and twist x slice"
     | _ -> "flip x slice, twist x slice, twist x flip x slice");

  Printf.printf "building pruning tables...\n%!";
  let p_fs =                        (* flip x slice *)
    bfs (n_flip * n_slice)
      (fun i k ->
        let f = i / n_slice and s = i mod n_slice in
        for m = 0 to 17 do k (mt_flip.(f).(m) * n_slice + mt_slice.(s).(m)) done)
      0 in
  let p_ts =                        (* twist x slice *)
    if not use_ts then Bytes.create 0 else
    bfs (n_twist * n_slice)
      (fun i k ->
        let t = i / n_slice and s = i mod n_slice in
        for m = 0 to 17 do k (mt_twist.(t).(m) * n_slice + mt_slice.(s).(m)) done)
      0 in

  (* The full phase-1 coordinate, twist x flip x slice = 2 217 093 120 states.
     The BFS is stopped at depth [cap]: everything not reached by then is at
     distance >= cap+1, so handing it cap+1 is still a lower bound.  That is
     what keeps the build affordable -- most states sit at the last levels. *)
  let cap = try int_of_string Sys.argv.(2) with _ -> 9 in
  let n_all = n_twist * n_flip * n_slice in
  if use_all then
    Printf.printf "building phase-1 table (%d states, cap %d)...\n%!" n_all cap;
  let p_all = Bytes.make (if use_all then n_all else 1) (Char.chr (cap + 1)) in
  Bytes.set p_all 0 '\000';
  let t0 = Unix.gettimeofday () in
  for cur = 0 to (if use_all then cap - 1 else -1) do
    let added = ref 0 in
    for t = 0 to n_twist - 1 do
      let mtt = mt_twist.(t) in
      for f = 0 to n_flip - 1 do
        let mtf = mt_flip.(f) in
        let base = (t * n_flip + f) * n_slice in
        for s = 0 to n_slice - 1 do
          if Char.code (Bytes.get p_all (base + s)) = cur then begin
            let mts = mt_slice.(s) in
            for m = 0 to 17 do
              let j = (mtt.(m) * n_flip + mtf.(m)) * n_slice + mts.(m) in
              if Char.code (Bytes.get p_all j) > cur + 1 then begin
                Bytes.set p_all j (Char.chr (cur + 1)); incr added
              end
            done
          end
        done
      done
    done;
    Printf.printf "   depth %d -> %d states (%.0f s)\n%!"
      (cur + 1) !added (Unix.gettimeofday () -. t0)
  done;

  (* the three axis variants: conjugation by the 120 degree rotation about
     URF-DBL relabels the faces U->R->F->U and D->L->B->D.  superflip is fixed
     by it, so the three variants start from the same coordinates. *)
  let sigma = Array.init 18 (fun m ->
    let f = m / 3 and t = m mod 3 in
    let f' = if f < 3 then (f + 1) mod 3 else 3 + ((f - 3 + 1) mod 3) in
    f' * 3 + t) in
  let mv = Array.make_matrix 3 18 0 in
  for m = 0 to 17 do
    mv.(0).(m) <- m;
    mv.(1).(m) <- sigma.(m);
    mv.(2).(m) <- sigma.(sigma.(m))
  done;

  let maxd = 21 in
  let cps = Array.init maxd (fun _ -> Array.make 8 0) in
  let eps = Array.init maxd (fun _ -> Array.make 12 0) in
  let tw = Array.make_matrix maxd 3 0 in
  let fl = Array.make_matrix maxd 3 0 in
  let sl = Array.make_matrix maxd 3 0 in
  let nodes = ref 0L in

  let heur d =
    let h = ref 0 in
    for k = 0 to 2 do
      let a = Char.code (Bytes.get p_fs (fl.(d).(k) * n_slice + sl.(d).(k))) in
      if a > !h then h := a;
      if use_ts then begin
        let b = Char.code (Bytes.get p_ts (tw.(d).(k) * n_slice + sl.(d).(k))) in
        if b > !h then h := b
      end;
      if use_all then begin
        let c = Char.code (Bytes.get p_all
                  ((tw.(d).(k) * n_flip + fl.(d).(k)) * n_slice + sl.(d).(k))) in
        if c > !h then h := c
      end
    done;
    !h in

  let is_solved d =
    (* the search carries the permutations, but the orientations only as
       coordinates, so they have to be read there.  Testing h = 0 instead
       is wrong as soon as the heuristic does not involve every coordinate:
       with flip x slice alone, h = 0 says nothing about the corner twist,
       and a cube with twisted corners is reported solved. *)
    let r = ref (tw.(d).(0) = 0 && fl.(d).(0) = 0) in
    for i = 0 to 7 do if cps.(d).(i) <> i then r := false done;
    for i = 0 to 11 do if eps.(d).(i) <> i then r := false done;
    !r in

  let opp f = (f + 3) mod 6 in
  (* argv 4: "norules" turns the redundancy rules off, to measure them *)
  let use_rules = not (Array.length Sys.argv > 4 && Sys.argv.(4) = "norules") in
  Printf.printf "redundancy rules: %b\n%!" use_rules;

  let rec dfs d rem prev =
    nodes := Int64.add !nodes 1L;
    let h = heur d in
    if h = 0 && is_solved d then true
    else if h > rem then false
    else if rem = 0 then false
    else begin
      let found = ref false in
      let m = ref 0 in
      while not !found && !m < 18 do
        let f = !m / 3 in
        if use_rules && prev >= 0 && (f = prev || (f = opp prev && f > prev)) then ()
        else begin
          let d' = d + 1 in
          let mcp = moves.(!m).cp and mep = moves.(!m).ep in
          for i = 0 to 7 do cps.(d').(i) <- cps.(d).(mcp.(i)) done;
          for i = 0 to 11 do eps.(d').(i) <- eps.(d).(mep.(i)) done;
          for k = 0 to 2 do
            let mk = mv.(k).(!m) in
            tw.(d').(k) <- mt_twist.(tw.(d).(k)).(mk);
            fl.(d').(k) <- mt_flip.(fl.(d).(k)).(mk);
            sl.(d').(k) <- mt_slice.(sl.(d).(k)).(mk)
          done;
          if dfs d' (rem - 1) f then found := true
        end;
        incr m
      done;
      !found
    end in

  (* root: superflip.  it is fixed by all 48 symmetries and is its own
     inverse, so the first move may be taken to be U or U2. *)
  let init () =
    for i = 0 to 7 do cps.(0).(i) <- sf.cp.(i) done;
    for i = 0 to 11 do eps.(0).(i) <- sf.ep.(i) done;
    for k = 0 to 2 do
      tw.(0).(k) <- twist sf; fl.(0).(k) <- flip sf; sl.(0).(k) <- slice sf
    done in

  Printf.printf "superflip coords: twist=%d flip=%d slice=%d  h=%d\n%!"
    (twist sf) (flip sf) (slice sf) (init (); heur 0);

  let target = try int_of_string Sys.argv.(1) with _ -> 19 in
  (try
    for t = 1 to target do
      init ();
      nodes := 0L;
      let t0 = Unix.gettimeofday () in
      (* first move restricted to U (0) and U2 (1) by symmetry *)
      let found = ref false in
      List.iter (fun m ->
        if not !found then begin
          let mcp = moves.(m).cp and mep = moves.(m).ep in
          for i = 0 to 7 do cps.(1).(i) <- cps.(0).(mcp.(i)) done;
          for i = 0 to 11 do eps.(1).(i) <- eps.(0).(mep.(i)) done;
          for k = 0 to 2 do
            let mk = mv.(k).(m) in
            tw.(1).(k) <- mt_twist.(tw.(0).(k)).(mk);
            fl.(1).(k) <- mt_flip.(fl.(0).(k)).(mk);
            sl.(1).(k) <- mt_slice.(sl.(0).(k)).(mk)
          done;
          if dfs 1 (t - 1) 0 then found := true
        end) [0; 1];
      Printf.printf "depth %2d : %14Ld nodes, %8.1f s, solution %b\n%!"
        t !nodes (Unix.gettimeofday () -. t0) !found;
      if !found then raise Exit
    done
  with Exit -> ())
