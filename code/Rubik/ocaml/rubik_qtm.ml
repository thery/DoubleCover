(* The quarter-turn lower bound, prototyped.  Same shape as rubik_par.ml, and
   for the same purpose: to measure how big the job is before anyone writes it
   in Rocq.  It is not part of any proof.

   The claim under test is Reid's, 1998: superflip composed with fourspot
   cannot be solved in fewer than 26 quarter turns.

   Two things differ from the half-turn program.

   THE MOVES ARE TWELVE, not eighteen.  A half turn is two moves here, so it
   is not a move of its own.

   THE LENGTH HAS A FIXED PARITY.  Every quarter turn is a 4-cycle on the
   corners, so it is an odd permutation of them, so the parity of the corner
   permutation flips at every move.  A position whose corner permutation is
   even is therefore at an even distance, and one whose corner permutation is
   odd is at an odd distance.  The target has even corner parity -- the
   program checks this and says so -- so its distance is even, 25 is
   impossible for free, and exhausting depth 24 already proves 26.  That is
   one whole level, worth about a factor of nine.

   usage: rubik_qtm <depth> <cap> <job> <njobs>   one prefix range, exhaustive
          rubik_qtm <depth> <cap> build           build the table only
          rubik_qtm <depth> <cap> verify          print the target, and search
                                                  for a solution, stopping at
                                                  the first one found          *)

type cube = { cp : int array; co : int array; ep : int array; eo : int array }

let solved () =
  { cp = Array.init 8 (fun i -> i); co = Array.make 8 0;
    ep = Array.init 12 (fun i -> i); eo = Array.make 12 0 }

let mult a b =
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

(* The six clockwise quarter turns, in the order U R F D L B.  Copied from
   rubik_par.ml unchanged, so the two programs agree on what a cube is.      *)
let basic = [|
  { cp = [|3;0;1;2;4;5;6;7|]; co = Array.make 8 0;
    ep = [|3;0;1;2;4;5;6;7;8;9;10;11|]; eo = Array.make 12 0 };
  { cp = [|4;1;2;0;7;5;6;3|]; co = [|2;0;0;1;1;0;0;2|];
    ep = [|8;1;2;3;11;5;6;7;4;9;10;0|]; eo = Array.make 12 0 };
  { cp = [|1;5;2;3;0;4;6;7|]; co = [|1;2;0;0;2;1;0;0|];
    ep = [|0;9;2;3;4;8;6;7;1;5;10;11|]; eo = [|0;1;0;0;0;1;0;0;1;1;0;0|] };
  { cp = [|0;1;2;3;5;6;7;4|]; co = Array.make 8 0;
    ep = [|0;1;2;3;5;6;7;4;8;9;10;11|]; eo = Array.make 12 0 };
  { cp = [|0;2;6;3;4;1;5;7|]; co = [|0;1;2;0;0;2;1;0|];
    ep = [|0;1;10;3;4;5;9;7;8;2;6;11|]; eo = Array.make 12 0 };
  { cp = [|0;1;3;7;4;5;2;6|]; co = [|0;0;1;2;0;0;2;1|];
    ep = [|0;1;2;11;4;5;6;10;8;9;3;7|]; eo = [|0;0;0;1;0;0;0;1;0;0;1;1|] };
|]

(* The eighteen half-turn-metric moves, used ONLY to build the target from a
   published maneuver.  The search never touches them.                       *)
let moves18 =
  Array.init 18 (fun m ->
    let b = basic.(m / 3) in
    match m mod 3 with
    | 0 -> b | 1 -> mult b b | _ -> mult (mult b b) b)

(* The twelve quarter turns.  Move m turns face m/2, clockwise when m is even
   and anticlockwise when m is odd.                                          *)
let nmv = 12
let moves =
  Array.init nmv (fun m ->
    let b = basic.(m / 2) in
    if m land 1 = 0 then b else mult (mult b b) b)

let face m = m / 2
let opp f = (f + 3) mod 6

let mvname =
  [| "U"; "U'"; "R"; "R'"; "F"; "F'"; "D"; "D'"; "L"; "L'"; "B"; "B'" |]

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

let slice c =
  let a = ref 0 and x = ref 0 in
  for j = 11 downto 0 do
    if c.ep.(j) >= 8 then begin a := !a + cnk.(11 - j).(!x + 1); incr x end
  done;
  !a

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
  let a = ref s and x = ref 4 in
  let pos = Array.make 12 0 in
  for j = 0 to 11 do
    if !x > 0 && !a >= cnk.(11 - j).(!x) then begin
      a := !a - cnk.(11 - j).(!x); decr x; pos.(j) <- 1
    end
  done;
  let ns = ref 8 and no = ref 0 in
  for j = 0 to 11 do
    if pos.(j) = 1 then begin c.ep.(j) <- !ns; incr ns end
    else begin c.ep.(j) <- !no; incr no end
  done;
  c

let mk_move_table n of_coord coord =
  let t = Array.make_matrix n nmv 0 in
  for i = 0 to n - 1 do
    let c = of_coord i in
    for m = 0 to nmv - 1 do t.(i).(m) <- coord (mult c moves.(m)) done
  done; t

let bfs size succ start =
  let d = Bytes.make size '\255' in
  Bytes.set d start '\000';
  let cur = ref 0 in
  (try while true do
    let added = ref 0 in
    for i = 0 to size - 1 do
      if Char.code (Bytes.get d i) = !cur then
        succ i (fun j ->
          if Char.code (Bytes.get d j) = 255 then begin
            Bytes.set d j (Char.chr (!cur + 1)); incr added end)
    done;
    if !added = 0 then raise Exit;
    incr cur
  done with Exit -> ());
  d

(* The parity of a permutation of n points, as 0 or 1.                       *)
let perm_parity p =
  let n = Array.length p in
  let seen = Array.make n false and r = ref 0 in
  for i = 0 to n - 1 do
    if not seen.(i) then begin
      let j = ref i and len = ref 0 in
      while not seen.(!j) do seen.(!j) <- true; j := p.(!j); incr len done;
      r := !r + !len - 1
    end
  done;
  !r land 1

let () =
  let depth = int_of_string Sys.argv.(1) in
  let cap = int_of_string Sys.argv.(2) in
  let mode = Sys.argv.(3) in
  let build_only = (mode = "build") in
  let verify = (mode = "verify") in
  let show = (mode = "target") in
  let job, njobs =
    if build_only || verify || show then 0, 1
    else int_of_string Sys.argv.(3), int_of_string Sys.argv.(4) in
  let log fmt = Printf.ksprintf
    (fun s -> if job = 0 then (print_string s; flush stdout)) fmt in

  (* ---- the target ------------------------------------------------------- *)
  (* Superflip, by the same 20-move word rubik_par.ml uses and checks:
        U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2                   *)
  let sf_man = [|0;4;6;15;3;16;3;1;12;16;3;2;11;4;6;5;12;16;1;7|] in
  (* Fourspot, by the usual word:  F2 B2 U D' R2 L2 U D'                     *)
  let fs_man = [|7;16;0;11;4;13;0;11|] in
  let apply man =
    let c = ref (solved ()) in
    Array.iter (fun m -> c := mult !c moves18.(m)) man; !c in

  let sf = apply sf_man in
  let ok = ref true in
  for i = 0 to 7 do if sf.cp.(i) <> i || sf.co.(i) <> 0 then ok := false done;
  for i = 0 to 11 do if sf.ep.(i) <> i || sf.eo.(i) <> 1 then ok := false done;
  if not !ok then (prerr_endline "superflip check FAILED"; exit 1);

  let target = apply (Array.append sf_man fs_man) in

  (* The parity that makes 25 impossible.  Say it out loud rather than assume
     it: if this prints 1 the argument below does not apply and the search
     has to go to 25.                                                        *)
  let par = perm_parity target.cp in
  log "target corner permutation parity: %d (%s)\n" par
    (if par = 0 then "even -- distance is EVEN, so exhausting 24 proves 26"
     else "odd -- distance is ODD, the search must reach 25");
  log "  cp = [|%s|]\n" (String.concat ";" (Array.to_list (Array.map string_of_int target.cp)));
  log "  co = [|%s|]\n" (String.concat ";" (Array.to_list (Array.map string_of_int target.co)));
  log "  ep = [|%s|]\n" (String.concat ";" (Array.to_list (Array.map string_of_int target.ep)));
  log "  eo = [|%s|]\n" (String.concat ";" (Array.to_list (Array.map string_of_int target.eo)));
  log "  edge permutation parity: %d\n" (perm_parity target.ep);
  (* `target' prints the position and stops, so the maneuvers can be checked
     against a reference without paying for the 2.2 GB table.                *)
  if show then exit 0;

  (* ---- the tables, all in the quarter-turn metric ----------------------- *)
  let mt_twist = mk_move_table n_twist cube_of_twist twist in
  let mt_flip  = mk_move_table n_flip  cube_of_flip  flip  in
  let mt_slice = mk_move_table n_slice cube_of_slice slice in

  let p_fs = bfs (n_flip * n_slice)
      (fun i k ->
        let f = i / n_slice and s = i mod n_slice in
        for m = 0 to nmv - 1 do
          k (mt_flip.(f).(m) * n_slice + mt_slice.(s).(m)) done) 0 in
  let p_ts = bfs (n_twist * n_slice)
      (fun i k ->
        let t = i / n_slice and s = i mod n_slice in
        for m = 0 to nmv - 1 do
          k (mt_twist.(t).(m) * n_slice + mt_slice.(s).(m)) done) 0 in

  let n_all = n_twist * n_flip * n_slice in
  let path = Printf.sprintf "qtm_cap%d.tbl" cap in
  let fresh = not (Sys.file_exists path) in
  let fd = Unix.openfile path
      (if fresh then [Unix.O_RDWR; Unix.O_CREAT] else [Unix.O_RDONLY]) 0o644 in
  let p_all = Bigarray.array1_of_genarray
      (Unix.map_file fd Bigarray.char Bigarray.c_layout fresh [| n_all |]) in
  Unix.close fd;
  if fresh then begin
    log "building the quarter-turn table (%d states, cap %d)...\n" n_all cap;
    let t0 = Unix.gettimeofday () in
    Bigarray.Array1.fill p_all (Char.chr (cap + 1));
    Bigarray.Array1.unsafe_set p_all 0 '\000';
    for cur = 0 to cap - 1 do
      let added = ref 0 in
      for t = 0 to n_twist - 1 do
        let mtt = mt_twist.(t) in
        for f = 0 to n_flip - 1 do
          let mtf = mt_flip.(f) in
          let base = (t * n_flip + f) * n_slice in
          for s = 0 to n_slice - 1 do
            if Char.code (Bigarray.Array1.unsafe_get p_all (base + s)) = cur then begin
              let mts = mt_slice.(s) in
              for m = 0 to nmv - 1 do
                let j = (mtt.(m) * n_flip + mtf.(m)) * n_slice + mts.(m) in
                if Char.code (Bigarray.Array1.unsafe_get p_all j) > cur + 1 then begin
                  Bigarray.Array1.unsafe_set p_all j (Char.chr (cur + 1)); incr added end
              done
            end
          done
        done
      done;
      log "   depth %d -> %d states (%.0f s)\n" (cur + 1) !added
        (Unix.gettimeofday () -. t0)
    done
  end;
  if build_only then exit 0;

  (* ---- the search ------------------------------------------------------- *)
  (* ONE VIEWING ANGLE, NOT THREE, AND ON PURPOSE.  The half-turn program
     reads the same table along three axes and keeps the largest answer.  It
     may start all three at the same coordinates because the superflip is
     fixed by all 48 symmetries, so the three agree at the root.  THIS TARGET
     IS NOT FIXED BY THE SYMMETRIES, so that shortcut is simply false here:
     the other two views would have to start at the coordinates of the
     conjugated cube, which needs the symmetry acting on cubies, which this
     prototype does not have.  Rather than help ourselves to a cut we cannot
     justify -- the mistake that made the half-turn prototype unsound for
     three years -- we take one view and say so.

     The consequence is that the node counts below are an UPPER BOUND on what
     a three-view search would visit.  If they say the job is affordable,
     it is affordable; if they say it is not, the three views are the first
     thing to add.                                                           *)
  let maxd = 30 in
  let cps = Array.init maxd (fun _ -> Array.make 8 0) in
  let eps = Array.init maxd (fun _ -> Array.make 12 0) in
  let tw = Array.make maxd 0 in
  let fl = Array.make maxd 0 in
  let sl = Array.make maxd 0 in
  let nodes = ref 0L in
  let sol = Array.make maxd 0 in

  let heur d =
    let t = tw.(d) and f = fl.(d) and s = sl.(d) in
    let a = Char.code (Bytes.unsafe_get p_fs (f * n_slice + s)) in
    let b = Char.code (Bytes.unsafe_get p_ts (t * n_slice + s)) in
    let c = Char.code (Bigarray.Array1.unsafe_get p_all
                         ((t * n_flip + f) * n_slice + s)) in
    let h = ref a in
    if b > !h then h := b;
    if c > !h then h := c;
    !h in

  let is_solved d =
    let r = ref (tw.(d) = 0 && fl.(d) = 0) in
    for i = 0 to 7 do if cps.(d).(i) <> i then r := false done;
    for i = 0 to 11 do if eps.(d).(i) <> i then r := false done;
    !r in

  let step d m =
    let d' = d + 1 in
    let mcp = moves.(m).cp and mep = moves.(m).ep in
    for i = 0 to 7 do cps.(d').(i) <- cps.(d).(mcp.(i)) done;
    for i = 0 to 11 do eps.(d').(i) <- eps.(d).(mep.(i)) done;
    tw.(d') <- mt_twist.(tw.(d)).(m);
    fl.(d') <- mt_flip.(fl.(d)).(m);
    sl.(d') <- mt_slice.(sl.(d)).(m) in

  (* THE REDUNDANCY RULE, and it is NOT the half-turn one.  Here U U is a
     legitimate pair -- it is the half turn -- so "never the same face twice
     running" would be unsound.  What is true:

       * three turns of a face in a row are one turn the other way, so a run
         is at most two long;
       * a run of two must be two of the SAME turn, since U U' is nothing;
       * opposite faces commute, so of the two orders only one is kept, and
         the rule is the same as in the half-turn program: after a run on
         face f, a face opp f greater than f is refused.

     A node therefore has twelve moves less two on its own face, less two
     more when the opposite face is cut, less one when the run is already
     two: between eight and eleven.                                          *)
  let allowed pm run m =
    if pm < 0 then true
    else
      let f = face m and pf = face pm in
      if f = pf then (m = pm && run = 1)
      else not (f = opp pf && f > pf) in

  let rec dfs d rem pm run =
    nodes := Int64.add !nodes 1L;
    let h = heur d in
    if h = 0 && is_solved d then true
    else if h > rem || rem = 0 then false
    else begin
      let found = ref false and m = ref 0 in
      while not !found && !m < nmv do
        if allowed pm run !m then begin
          step d !m;
          sol.(d) <- !m;
          let run' = if pm >= 0 && face !m = face pm then run + 1 else 1 in
          if dfs (d + 1) (rem - 1) !m run' then found := true
        end;
        incr m
      done;
      !found
    end in

  for i = 0 to 7 do cps.(0).(i) <- target.cp.(i) done;
  for i = 0 to 11 do eps.(0).(i) <- target.ep.(i) done;
  tw.(0) <- twist target; fl.(0) <- flip target; sl.(0) <- slice target;
  log "root heuristic: %d\n" (heur 0);

  let t0 = Unix.gettimeofday () in

  if verify then begin
    (* Deepen until a solution appears, and stop at the first one.  This is
       the CHEAP half: it gives the upper bound, and it also says whether the
       position is the one we think it is.                                   *)
    let d = ref (heur 0) in
    let got = ref false in
    while not !got && !d <= depth do
      nodes := 0L;
      let t1 = Unix.gettimeofday () in
      got := dfs 0 !d (-1) 0;
      Printf.printf "depth %2d : %Ld nodes, %.1f s%s\n%!" !d !nodes
        (Unix.gettimeofday () -. t1) (if !got then "  SOLVED" else "");
      if !got then begin
        let b = Buffer.create 64 in
        for i = 0 to !d - 1 do
          Buffer.add_string b mvname.(sol.(i)); Buffer.add_char b ' ' done;
        Printf.printf "solution (%d quarter turns): %s\n%!" !d (Buffer.contents b)
      end;
      incr d
    done;
    if not !got then
      Printf.printf "no solution up to depth %d -- so the distance exceeds it\n%!"
        depth;
    exit 0
  end;

  (* The exhaustive run.  The work is split on prefixes of length two, one
     range per job.  NO SYMMETRY REDUCTION IS APPLIED to the first move: the
     superflip is fixed by all 48 symmetries and this target is not, so the
     trick the half-turn program uses is simply not available here, and
     helping ourselves to it would be exactly the unsound cut that bit us
     before.  Twelve first moves, and every second move the rule allows.     *)
  let prefixes =
    let l = ref [] in
    for m1 = 0 to nmv - 1 do
      for m2 = 0 to nmv - 1 do
        if allowed m1 1 m2 then l := (m1, m2) :: !l
      done
    done;
    List.rev !l in
  log "prefixes: %d\n" (List.length prefixes);

  let found = ref false in
  List.iteri (fun idx (m1, m2) ->
    if idx mod njobs = job && not !found then begin
      step 0 m1; step 1 m2;
      let run = if face m2 = face m1 then 2 else 1 in
      if dfs 2 (depth - 2) m2 run then found := true
    end) prefixes;
  Printf.printf "job %d/%d depth %d : %Ld nodes, %.1f s, solution %b\n%!"
    job njobs depth !nodes (Unix.gettimeofday () -. t0) !found
