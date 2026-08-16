(* Reid's 1998 pruning table, rebuilt, and what it does to the quarter-turn
   search.  Same shape as rubik_qtm.ml, and for the same purpose: to measure
   the job before anyone writes it in Rocq.  It is not part of any proof.

   His post of 31 July 1998, kept in doc/reid-1998-optimal-solver.md, gives a
   subgroup  H  and says the cosets are described by a triple:

     the four middle-slice edges are home and unflipped,
     the four U corners are on the U face,
     every corner has its U or D facelet on the U or D face.

   The triple is  (e, cl, ct):  where those four edges sit and how they are
   flipped, 24 * 22 * 20 * 18 = 190080; which four corner places hold the U
   corners, 8 choose 4 = 70; and the corner orientations, 3^7 = 2187.  That
   is 29 099 347 200 cosets, and the table holds the distance of each from
   the solved cube.

   WHY IT IS WORTH BUILDING.  The best quarter-turn heuristic we had was an
   edge database of 42.6 million states.  This one is 680 times larger and
   reaches distance 14, where ours saturated far earlier, and the tree the
   search walks is what that difference is spent on.

   TWO THINGS ARE NOT DONE HERE, both on purpose.

   No symmetry reduction.  Reid folds the 16 symmetries that keep the U-D
   axis and stores 1 851 470 460 nibbles, 883 Mb.  We store one byte per
   coset and no folding, 29.1 Gb, which is a file the reference machine can
   hold and a great deal less code to get wrong.  The table is the same
   table; only its storage differs.

   One viewing angle, not three.  The same remark as in rubik_qtm.ml: the
   target is not fixed by the symmetries, so reading the table along the
   other two axes needs the symmetry acting on cubies, which this prototype
   does not have.  The node counts below are therefore an UPPER bound on
   what a three-angle search would visit.

   usage: rubik_h <depth> <cap> check          coordinates and a small table
          rubik_h <depth> <cap> build [<workers>]   build the table only
          rubik_h <depth> <cap> roots          the six positions and their
                                               table values, no search
          rubik_h <depth> <cap> count <k>      node counts from position k,
                                               every depth up to <depth>    *)

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
   rubik_par.ml unchanged, so all the programs agree on what a cube is.     *)
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
   published maneuver.  The search never touches them.                      *)
let moves18 =
  Array.init 18 (fun m ->
    let b = basic.(m / 3) in
    match m mod 3 with
    | 0 -> b | 1 -> mult b b | _ -> mult (mult b b) b)

(* The twelve quarter turns.  Move m turns face m/2, clockwise when m is even
   and anticlockwise when m is odd.                                         *)
let nmv = 12
let moves =
  Array.init nmv (fun m ->
    let b = basic.(m / 2) in
    if m land 1 = 0 then b else mult (mult b b) b)

let face m = m / 2
let opp f = (f + 3) mod 6

let mvname =
  [| "U"; "U'"; "R"; "R'"; "F"; "F'"; "D"; "D'"; "L"; "L'"; "B"; "B'" |]

(* ---- the three coordinates ---------------------------------------------- *)

let n_e = 190080 and n_cl = 70 and n_ct = 2187 and n_flip = 2048

(* Corner orientation, the seventh coordinate being forced by the other
   seven.  This is the `twist' of the other programs, under Reid's name.    *)
let ct_coord c = let s = ref 0 in for i = 6 downto 0 do s := 3 * !s + c.co.(i) done; !s

let cube_of_ct t =
  let c = solved () and t = ref t and s = ref 0 in
  for i = 0 to 6 do c.co.(i) <- !t mod 3; s := !s + c.co.(i); t := !t / 3 done;
  c.co.(7) <- (3 - !s mod 3) mod 3; c

let flip c = let s = ref 0 in for i = 10 downto 0 do s := 2 * !s + c.eo.(i) done; !s

let cube_of_flip f =
  let c = solved () and f = ref f and s = ref 0 in
  for i = 0 to 10 do c.eo.(i) <- !f land 1; s := !s + c.eo.(i); f := !f lsr 1 done;
  c.eo.(11) <- !s land 1; c

let cnk = Array.make_matrix 13 5 0
let () =
  for n = 0 to 12 do
    cnk.(n).(0) <- 1;
    for k = 1 to 4 do
      cnk.(n).(k) <- (if n = 0 then 0 else cnk.(n-1).(k-1) + cnk.(n-1).(k))
    done
  done

(* Which four corner places hold the U corners, which are the cubies 0 to 3.
   The same ranking the slice coordinate uses for edges.                    *)
let cl_coord c =
  let a = ref 0 and x = ref 0 in
  for j = 7 downto 0 do
    if c.cp.(j) < 4 then begin a := !a + cnk.(7 - j).(!x + 1); incr x end
  done;
  !a

let cube_of_cl s =
  let c = solved () in
  let a = ref s and x = ref 4 in
  let pos = Array.make 8 0 in
  for j = 0 to 7 do
    if !x > 0 && !a >= cnk.(7 - j).(!x) then begin
      a := !a - cnk.(7 - j).(!x); decr x; pos.(j) <- 1
    end
  done;
  let nu = ref 0 and nd = ref 4 in
  for j = 0 to 7 do
    if pos.(j) = 1 then begin c.cp.(j) <- !nu; incr nu end
    else begin c.cp.(j) <- !nd; incr nd end
  done;
  c

(* Where the four middle-slice edges sit and how they are flipped.  They are
   the cubies 8 to 11, and a place taken by one of them is taken in both its
   flipped and its unflipped reading, which is why the radices fall by two:
   24, then 22, then 20, then 18.                                          *)
let e_coord c =
  let slot = Array.make 4 0 in
  for j = 0 to 11 do
    let k = c.ep.(j) in
    if k >= 8 then slot.(k - 8) <- 2 * j + c.eo.(j)
  done;
  let used = Array.make 12 false and r = ref 0 in
  for i = 0 to 3 do
    let s = slot.(i) in
    let p = s / 2 in
    let idx = ref 0 in
    for q = 0 to p - 1 do if not used.(q) then idx := !idx + 2 done;
    r := !r * (24 - 2 * i) + !idx + (s land 1);
    used.(p) <- true
  done;
  !r

let cube_of_e r =
  let c = solved () and r = ref r in
  let idx = Array.make 4 0 in
  for i = 3 downto 0 do
    let radix = 24 - 2 * i in
    idx.(i) <- !r mod radix; r := !r / radix
  done;
  let used = Array.make 12 false in
  let pos = Array.make 4 0 and ori = Array.make 4 0 in
  for i = 0 to 3 do
    let k = ref idx.(i) and p = ref 0 and got = ref (-1) in
    while !got < 0 do
      if used.(!p) then incr p
      else if !k < 2 then got := 2 * !p + !k
      else begin k := !k - 2; incr p end
    done;
    pos.(i) <- !got / 2; ori.(i) <- !got land 1;
    used.(pos.(i)) <- true
  done;
  for j = 0 to 11 do c.ep.(j) <- -1 done;
  for i = 0 to 3 do c.ep.(pos.(i)) <- 8 + i; c.eo.(pos.(i)) <- ori.(i) done;
  let free = ref 0 in
  for j = 0 to 11 do
    if c.ep.(j) < 0 then begin c.ep.(j) <- !free; incr free end
  done;
  c

let mk_move_table n of_coord coord =
  let t = Array.make_matrix n nmv 0 in
  for i = 0 to n - 1 do
    let c = of_coord i in
    for m = 0 to nmv - 1 do t.(i).(m) <- coord (mult c moves.(m)) done
  done; t

(* ---- the table ---------------------------------------------------------- *)

(* One byte per coset, so the file is 29.1 Gb, and it is built in place by a
   breadth first sweep.  The sweep is shared out over WORKERS processes: each
   one scans its own slice of the first coordinate for the states of the
   current depth and writes their successors, wherever those land.  Two
   processes can reach the same successor and both write it -- they write the
   same value, so that is harmless, but it does make the number they count
   too large.  The count is therefore taken in a second pass, once every
   writer has finished.                                                     *)
(* One place prints, and it prints at once: a build that says nothing for an
   hour cannot be told from one that has hung.                              *)
let log fmt = Printf.ksprintf (fun s -> print_string s; flush stdout) fmt

let parallel nw f =
  for w = 0 to nw - 1 do
    match Unix.fork () with
    | 0 -> f w; exit 0
    | _ -> ()
  done;
  for _ = 1 to nw do ignore (Unix.waitpid [] (-1)) done

let counters path nw =
  let fd = Unix.openfile path [Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC] 0o644 in
  let a = Bigarray.array1_of_genarray
      (Unix.map_file fd Bigarray.int64 Bigarray.c_layout true [| nw |]) in
  Unix.close fd;
  Bigarray.Array1.fill a 0L;
  a

(* START IS NOT ZERO.  Two of the three rankings send the solved cube to the
   middle of their range, not to nought, so the sweep is told where to start
   rather than left to assume.  Assuming it builds a table of distances from
   a cube nobody asked about, and every value in it is wrong by a shift that
   is different for every coset.                                           *)
let build path cap nw start (na, mta) (nb, mtb) (nc, mtc) =
  let n_all = na * nb * nc in
  let fresh = not (Sys.file_exists path) in
  let fd = Unix.openfile path [Unix.O_RDWR; Unix.O_CREAT] 0o644 in
  if fresh then Unix.LargeFile.ftruncate fd (Int64.of_int n_all);
  let t = Bigarray.array1_of_genarray
      (Unix.map_file fd Bigarray.char Bigarray.c_layout true [| n_all |]) in
  Unix.close fd;
  if fresh then begin
    log "building %d cosets, cap %d, %d workers...\n" n_all cap nw;
    let t0 = Unix.gettimeofday () in
    Bigarray.Array1.fill t (Char.chr (cap + 1));
    Bigarray.Array1.unsafe_set t start '\000';
    let cnt = counters (path ^ ".cnt") nw in
    let slice w = (w * na / nw, (w + 1) * na / nw) in
    (try
      for cur = 0 to cap - 1 do
        parallel nw (fun w ->
          let lo, hi = slice w in
          for a = lo to hi - 1 do
            let ra = mta.(a) in
            for b = 0 to nb - 1 do
              let rb = mtb.(b) in
              let base = (a * nb + b) * nc in
              for c = 0 to nc - 1 do
                if Char.code (Bigarray.Array1.unsafe_get t (base + c)) = cur
                then begin
                  let rc = mtc.(c) in
                  for m = 0 to nmv - 1 do
                    let j = (ra.(m) * nb + rb.(m)) * nc + rc.(m) in
                    if Char.code (Bigarray.Array1.unsafe_get t j) > cur + 1
                    then Bigarray.Array1.unsafe_set t j (Char.chr (cur + 1))
                  done
                end
              done
            done
          done);
        parallel nw (fun w ->
          let lo, hi = slice w in
          let n = ref 0L in
          for i = lo * nb * nc to hi * nb * nc - 1 do
            if Char.code (Bigarray.Array1.unsafe_get t i) = cur + 1
            then n := Int64.add !n 1L
          done;
          Bigarray.Array1.set cnt w !n);
        let added = ref 0L in
        for w = 0 to nw - 1 do
          added := Int64.add !added (Bigarray.Array1.get cnt w) done;
        log "  depth %2d -> %Ld cosets (%.0f s)\n" (cur + 1) !added
          (Unix.gettimeofday () -. t0);
        if !added = 0L then raise Exit
      done
    with Exit -> ());
    (try Sys.remove (path ^ ".cnt") with _ -> ())
  end;
  t

(* ---- the redundancy rule, the quarter-turn one -------------------------- *)

(* Copied from rubik_qtm.ml.  Here U U is a legitimate pair -- it is the half
   turn -- so "never the same face twice running" would be unsound.  What is
   true: three turns of a face in a row are one turn the other way, so a run
   is at most two long; a run of two must be two of the SAME turn, since U U'
   is nothing; and of the two orders of two opposite faces only one is kept. *)
let allowed pm run m =
  if pm < 0 then true
  else
    let f = face m and pf = face pm in
    if f = pf then (m = pm && run = 1)
    else not (f = opp pf && f > pf)

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
  let arg4 n = if Array.length Sys.argv > 4 then int_of_string Sys.argv.(4) else n in

  (* ---- the target and Reid's six positions ------------------------------ *)
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

  (* Proposition 2 of doc/reid-1998-fourspot.md: every maneuver for this
     position can be turned into one beginning with one of six sequences.
     Reid searched the first through 22 quarter turns and the other five
     through 21, which with the prefix is depth 24 in every case.            *)
  let prefixes = [|
    "R U",       [| 2; 0 |];
    "R' U D",    [| 3; 0; 6 |];
    "R' U F'",   [| 3; 0; 5 |];
    "R' U R'",   [| 3; 0; 3 |];
    "R' U B'",   [| 3; 0; 11 |];
    "R' U L'",   [| 3; 0; 9 |];
  |] in
  let position k =
    let _, man = prefixes.(k) in
    let c = ref target in
    Array.iter (fun m -> c := mult !c moves.(m)) man; !c in

  (* ---- the move tables -------------------------------------------------- *)
  let mt_e  = mk_move_table n_e  cube_of_e  e_coord  in
  let mt_cl = mk_move_table n_cl cube_of_cl cl_coord in
  let mt_ct = mk_move_table n_ct cube_of_ct ct_coord in
  let mt_fl = mk_move_table n_flip cube_of_flip flip in

  (* The solved cube's triple, which is where every sweep starts and what the
     search is looking for.                                                 *)
  let e0 = e_coord (solved ()) and cl0 = cl_coord (solved ())
  and ct0 = ct_coord (solved ()) in
  let start = (e0 * n_cl + cl0) * n_ct + ct0 in

  (* ---- check: the coordinates, and the machinery on a small table ------- *)
  if mode = "check" then begin
    let round n of_coord coord name =
      let bad = ref 0 in
      for i = 0 to n - 1 do if coord (of_coord i) <> i then incr bad done;
      log "%-3s %8d values, %d round trips wrong\n" name n !bad;
      if !bad > 0 then exit 1 in
    round n_e  cube_of_e  e_coord  "e";
    round n_cl cube_of_cl cl_coord "cl";
    round n_ct cube_of_ct ct_coord "ct";
    (* A move has to act on a coordinate as a permutation of it.  A bad
       encoding shows up here at once: two states collapsing onto one.      *)
    let perm n mt name =
      for m = 0 to nmv - 1 do
        let seen = Array.make n false in
        for i = 0 to n - 1 do
          let j = mt.(i).(m) in
          if j < 0 || j >= n || seen.(j) then begin
            log "%s: move %s is not a permutation\n" name mvname.(m); exit 1
          end;
          seen.(j) <- true
        done
      done;
      log "%-3s all twelve moves permute it\n" name in
    perm n_e  mt_e  "e";
    perm n_cl mt_cl "cl";
    perm n_ct mt_ct "ct";
    (* The four turns of the U and D faces lie in H itself, so from the solved
       cube the twelve moves reach eight cosets and not twelve.  That is the
       first line of Reid's column, and it tests all three coordinates at
       once.                                                                *)
    let succ = Array.init nmv (fun m ->
      (mt_e.(e0).(m) * n_cl + mt_cl.(cl0).(m)) * n_ct + mt_ct.(ct0).(m)) in
    let fixed = ref [] and distinct = ref [] in
    Array.iteri (fun m j ->
      if j = start then fixed := mvname.(m) :: !fixed
      else if not (List.mem j !distinct) then distinct := j :: !distinct) succ;
    log "from solved: %d cosets at distance 1, fixed by %s\n"
      (List.length !distinct) (String.concat " " (List.rev !fixed));
    if List.length !distinct <> 8 then exit 1;
    (* The pair (cl, ct) is itself closed under the moves, and so is the pair
       (e, cl).  Building both is the cheap way to see that the sweep, the
       forks and the shared file work, and that the sweep reaches every state
       -- Reid says all combinations occur, so anything left unset is a bug
       in the coordinate and not a fact about the cube.                     *)
    let one = [| Array.make nmv 0 |] in
    let small name path (na, mta, sa) (nb, mtb, sb) =
      (try Sys.remove path with _ -> ());
      let t = build path 30 2 (sa * nb + sb) (1, one) (na, mta) (nb, mtb) in
      let h = Array.make 40 0 in
      for i = 0 to na * nb - 1 do
        let d = Char.code (Bigarray.Array1.get t i) in
        h.(d) <- h.(d) + 1 done;
      log "%s: %d states, %d never reached\n" name (na * nb) h.(31);
      for d = 0 to 30 do if h.(d) > 0 then log "  %2d %10d\n" d h.(d) done;
      (try Sys.remove path with _ -> ());
      if h.(31) > 0 then exit 1 in
    small "(cl, ct)" "h_check1.tbl" (n_cl, mt_cl, cl0) (n_ct, mt_ct, ct0);
    small "(e, cl)"  "h_check2.tbl" (n_e, mt_e, e0) (n_cl, mt_cl, cl0);
    exit 0
  end;

  (* ---- roots: the six positions, no table needed ------------------------ *)
  if mode = "roots" then begin
    log "target corner permutation parity: %d\n" (perm_parity target.cp);
    Array.iteri (fun k (name, man) ->
      let c = position k in
      log "%d  %-10s prefix %d  e %6d  cl %2d  ct %4d  parity %d\n"
        k name (Array.length man) (e_coord c) (cl_coord c) (ct_coord c)
        (perm_parity c.cp)) prefixes;
    exit 0
  end;

  (* ---- the table -------------------------------------------------------- *)
  let path = Printf.sprintf "h_cap%d.tbl" cap in
  if mode <> "build" && not (Sys.file_exists path) then begin
    prerr_endline (path ^ " is missing -- run the build first");
    exit 1
  end;
  let nw = if mode = "build" then arg4 1 else 1 in
  let t0 = Unix.gettimeofday () in
  let tbl = build path cap nw start (n_e, mt_e) (n_cl, mt_cl) (n_ct, mt_ct) in
  if mode = "build" then begin
    (* The distance histogram, which is the check that matters: it has to be
       Reid's quarter-turn column, coset for coset.                          *)
    let h = Array.make 32 0L in
    let n_all = n_e * n_cl * n_ct in
    for i = 0 to n_all - 1 do
      let d = Char.code (Bigarray.Array1.unsafe_get tbl i) in
      h.(d) <- Int64.add h.(d) 1L done;
    log "distance histogram, against Reid's column:\n";
    for d = 0 to 31 do
      if h.(d) <> 0L then log "  %2d %14Ld\n" d h.(d) done;
    log "built in %.0f s\n" (Unix.gettimeofday () -. t0);
    exit 0
  end;

  (* ---- the node count --------------------------------------------------- *)
  if mode <> "count" then (prerr_endline "unknown mode"; exit 1);
  let k = arg4 0 in
  let name, man = prefixes.(k) in
  let root = position k in

  let maxd = 32 in
  let cps = Array.init maxd (fun _ -> Array.make 8 0) in
  let eps = Array.init maxd (fun _ -> Array.make 12 0) in
  let ec = Array.make maxd 0 and cc = Array.make maxd 0 in
  let tc = Array.make maxd 0 and fc = Array.make maxd 0 in
  let nodes = ref 0L in

  let heur d =
    Char.code (Bigarray.Array1.unsafe_get tbl
                 ((ec.(d) * n_cl + cc.(d)) * n_ct + tc.(d))) in

  let is_solved d =
    let r = ref (tc.(d) = 0 && fc.(d) = 0) in
    for i = 0 to 7 do if cps.(d).(i) <> i then r := false done;
    for i = 0 to 11 do if eps.(d).(i) <> i then r := false done;
    !r in

  let step d m =
    let d' = d + 1 in
    let mcp = moves.(m).cp and mep = moves.(m).ep in
    for i = 0 to 7 do cps.(d').(i) <- cps.(d).(mcp.(i)) done;
    for i = 0 to 11 do eps.(d').(i) <- eps.(d).(mep.(i)) done;
    ec.(d') <- mt_e.(ec.(d)).(m);
    cc.(d') <- mt_cl.(cc.(d)).(m);
    tc.(d') <- mt_ct.(tc.(d)).(m);
    fc.(d') <- mt_fl.(fc.(d)).(m) in

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
          let run' = if pm >= 0 && face !m = face pm then run + 1 else 1 in
          if dfs (d + 1) (rem - 1) !m run' then found := true
        end;
        incr m
      done;
      !found
    end in

  for i = 0 to 7 do cps.(0).(i) <- root.cp.(i) done;
  for i = 0 to 11 do eps.(0).(i) <- root.ep.(i) done;
  ec.(0) <- e_coord root; cc.(0) <- cl_coord root;
  tc.(0) <- ct_coord root; fc.(0) <- flip root;
  log "position %d: superflip . fourspot . %s\n" k name;
  log "  prefix %d moves, so Reid's search of it is depth %d\n"
    (Array.length man) (24 - Array.length man);
  log "  root table value: %d\n" (heur 0);

  for d = 10 to depth do
    nodes := 0L;
    let t1 = Unix.gettimeofday () in
    let got = dfs 0 d (-1) 0 in
    let s = Unix.gettimeofday () -. t1 in
    log "depth %2d : %14Ld nodes, %8.1f s, %.2e nodes/s%s\n" d !nodes s
      (Int64.to_float !nodes /. (if s > 0. then s else 1.))
      (if got then "  SOLVED -- which would be a discovery, check it" else "")
  done
