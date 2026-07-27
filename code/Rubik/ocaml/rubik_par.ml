(* Parallel version: the phase-1 table lives in a memory-mapped file so all
   workers share one copy, and the root prefixes of length 2 are split across
   jobs -- the same decomposition a Rocq proof would use, one lemma per prefix.

   usage: rubik_par <depth> <cap> <job> <njobs>     (job = 0 .. njobs-1)
          rubik_par <depth> <cap> build             (build the table only) *)

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

let moves =
  Array.init 18 (fun m ->
    let b = basic.(m / 3) in
    match m mod 3 with
    | 0 -> b | 1 -> mult b b | _ -> mult (mult b b) b)

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
  let t = Array.make_matrix n 18 0 in
  for i = 0 to n - 1 do
    let c = of_coord i in
    for m = 0 to 17 do t.(i).(m) <- coord (mult c moves.(m)) done
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

let () =
  let depth = int_of_string Sys.argv.(1) in
  let cap = int_of_string Sys.argv.(2) in
  let mode = Sys.argv.(3) in
  let build_only = (mode = "build" || mode = "dump") in
  let job, njobs =
    if build_only then 0, 1
    else int_of_string Sys.argv.(3), int_of_string Sys.argv.(4) in
  let log fmt = Printf.ksprintf
    (fun s -> if job = 0 then (print_string s; flush stdout)) fmt in

  let man = [|0;4;6;15;3;16;3;1;12;16;3;2;11;4;6;5;12;16;1;7|] in
  let c = ref (solved ()) in
  Array.iter (fun m -> c := mult !c moves.(m)) man;
  let sf = !c in
  let ok = ref true in
  for i = 0 to 7 do if sf.cp.(i) <> i || sf.co.(i) <> 0 then ok := false done;
  for i = 0 to 11 do if sf.ep.(i) <> i || sf.eo.(i) <> 1 then ok := false done;
  if not !ok then (prerr_endline "superflip check FAILED"; exit 1);

  let mt_twist = mk_move_table n_twist cube_of_twist twist in
  let mt_flip  = mk_move_table n_flip  cube_of_flip  flip  in
  let mt_slice = mk_move_table n_slice cube_of_slice slice in

  if mode = "dump" then begin
    (* emit the three move tables as Rocq int63 lists *)
    let pr name n t =
      Printf.printf "Definition %s : list int := [" name;
      for i = 0 to n - 1 do
        for m = 0 to 17 do
          Printf.printf "%s%d" (if i = 0 && m = 0 then " " else "; ") t.(i).(m)
        done
      done;
      Printf.printf "]%%uint63.\n\n" in
    print_string "From Stdlib Require Import Uint63 List.\nImport ListNotations.\n\n";
    pr "mt_twist" n_twist mt_twist;
    pr "mt_flip"  n_flip  mt_flip;
    pr "mt_slice" n_slice mt_slice;
    exit 0
  end;

  let p_fs = bfs (n_flip * n_slice)
      (fun i k ->
        let f = i / n_slice and s = i mod n_slice in
        for m = 0 to 17 do k (mt_flip.(f).(m) * n_slice + mt_slice.(s).(m)) done) 0 in
  let p_ts = bfs (n_twist * n_slice)
      (fun i k ->
        let t = i / n_slice and s = i mod n_slice in
        for m = 0 to 17 do k (mt_twist.(t).(m) * n_slice + mt_slice.(s).(m)) done) 0 in

  (* phase-1 table, shared through the file system *)
  let n_all = n_twist * n_flip * n_slice in
  let path = Printf.sprintf "phase1_cap%d.tbl" cap in
  let fresh = not (Sys.file_exists path) in
  let fd = Unix.openfile path
      (if fresh then [Unix.O_RDWR; Unix.O_CREAT] else [Unix.O_RDONLY]) 0o644 in
  let p_all = Bigarray.array1_of_genarray
      (Unix.map_file fd Bigarray.char Bigarray.c_layout fresh [| n_all |]) in
  Unix.close fd;
  if fresh then begin
    log "building phase-1 table (%d states, cap %d)...\n" n_all cap;
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
              for m = 0 to 17 do
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

  let sigma = Array.init 18 (fun m ->
    let f = m / 3 and t = m mod 3 in
    let f' = if f < 3 then (f + 1) mod 3 else 3 + ((f - 3 + 1) mod 3) in
    f' * 3 + t) in
  let mv = Array.make_matrix 3 18 0 in
  for m = 0 to 17 do
    mv.(0).(m) <- m; mv.(1).(m) <- sigma.(m); mv.(2).(m) <- sigma.(sigma.(m))
  done;

  let maxd = 22 in
  let cps = Array.init maxd (fun _ -> Array.make 8 0) in
  let eps = Array.init maxd (fun _ -> Array.make 12 0) in
  let tw = Array.make_matrix maxd 3 0 in
  let fl = Array.make_matrix maxd 3 0 in
  let sl = Array.make_matrix maxd 3 0 in
  let nodes = ref 0L in

  let heur d =
    let h = ref 0 in
    for k = 0 to 2 do
      let t = tw.(d).(k) and f = fl.(d).(k) and s = sl.(d).(k) in
      let a = Char.code (Bytes.unsafe_get p_fs (f * n_slice + s)) in
      let b = Char.code (Bytes.unsafe_get p_ts (t * n_slice + s)) in
      let c = Char.code (Bigarray.Array1.unsafe_get p_all
                           ((t * n_flip + f) * n_slice + s)) in
      if a > !h then h := a;
      if b > !h then h := b;
      if c > !h then h := c
    done; !h in

  let is_solved d =
    let r = ref true in
    for i = 0 to 7 do if cps.(d).(i) <> i then r := false done;
    for i = 0 to 11 do if eps.(d).(i) <> i then r := false done;
    !r in

  let step d m =
    let d' = d + 1 in
    let mcp = moves.(m).cp and mep = moves.(m).ep in
    for i = 0 to 7 do cps.(d').(i) <- cps.(d).(mcp.(i)) done;
    for i = 0 to 11 do eps.(d').(i) <- eps.(d).(mep.(i)) done;
    for k = 0 to 2 do
      let mk = mv.(k).(m) in
      tw.(d').(k) <- mt_twist.(tw.(d).(k)).(mk);
      fl.(d').(k) <- mt_flip.(fl.(d).(k)).(mk);
      sl.(d').(k) <- mt_slice.(sl.(d).(k)).(mk)
    done in

  let opp f = (f + 3) mod 6 in

  let rec dfs d rem prev =
    nodes := Int64.add !nodes 1L;
    let h = heur d in
    if h = 0 && is_solved d then true
    else if h > rem || rem = 0 then false
    else begin
      let found = ref false and m = ref 0 in
      while not !found && !m < 18 do
        let f = !m / 3 in
        if not (f = prev || (f = opp prev && f > prev)) then begin
          step d !m;
          if dfs (d + 1) (rem - 1) f then found := true
        end;
        incr m
      done;
      !found
    end in

  (* root prefixes of length 2.  superflip is fixed by all 48 symmetries and
     is its own inverse, so the first move may be taken to be U or U2. *)
  let prefixes =
    let l = ref [] in
    List.iter (fun m1 ->
      let f1 = m1 / 3 in
      for m2 = 0 to 17 do
        let f2 = m2 / 3 in
        if not (f2 = f1 || (f2 = opp f1 && f2 > f1)) then l := (m1, m2) :: !l
      done) [0; 1];
    List.rev !l in

  for i = 0 to 7 do cps.(0).(i) <- sf.cp.(i) done;
  for i = 0 to 11 do eps.(0).(i) <- sf.ep.(i) done;
  for k = 0 to 2 do
    tw.(0).(k) <- twist sf; fl.(0).(k) <- flip sf; sl.(0).(k) <- slice sf done;
  if heur 0 <= 2 then (prerr_endline "root heuristic too small"; exit 1);

  let t0 = Unix.gettimeofday () in
  let found = ref false in
  List.iteri (fun idx (m1, m2) ->
    if idx mod njobs = job && not !found then begin
      step 0 m1; step 1 m2;
      if dfs 2 (depth - 2) (m2 / 3) then found := true
    end) prefixes;
  Printf.printf "job %d/%d depth %d : %Ld nodes, %.1f s, solution %b\n%!"
    job njobs depth !nodes (Unix.gettimeofday () -. t0) !found
