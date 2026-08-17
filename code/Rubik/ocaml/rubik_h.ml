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
   hour cannot be told from one that has hung.  It prints on the ERROR
   channel, because the dump mode has the standard one redirected into the
   Rocq file it writes, and a banner there is a syntax error.               *)
let log fmt = Printf.ksprintf (fun s -> prerr_string s; flush stderr) fmt

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
(* A HALF BUILT TABLE MUST NOT LOOK LIKE A BUILT ONE.  The sweep writes into
   `path.part' and renames it only when it has finished, so a build that is
   interrupted leaves nothing that a later run will pick up and believe.  An
   interrupted 29 Gb table is a bad thing to inherit in silence: it prunes
   almost nothing and the search still answers.                             *)
let build path cap nw start (na, mta) (nb, mtb) (nc, mtc) =
  let n_all = na * nb * nc in
  let fresh = not (Sys.file_exists path) in
  let wpath = if fresh then path ^ ".part" else path in
  if fresh then (try Sys.remove wpath with _ -> ());
  let fd = Unix.openfile wpath [Unix.O_RDWR; Unix.O_CREAT] 0o644 in
  if fresh then Unix.LargeFile.ftruncate fd (Int64.of_int n_all);
  let t = Bigarray.array1_of_genarray
      (Unix.map_file fd Bigarray.char Bigarray.c_layout true [| n_all |]) in
  Unix.close fd;
  if fresh then begin
    log "building %d cosets, cap %d, %d workers...\n" n_all cap nw;
    let t0 = Unix.gettimeofday () in
    Bigarray.Array1.fill t (Char.chr (cap + 1));
    Bigarray.Array1.unsafe_set t start '\000';
      let cnt = counters (wpath ^ ".cnt") nw in
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
    (try Sys.remove (wpath ^ ".cnt") with _ -> ());
    Sys.rename wpath path
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

(* ---- the three viewing angles ------------------------------------------- *)

(* H is built around the up-down axis, so the table answers "how far from H"
   for that axis alone.  Turn the whole cube and it answers for another axis,
   and every answer is a lower bound on the same distance, because a rotation
   does not change how far a position is from solved.  Three answers, keep
   the largest.

   No symmetry acting on cubies is needed for this.  A rotation relabels the
   faces, so it turns a maneuver into another maneuver -- the conjugated
   position is the conjugated WORD -- and along the search it turns a move
   into another move, so the same tables follow it with a permuted index.

   Face order U R F D L B.  The second line turns the cube about the front-
   back axis, U -> R -> D -> L -> U, which carries the up-down axis onto the
   right-left one; the third turns it about the right-left axis, U -> F -> D
   -> B -> U.  Both are rotations, so a clockwise turn stays clockwise.     *)
let nax = 3
let axis = [| [| 0; 1; 2; 3; 4; 5 |];
              [| 1; 3; 2; 4; 0; 5 |];
              [| 2; 1; 3; 5; 4; 0 |] |]

(* the same relabelling on the twelve quarter turns and on the eighteen *)
let cmv = Array.init nax (fun i ->
  Array.init nmv (fun m -> 2 * axis.(i).(face m) + (m land 1)))
let cmv18 = Array.init nax (fun i ->
  Array.init 18 (fun m -> 3 * axis.(i).(m / 3) + m mod 3))

(* ---- the sixteen symmetries of the up-down axis -------------------------- *)

(* H is invariant under every symmetry of the cube that keeps the up-down axis
   in place, and there are sixteen of those.  Two cosets carried onto each
   other by one of them are the same distance from solved, so one entry serves
   both, and Reid's 190 080 values of e fall into 12 094 families.  That count
   is the check on everything here.

   A symmetry is again a relabelling of the faces, and a mirror is allowed as
   well as a rotation: the fold only needs the distance to be preserved, and
   the mirror image of a maneuver solves the mirror image of the position.  A
   mirror does turn a clockwise turn into an anticlockwise one, which is the
   flag below.                                                              *)
let nsym = 16

let sym_compose (a1, m1) (a2, m2) =
  (Array.init 6 (fun f -> a2.(a1.(f))), m1 <> m2)

let syms =
  let gens = [ ([| 0; 2; 4; 3; 5; 1 |], false);  (* U fixed, R -> F -> L -> B *)
               ([| 3; 1; 5; 0; 4; 2 |], false);  (* U <-> D, F <-> B          *)
               ([| 0; 4; 2; 3; 1; 5 |], true) ]  (* the mirror R <-> L        *)
  in
  let l = ref [ (Array.init 6 (fun f -> f), false) ] in
  let grew = ref true in
  while !grew do
    grew := false;
    List.iter (fun g ->
      List.iter (fun x ->
        let (ya, ym) = sym_compose x g in
        if not (List.exists (fun (a, m) -> a = ya && m = ym) !l) then begin
          l := (ya, ym) :: !l; grew := true end) !l) gens
  done;
  Array.of_list (List.rev !l)

(* the same relabelling on the twelve quarter turns, direction reversed by a
   mirror *)
let smv = Array.map (fun (a, m) ->
  Array.init nmv (fun q ->
    2 * a.(face q) + (if m then 1 - (q land 1) else q land 1))) syms

(* How a symmetry acts on a coordinate.  A value is reached from the solved
   one by a word, the symmetry turns that word into another word, and the
   value that one reaches is the answer.  Taking the values in the order a
   breadth first sweep finds them means the parent's answer is always ready,
   so no word is ever written down.                                         *)
let sym_of_coord n mt start rel =
  let a = Array.make n (-1) in
  let order = Array.make n 0 and prev = Array.make n 0 and via = Array.make n 0 in
  let seen = Array.make n false in
  seen.(start) <- true; order.(0) <- start;
  let head = ref 0 and tail = ref 1 in
  while !head < !tail do
    let x = order.(!head) in incr head;
    for q = 0 to nmv - 1 do
      let y = mt.(x).(q) in
      if not seen.(y) then begin
        seen.(y) <- true; prev.(y) <- x; via.(y) <- q;
        order.(!tail) <- y; incr tail
      end
    done
  done;
  if !tail <> n then (prerr_endline "a coordinate is not connected"; exit 1);
  a.(start) <- start;
  for i = 1 to n - 1 do
    let x = order.(i) in
    a.(x) <- mt.(a.(prev.(x))).(rel.(via.(x)))
  done;
  a

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
  (* the same position seen along axis i, built by relabelling the words *)
  let position_ax i k =
    let _, man = prefixes.(k) in
    let c = ref (solved ()) in
    Array.iter (fun m -> c := mult !c moves18.(cmv18.(i).(m)))
      (Array.append sf_man fs_man);
    Array.iter (fun m -> c := mult !c moves.(cmv.(i).(m))) man;
    !c in

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

  (* WHAT MAKES A VIEW SOUND is that the relabelling is a rotation of the
     cube, so that the position it describes is at the same distance as the
     one being searched.  Anything else may read HIGHER than the distance,
     and then the search cuts the branch that holds the solution and says no.
     No run would report that, so it is checked here, twice.

     Once by hand: opposite faces must stay opposite, and the rotation must
     not be a mirror.  Faces are U R F D L B, so a face and its opposite are
     three apart, the axis of a face is its index modulo three and the sign
     is whether it is one of the first three.  A mirror shows up as a signed
     permutation of determinant minus one, and a mirror turns a clockwise
     turn into an anticlockwise one, which the relabelling does not do.

     Once by machine: conjugating a position by a rotation cannot change the
     cycle structure of its corner and edge permutations.  A relabelling that
     is not a rotation gets that wrong on a random word almost at once.     *)
  let rotation_ok a =
    let seen = Array.make 6 false and ok = ref true in
    Array.iter (fun f -> if f < 0 || f > 5 || seen.(f) then ok := false
                         else seen.(f) <- true) a;
    for f = 0 to 5 do
      if a.((f + 3) mod 6) <> (a.(f) + 3) mod 6 then ok := false done;
    let p = Array.init 3 (fun i -> a.(i) mod 3) in
    let sgn = ref 1 in
    for i = 0 to 2 do if a.(i) >= 3 then sgn := - !sgn done;
    let par = ref 1 in
    for i = 0 to 2 do for j = i + 1 to 2 do
      if p.(i) > p.(j) then par := - !par done done;
    !ok && !sgn * !par = 1 in

  let cycle_type p =
    let n = Array.length p in
    let seen = Array.make n false and l = ref [] in
    for i = 0 to n - 1 do
      if not seen.(i) then begin
        let j = ref i and len = ref 0 in
        while not seen.(!j) do seen.(!j) <- true; j := p.(!j); incr len done;
        l := !len :: !l
      end
    done;
    List.sort compare !l in

  let view_check words =
    for i = 0 to nax - 1 do
      if not (rotation_ok axis.(i)) then begin
        log "view %d is not a rotation of the cube\n" i; exit 1 end
    done;
    let st = ref 20260816 in
    let rnd k = st := (!st * 1103515245 + 12345) land 0x3FFFFFFF; !st mod k in
    let bad = ref 0 in
    for _ = 1 to words do
      let len = 1 + rnd 14 in
      let w = Array.init len (fun _ -> rnd nmv) in
      let build cw =
        let c = ref (solved ()) in
        Array.iter (fun m -> c := mult !c moves.(cw.(m))) w; !c in
      let g = build (Array.init nmv (fun m -> m)) in
      let tg = cycle_type g.cp, cycle_type g.ep in
      for i = 0 to nax - 1 do
        let h = build cmv.(i) in
        if (cycle_type h.cp, cycle_type h.ep) <> tg then incr bad
      done
    done;
    log "the three angles: rotations, and %d random words keep their cycles"
      words;
    log "%s\n" (if !bad = 0 then "" else Printf.sprintf " -- %d WRONG" !bad);
    if !bad > 0 then exit 1 in

  (* The sixteen symmetries and the families of e values they make.  This
     needs no distance table, so the count that checks it -- Reid's 12 094 --
     is had before anything big is built.                                   *)
  let families () =
    if Array.length syms <> nsym then begin
      log "the group came out at %d, not %d\n" (Array.length syms) nsym;
      exit 1 end;
    Array.iteri (fun i (a, _) ->
      let ok = ref (a.(0) = 0 || a.(0) = 3) in
      for f = 0 to 5 do
        if a.((f + 3) mod 6) <> (a.(f) + 3) mod 6 then ok := false done;
      if not !ok then begin
        log "symmetry %d does not keep the up-down axis\n" i; exit 1 end) syms;
    let sym_e  = Array.init nsym (fun i -> sym_of_coord n_e  mt_e  e0  smv.(i)) in
    let sym_cl = Array.init nsym (fun i -> sym_of_coord n_cl mt_cl cl0 smv.(i)) in
    let sym_ct = Array.init nsym (fun i -> sym_of_coord n_ct mt_ct ct0 smv.(i)) in
    let rep = Array.make n_e 0 and which = Array.make n_e 0 in
    for e = 0 to n_e - 1 do
      let best = ref max_int and bs = ref 0 in
      for i = 0 to nsym - 1 do
        if sym_e.(i).(e) < !best then (best := sym_e.(i).(e); bs := i) done;
      rep.(e) <- !best; which.(e) <- !bs
    done;
    let cls = Array.make n_e (-1) and nrep = ref 0 in
    for e = 0 to n_e - 1 do
      if rep.(e) = e then begin cls.(e) <- !nrep; incr nrep end done;
    log "%d symmetries keep the up-down axis, and %d values of e make %d families, a factor of %.2f\n"
      nsym n_e !nrep (float_of_int n_e /. float_of_int !nrep);
    if !nrep <> 12094 then begin
      log "Reid says 12 094 families, so the symmetries are wrong\n"; exit 1 end;
    (sym_cl, sym_ct, rep, which, cls, !nrep) in

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
      if h.(31) > 0 then exit 1;
      t in
    ignore (small "(cl, ct)" "h_check1.tbl" (n_cl, mt_cl, cl0) (n_ct, mt_ct, ct0));
    let t = small "(e, cl)"  "h_check2.tbl" (n_e, mt_e, e0) (n_cl, mt_cl, cl0) in
    ignore t;
    view_check 20000;
    ignore (families ());
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

  (* ---- the folded table, as Rocq: the 29 GB table is not needed --------- *)

  (* This reads the 883 Mb folded file and nothing else, so it comes before
     the big table is opened: a chunk can be emitted again after a reboot has
     emptied /dev/shm, without the ten minute build.

     The same shape as bench/p1gen.ml, which is the spec: fifteen four bit
     entries to an int63 word, chunks of two million words, and a PRIMITIVE
     ARRAY LITERAL rather than a list -- p1gen measured a list at 24 bytes a
     word for its cells and about 70 more for the term that denotes it, both
     of them still reachable next to the array built from them.

     1 851 470 460 entries is 123 431 364 words in 59 chunks, against the five
     that hold the folded phase 1 table.  Whether that can be loaded is the
     whole question, and one chunk answers it.                              *)
  if mode = "dump" then begin
    let nper = 15 and cwords = 1 lsl 21 in
    let fpath = try Sys.getenv "H_FTBL" with Not_found ->
      Printf.sprintf "h_fold%d.tbl" cap in
    if not (Sys.file_exists fpath) then begin
      prerr_endline (fpath ^ " is missing -- run the fold first"); exit 1 end;
    (* the fold's own count, so the two modes cannot drift apart *)
    let _, _, _, _, _, nrep = families () in
    let n_fold = nrep * n_cl * n_ct in
    let words = (n_fold + nper - 1) / nper in
    let nchunk = (words + cwords - 1) / cwords in
    let chunk = arg4 0 in
    Printf.eprintf "%d entries, %d words, %d chunks; emitting chunk %d\n%!"
      n_fold words nchunk chunk;
    if chunk < 0 || chunk >= nchunk then begin
      prerr_endline "no such chunk"; exit 1 end;
    let fd = Unix.openfile fpath [Unix.O_RDONLY] 0o644 in
    let f = Bigarray.array1_of_genarray
        (Unix.map_file fd Bigarray.char Bigarray.c_layout false
           [| (n_fold + 1) / 2 |]) in
    Unix.close fd;
    let get k =
      let b = Char.code (Bigarray.Array1.unsafe_get f (k / 2)) in
      if k land 1 = 0 then b land 0x0f else b lsr 4 in
    let word w =
      let v = ref 0 in
      for j = nper - 1 downto 0 do
        let k = w * nper + j in
        v := (!v lsl 4) lor (if k < n_fold then get k else 0)
      done;
      !v in
    Printf.printf
      "(* GENERATED by ocaml/rubik_h.ml -- do not edit.                    *)\n\
       (* Reid's table folded by the sixteen symmetries of the up-down     *)\n\
       (* axis, chunk %d of %d: words %d .. %d.                            *)\n\n\
       From Stdlib Require Import Uint63.\n\
       From Stdlib Require Import PArray.\n\n\
       Local Open Scope uint63_scope.\n\n" chunk nchunk
      (chunk * cwords) (min words ((chunk + 1) * cwords) - 1);
    let lo = chunk * cwords and hi = min words ((chunk + 1) * cwords) in
    Printf.printf "Definition h_chunk_%02d : array int := [|\n" chunk;
    for w = lo to hi - 1 do
      Printf.printf "%d%s" (word w)
        (if w = hi - 1 then "" else if (w - lo) mod 8 = 7 then ";\n" else "; ")
    done;
    Printf.printf "\n| 0 |].\n";
    exit 0
  end;

  (* ---- the table -------------------------------------------------------- *)
  (* WHERE THE TABLE LIVES IS NOT A DETAIL.  A file on an ordinary disk is
     written back by the kernel as the sweep dirties it, and from the tenth
     level on a level dirties the whole table, so the build stops computing
     and waits on the disk: measured on the reference machine, 18 workers
     idle at 65% iowait and 60 Mb a second.  On tmpfs the pages never leave
     memory.  H_TBL says where, and the Makefile puts it in /dev/shm.       *)
  let path =
    try Sys.getenv "H_TBL" with Not_found -> Printf.sprintf "h_cap%d.tbl" cap in
  if mode <> "build" && not (Sys.file_exists path) then begin
    prerr_endline (path ^ " is missing -- run the build first");
    exit 1
  end;
  let nw = if mode = "build" then arg4 1 else 1 in
  let t0 = Unix.gettimeofday () in
  let tbl = build path cap nw start (n_e, mt_e) (n_cl, mt_cl) (n_ct, mt_ct) in
  (* ---- the fold, for the sake of Rocq ----------------------------------- *)

  (* Rocq cannot be handed 29.1 GB, and it does not have to be.  One entry
     serves a whole family, so what is left is 12 094 x 70 x 2187 entries at
     four bits, 883 MB, and packed sixteen to an int63 word that is 116
     million cells -- fewer than the 149 million the phase 1 table already
     loads.                                                                 *)
  if mode = "fold" then begin
    let sym_cl, sym_ct, rep, which, cls, nrep = families () in
    let fpath = try Sys.getenv "H_FTBL" with Not_found ->
      Printf.sprintf "h_fold%d.tbl" cap in
    let n_fold = nrep * n_cl * n_ct in
    let bytes = (n_fold + 1) / 2 in
    log "folded table: %d entries, %d bytes\n" n_fold bytes;
    let fd = Unix.openfile (fpath ^ ".part")
        [Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC] 0o644 in
    Unix.LargeFile.ftruncate fd (Int64.of_int bytes);
    let f = Bigarray.array1_of_genarray
        (Unix.map_file fd Bigarray.char Bigarray.c_layout true [| bytes |]) in
    Unix.close fd;
    let t1 = Unix.gettimeofday () in
    for e = 0 to n_e - 1 do
      if rep.(e) = e then begin
        let src = e * n_cl * n_ct and dst = cls.(e) * n_cl * n_ct in
        for j = 0 to n_cl * n_ct - 1 do
          let v = Char.code (Bigarray.Array1.unsafe_get tbl (src + j)) in
          let k = dst + j in
          let b = Char.code (Bigarray.Array1.unsafe_get f (k / 2)) in
          Bigarray.Array1.unsafe_set f (k / 2) (Char.chr
            (if k land 1 = 0 then (b land 0xf0) lor v
             else (b land 0x0f) lor (v lsl 4)))
        done
      end
    done;
    log "written in %.0f s\n" (Unix.gettimeofday () -. t1);

    (* THE CHECK.  A lookup through the fold must give exactly what the flat
       table gives, on positions the search really meets.                   *)
    let fold_get e c t =
      let i = which.(e) in
      let k = (cls.(rep.(e)) * n_cl + sym_cl.(i).(c)) * n_ct + sym_ct.(i).(t) in
      let b = Char.code (Bigarray.Array1.unsafe_get f (k / 2)) in
      if k land 1 = 0 then b land 0x0f else b lsr 4 in
    let st = ref 17 and bad = ref 0 in
    let rnd k = st := (!st * 1103515245 + 12345) land 0x3FFFFFFF; !st mod k in
    for _ = 1 to 200000 do
      let e = ref e0 and c = ref cl0 and t = ref ct0 in
      for _ = 1 to 1 + rnd 20 do
        let q = rnd nmv in
        e := mt_e.(!e).(q); c := mt_cl.(!c).(q); t := mt_ct.(!t).(q)
      done;
      let flat = Char.code (Bigarray.Array1.unsafe_get tbl
                   ((!e * n_cl + !c) * n_ct + !t)) in
      if fold_get !e !c !t <> flat then incr bad
    done;
    log "200 000 random positions through the fold: %d disagree\n" !bad;
    if !bad > 0 then exit 1;
    Sys.rename (fpath ^ ".part") fpath;
    log "%s written\n" fpath;
    exit 0
  end;

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


  (* ---- the node count, and the run -------------------------------------- *)
  if mode <> "count" && mode <> "run" then
    (prerr_endline "unknown mode"; exit 1);
  let k = arg4 0 in
  let job, njobs =
    if mode = "run" && Array.length Sys.argv > 6
    then int_of_string Sys.argv.(5), int_of_string Sys.argv.(6) else 0, 1 in
  let name, man = prefixes.(k) in
  let root = position k in

  let maxd = 32 in
  let cps = Array.init maxd (fun _ -> Array.make 8 0) in
  let eps = Array.init maxd (fun _ -> Array.make 12 0) in
  let ec = Array.make_matrix nax maxd 0 in
  let cc = Array.make_matrix nax maxd 0 in
  let tc = Array.make_matrix nax maxd 0 in
  let fc = Array.make maxd 0 in
  let nodes = ref 0L in

  let heur d =
    let h = ref 0 in
    for i = 0 to nax - 1 do
      let v = Char.code (Bigarray.Array1.unsafe_get tbl
                ((ec.(i).(d) * n_cl + cc.(i).(d)) * n_ct + tc.(i).(d))) in
      if v > !h then h := v
    done;
    !h in

  let is_solved d =
    let r = ref (tc.(0).(d) = ct0 && fc.(d) = 0) in
    for i = 0 to 7 do if cps.(d).(i) <> i then r := false done;
    for i = 0 to 11 do if eps.(d).(i) <> i then r := false done;
    !r in

  let step d m =
    let d' = d + 1 in
    let mcp = moves.(m).cp and mep = moves.(m).ep in
    for i = 0 to 7 do cps.(d').(i) <- cps.(d).(mcp.(i)) done;
    for i = 0 to 11 do eps.(d').(i) <- eps.(d).(mep.(i)) done;
    for i = 0 to nax - 1 do
      let mi = cmv.(i).(m) in
      ec.(i).(d') <- mt_e.(ec.(i).(d)).(mi);
      cc.(i).(d') <- mt_cl.(cc.(i).(d)).(mi);
      tc.(i).(d') <- mt_ct.(tc.(i).(d)).(mi)
    done;
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
  for i = 0 to nax - 1 do
    let c = position_ax i k in
    ec.(i).(0) <- e_coord c; cc.(i).(0) <- cl_coord c; tc.(i).(0) <- ct_coord c
  done;
  fc.(0) <- flip root;
  (* Only one job talks.  With a job per prefix there are 132 of them.      *)
  if job = 0 then begin
    view_check 2000;
    log "position %d: superflip . fourspot . %s\n" k name;
    log "  prefix %d moves, so Reid's search of it is depth %d\n"
      (Array.length man) (24 - Array.length man);
    log "  root table value: %d\n" (heur 0)
  end;

  if mode = "count" then
    for d = 10 to depth do
      nodes := 0L;
      let t1 = Unix.gettimeofday () in
      let got = dfs 0 d (-1) 0 in
      let s = Unix.gettimeofday () -. t1 in
      log "depth %2d : %14Ld nodes, %8.1f s, %.2e nodes/s%s\n" d !nodes s
        (Int64.to_float !nodes /. (if s > 0. then s else 1.))
        (if got then "  SOLVED -- which would be a discovery, check it" else "")
    done
  else begin
    (* THE RUN.  One job takes some of the moves the search may play first,
       and every job plays every second move the rule allows after it.  The
       first move is NOT cut down: the reduction of doc/reid-1998-fourspot.md
       already fixed the beginning of the maneuver, and asking the rest to be
       canonical as well would need an argument nobody has made.             *)
    let pre = ref [] in
    for m1 = 0 to nmv - 1 do
      for m2 = 0 to nmv - 1 do
        if allowed m1 1 m2 then pre := (m1, m2) :: !pre done done;
    let pre = List.rev !pre in
    if job = 0 then log "%d prefixes over %d jobs\n" (List.length pre) njobs;
    if njobs > List.length pre && job = 0 then
      log "WARNING: more jobs than prefixes, the last ones have nothing to do\n";
    let t1 = Unix.gettimeofday () in
    let got = ref false in
    (* A JOB THAT SAYS NOTHING FOR AN HOUR CANNOT BE TOLD FROM ONE THAT HAS
       HUNG.  Every prefix it finishes prints a line, so the run can be seen
       to be moving and what is left can be read off it.                    *)
    let mine = List.length (List.filteri (fun i _ -> i mod njobs = job) pre) in
    let done_ = ref 0 in
    List.iteri (fun idx (m1, m2) ->
      if idx mod njobs = job && not !got then begin
        let n0 = !nodes in
        step 0 m1; step 1 m2;
        let run = if face m2 = face m1 then 2 else 1 in
        if dfs 2 (depth - 2) m2 run then got := true;
        incr done_;
        Printf.printf "  job %d prefix %s %s (%d of %d) : %Ld nodes, %.0f s\n%!"
          job mvname.(m1) mvname.(m2) !done_ mine
          (Int64.sub !nodes n0) (Unix.gettimeofday () -. t1)
      end) pre;
    Printf.printf
      "position %d job %d/%d depth %d : %Ld nodes, %.1f s, solution %b\n%!"
      k job njobs depth !nodes (Unix.gettimeofday () -. t1) !got
  end
