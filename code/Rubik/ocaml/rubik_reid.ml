(* Reid's proof that superflip composed with fourspot is exactly 26 quarter
   turns, checked.  Cube-Lovers, 2 August 1998; he reports 153 hours for the
   six searches.  This program is the prototype, to be mimicked in Rocq.

   His proof does NOT search to depth 24.  It searches six positions, one to
   22 quarter turns and five to 21, and gets the other two or three moves
   from an argument.  The argument is what this program checks first, since
   it is cheap and it is the whole saving.

   THE ENGINE.  Let p be the position and C the half turn of the whole cube
   about the up-down axis.  Reid observes that fourspot . C moves only face
   centres, (F B)(R L), and that quarter turns never move face centres, so
   fourspot . C commutes with every quarter turn; superflip is central in
   the cube group, so p . C does too.

   We have no face centres in this model -- a cube is eight corners and
   twelve edges -- so we check the consequence instead, which is what the
   proof actually uses:

       for every quarter turn q,   p^-1 q p = sigma q

   where sigma is conjugation by C: it swaps R with L and F with B, leaves U
   and D alone, and keeps the direction of every turn, C being a rotation.
   Twelve equalities between permutations of twenty cubies.  If they hold,
   a maneuver may be rotated: if p = m1 m2 ... mL then

       p = m2 ... mL (sigma m1)

   and that is Reid's cyclic shift, the thing that turns a depth-24 search
   into a depth-22 one.

   WHAT IS CHECKED HERE, and what is not.  The commutation, the shift, the
   26-move maneuver and the parity are all checked below.  Reid's
   propositions 1 and 2 -- that the position is a local maximum, and that
   every maneuver reduces to one of six prefixes -- are NOT checked; they
   are taken from the post.  Proposition 2 is what makes the six prefixes
   the right six, so the searches below prove the bound only together with
   it.  Proving it is the Rocq job.

   ONE TRAP, worth knowing before anyone ports this.  Reid's proposition 1
   needs that turns of R, L, F and B cannot flip an edge.  That is FALSE in
   the orientation convention this file uses, where F and B are the turns
   that flip; it is true in the convention where U and D are.  There is one
   such convention per axis and he uses the up-down one, as he must, since
   fourspot and his sixteen symmetries are built around that axis.

   usage: rubik_reid <cap> check           the cheap checks, no table
          rubik_reid <cap> build           build the 2.2 GB table
          rubik_reid <cap> run <i> <d>     search prefix i (0..5) at depth d *)

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

let inv a =
  let r = solved () in
  for i = 0 to 7 do r.cp.(a.cp.(i)) <- i; r.co.(a.cp.(i)) <- (3 - a.co.(i)) mod 3 done;
  for i = 0 to 11 do r.ep.(a.ep.(i)) <- i; r.eo.(a.ep.(i)) <- a.eo.(i) done;
  r

let eqc a b =
  let r = ref true in
  for i = 0 to 7 do if a.cp.(i) <> b.cp.(i) || a.co.(i) <> b.co.(i) then r := false done;
  for i = 0 to 11 do if a.ep.(i) <> b.ep.(i) || a.eo.(i) <> b.eo.(i) then r := false done;
  !r

(* The six clockwise quarter turns, U R F D L B, as in rubik_par.ml.        *)
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

let moves18 =
  Array.init 18 (fun m ->
    let b = basic.(m / 3) in
    match m mod 3 with
    | 0 -> b | 1 -> mult b b | _ -> mult (mult b b) b)

let nmv = 12
let moves =
  Array.init nmv (fun m ->
    let b = basic.(m / 2) in
    if m land 1 = 0 then b else mult (mult b b) b)

let face m = m / 2
let opp f = (f + 3) mod 6
let mvname = [| "U"; "U'"; "R"; "R'"; "F"; "F'"; "D"; "D'"; "L"; "L'"; "B"; "B'" |]

(* sigma: conjugation by the half turn of the whole cube about the up-down
   axis.  It sends R to L and F to B, fixes U and D, and keeps directions.  *)
let sigface = [| 0; 4; 5; 3; 1; 2 |]
let sigma m = 2 * sigface.(face m) + (m land 1)

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

(* ---- the corner database ------------------------------------------------ *)
(* The eight corners on their own: how they are arranged, 8! of that, and how
   they are twisted, 3^7 of that.  88 179 840 states, one byte each, so 88 MB
   -- twenty-five times smaller than the summary table, and its distances run
   higher, which is the whole point.  Distance among the corners alone is a
   lower bound on distance in the group, so it is a legal estimate.

   The two halves move independently: where a corner goes depends only on the
   arrangement, and how it is twisted only on the twists, so one small table
   for each and the index is arrangement * 2187 + twist.                     *)
let n_cperm = 40320

let fact = [| 1; 1; 2; 6; 24; 120; 720; 5040 |]

let cprank (p : int array) =
  let r = ref 0 in
  for i = 0 to 6 do
    let c = ref 0 in
    for j = i + 1 to 7 do if p.(j) < p.(i) then incr c done;
    r := !r + !c * fact.(7 - i)
  done; !r

let cperm_of_rank r =
  let left = Array.init 8 (fun i -> i) and n = ref 8 and r = ref r in
  let p = Array.make 8 0 in
  for i = 0 to 7 do
    let d = !r / fact.(7 - i) in
    r := !r mod fact.(7 - i);
    p.(i) <- left.(d);
    for j = d to !n - 2 do left.(j) <- left.(j + 1) done;
    decr n
  done; p

let mk_mt_cp () =
  let t = Array.make_matrix n_cperm nmv 0 in
  for i = 0 to n_cperm - 1 do
    let q = cperm_of_rank i in
    for m = 0 to nmv - 1 do
      let mcp = moves.(m).cp in
      t.(i).(m) <- cprank (Array.init 8 (fun k -> q.(mcp.(k))))
    done
  done; t


(* ---- an edge database --------------------------------------------------- *)
(* The corner database is the wrong one for this position: its corners are
   nearly solved -- no twist at all, and the arrangement an involution -- so
   it scores only 8 where the summary table scores 12.  All the difficulty is
   in the edges, every one of the twelve flipped.  So: six chosen edges, where
   they sit and which way round.  12*11*10*9*8*7 = 665 280 arrangements times
   2^6 flips = 42 577 920 states, 42 MB.

   The two halves are cheap to move.  A move takes the edge in slot j to the
   slot i with m.ep(i) = j, and adds m.eo(i) to its orientation.  The edge
   keeps its name, so the six flip bits are never permuted -- they are only
   flipped by a mask.  One table for the new arrangement and one for the mask,
   both indexed by (arrangement, move), and the search updates the pair with
   two lookups.                                                              *)
let n_earr = 665280            (* 12*11*10*9*8*7, six labelled edges in twelve slots *)
let n_edb = n_earr * 64

(* the six edges this database watches, by name *)
let eset = [| 0; 1; 2; 3; 4; 5 |]
let eset2 = [| 6; 7; 8; 9; 10; 11 |]

let erank (slots : int array) =
  let avail = Array.init 12 (fun i -> i) and n = ref 12 and r = ref 0 in
  for k = 0 to 5 do
    let d = ref 0 in
    while avail.(!d) <> slots.(k) do incr d done;
    r := !r * !n + !d;
    for j = !d to !n - 2 do avail.(j) <- avail.(j + 1) done;
    decr n
  done; !r

let eunrank r =
  (* erank builds  r = d0*11*10*9*8*7 + d1*10*9*8*7 + ... + d5,  with dk in
     0 .. 11-k, so the digits come back smallest radix first.                *)
  let d = Array.make 6 0 and r = ref r in
  for k = 5 downto 0 do
    let radix = 12 - k in
    d.(k) <- !r mod radix; r := !r / radix
  done;
  let avail = Array.init 12 (fun i -> i) and n = ref 12 in
  let out = Array.make 6 0 in
  for k = 0 to 5 do
    out.(k) <- avail.(d.(k));
    for j = d.(k) to !n - 2 do avail.(j) <- avail.(j + 1) done;
    decr n
  done; out

let mepinv = Array.init nmv (fun m ->
  let a = Array.make 12 0 in
  for i = 0 to 11 do a.(moves.(m).ep.(i)) <- i done; a)

let mk_edge_tables () =
  let newarr = Array.make (n_earr * nmv) 0 in
  let fmask = Bytes.make (n_earr * nmv) '\000' in
  let tmp = Array.make 6 0 in
  for a = 0 to n_earr - 1 do
    let slots = eunrank a in
    for m = 0 to nmv - 1 do
      let mi = mepinv.(m) and meo = moves.(m).eo in
      let msk = ref 0 in
      for k = 0 to 5 do
        let ns = mi.(slots.(k)) in
        tmp.(k) <- ns;
        if meo.(ns) <> 0 then msk := !msk lor (1 lsl k)
      done;
      newarr.(a * nmv + m) <- erank tmp;
      Bytes.unsafe_set fmask (a * nmv + m) (Char.unsafe_chr !msk)
    done
  done;
  (newarr, fmask)

(* the state of the six watched edges, read off a cube *)
let ecoord (set : int array) c =
  let slots = Array.make 6 0 and fl = ref 0 in
  for i = 0 to 11 do
    for k = 0 to 5 do
      if c.ep.(i) = set.(k) then begin
        slots.(k) <- i;
        if c.eo.(i) <> 0 then fl := !fl lor (1 lsl k)
      end
    done
  done;
  erank slots * 64 + !fl

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

(* ---- the position, and the six prefixes of Reid's proposition 2 --------- *)

(* superflip, by the 20-face-turn word rubik_par.ml also uses               *)
let sf_man = [|0;4;6;15;3;16;3;1;12;16;3;2;11;4;6;5;12;16;1;7|]
(* fourspot, F2 B2 U D' R2 L2 U D', his choice of orientation               *)
let fs_man = [|7;16;0;11;4;13;0;11|]
let apply18 man =
  let c = ref (solved ()) in Array.iter (fun m -> c := mult !c moves18.(m)) man; !c

let applyq w =
  let c = ref (solved ()) in List.iter (fun m -> c := mult !c moves.(m)) w; !c

(* U2 D2 L F2 U' D R2 B U' D' R L F2 R U D' R' L U F' B'   (26q)            *)
let man26 =
  [0;0; 6;6; 8; 4;4; 1; 6; 2;2; 10; 1; 7; 2; 8; 4;4; 2; 0; 7; 3; 8; 0; 5; 11]

(* R U ;  R' U D ;  R' U F' ;  R' U R' ;  R' U B' ;  R' U L'                *)
let prefixes =
  [| [2;0]; [3;0;6]; [3;0;5]; [3;0;3]; [3;0;11]; [3;0;9] |]

let word_str w = String.concat " " (List.map (fun m -> mvname.(m)) w)

let () =
  let cap = int_of_string Sys.argv.(1) in
  let mode = Sys.argv.(2) in

  let sf = apply18 sf_man in
  let ok = ref true in
  for i = 0 to 7 do if sf.cp.(i) <> i || sf.co.(i) <> 0 then ok := false done;
  for i = 0 to 11 do if sf.ep.(i) <> i || sf.eo.(i) <> 1 then ok := false done;
  if not !ok then (prerr_endline "superflip check FAILED"; exit 1);
  let p = apply18 (Array.append sf_man fs_man) in

  (* ---- the cheap checks ------------------------------------------------- *)
  let fail s = Printf.printf "  FAILED: %s\n%!" s; exit 1 in
  let pass s = Printf.printf "  ok: %s\n%!" s in

  Printf.printf "checking Reid's engine\n";

  (* 1. the commutation, twelve equalities                                   *)
  let pi = inv p in
  for m = 0 to nmv - 1 do
    if not (eqc (mult (mult pi moves.(m)) p) moves.(sigma m)) then
      fail (Printf.sprintf "p^-1 %s p <> sigma %s" mvname.(m) mvname.(m))
  done;
  pass "p^-1 q p = sigma q for all twelve quarter turns";

  (* sigma really is an involution on the moves, as a half turn must be      *)
  for m = 0 to nmv - 1 do
    if sigma (sigma m) <> m then fail "sigma is not an involution" done;
  pass "sigma is an involution";

  (* 2. the 26-move word gives the position                                  *)
  if not (eqc (applyq man26) p) then fail "the 26q maneuver does not give p";
  pass (Printf.sprintf "the 26q maneuver gives p: %s" (word_str man26));

  (* 3. the cyclic shift, applied all the way round                          *)
  let shift = function [] -> [] | m :: w -> w @ [sigma m] in
  let w = ref man26 in
  for i = 1 to List.length man26 do
    w := shift !w;
    if not (eqc (applyq !w) p) then
      fail (Printf.sprintf "shift %d of the 26q maneuver does not give p" i)
  done;
  if !w <> man26 then
    Printf.printf "  note: %d shifts do not return the same word (sigma is applied)\n"
      (List.length man26);
  pass "every cyclic shift of the 26q maneuver still gives p";

  (* 4. the parity that rules out 25                                         *)
  let par = perm_parity p.cp in
  if par <> 0 then fail "the corner permutation is odd -- 25 is NOT excluded";
  pass "the corner permutation is even, so the distance is even and 25 is out";

  Printf.printf "so: nothing at 24 proves 26, and the 26q word proves at most 26.\n";

  (* the edge coordinate must be a bijection before anything is built on it *)
  let bad = ref 0 in
  for a = 0 to n_earr - 1 do
    if erank (eunrank a) <> a then incr bad done;
  if !bad > 0 then fail (Printf.sprintf "erank/eunrank disagree on %d of %d" !bad n_earr);
  pass (Printf.sprintf "erank and eunrank are inverse on all %d arrangements" n_earr);

  (* ---- the rephrasing, tested ------------------------------------------- *)
  (* Reid needs "a maneuver of only {R,R',F,F',L,L',B,B'} cannot flip any
     edge".  That is FALSE in this file's convention, where F and B are the
     turns that flip.  The fix is not to change the convention but to turn
     the POSITION: he says outright that the orientation of fourspot is a
     choice, so choose the front-back one.  Then his special four turns are
     {F,F',B,B'} and his other eight are {U,U',D,D',R,R',L,L'} -- which are
     exactly the turns that carry no flip here.  Everything below tests that
     this really works.                                                      *)
  if mode = "rephrase" then begin
    Printf.printf "\ntesting the rephrasing: fourspot about the front-back axis\n";

    (* his word rotated by U->F, F->D, D->B, B->U, R and L fixed:
       F2 B2 U D' R2 L2 U D'   becomes   D2 U2 F B' R2 L2 F B'            *)
    let fs_fb = [|10;1;6;17;4;13;6;17|] in
    let p' = apply18 (Array.append sf_man fs_fb) in

    (* sigma', conjugation by the half turn about the front-back axis:
       it swaps U with D and R with L, and fixes F and B.                    *)
    let sigface' = [| 3; 4; 2; 0; 1; 5 |] in
    let sigma' m = 2 * sigface'.(face m) + (m land 1) in
    let pi' = inv p' in
    for m = 0 to nmv - 1 do
      if not (eqc (mult (mult pi' moves.(m)) p') moves.(sigma' m)) then
        fail (Printf.sprintf "p'^-1 %s p' <> sigma' %s" mvname.(m) mvname.(m))
    done;
    pass "the engine still holds: p'^-1 q p' = sigma' q for all twelve turns";

    if perm_parity p'.cp <> 0 then fail "p' has odd corner parity";
    pass "p' still has even corner parity, so 25 is still out";

    (* the eight, in this convention: U U' D D' R R' L L'                    *)
    let eight = [0;1;6;7;2;3;8;9] and four = [4;5;10;11] in
    Printf.printf "  the eight: %s        the four: %s\n"
      (word_str eight) (word_str four);

    (* each of the eight carries no flip at all, so a product of them
       permutes the orientation vector and never changes a value            *)
    List.iter (fun m ->
      Array.iter (fun x -> if x <> 0 then
        fail (Printf.sprintf "%s carries a flip" mvname.(m))) moves.(m).eo) eight;
    pass "none of the eight carries a flip, so no product of them flips an edge";

    (* and Reid's own eight, read literally here, DOES flip -- which is why
       the naive port would be unsound                                       *)
    let reid_eight = [2;3;4;5;8;9;10;11] in
    let bad = List.filter (fun m ->
      Array.exists (fun x -> x <> 0) moves.(m).eo) reid_eight in
    if bad = [] then fail "expected Reid's literal eight to flip here"
    else Printf.printf
      "  ok: read literally in this convention his eight WOULD flip (%s), \
so the turn of the position is doing real work\n" (word_str bad);

    if Array.exists (fun x -> x <> 1) p'.eo then
      fail "p' does not have every edge flipped";
    pass "p' has every edge flipped, so the eight alone cannot reach it";

    (* the other half: the four alone generate only sixteen positions, F and
       B sharing no cubie, and p' is not one of them                         *)
    let gen = ref [solved ()] in
    for _ = 1 to 4 do
      List.iter (fun c ->
        List.iter (fun m ->
          let d = mult c moves.(m) in
          if not (List.exists (eqc d) !gen) then gen := d :: !gen) four) !gen
    done;
    (* and it really is closed, not merely a ball of radius four            *)
    List.iter (fun c -> List.iter (fun m ->
      if not (List.exists (eqc (mult c moves.(m))) !gen) then
        fail "the set generated by the four is not closed") four) !gen;
    Printf.printf "  the four generate %d positions, and the set is closed\n"
      (List.length !gen);
    if List.exists (eqc p') !gen then fail "p' is reachable by the four alone";
    pass "p' is not among them, so the four alone cannot reach it either";

    Printf.printf "so both twist types must occur, which is what proposition 1 needs.\n";
    exit 0
  end;

  Printf.printf "NOT checked here, taken from the post: propositions 1 and 2,\n";
  Printf.printf "which are what make these the right six prefixes:\n";
  Array.iteri (fun i pre ->
    Printf.printf "   %d: %-12s searched to %d\n" i (word_str pre)
      (24 - List.length pre)) prefixes;
  if mode = "check" then exit 0;

  (* ---- the tables ------------------------------------------------------- *)
  let mt_twist = mk_move_table n_twist cube_of_twist twist in
  let mt_flip  = mk_move_table n_flip  cube_of_flip  flip  in
  let mt_slice = mk_move_table n_slice cube_of_slice slice in
  let p_fs = bfs (n_flip * n_slice)
      (fun i k -> let f = i / n_slice and s = i mod n_slice in
        for m = 0 to nmv - 1 do
          k (mt_flip.(f).(m) * n_slice + mt_slice.(s).(m)) done) 0 in
  let p_ts = bfs (n_twist * n_slice)
      (fun i k -> let t = i / n_slice and s = i mod n_slice in
        for m = 0 to nmv - 1 do
          k (mt_twist.(t).(m) * n_slice + mt_slice.(s).(m)) done) 0 in
  (* the edge databases.  One pair of transition tables serves both, since
     the arrangement rank does not know which edges it is watching; only the
     solved state differs.                                                   *)
  let t0e = Unix.gettimeofday () in
  Printf.printf "building the edge transition tables...\n%!";
  let (newarr, fmask) = mk_edge_tables () in
  Printf.printf "   done (%.0f s)\n%!" (Unix.gettimeofday () -. t0e);
  let edge_bfs set =
    let d = Bytes.make n_edb '\255' in
    let s0 = ecoord set (solved ()) in
    Bytes.unsafe_set d s0 '\000';
    let cur = ref 0 and go = ref true in
    while !go do
      let added = ref 0 in
      for a = 0 to n_earr - 1 do
        let base = a * nmv in
        for f = 0 to 63 do
          if Char.code (Bytes.unsafe_get d (a * 64 + f)) = !cur then
            for m = 0 to nmv - 1 do
              let j = newarr.(base + m) * 64
                      + (f lxor Char.code (Bytes.unsafe_get fmask (base + m))) in
              if Char.code (Bytes.unsafe_get d j) = 255 then begin
                Bytes.unsafe_set d j (Char.unsafe_chr (!cur + 1)); incr added end
            done
        done
      done;
      Printf.printf "   edge depth %d -> %d states (%.0f s)\n%!"
        (!cur + 1) !added (Unix.gettimeofday () -. t0e);
      if !added = 0 then go := false else incr cur
    done; d in
  Printf.printf "building edge database 1 (%d states)...\n%!" n_edb;
  let p_e1 = edge_bfs eset in
  Printf.printf "building edge database 2...\n%!";
  let p_e2 = edge_bfs eset2 in

  (* the corner database, built in memory: 88 MB, and a couple of minutes *)
  let mt_cp = mk_mt_cp () in
  let n_cnr = n_cperm * n_twist in
  let p_cnr =
    let t0 = Unix.gettimeofday () in
    Printf.printf "building the corner database (%d states)...\n%!" n_cnr;
    let d = Bytes.make n_cnr '\255' in
    Bytes.unsafe_set d 0 '\000';
    let cur = ref 0 and go = ref true in
    while !go do
      let added = ref 0 in
      for c = 0 to n_cperm - 1 do
        let mc = mt_cp.(c) in
        for t = 0 to n_twist - 1 do
          if Char.code (Bytes.unsafe_get d (c * n_twist + t)) = !cur then begin
            let mtt = mt_twist.(t) in
            for m = 0 to nmv - 1 do
              let j = mc.(m) * n_twist + mtt.(m) in
              if Char.code (Bytes.unsafe_get d j) = 255 then begin
                Bytes.unsafe_set d j (Char.chr (!cur + 1)); incr added end
            done
          end
        done
      done;
      Printf.printf "   corner depth %d -> %d states (%.0f s)\n%!"
        (!cur + 1) !added (Unix.gettimeofday () -. t0);
      if !added = 0 then go := false else incr cur
    done;
    d in

  (* cap 0 means: corner database only, and skip the 2.2 GB summary table.  *)
  let n_all = n_twist * n_flip * n_slice in
  let path = Printf.sprintf "qtm_cap%d.tbl" cap in
  let fresh = cap > 0 && not (Sys.file_exists path) in
  let p_all =
    if cap = 0 then Bigarray.Array1.create Bigarray.char Bigarray.c_layout 1
    else begin
      let fd = Unix.openfile path
          (if fresh then [Unix.O_RDWR; Unix.O_CREAT] else [Unix.O_RDONLY]) 0o644 in
      let a = Bigarray.array1_of_genarray
          (Unix.map_file fd Bigarray.char Bigarray.c_layout fresh [| n_all |]) in
      Unix.close fd; a
    end in
  if fresh then begin
    Printf.printf "building the table (%d states, cap %d)...\n%!" n_all cap;
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
                  Bigarray.Array1.unsafe_set p_all j (Char.chr (cur + 1));
                  incr added end
              done
            end
          done
        done
      done;
      Printf.printf "   depth %d -> %d states (%.0f s)\n%!" (cur + 1) !added
        (Unix.gettimeofday () -. t0)
    done
  end;
  if mode = "build" then exit 0;

  (* ---- one prefix, exhaustively ----------------------------------------- *)
  let which = int_of_string Sys.argv.(3) in
  let depth = int_of_string Sys.argv.(4) in
  let pre = prefixes.(which) in
  let start = mult p (applyq pre) in

  let maxd = 30 in
  let cps = Array.init maxd (fun _ -> Array.make 8 0) in
  let eps = Array.init maxd (fun _ -> Array.make 12 0) in
  let tw = Array.make maxd 0 and fl = Array.make maxd 0 and sl = Array.make maxd 0 in
  let cr = Array.make maxd 0 in
  let e1a = Array.make maxd 0 and e1f = Array.make maxd 0 in
  let e2a = Array.make maxd 0 and e2f = Array.make maxd 0 in
  let nodes = ref 0L in

  let heur d =
    let t = tw.(d) and f = fl.(d) and s = sl.(d) in
    let a = Char.code (Bytes.unsafe_get p_fs (f * n_slice + s)) in
    let b = Char.code (Bytes.unsafe_get p_ts (t * n_slice + s)) in
    let k = Char.code (Bytes.unsafe_get p_cnr (cr.(d) * n_twist + t)) in
    let g1 = Char.code (Bytes.unsafe_get p_e1 (e1a.(d) * 64 + e1f.(d))) in
    let g2 = Char.code (Bytes.unsafe_get p_e2 (e2a.(d) * 64 + e2f.(d))) in
    let h = ref a in
    if b > !h then h := b;
    if k > !h then h := k;
    if g1 > !h then h := g1;
    if g2 > !h then h := g2;
    if cap > 0 then begin
      let c = Char.code (Bigarray.Array1.unsafe_get p_all
                           ((t * n_flip + f) * n_slice + s)) in
      if c > !h then h := c
    end;
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
    sl.(d') <- mt_slice.(sl.(d)).(m);
    cr.(d') <- mt_cp.(cr.(d)).(m);
    let b1 = e1a.(d) * nmv + m in
    e1a.(d') <- newarr.(b1);
    e1f.(d') <- e1f.(d) lxor Char.code (Bytes.unsafe_get fmask b1);
    let b2 = e2a.(d) * nmv + m in
    e2a.(d') <- newarr.(b2);
    e2f.(d') <- e2f.(d) lxor Char.code (Bytes.unsafe_get fmask b2) in

  (* A run of at most two, both the same turn -- U U is the half turn -- and
     the usual order on opposite faces.                                      *)
  let allowed pm run m =
    if pm < 0 then true
    else let f = face m and pf = face pm in
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
          let run' = if pm >= 0 && face !m = face pm then run + 1 else 1 in
          if dfs (d + 1) (rem - 1) !m run' then found := true
        end;
        incr m
      done;
      !found
    end in

  for i = 0 to 7 do cps.(0).(i) <- start.cp.(i) done;
  for i = 0 to 11 do eps.(0).(i) <- start.ep.(i) done;
  tw.(0) <- twist start; fl.(0) <- flip start; sl.(0) <- slice start;
  cr.(0) <- cprank start.cp;
  let c1 = ecoord eset start and c2 = ecoord eset2 start in
  e1a.(0) <- c1 / 64; e1f.(0) <- c1 mod 64;
  e2a.(0) <- c2 / 64; e2f.(0) <- c2 mod 64;
  Printf.printf "root heuristic: %d\n%!" (heur 0);
  let t0 = Unix.gettimeofday () in
  let found = dfs 0 depth (-1) 0 in
  Printf.printf "prefix %d (%s), depth %d : %Ld nodes, %.1f s, solution %b\n%!"
    which (word_str pre) depth !nodes (Unix.gettimeofday () -. t0) found
