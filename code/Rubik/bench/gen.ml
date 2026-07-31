(* THE GENERATOR, on a running example.
   Same pipeline the phase 1 table will use -- srank, fsclass, the symmetry
   fold, the 2 bit clamped pack, the two level read -- but run on the flip x
   slice table we already ship, which is 1/140th the size and whose values we
   can check.  If the folded read reproduces the direct BFS distance for all
   1 013 760 coordinates, the pipeline is right. *)
open Cubedata
let n = 48
let sy = [|2;4;7;1;6;0;3;5;32;33;34;35;36;37;38;39;8;9;10;11;12;13;14;15;
           16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;45;43;40;46;41;47;44;42|]
let sx = [|39;38;37;36;35;34;33;32;13;11;8;14;9;15;12;10;0;1;2;3;4;5;6;7;
           26;28;31;25;30;24;27;29;47;46;45;44;43;42;41;40;16;17;18;19;20;21;22;23|]
let sm = [|2;1;0;4;3;7;6;5;26;25;24;28;27;31;30;29;18;17;16;20;19;23;22;21;
           10;9;8;12;11;15;14;13;34;33;32;36;35;39;38;37;42;41;40;44;43;47;46;45|]
let comp a b = Array.init n (fun i -> b.(a.(i)))
let inv a = let c = Array.make n 0 in
            for i = 0 to n-1 do c.(a.(i)) <- i done; c
let ident = Array.init n (fun i -> i)
let group gens =
  let seen = Hashtbl.create 64 in
  let rec add a = let k = Array.to_list a in
    if not (Hashtbl.mem seen k) then begin
      Hashtbl.add seen k a; List.iter (fun g -> add (comp a g)) gens end in
  add ident; Hashtbl.fold (fun _ v acc -> v :: acc) seen []
let bit m i = (m lsr i) land 1 = 1
let ecoordi u =
  let acc = ref 0 in
  for k = 0 to 23 do
    let b = if k < 12 then not (bit pmask u.(eprim.(k)))
            else bit smask u.(eprim.(k-12)) in
    if b then acc := !acc lor (1 lsl k)
  done; !acc
let coordi a = ecoordi (inv a)

let nslice = 495
let nfs = 1013760
let time name f = let t = Unix.gettimeofday () in let r = f () in
  Printf.printf "  %-34s %6.2f s\n%!" name (Unix.gettimeofday () -. t); r

let () =
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

  (* ---- BFS the flip x slice distance, deduped by coordinate ------------- *)
  let dist = Array.make nfs (-1) and rep = Array.make nfs ident in
  let cnt = ref 0 in
  time "BFS the flip x slice distance" (fun () ->
    let q = Queue.create () in
    let i0 = fsidx (coordi ident) in
    dist.(i0) <- 0; rep.(i0) <- ident; incr cnt; Queue.add (ident, 0) q;
    while not (Queue.is_empty q) do
      let (a, d) = Queue.pop q in
      for k = 0 to 17 do
        let b = comp a moves.(k) in
        let i = fsidx (coordi b) in
        if dist.(i) < 0 then
          (dist.(i) <- d+1; rep.(i) <- b; incr cnt; Queue.add (b, d+1) q)
      done
    done);
  Printf.printf "reached %d of %d coordinates, max distance %d\n%!"
    !cnt nfs (Array.fold_left max 0 dist);

  (* ---- the 16 symmetries that act on the coordinate --------------------- *)
  let syms = Array.of_list (group [sy;sx;sm]) in
  let acts = Array.to_list syms |> List.filter (fun s ->
    let si = inv s in
    (* well defined iff it maps equal coordinates to equal coordinates; test
       against the BFS representatives and their move images *)
    let ok = ref true in
    (try for i = 0 to 2000 do
      let a = rep.(i * 401 mod nfs) in
      for k = 0 to 17 do
        let b = comp a moves.(k) in
        let b' = rep.(fsidx (coordi b)) in
        if coordi (comp si (comp b s)) <> coordi (comp si (comp b' s))
        then (ok := false; raise Exit)
      done done with Exit -> ());
    !ok) |> Array.of_list in
  Printf.printf "symmetries acting on the coordinate: %d\n%!" (Array.length acts);

  (* ---- does the distance really respect them?  the fold rests on this --- *)
  let viol = ref 0 in
  time "check the distance is orbit constant" (fun () ->
    for i = 0 to nfs - 1 do
      if dist.(i) >= 0 && i mod 7 = 0 then
        Array.iter (fun s ->
          let j = fsidx (coordi (comp (inv s) (comp rep.(i) s))) in
          if dist.(j) <> dist.(i) then incr viol) acts
    done);
  Printf.printf "orbit constancy violations: %d\n%!" !viol;

  (* ---- fsclass : coordinate -> class * 16 + sym ------------------------- *)
  let m = Array.length acts in
  let acti = Array.map inv acts in
  let mincoord = Array.make nfs 0 and minsym = Array.make nfs 0 in
  time "fold: minimum over the orbit" (fun () ->
    for i = 0 to nfs - 1 do
      let best = ref max_int and bs = ref 0 in
      for j = 0 to m - 1 do
        let c = fsidx (coordi (comp acti.(j) (comp rep.(i) acts.(j)))) in
        if c < !best then (best := c; bs := j)
      done;
      mincoord.(i) <- !best; minsym.(i) <- !bs
    done);
  let seen = Hashtbl.create 200_003 in
  let rank = Array.make nfs (-1) in
  let nc = ref 0 in
  for i = 0 to nfs - 1 do
    let mc = mincoord.(i) in
    (match Hashtbl.find_opt seen mc with
     | Some _ -> () | None -> Hashtbl.add seen mc !nc; incr nc)
  done;
  for i = 0 to nfs - 1 do rank.(i) <- Hashtbl.find seen mincoord.(i) done;
  Printf.printf "classes: %d (reduction %.2fx)\n%!" !nc
    (float_of_int nfs /. float_of_int !nc);
  let fsclass = Array.init nfs (fun i -> rank.(i) * 16 + minsym.(i)) in

  (* ---- pack the folded table, 2 bits per entry, 31 per word ------------- *)
  let base = 4 in                      (* clamp to [base, base+3] *)
  let words = (!nc + 30) / 31 in
  let tab = Array.make words 0 in
  time "pack the folded table" (fun () ->
    for i = 0 to nfs - 1 do
      let c = rank.(i) in
      let v = dist.(i) - base in
      let v = if v < 0 then 0 else if v > 3 then 3 else v in
      tab.(c / 31) <- tab.(c / 31) lor (v lsl ((c mod 31) * 2))
    done);
  let get i = (tab.(i / 31) lsr ((i mod 31) * 2)) land 3 in

  (* ---- VERIFY: folded read vs the direct BFS distance ------------------- *)
  let bad = ref 0 and exact = ref 0 in
  for i = 0 to nfs - 1 do
    let want = let v = dist.(i) - base in
               if v < 0 then 0 else if v > 3 then 3 else v in
    let got = get (fsclass.(i) / 16) in
    if got <> want then incr bad;
    if base + got = dist.(i) then incr exact
  done;
  Printf.printf "\nVERIFY folded read vs direct BFS: %d mismatches out of %d\n%!"
    !bad nfs;
  Printf.printf "clamp exact for %d (%.1f%%)\n%!" !exact
    (100.0 *. float_of_int !exact /. float_of_int nfs);
  Printf.printf "table: %d classes -> %d words = %.1f MB (unfolded would be %d words)\n%!"
    !nc words (float_of_int words *. 8.0 /. 1048576.0) ((nfs + 30) / 31)
