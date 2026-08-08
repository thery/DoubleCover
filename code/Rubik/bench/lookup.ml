(* =========================================================================
   lookup.ml -- what a folded heuristic lookup costs against an unfolded one.

   The phase 1 heuristic is read once per position, and folding the table by
   the sixteen symmetries makes that read indirect:

     unfolded   p.(t * nfs + f)
     folded     let (r, s) = repsym.(f) in q.(r * ntwist + twsym.(t * 16 + s))

   so the folded read costs two extra lookups, into tables small enough to
   stay in cache, and one read into a table 15.73 times smaller.  Which wins
   is a question about caches, so it is measured here at the real sizes with
   the real access pattern -- random, which is what a search does.

   The tables are filled with arbitrary bytes: this measures the reads, not
   the distances.
   ========================================================================= *)

let ntwist = 2187
let nfs = 1013760
let norb = 64430                        (* flip x slice orbits, p1gen sym16 *)
let nsym = 16

let time name n f =
  let t0 = Unix.gettimeofday () in
  let s = f () in
  let d = Unix.gettimeofday () -. t0 in
  Printf.printf "%-28s %6.2f s  %6.1f ns a lookup   (sink %d)\n%!"
    name d (d *. 1e9 /. float_of_int n) s

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 20_000_000 in

  let nunf = ntwist * nfs in
  let nfold = ntwist * norb in
  Printf.printf "unfolded %d entries (%.2f GB), folded %d (%.0f MB)\n%!"
    nunf (float_of_int nunf /. 1073741824.0)
    nfold (float_of_int nfold /. 1048576.0);

  let p = Bytes.make nunf '\007' in
  let q = Bytes.make nfold '\007' in
  (* repsym: the orbit representative and the symmetry that reaches it *)
  let rep = Array.init nfs (fun f -> f mod norb) in
  let sym = Array.init nfs (fun f -> f land (nsym - 1)) in
  let twsym = Array.init (ntwist * nsym) (fun i -> i mod ntwist) in

  (* a cheap generator, so the loop measures the reads and not the random *)
  let seed = ref 123456789 in
  let next () = seed := (!seed * 1103515245 + 12345) land max_int; !seed in

  (* the same index stream for both, so they see the same positions *)
  let ts = Array.init n (fun _ -> next () mod ntwist) in
  let fs = Array.init n (fun _ -> next () mod nfs) in

  time "unfolded" n (fun () ->
    let s = ref 0 in
    for i = 0 to n - 1 do
      let t = Array.unsafe_get ts i and f = Array.unsafe_get fs i in
      s := !s + Char.code (Bytes.unsafe_get p (t * nfs + f))
    done; !s);

  time "folded, three steps" n (fun () ->
    let s = ref 0 in
    for i = 0 to n - 1 do
      let t = Array.unsafe_get ts i and f = Array.unsafe_get fs i in
      let r = Array.unsafe_get rep f and y = Array.unsafe_get sym f in
      let t' = Array.unsafe_get twsym (t * nsym + y) in
      s := !s + Char.code (Bytes.unsafe_get q (r * ntwist + t'))
    done; !s)

(* rep and sym in one array, so the indirection is one read and not two *)
let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 20_000_000 in
  let nfold = ntwist * norb in
  let q = Bytes.make nfold '\007' in
  let repsym = Array.init nfs (fun f -> (f mod norb) * nsym + (f land 15)) in
  let twsym = Array.init (ntwist * nsym) (fun i -> i mod ntwist) in
  let seed = ref 123456789 in
  let next () = seed := (!seed * 1103515245 + 12345) land max_int; !seed in
  let ts = Array.init n (fun _ -> next () mod ntwist) in
  let fs = Array.init n (fun _ -> next () mod nfs) in
  time "folded, packed repsym" n (fun () ->
    let s = ref 0 in
    for i = 0 to n - 1 do
      let t = Array.unsafe_get ts i and f = Array.unsafe_get fs i in
      let rs = Array.unsafe_get repsym f in
      let t' = Array.unsafe_get twsym (t * nsym + (rs land 15)) in
      s := !s + Char.code (Bytes.unsafe_get q ((rs lsr 4) * ntwist + t'))
    done; !s)
