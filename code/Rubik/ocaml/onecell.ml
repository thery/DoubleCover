(* onecell.ml -- one cell, written over and over.

   The row's map is millions of cells and a write touches one of them.  This
   is the other extreme: ONE cell, written again and again with a different
   value each time, so no guard can ever fire.  It says what a long chain of
   records on a single place costs, and whether it is collected. *)

type 'a t = 'a kind ref
and 'a kind = Arr of 'a array | Diff of int * 'a * 'a t

let make n v : 'a t = ref (Arr (Array.make n v))

let rec reroot (t : 'a t) : 'a array =
  match !t with
  | Arr a -> a
  | Diff (i, v, t') ->
      let a = reroot t' in
      let old = a.(i) in
      a.(i) <- v; t := Arr a; t' := Diff (i, old, t); a

let set (t : 'a t) i v : 'a t =
  let a = reroot t in
  let old = a.(i) in
  a.(i) <- v;
  let res = ref (Arr a) in
  t := Diff (i, old, res);
  res

let get (t : 'a t) i = (reroot t).(i)

let branch = 4
let nwrite = try int_of_string (Sys.getenv "NW") with _ -> 10

(* the ten writes put 1, 2, ... 10 into the one cell, one after the other *)
let rec ifold n x f a = if n = 0 then a else ifold (n - 1) (x + 1) f (f x a)
let mark (m : int t) = ifold nwrite 0 (fun w a -> set a 0 (w + 1)) m

let rec dfs d (m : int t) : int t =
  if d = 0 then mark m
  else ifold branch 0 (fun _ a -> dfs (d - 1) a) m

let () =
  let d = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 11 in
  if Array.length Sys.argv > 2 then
    Gc.set { (Gc.get ()) with Gc.space_overhead = int_of_string Sys.argv.(2) };
  Gc.compact ();
  let t0 = Unix.gettimeofday () in
  let m = dfs d (make 1 0) in
  let t1 = Unix.gettimeofday () in
  let s = Gc.quick_stat () in
  Printf.printf
    "one cell, depth %2d, %10.0f writes  %7.2f s  peak heap %6.1f MB  last %d\n%!"
    d (float_of_int nwrite *. (float_of_int branch ** float_of_int d))
    (t1 -. t0)
    (float_of_int s.Gc.top_heap_words *. 8.0 /. 1048576.0)
    (get m 0)
