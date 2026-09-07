(* parrayleak.ml -- what a depth first search costs a persistent array.

   THE QUESTION.  The row's search walks a tree and marks members into a
   persistent array as it goes.  The memory grows through a level and we do
   not know which of two things does it:

     - the writes themselves.  A persistent array keeps a small record of
       every write, and the search reaches the same member by many different
       words, so most of its writes set a bit that is already set.
     - the walk.  `ifold n1 (x+1) f (f x a)' computes `f x a' FIRST, so a
       subtree runs with the fold's frame still open above it, and that frame
       holds the array as it was when the branch began.  Written in
       continuation passing style the frame is not open: f ends by calling
       the continuation, which is a tail call.

   This file is the two questions crossed: fold against CPS, guarded writes
   against unguarded.  Four runs, each printing its own peak heap.

   Nothing here is about the cube.  The array is the same shape the row's map
   has -- a table of chunks -- so that a write costs two records as it does
   there, and the tree is walked with the same branching and depth. *)

(* ---- a persistent array, the way the Rocq kernel has one ---------------- *)

type 'a t = 'a kind ref
and 'a kind = Arr of 'a array | Diff of int * 'a * 'a t

let make n v : 'a t = ref (Arr (Array.make n v))

let rec reroot (t : 'a t) : 'a array =
  match !t with
  | Arr a -> a
  | Diff (i, v, t') ->
      let a = reroot t' in
      let old = a.(i) in
      a.(i) <- v;
      t := Arr a;
      t' := Diff (i, old, t);
      a

let get (t : 'a t) i = (reroot t).(i)

(* the write, and it is what leaves a record: one ref and one Diff, six
   words, whether or not anyone will ever read the old version *)
let set (t : 'a t) i v : 'a t =
  let a = reroot t in
  let old = a.(i) in
  a.(i) <- v;
  let res = ref (Arr a) in
  t := Diff (i, old, res);
  res

(* ---- the map's shape: a table of chunks, so one word is two writes ------ *)

let nchunk = 194
let csize = 1 lsl 16                    (* smaller than the row's, same shape *)

type map = int t t

let mkempty () : map =
  let m = ref (Arr (Array.init nchunk (fun _ -> make csize 0))) in
  m

let gget (m : map) g =
  get (get m (g / csize)) (g mod csize)

(* unguarded: what `gor' was -- three reads and two writes, always *)
let gor_plain (m : map) g v : map =
  let c = g / csize and i = g mod csize in
  let a = get m c in
  set m c (set a i ((get a i) lor v))

(* guarded: one read of the table, one of the chunk, and no write at all
   when the word is already what it would become *)
let gor_guard (m : map) g v : map =
  let c = g / csize and i = g mod csize in
  let a = get m c in
  let old = get a i in
  let w = old lor v in
  if w = old then m else set m c (set a i w)

(* ---- the walk, twice --------------------------------------------------- *)

let branch = 4
let depth = ref 11                      (* 4 ^ 11 = 4 194 304 leaves        *)
let ncell = nchunk * csize

(* which cell a leaf marks.  The point is that leaves COLLIDE: a few million
   leaves land on far fewer cells, exactly as the search reaches the same
   member by many words. *)
let cellof node = (node * 2654435761) land (ncell - 1) mod ncell
let bitof node = 1 lsl ((node lsr 3) land 47)

(* the fold, as ifold is written: f x a is computed first *)
let rec ifold n x f a = if n = 0 then a else ifold (n - 1) (x + 1) f (f x a)

(* TEN WRITES A LEAF, not one: what the row does at a node is nearer this.   *)
let nwrite = 10

(* COLLECT AFTER THE TEN, when asked.  If the records are really garbage a    *)
(* collection here should keep the heap at the size of the map and no more.   *)
let gcevery = ref 0
let seen = ref 0
let mark gor (m : map) node =
  let r =
    ifold nwrite 0
      (fun w a -> let x = node * nwrite + w in gor a (cellof x) (bitof x)) m in
  if !gcevery > 0 then begin
    incr seen;
    if !seen mod !gcevery = 0 then Gc.full_major ()
  end;
  r

let rec dfs_fold gor d node (m : map) : map =
  if d = 0 then mark gor m node
  else ifold branch 0 (fun k a -> dfs_fold gor (d - 1) (node * branch + k) a) m

(* and the same in continuation passing style: every call is a tail call *)
let rec ifoldk n x f a k = if n = 0 then k a else f x a (fun b -> ifoldk (n - 1) (x + 1) f b k)

let rec dfs_cps gor d node (m : map) (k : map -> map) : map =
  if d = 0 then k (mark gor m node)
  else ifoldk branch 0
         (fun i a kk -> dfs_cps gor (d - 1) (node * branch + i) a kk) m k

(* ---- and what each of the four costs ------------------------------------ *)

let run name f =
  Gc.compact ();
  let t0 = Unix.gettimeofday () in
  let m = f () in
  let t1 = Unix.gettimeofday () in
  let s = Gc.quick_stat () in
  (* one read so the map cannot be optimised away *)
  let _ = gget m 0 in
  Printf.printf "%-22s %7.2f s   peak heap %8.0f MB   allocated %8.0f MB\n%!"
    name (t1 -. t0)
    (float_of_int s.Gc.top_heap_words *. 8.0 /. 1048576.0)
    ((s.Gc.minor_words +. s.Gc.major_words -. s.Gc.promoted_words)
     *. 8.0 /. 1048576.0)

let () =
  if Array.length Sys.argv > 2 then depth := int_of_string Sys.argv.(2);
  if Array.length Sys.argv > 3 then gcevery := int_of_string Sys.argv.(3);
  if Array.length Sys.argv > 4 then
    Gc.set { (Gc.get ()) with Gc.space_overhead = int_of_string Sys.argv.(4) };
  let d = !depth in
  Printf.printf "branching %d, depth %d, %.0f leaves; map %d cells = %.0f MB\n%!"
    branch d (float_of_int branch ** float_of_int d)
    ncell (float_of_int ncell *. 8.0 /. 1048576.0);
  Printf.printf "  full_major every %d leaves; space_overhead %d\n%!"
    !gcevery (Gc.get ()).Gc.space_overhead;
  (match Sys.argv.(1) with
   | "fold-plain" -> run "fold, unguarded" (fun () -> dfs_fold gor_plain d 1 (mkempty ()))
   | "fold-guard" -> run "fold, guarded"   (fun () -> dfs_fold gor_guard d 1 (mkempty ()))
   | "cps-plain"  -> run "CPS, unguarded"  (fun () -> dfs_cps gor_plain d 1 (mkempty ()) (fun m -> m))
   | "cps-guard"  -> run "CPS, guarded"    (fun () -> dfs_cps gor_guard d 1 (mkempty ()) (fun m -> m))
   | _ ->
     prerr_endline "usage: parrayleak <fold-plain|fold-guard|cps-plain|cps-guard> [depth]";
     exit 1)
