(* How long a C-like program takes to check the row's map is full.
   The map is 812 851 200 words of twenty four bits, held as Rocq holds it:
   chunks of 2^21 words.  Two loops are timed, and the difference between
   them is the whole point.

     by index   the index is split into a chunk and an offset every word,
                which is what Rocq's gget does
     by chunk   each chunk is walked once from end to end

   Run:  ocamlfind ocamlopt -package unix -linkpkg mfullbench.ml -o mfullbench
         ./mfullbench                                                        *)

let allbits = 16777215
let cwlog = 21
let cwords = 1 lsl cwlog
let words = 812851200
let nchunk = (words + cwords - 1) / cwords

let time name f =
  let t = Unix.gettimeofday () in
  let r = f () in
  Printf.printf "  %-10s %7.2f s   (%b)\n%!" name (Unix.gettimeofday () -. t) r

let () =
  Printf.printf "building %d chunks of %d words (%.1f GB)\n%!"
    nchunk cwords (float_of_int words *. 8.0 /. 1e9);
  let m = Array.init nchunk (fun _ -> Array.make cwords allbits) in

  time "by index" (fun () ->
    let ok = ref true in
    for i = 0 to words - 1 do
      let c = i lsr cwlog and o = i land (cwords - 1) in
      if m.(c).(o) <> allbits then ok := false
    done;
    !ok);

  time "by chunk" (fun () ->
    let ok = ref true in
    for c = 0 to nchunk - 1 do
      let a = m.(c) in
      for o = 0 to cwords - 1 do
        if Array.unsafe_get a o <> allbits then ok := false
      done
    done;
    !ok)
