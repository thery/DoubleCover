(* elpijs.ml — a minimal JS API over Elpi's embedding API (js_of_ocaml).
   globalThis.elpi = {
     addFile(name, text)      : puts text at /static/elpi/<name> (jsoo pseudo-fs)
     load(mainFile)           : parse + compile the program (accumulates resolved in /static/elpi)
     query(prog, goal)        : compile the goal against prog, run it once
                                -> {ok, out, err, msg}
   } *)
open Js_of_ocaml
module A = Elpi.API

let root = "/static/elpi/"
let out_buf = Buffer.create 4096
let err_buf = Buffer.create 1024
let flushers = lazy (
  Sys_js.set_channel_flusher stdout (Buffer.add_string out_buf);
  Sys_js.set_channel_flusher stderr (Buffer.add_string err_buf))

exception Elpi_error of string
let () =
  A.Setup.set_error (fun ?loc msg ->
    let l = match loc with None -> "" | Some l -> A.Ast.Loc.show l ^ ": " in
    raise (Elpi_error (l ^ msg)));
  A.Setup.set_anomaly (fun ?loc msg ->
    let l = match loc with None -> "" | Some l -> A.Ast.Loc.show l ^ ": " in
    raise (Elpi_error ("anomaly: " ^ l ^ msg)));
  A.Setup.set_type_error (fun ?loc msg ->
    let l = match loc with None -> "" | Some l -> A.Ast.Loc.show l ^ ": " in
    raise (Elpi_error ("type error: " ^ l ^ msg)));
  A.Setup.set_warn (fun ?loc:_ ~id:_ _ -> ())

(* new_int as in Elpi, but its counter is reset before every query, so that a
   query gives the same fresh names as a fresh `elpi` process. *)
let fresh_int = ref 0
let new_int =
  let open A.BuiltIn in let open A.BuiltInPredicate in
  MLCode (Pred ("new_int",
    Out (A.BuiltInData.int, "N", Easy "unifies N with a different int every time it is called"),
    (fun _ ~depth:_ -> incr fresh_int; Notation.(!: !fresh_int))), DocAbove)

(* builtin sets: "full" = Elpi's std_declarations;
   "min" = without std.map/std.set (LP), the Teyjus extras and the OCaml runtime builtins;
   "min-nostd" = "min" without the LP code of the standard library (std dot everything), which is
   then compiled as an ordinary (precompilable) unit, builtin_stdlib.elpi *)
let mode () =
  match Js.Optdef.to_option (Js.Unsafe.get Js.Unsafe.global "ELPI_BUILTINS") with
  | None -> "full" | Some s -> Js.to_string s
let is_stdlib_src = function
  | A.BuiltIn.LPCode s -> String.length s > 29 && String.sub s 0 29 = "#line 1 \"builtin_stdlib.elpi\""
  | _ -> false
let declarations () =
  let open Elpi.Builtin in
  let ds = match mode () with
    | "full" -> std_declarations
    | "min" -> core_builtins @ io_builtins @ elpi_builtins @ elpi_nonlogical_builtins @ elpi_stdlib @ ocaml_runtime
    | "min-nostd" -> core_builtins @ io_builtins @ elpi_builtins @ elpi_nonlogical_builtins
                     @ List.filter (fun d -> not (is_stdlib_src d)) elpi_stdlib @ ocaml_runtime
    | m -> failwith ("ELPI_BUILTINS: " ^ m) in
  List.map (function
    | A.BuiltIn.MLCode (A.BuiltInPredicate.Pred ("new_int", _, _), _) -> new_int
    | d -> d) ds

let builtins () = A.BuiltIn.declare ~file_name:"builtin_js.elpi" (declarations ())

let elpi =
  lazy (A.Setup.init ~builtins:[builtins ()]
          ~file_resolver:(A.Parse.std_resolver ~cwd:root ~paths:[root] ()) ())

let now () = Js.to_float (new%js Js.date_now)##getTime

let add_file name text =
  Sys_js.create_file ~name:(root ^ Js.to_string name) ~content:(Js.to_string text)

let flush_all () = Format.pp_print_flush Format.std_formatter (); flush stdout; flush stderr

let guard f =
  Lazy.force flushers;
  Buffer.clear out_buf; Buffer.clear err_buf;
  let res, msg =
    try f (), ""
    with
    | Elpi_error m -> false, m
    | A.Parse.ParseError (l, m) -> false, A.Ast.Loc.show l ^ ": " ^ m
    | A.Compile.CompileError (l, m) ->
        false, (match l with None -> "" | Some l -> A.Ast.Loc.show l ^ ": ") ^ m
    | e -> false, Printexc.to_string e in
  flush_all ();
  res, msg

(* programs are kept on the OCaml side, referred to by index *)
let progs : A.Compile.program array ref = ref [||]

let add_prog p = progs := Array.append !progs [|p|]; Array.length !progs - 1

let result ok msg t extra =
  let o = object%js
    val ok = Js.bool ok
    val out = Js.string (Buffer.contents out_buf)
    val err = Js.string (Buffer.contents err_buf)
    val msg = Js.string msg
    val ms = Js.number_of_float t
    val id = extra
  end in o

let load main =
  let t0 = now () in
  let id = ref (-1) in
  let ok, msg = guard (fun () ->
    let elpi = Lazy.force elpi in
    let p = A.Parse.program ~elpi ~file:(root ^ Js.to_string main) in
    let prog = A.Compile.program ~elpi p in
    id := add_prog prog; true) in
  result ok msg (now () -. t0) !id

let last_split = ref [||]
let query id goal =
  let t0 = now () in
  fresh_int := 0;
  let ok, msg = guard (fun () ->
    let elpi = Lazy.force elpi in
    let g = A.Parse.goal ~elpi ~loc:(A.Ast.Loc.initial "(js)") ~text:(Js.to_string goal) in
    let t1 = now () in
    let q = A.Compile.query (!progs).(id) g in
    let t2 = now () in
    let exe = A.Compile.optimize q in
    let t3 = now () in
    let r = A.Execute.once exe in
    let t4 = now () in
    last_split := [| t1 -. t0; t2 -. t1; t3 -. t2; t4 -. t3;
                     A.Compile.total_type_checking_time q *. 1000.; A.Compile.total_det_checking_time q *. 1000. |];
    match r with
    | A.Execute.Success _ -> true
    | A.Execute.Failure -> false
    | A.Execute.NoMoreSteps -> false) in
  result ok msg (now () -. t0) id

(* Separate compilation: the static program as marshaled compilation units. *)
let units_of_file elpi file =
  let p = A.Parse.program ~elpi ~file in
  let scoped = A.Compile.scope_ast ~elpi p in
  let base = A.Compile.empty_base ~elpi in
  let _, units, _ = List.fold_left (fun (base, acc, seen) sp ->
      let d = A.Compile.scoped_program_digest sp in
      if List.mem d seen then (base, acc, seen) else
      let u = A.Compile.unit ~elpi ~base sp in
      (A.Compile.extend ~base u, u :: acc, d :: seen)) (base, [], []) scoped in
  List.rev units

let precompile main =
  let t0 = now () in
  let blob = ref "" in
  let ok, msg = guard (fun () ->
    let elpi = Lazy.force elpi in
    let us = units_of_file elpi (root ^ Js.to_string main) in
    blob := Marshal.to_string (us : A.Compile.compilation_unit list) []; true) in
  let r = result ok msg (now () -. t0) (-1) in
  Js.Unsafe.set r "blob" (Js.bytestring !blob); r

let load_units blob =
  let t0 = now () in
  let id = ref (-1) in
  let ok, msg = guard (fun () ->
    let elpi = Lazy.force elpi in
    let us : A.Compile.compilation_unit list = Marshal.from_string (Js.to_bytestring blob) 0 in
    let p = List.fold_left (fun base u -> A.Compile.extend ~base u) (A.Compile.empty_base ~elpi) us in
    id := add_prog p; true) in
  result ok msg (now () -. t0) !id

(* extend program [id] with the clauses of [text] (no accumulate), as a new program *)
let extend id name text =
  let t0 = now () in
  let nid = ref (-1) in
  let ok, msg = guard (fun () ->
    let elpi = Lazy.force elpi in
    let text = Js.to_string text in
    let p = A.Parse.program_from ~elpi ~loc:(A.Ast.Loc.initial (Js.to_string name))
              ~digest:(Digest.string text) (Lexing.from_string text) in
    let base = (!progs).(id) in
    let p = List.fold_left (fun base sp -> A.Compile.extend ~base (A.Compile.unit ~elpi ~base sp))
              base (A.Compile.scope_ast ~elpi p) in
    nid := add_prog p; true) in
  result ok msg (now () -. t0) !nid

(* warm up the elpi instance (builtins header) and report its time *)
let init () =
  let t0 = now () in
  (try ignore (Lazy.force elpi)
   with e -> Js_of_ocaml.Console.console##log (Js.string ("init: " ^ Printexc.to_string e)));
  now () -. t0

let () =
  Js.export "elpi" (object%js
    method addFile n t = add_file n t
    method load m = load m
    method query id g = query id g
    method precompile m = precompile m
    method loadUnits b = load_units b
    method extend id n t = extend id n t
    method init = Js.number_of_float (init ())
    method split = Js.array (Array.map Js.number_of_float !last_split)
  end)
