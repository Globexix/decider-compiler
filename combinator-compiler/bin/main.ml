open Combinator_compiler

let read_file path = In_channel.with_open_bin path In_channel.input_all

let write_file path text = Out_channel.with_open_bin path (fun oc -> output_string oc text)

let fail = Error.fail

exception Fas_failed of string

let fas_ir fas path =
  let out = Filename.temp_file "fas" ".json" and err = Filename.temp_file "fas" ".err" in
  let command = Printf.sprintf "%s --emit-ir-json %s > %s 2> %s" (Filename.quote fas) (Filename.quote path)
      (Filename.quote out) (Filename.quote err) in
  let status = Sys.command command in
  let stdout = read_file out and stderr = String.trim (read_file err) in
  Sys.remove out;
  Sys.remove err;
  if status <> 0 then raise (Fas_failed (if stderr = "" then "fas compilation failed" else stderr));
  stdout

let json what text =
  try Yojson.Safe.from_string text with Yojson.Json_error m -> fail "%s: invalid JSON: %s" what m

let extras = [ "blueprint"; "ir"; "project"; "manifest"; "transitions" ]

let run input bindings output fas no_optimize min_ups emit =
  let emit = if List.mem "all" emit then extras else emit in
  let ctx = ref { Report.input; source = None; bindings; origins = [] } in
  try
    let is_fas = Filename.check_suffix input ".fas" in
    if is_fas then ctx := { !ctx with source = Some (read_file input) };
    let ir = json input (if is_fas then fas_ir fas input else read_file input) in
    let program = Ir.of_json ir in
    let config = match bindings with
      | Some path -> json path (read_file path)
      | None ->
        if not is_fas then
          fail ~help:[ "compile the .fas source instead, or pass --bindings FILE" ] "JSON IR input needs --bindings";
        let config, origins = Declarations.bindings_with_origins (Option.get !ctx.source) program in
        ctx := { !ctx with origins };
        config in
    let name = Filename.remove_extension (Filename.basename input) in
    let r = Compile.compile ~optimize:(not no_optimize) ~name ~min_ups program config in
    let rec mkdir_p dir =
      if not (Sys.file_exists dir) then (mkdir_p (Filename.dirname dir); Sys.mkdir dir 0o755) in
    mkdir_p output;
    let save name v = write_file (Filename.concat output name) (Pjson.pretty v ^ "\n") in
    List.iter (fun (kind, v) -> if List.mem kind emit then save (kind ^ ".json") v)
      [ ("ir", ir); ("project", r.project); ("manifest", r.manifest); ("transitions", r.rows); ("blueprint", r.blueprint) ];
    write_file (Filename.concat output "blueprint.txt") (Emit.exchange_string r.blueprint ^ "\n");
    Printf.printf "%s: one decider, %d lanes, %d conditions, %d transition rows, ~%.2f ms/tick, %s\n" output r.lanes
      r.conditions r.row_count r.ms_per_tick (if Signals.uses_space_age r.blueprint then "needs Space Age" else "base game");
    List.iter (fun (l : Model.latch) ->
        Printf.printf "  latched `%s` while %s is %s\n" l.callee l.phase (String.concat ", " (List.map string_of_int l.uses))) r.latches;
    0
  with
  | Error.Compile_error e -> prerr_string (Report.render !ctx e); 1
  | Fas_failed m -> prerr_endline m; 1
  | Sys_error m -> Printf.eprintf "combinator-compiler: error: %s\n" m; 1

let usage = {|usage: combinator-compiler FILE.fas -o DIR [options]
       combinator-compiler FILE.json --bindings FILE -o DIR [options]
Writes DIR/blueprint.txt: one Factorio 2.1 decider combinator and its display panels.
options:
  -o DIR           output directory
  --bindings FILE  JSON bindings for Fas IR input (default: the source's declarations)
  --fas PATH       Fas compiler (default fas)
  --no-optimize    skip condition minimization (faster compiles)
  --min-ups N      fail if the estimated speed is below N UPS (default 20; 0 disables)
  --emit KIND      also write DIR/KIND.json (repeatable)
                   KIND is blueprint, ir, project, manifest, transitions or all
  -h, --help       show this help
|}

let () =
  let die fmt = Printf.ksprintf (fun m -> Printf.eprintf "combinator-compiler: error: %s\n(see combinator-compiler --help)\n" m; exit 2) fmt in
  let input = ref None and output = ref None and bindings = ref None and fas = ref "fas"
  and no_optimize = ref false and min_ups = ref 20. and emit = ref [] in
  let rec parse = function
    | [] -> ()
    | ("-h" | "--help") :: _ -> print_string usage; exit 0
    | "--no-optimize" :: rest -> no_optimize := true; parse rest
    | flag :: rest when String.length flag > 2 && String.starts_with ~prefix:"--" flag && String.contains flag '=' ->
      let i = String.index flag '=' in
      parse (String.sub flag 0 i :: String.sub flag (i + 1) (String.length flag - i - 1) :: rest)
    | ("-o" | "--bindings" | "--fas" | "--emit" | "--min-ups") as flag :: value :: rest ->
      (match flag with
       | "-o" -> output := Some value
       | "--bindings" -> bindings := Some value
       | "--fas" -> fas := value
       | "--min-ups" ->
         (match float_of_string_opt value with
          | Some v when v >= 0. -> min_ups := v
          | _ -> die "--min-ups needs a number, got `%s`" value)
       | _ ->
         if not (List.mem value ("all" :: extras)) then
           die "unknown --emit kind `%s`; expected %s or all" value (String.concat ", " extras);
         emit := value :: !emit);
      parse rest
    | ("-o" | "--bindings" | "--fas" | "--emit" | "--min-ups") as flag :: [] -> die "%s needs a value" flag
    | arg :: _ when String.length arg > 1 && arg.[0] = '-' -> die "unknown option %s" arg
    | arg :: rest ->
      if !input <> None then die "more than one input file";
      input := Some arg; parse rest in
  parse (List.tl (Array.to_list Sys.argv));
  match !input, !output with
  | None, _ -> print_string usage; exit 2
  | Some _, None -> die "missing -o DIR"
  | Some input, Some output -> exit (run input !bindings output !fas !no_optimize !min_ups (List.rev !emit))
