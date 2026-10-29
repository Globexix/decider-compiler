open Circuit

type json = Yojson.Safe.t

type node = { id : string; kind : string; config : json }
type edge = { src : string; dst : string; color : string; src_port : string; dst_port : string }

type project = { mutable nodes : node list; mutable edges : edge list }

let project () = { nodes = []; edges = [] }
let add_node p id kind config = p.nodes <- p.nodes @ [ { id; kind; config } ]

let wire p ?(src_port = "output") ?(dst_port = "input") src dst color =
  p.edges <- p.edges @ [ { src; dst; color; src_port; dst_port } ]

let wires_name = function Red -> "red" | Green -> "green"

let operand_json = function
  | Signal (name, w) -> `Assoc [ ("kind", `String "signal"); ("name", `String name); ("wires", `String (wires_name w)) ]
  | Each -> `Assoc [ ("kind", `String "each"); ("name", `String "each"); ("wires", `String "green") ]

let flatten groups =
  List.concat (List.mapi (fun g group ->
      List.mapi (fun i c -> (c, if i > 0 then Some "and" else if g > 0 then Some "or" else None)) group) groups)

let condition_json (c, join) =
  `Assoc [ ("left", operand_json c.left); ("cmp", `String c.cmp);
           ("right", `Assoc [ ("kind", `String "constant"); ("value", `Int c.right) ]);
           ("join", match join with Some j -> `String j | None -> `Null) ]

type output = { signal : string; copy_red : bool; value : int }

let output_json o =
  `Assoc [ ("signal", `String o.signal); ("mode", `String (if o.copy_red then "input" else "constant"));
           ("value", `Int o.value); ("inputWires", `String (if o.copy_red then "red" else "both")) ]

let project_json p =
  `Assoc [ ("nodes", `List (List.map (fun n -> `Assoc [ ("id", `String n.id); ("type", `String n.kind); ("config", n.config) ]) p.nodes));
           ("edges", `List (List.map (fun e ->
                `Assoc [ ("from", `String e.src); ("to", `String e.dst); ("color", `String e.color);
                         ("fromConnector", `String e.src_port); ("toConnector", `String e.dst_port) ]) p.edges)) ]

let signal name = Signals.to_json (if name = "each" then "signal-each" else name)

let networks ~red = `Assoc [ ("red", `Bool red); ("green", `Bool (not red)) ]

let comparator = function ">=" -> "\u{2265}" | "<=" -> "\u{2264}" | "!=" -> "\u{2260}" | c -> c

let decider_json conditions outputs else_outputs =
  let condition i (c, join) =
    let first, red = match c.left with Signal (n, w) -> (n, w = Red) | Each -> ("each", false) in
    `Assoc ([ ("first_signal", signal first); ("first_signal_networks", networks ~red);
              ("comparator", `String (comparator c.cmp)); ("constant", `Int c.right) ]
            @ if i > 0 then [ ("compare_type", `String (Option.value join ~default:"and")) ] else []) in
  let output o =
    if o.copy_red then `Assoc [ ("signal", signal o.signal); ("networks", networks ~red:true) ]
    else `Assoc [ ("signal", signal o.signal); ("copy_count_from_input", `Bool false); ("constant", `Int o.value) ] in
  `Assoc [ ("decider_conditions", `Assoc [ ("conditions", `List (List.mapi condition conditions));
                                           ("outputs", `List (List.map output outputs));
                                           ("else_outputs", `List (List.map output else_outputs)) ]) ]

let blueprint_version = (2 lsl 48) lor (1 lsl 32) lor (23 lsl 16)

let blueprint (p : project) ~label ~decider ~(inputs : Spec.input list) =
  let entities = ref [] and ids = Hashtbl.create 64 in
  let add ?name fields =
    let number = List.length !entities + 1 in
    entities := `Assoc (fields @ [ ("entity_number", `Int number) ]) :: !entities;
    Option.iter (fun n -> Hashtbl.replace ids n number) name;
    number in
  let pos x y = ("position", `Assoc [ ("x", `Float x); ("y", `Float y) ]) in
  let bottom = List.fold_left (fun m n ->
      match String.split_on_char '_' n.id with
      | [ "pixel"; _; y ] -> max m (float_of_string y)
      | _ -> m) 0. p.nodes in
  let input_index name = let rec go i = function [] -> 0 | (x : Spec.input) :: r -> if x.input = name then i else go (i + 1) r in go 0 inputs in
  List.iter (fun n ->
      let described = ("player_description", `String n.id) in
      match n.kind with
      | "decider" ->
        ignore (add ~name:n.id [ described; ("name", `String "decider-combinator"); pos 0. (bottom +. 0.5);
                                 ("direction", `Int 4); ("control_behavior", decider) ])
      | "sensor_wall" ->
        let is_start = n.id = "start" and is_wake = String.starts_with ~prefix:"wake_" n.id in
        let drop k = String.sub n.id k (String.length n.id - k) in
        let input = if is_start then "" else if is_wake then drop 5 else drop 8 in
        let index = if is_start then 0 else input_index input in
        let sx, sy = if is_start then (-2.5, 1.5) else ((if is_wake then -2.5 else -4.5), 5.5 +. 5. *. float_of_int index) in
        let sy = sy +. bottom in
        let s = match n.config with `Assoc l -> (match List.assoc "signal" l with `String s -> s | _ -> "") | _ -> "" in
        ignore (add ~name:n.id [ described; ("name", `String "stone-wall"); pos sx sy;
                                 ("control_behavior", `Assoc [ ("circuit_open_gate", `Bool false); ("circuit_read_sensor", `Bool true);
                                                               ("output_signal", signal s) ]) ]);
        if not is_wake then
          ignore (add [ ("name", `String "gate"); pos (sx +. 1.) sy; ("direction", `Int 4);
                        ("player_description", `String (if is_start then "START: walk here once" else input ^ ": " ^ s)) ])
      | _ ->
        let x, y = match String.split_on_char '_' n.id with
          | [ _; x; y ] -> (int_of_string x, int_of_string y)
          | _ -> invalid_arg n.id in
        ignore (add ~name:n.id [ described; ("name", `String "display-panel");
                                 pos (4.5 +. float_of_int x) (0.5 +. float_of_int y);
                                 ("always_show", `Bool true); ("control_behavior", n.config) ])) p.nodes;
  ignore (add [ ("name", `String "medium-electric-pole"); pos (-0.5) (bottom -. 0.5) ]);
  let port name connector color =
    let red = color = "red" in
    if name <> "machine" || connector = "input" then if red then 1 else 2 else if red then 3 else 4 in
  let wires =
    List.map (fun e -> [ Hashtbl.find ids e.src; port e.src e.src_port e.color; Hashtbl.find ids e.dst; port e.dst e.dst_port e.color ]) p.edges in
  `Assoc [ ("blueprint", `Assoc [
      ("item", `String "blueprint"); ("version", `Int blueprint_version);
      ("label", `String label);
      ("entities", `List (List.rev !entities));
      ("wires", `List (List.map (fun w -> `List (List.map (fun n -> `Int n) w)) wires));
      ("icons", `List [ `Assoc [ ("signal", `Assoc [ ("type", `String "item"); ("name", `String "decider-combinator") ]);
                                 ("index", `Int 1) ] ]) ]) ]

let zlib data =
  let len = String.length data in
  let i = De.bigstring_create De.io_buffer_size and o = De.bigstring_create De.io_buffer_size in
  let w = De.Lz77.make_window ~bits:15 and q = De.Queue.create 0x1000 in
  let out = Buffer.create (len / 4) and pos = ref 0 in
  let refill buf =
    let n = min (len - !pos) De.io_buffer_size in
    for k = 0 to n - 1 do Bigarray.Array1.unsafe_set buf k data.[!pos + k] done;
    pos := !pos + n;
    n in
  let flush buf n = for k = 0 to n - 1 do Buffer.add_char out (Bigarray.Array1.unsafe_get buf k) done in
  Zl.Higher.compress ~level:9 ~w ~q ~refill ~flush i o;
  Buffer.contents out

let base64 data =
  let table = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/" in
  let n = String.length data in
  let buf = Buffer.create ((n + 2) / 3 * 4) in
  let byte i = if i < n then Char.code data.[i] else 0 in
  let rec go i =
    if i < n then begin
      let v = (byte i lsl 16) lor (byte (i + 1) lsl 8) lor byte (i + 2) in
      for k = 0 to 3 do
        Buffer.add_char buf (if i + k - 1 < n || k < 2 then table.[(v lsr (18 - 6 * k)) land 63] else '=')
      done;
      go (i + 3)
    end in
  go 0;
  Buffer.contents buf

let exchange_string blueprint = "0" ^ base64 (zlib (Pjson.compact blueprint))
