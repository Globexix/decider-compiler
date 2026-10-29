open Error

let step (spec : Spec.t) (program : Ir.program) (env : (string * int) list) =
  let mem = Interp.create_memory () in
  let roots = List.map (fun (g : Spec.group) ->
      let ptr = Interp.alloc program mem (Ir.Array (g.count, Ir.Struct g.struct_name)) in
      let root = match ptr with Interp.Ptr { root; _ } -> root | Interp.Int _ -> assert false in
      for i = 0 to g.count - 1 do
        List.iter (fun (f : Spec.field) ->
            let ty, w = match f.scalar with `I32 -> (Ir.Int 32, 32) | `Bool -> (Ir.Int 8, 8) in
            let v = List.assoc (Printf.sprintf "%s[%d].%s" g.group i f.field) env in
            Hashtbl.replace mem.cells (root, i * g.stride + f.offset, ty) (Some (Interp.Int (Interp.normalize w v)))) g.fields
      done;
      (g.group, (ptr, root))) spec.arrays in
  let snapshot = Hashtbl.copy mem.cells in
  let results = Hashtbl.create 8 in
  List.map (fun (s : Spec.state) ->
      let u = List.find (fun (u : Spec.update) -> u.target = s.name) spec.updates in
      let f = match Ir.find_func program u.func with Some f -> f | None -> fail "unknown function %s" u.func in
      let key = (u.func, u.args) in
      let cells = match Hashtbl.find_opt results key with
        | Some r -> r
        | None ->
          let mem = { mem with cells = Hashtbl.copy snapshot } in
          let args = List.map2 (fun a (_, ty) ->
              match List.assoc_opt a roots with
              | Some (ptr, _) -> ptr
              | None -> Interp.Int (Interp.normalize (Interp.width_of ty) (List.assoc a env))) u.args f.params in
          let r = Interp.call program mem f args ~depth:0 in
          Hashtbl.replace results key (r, mem.cells); (r, mem.cells) in
      let result, cells = cells in
      let widen w n = Interp.normalize 32 (if w < 32 then Interp.unsigned w n else n) in
      let v = match String.index_opt s.name '[' with
        | Some i when List.mem_assoc (String.sub s.name 0 i) roots ->
            let g = List.find (fun (g : Spec.group) -> g.group = String.sub s.name 0 i) spec.arrays in
            let _, root = List.assoc g.group roots in
            let rest = String.sub s.name i (String.length s.name - i) in
            let index, field = Scanf.sscanf rest "[%d].%s" (fun a b -> (a, b)) in
            let f = List.find (fun (f : Spec.field) -> f.field = field) g.fields in
            let ty, w = match f.scalar with `I32 -> (Ir.Int 32, 32) | `Bool -> (Ir.Int 8, 8) in
            (match Hashtbl.find_opt cells (root, index * g.stride + f.offset, ty) with
             | Some (Some (Interp.Int n)) -> widen w n
             | _ -> fail "%s: array field became uninitialized" s.name)
        | _ ->
          match result, f.ret with
            | Some (Interp.Int n), Ir.Int w -> widen w n
            | _ -> fail "%s: update must return a value" u.func in
      (s.name, v)) spec.states
