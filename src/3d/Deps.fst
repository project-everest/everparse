module Deps
open FStar.List.Tot
open FStar.IO
open FStar.All
open Ast

module H = Hashtable

type edge = string & string

type dep_graph' = list edge

type dep_graph = {
  graph: dep_graph';
  modules_with_entrypoint: list string;
  modules_with_static_assertions: list string;
  modules_with_output_types: list string;
  modules_with_out_exprs: list string;
  modules_with_extern_types: list string;
  modules_with_extern_functions: list string;
  modules_with_extern_probe: list string;
}

let all_edges_from (g:dep_graph') (node:string) : Tot (list edge) =
  List.Tot.filter (fun (src, _dst) -> src = node) g

let dependencies graph modul =
  List.Tot.map snd (all_edges_from graph.graph modul)

let dep_exists dirname name =
  OS.file_exists (Options.get_file_name (OS.concat dirname name))

(*
 * root is already greyed
 *)
let rec topsort_aux (g:dep_graph') (root:string) (acc:list string & list string)
  : ML (list string & list string) =  //grey nodes & finished nodes

  let finish (acc:list string & list string) : ML (list string & list string) =
    let grey, finished = acc in
    List.filter (fun s -> s <> root) grey, root::finished in

  let all_edges_from_root = all_edges_from g root in
  if List.length all_edges_from_root = 0
  then finish acc
  else
    all_edges_from_root
    |> List.fold_left (fun (grey, finished) (_src, dst) ->
        if List.mem dst grey
        then raise (Error (Printf.sprintf "Cycle in the dependency graph (%s)"
               (List.fold_left (fun s m -> Printf.sprintf "%s <== %s" s m) dst grey)))
        else if List.mem dst finished then (grey, finished)
        else topsort_aux g dst (dst::grey, finished)) acc
    |> finish

let topsort (g:dep_graph') (root:string) : ML (list string) =
  topsort_aux g root ([root], []) |> snd |> List.rev

noeq
type scan_deps_t = {
  sd_deps: list string;
  sd_has_entrypoint: bool;
  sd_has_static_assertions: bool;
  sd_has_output_types: bool;
  sd_has_out_exprs: bool;
  sd_has_extern_types: bool;
  sd_has_extern_functions: bool;
  sd_has_extern_probe: bool;
}

let scan_deps (fn:string) : ML scan_deps_t =
  let dirname = OS.dirname fn in
  let decls, refinement = ParserDriver.parse fn in  //AR: TODO: look into refinement too?

  let has_entrypoint = List.Tot.existsb is_entrypoint decls in
  let has_static_assertions = Some? refinement in

  let abbrevs = H.create 10 in

  let maybe_dep (i:ident) : ML (list string) =
    match i.v.modul_name with
    | None -> []
    | Some s ->
      let dep =
        match H.try_find abbrevs s with
        | None -> s
        | Some m -> m
      in
      if dep_exists dirname dep
      then [dep]
      else error (Printf.sprintf "Dependency not found: %s" dep) i.range
  in

  let deps_of_opt (#a:Type) (f:a -> ML (list string)) (x:option a) : ML (list string) =
    match x with
    | None -> []
    | Some x -> f x in

  let rec deps_of_expr (e:expr) : ML (list string) =
    match e.v with
    | Constant _ -> []
    | Identifier i -> maybe_dep i
    | This -> []
    | Static e -> deps_of_expr e
    | App _op args -> List.collect deps_of_expr args in

  let deps_of_typ_param (p:typ_param) : ML (list string) =
    match p with
    | Inl e -> deps_of_expr e
    | _ -> [] in  //AR: no dependencies from the output expressions

  let rec deps_of_typ (t:typ) : ML (list string) =
    match t.v with
    | Type_app hd _ gs args -> (maybe_dep hd)@(List.collect deps_of_expr gs)@(List.collect deps_of_typ_param args)
    | Pointer t _ -> deps_of_typ t
    | Type_arrow ts t -> List.collect deps_of_typ (t::ts) in

  let deps_of_atomic_action (ac:atomic_action) : ML (list string) =
    match ac with
    | Action_return e -> deps_of_expr e
    | Action_abort | Action_field_pos_64 | Action_field_pos_32 | Action_field_ptr -> []
    | Action_deref _i -> []  //a local variable
    | Action_field_ptr_after sz _write_to -> deps_of_expr sz
    | Action_assignment _lhs rhs -> deps_of_expr rhs
    | Action_call hd args -> (maybe_dep hd)@(List.collect deps_of_expr args) in

  let rec deps_of_action (a:action) : ML (list string) =
    match a.v with
    | Atomic_action ac -> deps_of_atomic_action ac
    | Action_seq hd tl -> (deps_of_atomic_action hd)@(deps_of_action tl)
    | Action_ite hd then_ else_ ->
      (deps_of_expr hd)@
      (deps_of_action then_)@
      (deps_of_opt deps_of_action else_)
    | Action_let _i a k -> (deps_of_atomic_action a)@(deps_of_action k)
    | Action_act a -> deps_of_action a in

  let deps_of_probe_atomic_action (a:probe_atomic_action) : ML (list string) =
    match a with
    | Probe_action_return e -> deps_of_expr e
    | Probe_action_call f args -> List.collect deps_of_expr args
    | Probe_action_read f -> []
    | Probe_action_write f v -> deps_of_expr v
    | Probe_action_copy f len -> deps_of_expr len
    | Probe_action_skip len -> deps_of_expr len
    | Probe_action_fail -> [] in

  let rec deps_of_probe_action (a:probe_action) : ML (list string) =
    match a.v with
    | Probe_atomic_action a -> deps_of_probe_atomic_action a
    | Probe_action_var e -> deps_of_expr e
    | Probe_action_simple _i len -> deps_of_expr len
    | Probe_action_seq hd tl -> (deps_of_probe_action hd)@(deps_of_probe_action tl)
    | Probe_action_let i a k -> (deps_of_probe_atomic_action a)@(deps_of_probe_action k)
    | Probe_action_ite e th el -> deps_of_expr e @ deps_of_probe_action th @ deps_of_probe_action el
  in
  let deps_of_params params : ML (list string) =
    params |> List.collect (fun (t, _, _) -> deps_of_typ t) in

  let deps_of_bitfield_attr (b:bitfield_attr) : ML (list string) =
    deps_of_typ b.v.bitfield_type in

  let deps_of_field_bitwidth_t (fb:field_bitwidth_t) : ML (list string) =
    match fb with
    | Inr b -> deps_of_bitfield_attr b
    | _ -> [] in

  let deps_of_field_array_t (fa:field_array_t) : ML (list string) =
    match fa with
    | FieldScalar -> []
    | FieldArrayQualified (e, _) -> deps_of_expr e
    | FieldString eopt -> deps_of_opt deps_of_expr eopt
    | FieldConsumeAll -> []
  in

  let deps_of_atomic_field (af:atomic_field) : ML (list string) =
      let af = af.v in
      (deps_of_typ af.field_type)@
      (deps_of_field_array_t af.field_array_opt)@
      (deps_of_opt deps_of_expr af.field_constraint)@
      (deps_of_opt deps_of_field_bitwidth_t af.field_bitwidth)@
      (deps_of_opt (fun (a, _) -> deps_of_action a) af.field_action)@
      (deps_of_opt (fun pc -> deps_of_probe_action pc.probe_block @ maybe_dep pc.probe_dest) af.field_probe)
  in

  let rec deps_of_field (f:field) : ML (list string) = 
    match f.v with
    | AtomicField af -> deps_of_atomic_field af
    | RecordField fs _ -> List.collect deps_of_field fs
    | SwitchCaseField swc _ -> deps_of_switch_case swc
  and deps_of_case (c:case) : ML (list string) =
    match c with
    | Case e f -> (deps_of_expr e)@(deps_of_field f)
    | DefaultCase f -> deps_of_field f
    
  and deps_of_switch_case (sc:switch_case) : ML (list string) =
    let e, l = sc in
    (deps_of_expr e)@(List.collect deps_of_case l) in

  let deps_of_enum_case (ec:enum_case) : ML (list string) =
    match snd ec with
    | Some (Inr i) -> maybe_dep i
    | _ -> [] in

  let deps_of_attribute (a:attribute) : ML (list string) = match a with
    | Entrypoint (Some p) -> maybe_dep p.probe_ep_fn `List.Tot.append` deps_of_expr p.probe_ep_length
    | _ -> []
  in

  let deps_of_typedef_names (td: typedef_names) : ML (list string) =
    List.collect deps_of_attribute td.typedef_attributes
  in

  let deps_of_decl (d:decl) : ML (list string) =
    match d.d_decl.v with
    | ModuleAbbrev i m ->
      H.insert abbrevs i.v.name m.v.name;
      [m.v.name]
    | Define _ None _ -> []
    | Define _ (Some t) _ -> deps_of_typ t
    | TypeAbbrev attrs t _ _ _ ->
      List.collect deps_of_attribute attrs @
      deps_of_typ t
    | Enum _base_t _ l -> List.collect deps_of_enum_case l
    | Record tdnames _generics params wopt flds ->
      (deps_of_typedef_names tdnames)@
      (deps_of_params params)@
      (deps_of_opt deps_of_expr wopt)@
      (List.collect deps_of_field flds)
    | CaseType tdnames _generics params sc ->
      (deps_of_typedef_names tdnames)@
      (deps_of_params params)@
      (deps_of_switch_case sc)
    | ProbeFunction f params probe_action _ ->
      (deps_of_params params)@
      (deps_of_probe_action probe_action)
    | CoerceProbeFunctionStub _ ps _ -> deps_of_params ps
    | Specialize _ _ _
    | OutputType _
    | ExternType _
    | ExternFn _ _ _ _
    | ExternProbe _ _ -> []  //AR: no dependencies from the output/extern types yet
  in

  let has_output_types (ds:list decl) : bool =
    List.Tot.existsb (fun d -> OutputType? d.d_decl.v) ds in

  let has_out_exprs (ds:list decl) : bool =
    List.Tot.existsb decl_has_out_expr ds in

  let has_extern_types (ds:list decl) : bool =
    List.Tot.existsb (fun d -> ExternType? d.d_decl.v) ds in

  let has_extern_functions (ds:list decl) : bool =
    List.Tot.existsb (fun d -> ExternFn? d.d_decl.v) ds in

  let has_extern_probe (ds: list decl) : bool =
    List.Tot.existsb (fun d -> ExternProbe? d.d_decl.v) ds in

  {
    sd_deps = List.collect deps_of_decl decls;
    sd_has_entrypoint = has_entrypoint;
    sd_has_static_assertions = has_static_assertions;
    sd_has_output_types = has_output_types decls;
    sd_has_out_exprs = has_out_exprs decls;
    sd_has_extern_types = has_extern_types decls;
    sd_has_extern_functions = has_extern_functions decls;
    sd_has_extern_probe = has_extern_probe decls;
  }

let rec build_dep_graph_aux (dirname:string) (mname:string) (acc:dep_graph & list string)
  : ML (dep_graph & list string) =  //seen

  let g, seen = acc in
  if List.mem mname seen then acc
  else
    let {sd_has_entrypoint = has_entrypoint;
         sd_deps = deps;
         sd_has_static_assertions = has_static_assertions;
         sd_has_output_types = has_output_types;
         sd_has_out_exprs = has_out_exprs;
         sd_has_extern_types = has_extern_types;
         sd_has_extern_functions = has_extern_functions;
         sd_has_extern_probe = has_extern_probe;
        } =
      scan_deps (Options.get_file_name (OS.concat dirname mname))
    in
    let edges = List.fold_left (fun edges dep ->
      if List.mem (mname, dep) edges
      then edges
      else (mname, dep)::edges) [] deps in
    let g' = {
      graph = g.graph @ edges;
      modules_with_entrypoint = (if has_entrypoint then mname :: g.modules_with_entrypoint else g.modules_with_entrypoint);
      modules_with_static_assertions = (if has_static_assertions then mname :: g.modules_with_static_assertions else g.modules_with_static_assertions);
      modules_with_output_types = (if has_output_types then mname::g.modules_with_output_types else g.modules_with_output_types);
      modules_with_out_exprs = (if has_out_exprs then mname::g.modules_with_out_exprs else g.modules_with_out_exprs);
      modules_with_extern_types = (if has_extern_types then mname::g.modules_with_extern_types else g.modules_with_extern_types);
      modules_with_extern_functions = (if has_extern_functions then mname::g.modules_with_extern_functions else g.modules_with_extern_functions);
      modules_with_extern_probe = (if has_extern_probe then mname::g.modules_with_extern_probe else g.modules_with_extern_probe);
    }
    in
    List.fold_left (fun acc dep -> build_dep_graph_aux dirname dep acc)
      (g', mname::seen) deps

let build_dep_graph_from_list files =
  let g0 = {
    graph = [];
    modules_with_entrypoint = [];
    modules_with_static_assertions = [];
    modules_with_output_types = [];
    modules_with_out_exprs = [];
    modules_with_extern_types = [];
    modules_with_extern_functions = [];
    modules_with_extern_probe = [];
  }
  in
  let g1 = List.fold_left (fun acc fn -> build_dep_graph_aux (OS.dirname fn) (Options.get_module_name fn) acc) (g0, []) files
  |> fst
  in
  {g1 with graph =
    List.Tot.sortWith
      (fun (l1, r1) (l2, r2) ->
        let c = String.compare l1 l2 in
        if c = 0
        then String.compare r1 r2
        else c
      )
      g1.graph
  }

let get_sorted_deps (g: dep_graph) (ml: list string) : ML (list string) =
  List.collect (fun m -> topsort g.graph m) (List.Tot.sortWith String.compare ml)

let collect_and_sort_dependencies_from_graph (g: dep_graph) (files:list string) : ML (list string) =
  let dirname = files |> List.hd |> OS.dirname in
  let filename_of modul = Options.get_file_name (OS.concat dirname modul) in
  files
  |> List.map Options.get_module_name
  |> get_sorted_deps g
  |> List.fold_left (fun acc mod -> if List.mem mod acc then acc else mod::acc) []
  |> List.rev
  |> List.map filename_of

let has_entrypoint g m = List.Tot.mem m g.modules_with_entrypoint

let has_static_assertions g m = List.Tot.mem m g.modules_with_static_assertions

let has_output_types g m = List.Tot.mem m g.modules_with_output_types

let has_out_exprs g m = List.Tot.mem m g.modules_with_out_exprs

let has_extern_types g m = List.Tot.mem m g.modules_with_extern_types

let has_extern_functions g m = List.Tot.mem m g.modules_with_extern_functions

let has_extern_probe g m = List.Tot.mem m g.modules_with_extern_probe


#push-options "--warn_error -272"
let parsed_config : ref (option (Config.config & string)) = ST.alloc None
#pop-options

let parse_config () =
  match Options.get_config_file () with
  | None -> None
  | Some fn -> 
    let module_name = Options.config_module_name () in
    if None? module_name then failwith "Impossible"
    else if not (OS.file_exists fn)
    then raise (Error ("Unable to file configuration file: " ^ fn))
    else 
      let s = 
        try OS.file_contents fn
        with
        | _ -> raise (Error ("Unable to read configuration file: "^fn))
      in
      match JSON.config_of_json s with
      | Pervasives.Inl c -> Some (c, Some?.v module_name)
      | Pervasives.Inr err -> 
        let msg = 
          Printf.sprintf "Unable to parse configuration: %s\n\
                          A sample configuration is shown below:\n\
                          %s"
                          err
                          (JSON.config_to_json { compile_time_flags = { flags = ["FLAG1"; "FLAG2"; "FLAG3"];
                                                                        include_file = "flags.h" }}) in
        raise (Error msg)

let get_config () = 
  match !parsed_config with
  | Some c -> Some c
  | None ->
    let copt = parse_config () in
    parsed_config := copt;
    copt
