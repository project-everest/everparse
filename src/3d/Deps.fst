module Deps

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
    | App _op args -> List.collect deps_of_expr args in

  let rec deps_of_typ (t:typ) : ML (list string) =
    match t.v with
    | Type_app hd args -> (maybe_dep hd)@(List.collect deps_of_expr args)
    | Pointer t -> deps_of_typ t in

  let deps_of_atomic_action (ac:atomic_action) : ML (list string) =
    match ac with
    | Action_return e -> deps_of_expr e
    | Action_abort | Action_field_pos | Action_field_ptr -> []
    | Action_deref _i -> []  //a local variable
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
    | Action_let _i a k -> (deps_of_atomic_action a)@(deps_of_action k) in

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
    | FieldString eopt -> deps_of_opt deps_of_expr eopt in

  let deps_of_struct_field (sf:struct_field) : ML (list string) =
    (deps_of_typ sf.field_type)@
    (deps_of_field_array_t sf.field_array_opt)@
    (deps_of_opt deps_of_expr sf.field_constraint)@
    (deps_of_opt deps_of_field_bitwidth_t sf.field_bitwidth)@
    (deps_of_opt (fun (a, _) -> deps_of_action a) sf.field_action) in

  let deps_of_case (c:case) : ML (list string) =
    match c with
    | Case e f -> (deps_of_expr e)@(deps_of_struct_field f.v)
    | DefaultCase f -> deps_of_struct_field f.v in

  let deps_of_switch_case (sc:switch_case) : ML (list string) =
    let e, l = sc in
    (deps_of_expr e)@(List.collect deps_of_case l) in

  let deps_of_enum_case (ec:enum_case) : ML (list string) =
    match snd ec with
    | Some (Inr i) -> maybe_dep i
    | _ -> [] in

  let rec deps_of_decl (d:decl) : ML (list string) =
    match d.d_decl.v with
    | ModuleAbbrev i m ->
      H.insert abbrevs i.v.name m.v.name;
      [m.v.name]
    | Define _ None _ -> []
    | Define _ (Some t) _ -> deps_of_typ t
    | TypeAbbrev t _ -> deps_of_typ t
    | Enum _base_t _ l -> List.collect deps_of_enum_case l
    | Record _ params wopt flds ->
      (deps_of_params params)@
      (deps_of_opt deps_of_expr wopt)@
      (List.collect (fun f -> deps_of_struct_field f.v) flds)
    | CaseType _ params sc ->
      (deps_of_params params)@
      (deps_of_switch_case sc) in

  {
    sd_deps = List.collect deps_of_decl decls;
    sd_has_entrypoint = has_entrypoint;
    sd_has_static_assertions = has_static_assertions;
  }

let rec build_dep_graph_aux (dirname:string) (mname:string) (acc:dep_graph & list string)
  : ML (dep_graph & list string) =  //seen

  let g, seen = acc in
  if List.mem mname seen then acc
  else
    let {sd_has_entrypoint = has_entrypoint; sd_deps = deps; sd_has_static_assertions = has_static_assertions} =
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
    }
    in
    List.fold_left (fun acc dep -> build_dep_graph_aux dirname dep acc)
      (g', mname::seen) deps

let build_dep_graph_from_list files =
  let g0 = {
    graph = [];
    modules_with_entrypoint = [];
    modules_with_static_assertions = [];
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

let get_sorted_deps (g: dep_graph) (fl: list string) : ML (list string) =
  List.collect (fun fn -> topsort g.graph (Options.get_module_name fn)) fl

let collect_and_sort_dependencies_from_graph (g: dep_graph) (files:list string) : ML (list string) =
  let dirname = files |> List.hd |> OS.dirname in
  let filename_of modul = Options.get_file_name (OS.concat dirname modul) in
  files
  |> get_sorted_deps g
  |> List.fold_left (fun acc mod -> if List.mem mod acc then acc else mod::acc) []
  |> List.rev
  |> List.map filename_of

let has_entrypoint g m = List.Tot.mem m g.modules_with_entrypoint

let has_static_assertions g m = List.Tot.mem m g.modules_with_static_assertions
