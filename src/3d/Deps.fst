module Deps

open FStar.IO
open FStar.All
open Ast

module H = Hashtable

type edge = string & string

type dep_graph = list edge

let all_edges_from (g:dep_graph) (node:string) : ML (list edge) =
  g |> List.filter (fun (src, _dst) -> src = node)

type acc_t = list string & list string  //seen nodes and sorted nodes

let rec topsort_aux (g:dep_graph) (root:string) (acc:acc_t)
  : ML acc_t =  //seen and sorted

  let seen, sorted = acc in
  let all_edges_from_root = all_edges_from g root in
  if List.length all_edges_from_root = 0
  then seen, root::sorted  //finished DFS at root
  else
    all_edges_from_root |> List.fold_left (fun (seen, sorted) (_src, dst) ->
      let b = List.mem dst seen in
      if b
      then error "Cycle in the dependency graph" Ast.dummy_range
      else
        let seen, sorted = topsort_aux g dst (dst::seen, sorted) in
        seen, root::sorted) (seen, sorted)

let topsort (g:dep_graph) (root:string) : ML (list string) =
  topsort_aux g root ([], []) |> snd |> List.rev

let scan_deps (fn:string) : ML (list string) =
  let decls, __refinement = ParserDriver.parse fn in  //AR: TODO: look into refinement too?

  let abbrevs = H.create 10 in

  let maybe_dep (i:ident) =
    match i.v.modul_name with
    | None -> []
    | Some s ->
      match H.try_find abbrevs s with
      | None -> [s]
      | Some m -> [m] in

  //AR: TODO: collect deps from expressions etc.

  let rec deps_of_typ (t:typ) : ML (list string) =
    match t.v with
    | Type_app hd _ -> maybe_dep hd
    | Pointer t -> deps_of_typ t in

  let deps_of_params params : ML (list string) =
    params |> List.collect (fun (t, _, _) -> deps_of_typ t) in

  let rec deps_of_decl (d:decl) : ML (list string) =
    match d.v with
    | ModuleAbbrev i m ->
      H.insert abbrevs i.v.name m.v.name;
      [m.v.name]
    | Define _ None _ -> []
    | Define _ (Some t) _ -> deps_of_typ t
    | TypeAbbrev t _ -> deps_of_typ t
    | Enum _ _ _ -> []
    | Record _ params _ flds ->
      (deps_of_params params) @
      (List.collect (fun fld -> deps_of_typ fld.v.field_type) flds)
    | CaseType _ params (_, cases) ->
      (deps_of_params params) @
      (List.collect (fun case -> match case with
                              | Case _ fld
                              | DefaultCase fld -> deps_of_typ fld.v.field_type) cases) in
  List.collect deps_of_decl decls

let rec build_dep_graph_aux (dirname:string) (mname:string) (acc:dep_graph & list string)
  : ML (dep_graph & list string) =  //seen

  let g, seen = acc in
  if List.mem mname seen then acc
  else
    let deps = scan_deps (Options.get_file_name (OS.concat dirname mname)) in
    let edges = List.fold_left (fun edges dep ->
      if List.mem (mname, dep) edges
      then edges
      else (mname, dep)::edges) [] deps in
    List.fold_left (fun acc dep -> build_dep_graph_aux dirname dep acc)
      (g@edges, mname::seen) deps

let build_dep_graph (fn:string) : ML dep_graph =
  build_dep_graph_aux (OS.dirname fn) (Options.get_module_name fn) ([], [])
  |> fst

let get_sorted_deps fn =
  let dep_graph = build_dep_graph fn in
  topsort dep_graph (Options.get_module_name fn)
