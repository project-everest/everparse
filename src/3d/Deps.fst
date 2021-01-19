module Deps

open FStar.IO
open FStar.All
open Ast

module H = Hashtable

type edge = string & string

type dep_graph = list edge

let all_edges_from (g:dep_graph) (node:string) : Tot (list edge) =
  List.Tot.filter (fun (src, _dst) -> src = node) g

(*
 * root is already in the visited nodes
 *)
let rec topsort_aux (g:dep_graph) (root:string) (acc:list string & list string)
  : ML (list string & list string) =  //visited nodes & sorted nodes

  let visited, sorted = acc in
  let all_edges_from_root = all_edges_from g root in
  if List.Tot.length all_edges_from_root = 0
  then visited, root::sorted  //finished DFS at root
  else
    let visited, sorted = 
      all_edges_from_root |> List.fold_left (fun (visited, sorted) (_src, dst) ->
        if List.Tot.mem dst visited
        then raise (Error "Cycle in the dependency graph")
        else topsort_aux g dst (dst::visited, sorted)) (visited, sorted) in
    visited, root::sorted

let topsort (g:dep_graph) (root:string) : ML (list string) =
  topsort_aux g root ([root], []) |> snd |> List.rev

let scan_deps (fn:string) : ML (list string) =
  let decls, __refinement = ParserDriver.parse fn in  //AR: TODO: look into refinement too?

  let abbrevs = H.create 10 in

  let maybe_dep (i:ident) : ML (list string) =
    match i.v.modul_name with
    | None -> []
    | Some s ->
      (match H.try_find abbrevs s with
       | None -> [s]
       | Some m -> [m]) in

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
    match d.v with
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
