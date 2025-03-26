module Specialize
(*
  This module implements a pass over the source AST,
  elaborating the `specialize` declaration
*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
module B = Binding
module G32 = Generate32BitTypes
let rec specialize_type (e:B.env) (t:typ)
: ML (ident & typ)
= match t.v with
  | Type_app i k gs ps -> (
    let d, _ = B.lookup_type_decl e i in
    let gs', _ = B.params_of_decl d in
    let instantiations =
      List.map
        (fun (GenericProbeFunction _ _ t) -> G32.coercion_for_type t) gs'
    in
    let insts = List.map (fun i -> with_dummy_range <| Identifier i) instantiations in
    i, {t with v = Type_app i k insts ps}
  )
  | Pointer t (PQ UInt64 false) ->
    let i, t' = specialize_type e t in
    i, {t with v = Pointer t' (PQ UInt32 true)}
  | Pointer t (PQ pq true) ->
    let i, t' = specialize_type e t in
    i, {t with v = Pointer t' (PQ pq true)}
  | Type_arrow _ _ -> failwith "Cannot specialize function types"
  

let specialize_atomic_field (e:B.env) (af:atomic_field)
: ML atomic_field
= let ht, ft = specialize_type e af.v.field_type in
  let pc =
    match af.v.field_probe with
    | None -> None
    | Some pc -> (
      let coercion = G32.coercion_for_type ht in
      let pb =
        match pc.probe_block.v with
        | Probe_action_var { v = Identifier i } -> 
          with_dummy_range <| Identifier coercion
        | Probe_action_var { v = App (ProbeFunctionName f) args } -> 
          with_dummy_range <| App (ProbeFunctionName coercion) args
        | _ -> failwith "Unexpected probe block"
      in
      Some { pc with probe_block = with_dummy_range <| Probe_action_var pb }
    )
  in
  let af' = {af with v = {af.v with field_type = ft; field_probe=pc}} in
  af'
  

let specialize_fields (e:B.env) (fields: list field)
: ML (list field)
= let rec specialize_field (f:field)
  : ML field
  = match f.v with
    | AtomicField af -> 
      {f with v = AtomicField <| specialize_atomic_field e af }
    | RecordField r i -> { f with v = RecordField (List.map specialize_field r) i }
    | SwitchCaseField sw i -> { f with v = SwitchCaseField (fst sw, List.map specialize_case <| snd sw) i }
  and specialize_case (c:case)
  : ML case
  = match c with
    | Case e f -> Case e (specialize_field f)
    | DefaultCase f -> DefaultCase (specialize_field f)
  in
  List.map specialize_field fields

let specialize_one (e:GlobalEnv.global_env) (d: decl { Specialize? d.d_decl.v })
: ML decl
= let e = B.mk_env e in
  let Specialize qs i j = d.d_decl.v in
  let di, attrs = B.resolve_record_type e i in
  let nm = { i with v = { i.v with name = reserved_prefix ^ "specialized_" ^ j.v.name }} in
  let Record names gs params wh fields = di.d_decl.v in
  let names = { 
    names with
    typedef_name = nm; 
    typedef_abbrev = j;
    typedef_ptr_abbrev = None 
  } in
  let fields = specialize_fields e fields in
  let dj = Record names [] params wh fields in
  let d = { d with d_decl = { d.d_decl with v = dj }} in
  d

let specialize (e:GlobalEnv.global_env) (ds: list decl)
: ML (list decl & bool)
= let specialized : ref bool = alloc false in
  let ds = 
    List.map
      (fun (d:decl) ->
        if Specialize? d.d_decl.v 
        then (
          specialized := true;
          specialize_one e d
        )
        else d)
      ds
  in
  ds, !specialized