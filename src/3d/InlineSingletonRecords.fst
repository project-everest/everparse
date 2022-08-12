(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module InlineSingletonRecords
open Ast
open FStar.All
module H = Hashtable
type singleton_record = list param & field
let env = H.t ident' singleton_record

(*
  This module implements a pass over the source AST
  
    1. Inlining records that contain only a single field
    2. Inlining enumerated types that have dependences

  Both of these are necessary to avoid double fetches
*)
    
  
let choose_one (a b:option 'a) : ML (option 'a) = 
  match a, b with
  | Some fc, _
  | _, Some fc -> Some fc
  | _ -> None
                 
let simplify_field (env:env) (f:field)
  : ML field
  = let field = f.v in
    let field = 
      match field.field_type.v with
      | Pointer _ -> failwith "Impossible: field types cannot be pointers"
      | Type_app hd _ args ->
        begin
        match H.try_find env hd.v with
        | None -> //not a singleton record
          field
        | Some (params, inlined_field) ->
          match field.field_array_opt, field.field_bitwidth with
          | FieldArrayQualified _, _
          | FieldString _, _
          | _, Some _ ->  //cannot be inlined
            field
          | _ -> 
            let subst = 
               List.map2 
               (fun (_t, x, _q) e ->
                match e with
                | Inr _ -> failwith "Cannot inline singleton records with output type parameters"
                | Inl e -> (x, e))
               params args
            in
            let subst = (inlined_field.v.field_ident, with_dummy_range (Identifier field.field_ident)) :: subst in
            let inlined_field = subst_field (mk_subst subst) inlined_field in
            let error msg = 
              let msg = 
                Printf.sprintf "Other types depend on the value of this field, but this field cannot be read because %s"
                               msg
              in
              error msg f.range
            in
            match field, inlined_field.v with
            | { field_action = Some _ }, { field_action = Some _ } ->
              error "it has multiple actions"
  
            | { field_constraint = Some _ }, { field_action = Some _ } ->
              error "reading it would alter the order of evaluation of refinement and action"
  
            | { field_array_opt = FieldArrayQualified _ }, _
            | _, { field_array_opt = FieldArrayQualified _ } ->
              error "it contains an array"
  
            | { field_array_opt = FieldString _ }, _
            | _, { field_array_opt = FieldString _ } ->
              error "it contains a string"

            | { field_bitwidth = Some _ }, _        
            | _, { field_bitwidth = Some _ } ->
              error "it contains a bit field"
          
            | _, _ ->
              let join_constraints c1 c2 =
                match c1, c2 with
                | None, None -> None
                | Some c, None 
                | None, Some c -> Some c
                | Some c1, Some c2 -> Some (with_dummy_range (App And [c1;c2]))
              in
              { field with 
                field_type = inlined_field.v.field_type;
                field_constraint = join_constraints field.field_constraint inlined_field.v.field_constraint;
                field_action = choose_one field.field_action inlined_field.v.field_action }
          end
    in
    { f with v = field }

let simplify_decl (env:env) (d:decl) : ML decl =
  match d.d_decl.v with
  | ModuleAbbrev _ _ ->
    d

  | Define _ _ _ ->
    d

  | TypeAbbrev t i ->
    d

  | Enum t i cases ->
    let field_name =
      let s = 
        reserved_prefix ^
        "field_name_" ^
        i.v.name
      in
      with_dummy_range (to_ident' s)
    in
    let exp e = with_dummy_range e in
    let constraint =
        let constr_opt =
          List.fold_right 
            (fun (i, _) out_opt -> 
              let eq = with_dummy_range (App Eq [exp <| Identifier i; exp <| Identifier field_name]) in
              match out_opt with
              | None -> Some eq
              | Some out -> Some (with_dummy_range (App Or [eq; out])))
            cases
            None
        in
        match constr_opt with
        | Some e -> e
        | None -> with_dummy_range (Constant (Bool false))
    in
    let field =
        { field_dependence = false;
          field_ident = field_name;
          field_type = t;
          field_array_opt = FieldScalar;
          field_constraint = Some constraint;
          field_bitwidth = None;
          field_action = None }
    in
    let field = with_dummy_range field in
    Options.debug_print_string 
      (Printf.sprintf "For Enum %s, inserting field = %s\n"
        i.v.name
        (print_field field));
    H.insert env i.v ([], field);
    d
    
  | Record tdnames params None [field] -> //singleton
    begin
    match field.v with
    | { field_array_opt = FieldArrayQualified _ }
    | { field_array_opt = FieldString _ }
    | { field_bitwidth = Some _ } ->
       d
    | _ -> 
      let field = simplify_field env field in
      H.insert env tdnames.typedef_name.v (params, field);
      decl_with_v d (Record tdnames params None [field])
    end
  
  | Record tdnames params wopt fields ->
    let fields = List.map (simplify_field env) fields in
    decl_with_v d (Record tdnames params wopt fields)

  | CaseType tdnames params switch ->
    let hd, cases = switch in
    let cases = List.map (function Case e f -> Case e (simplify_field env f)
                                 | DefaultCase f -> DefaultCase (simplify_field env f)) 
                         cases in
    decl_with_v d (CaseType tdnames params (hd, cases))

  | OutputType _
  | ExternType _
  | ExternFn _ _ _
  | CompileTimeFlag _ -> d

let simplify_prog (p:list decl) =
  let env = H.create 10 in
  List.map (simplify_decl env) p
