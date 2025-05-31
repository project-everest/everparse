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
module BitFields
open FStar.List.Tot
open FStar.Mul
open Ast
open FStar.All
module B = Binding
module H = Hashtable

(* This module implements a pass over the source AST

   coalescing adjacent bit fields and replacing expressions on
   bitfields using offsets into larger fgields

*)

let bitfield_group = int & typ & list atomic_field
let grouped_fields = either field bitfield_group

let group_bit_fields (rewrite_composite_field: field -> ML field)
                     (fields: list field)
  : ML (list grouped_fields)
  = List.fold_right
      (fun field out ->
        match field.v with
        | RecordField _ _
        | SwitchCaseField _ _ ->
          Inl (rewrite_composite_field field) :: out

        | AtomicField af ->
          match af.v.field_bitwidth with
          | None ->
            Inl field :: out

          | Some (Inl _) ->
            failwith "Bit fields should have been elaborated already"

          | Some (Inr bf) ->
            match out with
            | Inr (index, typ, atomic_fields)::tl ->
              if index = bf.v.bitfield_identifier
              then Inr(index, typ, af :: atomic_fields) :: tl //extend this bitfield group
              else Inr(bf.v.bitfield_identifier, bf.v.bitfield_type, [af]) :: out //new bitfield group

            | _ -> Inr (bf.v.bitfield_identifier, bf.v.bitfield_type, [af]) :: out //new bitfield group
        )
       fields
       []

let subst' = list (ident & expr)

let coalesce_grouped_bit_field env (f:bitfield_group)
  : ML (field & subst')
  = let id, typ, fields = f in
    let size = B.size_of_integral_typ env typ typ.range in
    let bitsize = 8 * size in
    let order = B.bit_order_of_integral_typ env typ typ.range in
    let field_id = with_range (to_ident' (Printf.sprintf "__bitfield_%d" id)) dummy_range in
    let id = with_range (Identifier field_id) field_id.range in
    let mk_e (e:expr') :expr = with_range e field_id.range in
    let bitfield_attrs f : ML _ =
      match f.field_bitwidth with
      | Some (Inr bf) -> bf.v
      | _ -> failwith "Must have elaborated bitfield"
    in
    let field_dependence, field_constraint, field_action, subst =
      List.fold_left
        (fun (acc:(bool & _ & option (action & bool) & _)) f ->
          let (dep, acc_constraint, acc_action, subst) = acc in
          let f = f.v in
          let acc_action, acc_dep = 
            match acc_action, f.field_action with
            | None, None
            | Some _, None -> acc_action, false
            | None, Some (_, d) -> f.field_action, d
            | Some (acc, dep_0), Some (fa, dep_1) ->
              if Action_act? acc.v 
              && Action_act? fa.v
              then
                Some (Ast.sequence_non_failing_actions acc fa, dep_0 || dep_1),
                dep_0 || dep_1
              else
                failwith "Multiple, potentially failing actions are not supported on bitfields"
          in
          let dep = dep || acc_dep || f.field_dependence in
          let acc_constraint =
            match f.field_constraint, acc_constraint with
            | None, _ -> acc_constraint
            | Some _, None -> f.field_constraint
            | Some c, Some acc -> Some (mk_e (App And [acc; c]))
          in
          let bf_exp =
            App
              (BitFieldOf bitsize order)
              [id;
              mk_e (Constant (Int UInt32 (bitfield_attrs f).bitfield_from));
              mk_e (Constant (Int UInt32 (bitfield_attrs f).bitfield_to))]
          in
          let subst = (f.field_ident, mk_e bf_exp) :: subst in
          dep, acc_constraint, acc_action, subst)
       (false, None, None, [])
       fields
    in
    let struct_field = {
      field_dependence = field_dependence;
      field_ident = field_id;
      field_type = typ;
      field_array_opt = FieldScalar;
      field_constraint = field_constraint;
      field_bitwidth = None;
      field_action = field_action;
      field_probe = None
    } in
    let af = with_dummy_range struct_field in
    with_dummy_range (AtomicField af),
    subst
  
let rec rewrite_field (env:B.global_env) (f:field) 
  : ML (f':field  {field_tag_equal f f'})
  = match f.v with
    | AtomicField _ -> f
          
    | RecordField fs field_name -> 
      let gfs = group_bit_fields (rewrite_field env) fs in
      let fs, subst =
          List.fold_right
            (fun f (fields, subst) ->
               match f with
               | Inl f -> (f::fields, subst)
               | Inr gf ->
                 let f, subst' = coalesce_grouped_bit_field (B.mk_env env) gf in
                 f::fields, subst'@subst)
            gfs
            ([], [])
      in
      let fs = List.map (subst_field (mk_subst subst)) fs in
      { f with v = RecordField fs field_name }

    | SwitchCaseField (e, cases) field_name ->
      let cases = 
          List.map
            (function
              | Case p f ->
                Case p (rewrite_field env f)
                    
              | DefaultCase f ->
                DefaultCase (rewrite_field env f))
            cases
      in
      { f with v = SwitchCaseField (e, cases) field_name }

   
let eliminate_one_decl (env:B.global_env) (d:decl) : ML decl =
  match d.d_decl.v with
  | Record names generics params where fields ->
    let i = with_dummy_range (to_ident' "_") in
    let { v = RecordField fields _ } = rewrite_field env (with_range (RecordField fields i) d.d_decl.range) in
    List.iter (fun f ->
      Options.debug_print_string
            (Printf.sprintf "Bitfields: Field %s has comments <%s>\n"
                  (print_field f)
                  (String.concat "\n" f.comments))) fields;

    let fields =
      match fields with
      | [{v=AtomicField af; range; comments}] -> //just one field, it need no longer be dependent
        let af' = { af.v with field_dependence = false } in
        let af' = { af with v = af' } in
        [{v=AtomicField af; range; comments}]
      | _ -> fields
    in
    decl_with_v d (Record names generics params where fields)
  | _ -> d

let eliminate_decls (env:B.global_env) (ds:list decl) : ML (list decl) =
  List.map (eliminate_one_decl env) ds
