(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain as copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Binding

(*
  This module implements a pass over the source AST
     -- checking that all names are properly bound
     -- well-typed
     -- computing the size of types
     -- computing which fields are dependent on others
*)
open FStar.Mul
open FStar.List.Tot
open Ast
open FStar.All
module H = Hashtable
include GlobalEnv

/// Maps locally bound names, i.e., a field name to its type
///  -- the bool signifies that this identifier has been used, and is
///     therefore marked as a dependent field
///
/// The modul_name in these ident' must be None -- TODO: add a refinement?
let local_env = H.t ident' (ident' & typ & bool)

/// `env` includes both a global and local env, together with a
/// binding for the `this` variable (bound to the name of a type) in
/// the current scope
noeq
type env = {
  this: option ident;
  locals: local_env;
  globals: global_env;
}

let mk_env (g:global_env) =
  { this = None;
    locals = H.create 10;
    globals = g }

let copy_env (e:env) =
  let locals = H.create 10 in
  H.iter (fun k v -> H.insert locals k v) e.locals;
  {
    this = e.this;
    globals = e.globals;
    locals = locals
  }

#push-options "--warn_error -272"  //intentional top-level effect
let env_of_global_env 
  : global_env -> env
  = let locals = H.create 1 in
    fun g -> { this = None; locals; globals = g }
#pop-options

let global_env_of_env e = e.globals

let params_of_decl (d:decl) : list param =
  match d.d_decl.v with
  | ModuleAbbrev _ _
  | Define _ _ _
  | TypeAbbrev _ _
  | Enum _ _ _ -> []
  | Record _ params _ _
  | CaseType _ params _ -> params
  | OutputType _ -> []
  | ExternType _ -> []
  | ExternFn _ _ ps -> ps
  | ExternProbe _ -> []

let check_shadow (e:H.t ident' 'a) (i:ident) (r:range) =
  match H.try_find e i.v with
  | Some j ->
    let msg = Printf.sprintf "Declaration %s clashes with previous declaration" (ident_to_string i) in
    error msg i.range
  | _ -> ()

let typedef_names (d:decl) : option typedef_names =
  match d.d_decl.v with
  | Record td _ _ _
  | CaseType td _ _ -> Some td
  | _ -> None

let format_identifier (e:env) (i:ident) : ML ident =
  let j =
    match String.list_of_string i.v.name with
    | [] ->
      failwith "Impossible: empty identifier"
    | c0::cs ->
      if FStar.Char.lowercase c0 = c0
      then i //it starts with a lowercase symbol; that's ok
      else //otherwise, add an underscore
           {i with v = {i.v with name=Ast.reserved_prefix ^ i.v.name}}
  in
  match H.try_find e.globals.ge_h j.v, H.try_find e.locals j.v with
  | None, None -> j
  | _ ->
    let msg = Printf.sprintf
      "This name (%s) starts will clash with another name in scope (%s) as it is translated. \
       Please rename it"
       (ident_to_string i) (ident_to_string j) in
    error msg i.range

let add_global (e:global_env) (i:ident) (d:decl) (t:either decl_attributes macro_signature) : ML unit =
  let insert k v =
    Options.debug_print_string
      (Printf.sprintf "Inserting global: %s\n" (ident_to_string k));
    H.insert e.ge_h k.v v
  in

  check_shadow e.ge_h i d.d_decl.range;
  let env = mk_env e in
  let i' = format_identifier env i in
  insert i (d, t);
  insert i' (d, t);
  match typedef_names d with
  | None -> ()
  | Some td ->
    if td.typedef_abbrev.v <> i.v
    then begin
      check_shadow e.ge_h td.typedef_abbrev d.d_decl.range;
      let abbrev = format_identifier env td.typedef_abbrev in
      insert td.typedef_abbrev (d, t);
      insert abbrev (d, t)
    end

let add_local (e:env) (i:ident) (t:typ) : ML unit =
  check_shadow e.globals.ge_h i t.range;
  check_shadow e.locals i t.range;
  let i' = format_identifier e i in
  H.insert e.locals i.v (i'.v, t, false);
  H.insert e.locals i'.v (i'.v, t, false)

let try_lookup (e:env) (i:ident) : ML (option (either typ (decl & either decl_attributes macro_signature))) =
  match H.try_find e.locals i.v with
  | Some (_, t, true) ->
    Some (Inl t)
  | Some (j, t, false) ->  //mark it as used
    H.remove e.locals i.v;
    H.insert e.locals i.v (j, t, true);
    Some (Inl t)
  | None ->
    match H.try_find e.globals.ge_h i.v with
    | Some d -> Some (Inr d)
    | None -> None

let lookup (e:env) (i:ident) : ML (either typ (decl & either decl_attributes macro_signature)) =
  match try_lookup e i with
  | None -> error (Printf.sprintf "Variable %s not found" (ident_to_string i)) i.range
  | Some v -> v
  
let remove_local (e:env) (i:ident) : ML unit =
  match H.try_find e.locals i.v with
  | Some (j, _, _) ->
    H.remove e.locals i.v;
    H.remove e.locals j
  | _ -> ()

let resolve_record_case_output_extern_type_name (env:env) (i:ident) =
  match H.try_find (global_env_of_env env).ge_out_t i.v with
  | Some ({d_decl={v=OutputType ({out_typ_names=names})}}) -> names.typedef_abbrev
  | _ ->
    (match H.try_find (global_env_of_env env).ge_extern_t i.v with
     | Some ({d_decl={v=ExternType td_names}}) -> td_names.typedef_abbrev
     | _ ->
       (match lookup env i with
        | Inr ({d_decl={v=Record names _ _ _}}, _)
        | Inr ({d_decl={v=CaseType names _ _}}, _) ->
          names.typedef_name
        | _ -> i))

let lookup_expr_name (e:env) (i:ident) : ML typ =
  match lookup e i with
  | Inl t -> t
  | Inr (_, Inr ({ macro_arguments_t=[]; macro_result_t=t })) -> t
  | Inr _ ->
    error (Printf.sprintf "Variable %s is not an expression identifier" (ident_to_string i)) i.range

let lookup_macro_name (e:env) (i:ident) : ML macro_signature =
  match lookup e i with
  | Inr (_, Inr m) -> m
  | _ -> error (Printf.sprintf "%s is an unknown operator" (ident_to_string i)) i.range

let lookup_macro_definition (e:env) (i:ident) =
  try
    let m = lookup_macro_name e i in
    m.macro_defn_t
  with
  | _ -> None

let try_lookup_enum_cases (e:env) (i:ident)
  : ML (option (list ident & typ))
  = match lookup e i with
    | Inr ({d_decl={v=Enum t _ tags}}, _) ->
      Some (Desugar.check_desugared_enum_cases tags, t)
    | _ -> None

let lookup_enum_cases (e:env) (i:ident)
  : ML (list ident & typ)
  = match try_lookup_enum_cases e i with
    | Some (tags, t) -> tags, t
    | _ -> error (Printf.sprintf "Type %s is not an enumeration" (ident_to_string i)) i.range

let is_enum (e:env) (t:typ) =
  match t.v with
  | Type_app i KindSpec [] ->
    Some? (try_lookup_enum_cases e i)
  | _ -> false

let is_used (e:env) (i:ident) : ML bool =
  match H.try_find e.locals i.v with
  | Some (_, t, b) -> b
  | _ ->  error (Printf.sprintf "Variable %s not found" (ident_to_string i)) i.range

let type_of_integer_type = function
  | UInt8  -> tuint8
  | UInt16 -> tuint16
  | UInt32 -> tuint32
  | UInt64 -> tuint64

let check_integer_bounds t i =
    match t with
    | UInt8  -> FStar.UInt.fits i 8
    | UInt16 -> FStar.UInt.fits i 16
    | UInt32 -> FStar.UInt.fits i 32
    | UInt64 -> FStar.UInt.fits i 64

let type_of_constant rng (c:constant) : ML typ =
  match c with
  | Unit -> tunit
  | Int tag i ->
    if check_integer_bounds tag i
    then type_of_integer_type tag
    else error (Printf.sprintf "Constant %d is too large for its type %s" i (Ast.print_integer_type tag)) rng
  | XInt tag _ -> //bounds checked by the syntax
    type_of_integer_type tag
  | Bool _ -> tbool


let parser_may_fail (env:env) (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> true
  | Type_app hd _ _ ->
    match lookup env hd with
    | Inr (d, Inl attrs) -> attrs.may_fail
    | _ -> false

let typ_is_integral env (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> false
  | Type_app hd _ _ ->
    match lookup env hd with
    | Inr (d, Inl attrs) -> Some? attrs.integral
    | _ -> false

let tag_of_integral_typ env (t:typ) : ML (option _) =
  match t.v with
  | Pointer _ -> None
  | Type_app hd _ _ ->
    match lookup env hd with
    | Inr (_, Inl attrs) -> attrs.integral
    | _ -> None

let tag_and_bit_order_of_integral_typ env (t:typ) : ML (tag_and_bit_order: (option integer_type & option bitfield_bit_order) { Some? (snd tag_and_bit_order) ==> Some? (fst tag_and_bit_order) }) =
  match t.v with
  | Pointer _ -> None, None
  | Type_app hd _ _ ->
    match lookup env hd with
    | Inr (_, Inl attrs) -> attrs.integral, attrs.bit_order
    | _ -> None, None

let has_reader (env:global_env) (id:ident) : ML bool =
  match H.try_find env.ge_h id.v with
  | Some (_, Inl attrs) -> attrs.has_reader
  | _ -> false

let parser_kind_nz (env:global_env) (id:ident) : ML (option bool) =
  match H.try_find env.ge_h id.v with
  | Some (_, Inl attrs) -> attrs.parser_kind_nz
  | _ -> None

let parser_weak_kind (env:global_env) (id:ident) : ML (option _) =
  match H.try_find env.ge_h id.v with
  | Some (_, Inl attrs) -> Some attrs.parser_weak_kind
  | _ -> None

let rec typ_weak_kind env (t:typ) : ML (option weak_kind) =
  match t.v with
  | Pointer _ -> typ_weak_kind env tuint64
  | Type_app hd _ _ -> parser_weak_kind env.globals hd

let typ_has_reader env (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> false
  | Type_app hd _ _ ->
    has_reader env.globals hd

let rec unfold_typ_abbrev_only (env:env) (t:typ) : ML typ =
  match t.v with
  | Type_app hd _ [] -> //type abbreviations are not parameterized
    begin
    match try_lookup env hd with
    | Some (Inr (d, _)) ->
      begin
      match d.d_decl.v with
      | TypeAbbrev t _ -> unfold_typ_abbrev_only env t
      | _ -> t
      end
    | _ -> t
    end
  | _ -> t

let update_typ_abbrev (env:env) (i:ident) (t:typ) 
  : ML unit
  = match H.try_find env.globals.ge_h i.v with
    | Some (d, ms) ->
      let d_decl =
        match d.d_decl.v with
        | TypeAbbrev _ _ -> {d.d_decl with v = TypeAbbrev t i }
        | _ -> failwith "Expected a type abbreviation"
      in
      let d = {d with d_decl = d_decl } in
      let entry = (d, ms) in
      H.insert env.globals.ge_h i.v entry
      
   | _ -> 
     failwith "Type abbreviation not found"

let rec unfold_typ_abbrev_and_enum (env:env) (t:typ) : ML typ =
  match t.v with
  | Type_app hd _ [] -> //type abbreviations are not parameterized
    begin
    match lookup env hd with
    | Inr (d, _) ->
      begin
      match d.d_decl.v with
      | TypeAbbrev t _ -> unfold_typ_abbrev_and_enum env t
      | Enum t _ _ -> unfold_typ_abbrev_and_enum env t
      | _ -> t
      end
    | _ -> t
    end
  | _ -> t

let size_of_integral_typ (env:env) (t:typ) r
  : ML int
  = let t = unfold_typ_abbrev_and_enum env t in
    if not (typ_is_integral env t)
    then error (Printf.sprintf "Expected and integral type, got %s"
                                                (print_typ t))
               r;
    match tag_of_integral_typ env t with
    | None -> failwith "Impossible"
    | Some UInt8 -> 1
    | Some UInt16 -> 2
    | Some UInt32 -> 4
    | Some UInt64 -> 8

let bit_order_of_integral_typ (env:env) (t:typ) r
  : ML bitfield_bit_order
  = let t = unfold_typ_abbrev_and_enum env t in
    if not (typ_is_integral env t)
    then error (Printf.sprintf "Expected and integral type, got %s"
                                                (print_typ t))
               r;
    match tag_and_bit_order_of_integral_typ env t with
    | _, None -> failwith "Impossible"
    | _, Some order -> order

let eq_typ env t1 t2 =
  if Ast.eq_typ t1 t2 then true
  else Ast.eq_typ (unfold_typ_abbrev_and_enum env t1) (unfold_typ_abbrev_and_enum env t2)

let eq_typs env ts =
  List.for_all (fun (t1, t2) -> eq_typ env t1 t2) ts

let cast e t t' = { e with v = App (Cast (Some t) t') [e] }

let try_cast_integer env et to : ML (option expr) =
  let e, from = et in
  let i_to = typ_is_integral env to in
  let i_from = typ_is_integral env from in
  if i_from && i_to
  then
    let i_from = typ_as_integer_type (unfold_typ_abbrev_and_enum env from) in
    let i_to = typ_as_integer_type (unfold_typ_abbrev_and_enum env to) in
    if i_from = i_to
    then Some e
    else if integer_type_leq i_from i_to
    then Some (cast e i_from i_to)
    else None
  else None

let _or_ b1 b2 = b1 || b2
let _and_ b1 b2 = b1 && b2
let try_retype_arith_exprs (env:env) e1 e2 rng : ML (option (expr & expr & typ))=
  let e1, t1 = e1 in
  let e2, t2 = e2 in
  let fail #a i : ML a  = raise (Error (Printf.sprintf "(%d) Failed to retype exprs (%s : %s) and (%s : %s)"
                                                        i
                                                        (print_expr e1)
                                                        (print_typ t1)
                                                        (print_expr e2)
                                                        (print_typ t2))) in
  try
    let t1, t2 = unfold_typ_abbrev_and_enum env t1, unfold_typ_abbrev_and_enum env t2 in
    if not (typ_is_integral env t1 `_and_`
            typ_is_integral env t2)
    then fail 1;
    let tt1 = typ_as_integer_type t1 in
    let tt2 = typ_as_integer_type t2 in
    let cast e t t' = { e with v = App (Cast (Some t) t') [e] } in
    let e1, e2, t =
      if integer_type_leq tt1 tt2
      then cast e1 tt1 tt2,
           e2,
           t2
      else if integer_type_leq tt2 tt1
      then e1,
           cast e2 tt2 tt1,
           t1
      else fail 0
    in
    // FStar.IO.print_string
    //   (Printf.sprintf "Retyped to (%s, %s, %s)\n"
    //     (print_expr e1)
    //     (print_expr e2)
    //     (print_typ t));
    Some (e1, e2, t)
  with
    | Error msg ->
      FStar.IO.print_string msg;
      None
    | _ -> None

(*
 * Add output type to the environment
 *
 * TODO: check_shadow
 *)
let add_output_type (ge:global_env) (i:ident) (d:decl{OutputType? d.d_decl.v}) : ML unit =
  let insert i = H.insert ge.ge_out_t i d in
  insert i.v;
  let td_abbrev = (OutputType?._0 d.d_decl.v).out_typ_names.typedef_abbrev in
  insert td_abbrev.v

(*
 * Add extern type to the environment
 *
 * TODO: check shadow
 *)
let add_extern_type (ge:global_env) (i:ident) (d:decl{ExternType? d.d_decl.v}) : ML unit =
  let insert i = H.insert ge.ge_extern_t i d in
  insert i.v;
  let td_abbrev = (ExternType?._0 d.d_decl.v).typedef_abbrev in
  insert td_abbrev.v

(*
 * Add extern probe function to the environment
 *
 * TODO: check shadow
 *)
let add_extern_probe (ge:global_env) (i:ident) (d:decl{ExternProbe? d.d_decl.v}) : ML unit =
  H.insert ge.ge_probe_fn i.v d


(*
 * Add extern function to the environment
 *
 * TODO: check shadow
 *)
let add_extern_fn (ge:global_env) (i:ident) (d:decl{ExternFn? d.d_decl.v}) : ML unit =
  H.insert ge.ge_extern_fn i.v d

let lookup_output_type (ge:global_env) (i:ident) : ML out_typ =
  match H.try_find ge.ge_out_t i.v with
  | Some ({d_decl={v=OutputType out_t}}) -> out_t
  | _ -> error (Printf.sprintf "Cannot find output type %s" (ident_to_string i)) i.range

(*
 * Returns the type of the field, with optional bitwidth if the field is a bitfield
 *)
let lookup_output_type_field (ge:global_env) (i f:ident) : ML (typ & option int) =
  let out_t = lookup_output_type ge i in
  let rec find (flds:list out_field) : (option (typ & option int)) =
    match flds with
    | [] -> None
    | (Out_field_named f' t n)::tl ->
      if eq_idents f f' then Some (t, n)
      else find tl
    | (Out_field_anon l _)::tl ->
      (match find l with
       | None -> find tl
       | Some t -> Some t) in
  match find out_t.out_typ_fields with
  | Some t -> t
  | None ->
    error (Printf.sprintf "Cannot find output field %s:%s" (ident_to_string i) (ident_to_string f)) f.range

let lookup_extern_type (ge:global_env) (i:ident) : ML unit =
  match H.try_find ge.ge_extern_t i.v with
  | Some ({d_decl={v=ExternType _}}) -> ()
  | _ -> error (Printf.sprintf "Cannot find declaration for extern type %s" (ident_to_string i)) i.range

let lookup_extern_fn (ge:global_env) (f:ident) : ML (typ & list param) =
  match H.try_find ge.ge_extern_fn f.v with
  | Some ({d_decl={v=ExternFn _ ret ps}}) -> ret, ps
  | _ -> error (Printf.sprintf "Cannot find declaration for extern function %s" (ident_to_string f)) f.range

let check_output_type (ge:global_env) (t:typ) : ML ident =
  let err () : ML ident =
    error (Printf.sprintf "Type %s is not an output type" (print_typ t)) t.range in
  match t.v with
  | Type_app i KindOutput [] -> i
  | _ -> err ()


/// Populated the output expression metadata
///
/// We enforce that the spec cannot take address of output type bitfields

let rec check_out_expr (env:env) (oe0:out_expr)
  : ML (oe:out_expr{Some? oe.out_expr_meta}) =
  
  match oe0.out_expr_node.v with
  | OE_id i ->
    let t = lookup_expr_name env i in
    {oe0 with
     out_expr_meta = Some ({
       out_expr_base_t = t;
       out_expr_t = t;
       out_expr_bit_width = None})}
  | OE_star oe ->
    let oe = check_out_expr env oe in
    let { out_expr_base_t = oe_bt;
          out_expr_t = oe_t;
          out_expr_bit_width = bopt } = Some?.v oe.out_expr_meta in
    (match oe_t.v, bopt with
     | Pointer t, None ->
       {oe0 with
        out_expr_node={oe0.out_expr_node with v=OE_star oe};
        out_expr_meta=Some ({ out_expr_base_t = oe_bt;
                              out_expr_t = t;
                              out_expr_bit_width = None })}
     | _ ->
       error
         (Printf.sprintf "Output expression %s is ill-typed since base type %s is not a pointer type"
           (print_out_expr oe0) (print_typ oe_t)) oe.out_expr_node.range)
  | OE_addrof oe ->
    let oe = check_out_expr env oe in
    let { out_expr_base_t = oe_bt;
          out_expr_t = oe_t;
          out_expr_bit_width = bopt } = Some?.v oe.out_expr_meta in
    (match bopt with
     | None ->
       {oe0 with
        out_expr_node={oe0.out_expr_node with v=OE_addrof oe};

        out_expr_meta=Some ({
          out_expr_base_t = oe_bt;
          out_expr_t = with_range (Pointer oe_t) oe.out_expr_node.range;
          out_expr_bit_width = None })}
     | _ ->
       error
         (Printf.sprintf "Cannot take address of a bit field %s"
           (print_out_expr oe0)) oe.out_expr_node.range)
  | OE_deref oe f ->
    let oe = check_out_expr env oe in
    let { out_expr_base_t = oe_bt;
          out_expr_t = oe_t;
          out_expr_bit_width = bopt }  = Some?.v oe.out_expr_meta in
    (match oe_t.v, bopt with
     | Pointer t, None ->
       let i = check_output_type (global_env_of_env env) t in
       let out_expr_t, out_expr_bit_width = lookup_output_type_field
         (global_env_of_env env)
         i f in
       {oe0 with
        out_expr_node={oe0.out_expr_node with v=OE_deref oe f};
        out_expr_meta=Some ({
          out_expr_base_t = oe_bt;
          out_expr_t = out_expr_t;
          out_expr_bit_width = out_expr_bit_width})}
     | _ -> 
       error
         (Printf.sprintf "Output expression %s is ill-typed since base type %s is not a pointer type"
           (print_out_expr oe0) (print_typ oe_t)) oe.out_expr_node.range)
  | OE_dot oe f ->
    let oe = check_out_expr env oe in
    let { out_expr_base_t = oe_bt;
          out_expr_t = oe_t;
          out_expr_bit_width = bopt } = Some?.v oe.out_expr_meta in
    (match bopt with
     | None ->
       let i = check_output_type (global_env_of_env env) oe_t in
       let out_expr_t, out_expr_bit_width = lookup_output_type_field
         (global_env_of_env env)
         i f in
       {oe0 with
        out_expr_node={oe0.out_expr_node with v=OE_dot oe f};
        out_expr_meta=Some ({
          out_expr_base_t = oe_bt;
          out_expr_t = out_expr_t;
          out_expr_bit_width = out_expr_bit_width})}
     | _ ->
       error
         (Printf.sprintf "Cannot take address of a bit field %s"
           (print_out_expr oe0)) oe.out_expr_node.range)

let range_of_typ_param (p:typ_param) = match p with
  | Inl e -> e.range
  | Inr p -> p.out_expr_node.range

#push-options "--z3rlimit_factor 4"
let rec check_typ (pointer_ok:bool) (env:env) (t:typ)
  : ML typ
  = match t.v with
    | Pointer t0 ->
      if pointer_ok
      then { t with v = Pointer (check_typ pointer_ok env t0) }
      else error (Printf.sprintf "Pointer types are not permissible here; got %s" (print_typ t)) t.range

    | Type_app s KindSpec ps ->
      (match lookup env s with
       | Inl _ ->
         error (Printf.sprintf "%s is not a type" (ident_to_string s)) s.range

       | Inr (d, _) ->
         let params = params_of_decl d in
         if List.length params <> List.length ps
         then error (Printf.sprintf "Not enough arguments to %s" (ident_to_string s)) s.range;
         let ps =
           List.map2 (fun (t, _, _) p ->
             let p, t' = check_typ_param env p in
             if not (eq_typ env t t')
             then begin
               match p with
               | Inl e -> (match try_cast_integer env (e, t') t with
                          | Some e -> Inl e
                          | _ -> error "Argument type mismatch after trying integer cast" (range_of_typ_param p))
               | _ ->
                 error (Printf.sprintf
                          "Argument type mismatch (%s vs %s)"
                          (Ast.print_typ t) (Ast.print_typ t')) (range_of_typ_param p)
             end
             else p)
             params
             ps
         in
         {t with v = Type_app s KindSpec ps})

    | Type_app i KindExtern args ->
      if List.length args <> 0
      then error (Printf.sprintf "Cannot apply the extern type %s" (ident_to_string i)) i.range
      else t

    | Type_app _ KindOutput _ ->
      error "Impossible, check_typ is not supposed to typecheck output types!" t.range

and check_ident (env:env) (i:ident)
  : ML (ident & typ)
  = let t = lookup_expr_name env i in
    i, t

and check_expr (env:env) (e:expr)
  : ML (expr & typ)
  = let w e' = with_range e' e.range in
    let arith_op_t op t : ML Ast.op =
      let t = tag_of_integral_typ env t in
      match op with
      | Plus _ -> Plus t
      | Minus _ -> Minus t
      | Mul _ -> Mul t
      | Division _ -> Division t
      | Remainder _ -> Remainder t
      | BitwiseNot _ -> BitwiseNot t
      | BitwiseAnd _ -> BitwiseAnd t
      | BitwiseOr _ -> BitwiseOr t
      | BitwiseXor _ -> BitwiseXor t
      | ShiftLeft _ -> ShiftLeft t
      | ShiftRight _ -> ShiftRight t
      | LE _ -> LE t
      | LT _ -> LT t
      | GE _ -> GE t
      | GT _ -> GT t
      | _ -> op
    in
    match e.v with
    | Constant c ->
      e, type_of_constant e.range c

    | Identifier i ->
      let i, t = check_ident env i in
      { e with v = Identifier i }, t

    | Static _ -> 
      failwith "Static expressions should have been desugared already"
      
    | This ->
      error "`this` is not a valid expression" e.range

    | App (Cast _ to) [n] ->
      let n, from = check_expr env n in
      begin
      if not (typ_is_integral env from)
      then error (Printf.sprintf "Casts are only supported on integral types; %s is not integral"
                    (print_typ from)) e.range
      else match from.v with
           | Type_app i KindSpec _ ->
             let from_t = as_integer_typ i in
             // if integer_type_lub to from_t <> to
             // then error (Printf.sprintf "Only widening casts are supported; casting %s to %s loses precision"
             //                    (print_typ from)
             //                    (print_integer_type to))
             //            e.range
             // else
             let e = {e with v = App (Cast (Some from_t) to) [n]} in
             let t = type_of_integer_type to in
             Options.debug_print_string
               (Printf.sprintf "--------------- %s has type %s\n" (print_expr e) (print_typ t));
             e, t
           | _ -> failwith "Impossible: must be an integral type"
      end

    | App SizeOf [{v=This;range=r}] ->
      let e =
        match env.this with
        | None ->
          error "`this` is not in scope" r
        | Some i ->
          with_range (App SizeOf [with_range (Identifier i) r]) e.range
      in
      e, tuint32

    | App SizeOf [{v=Identifier i;range=r}] ->
      begin
      match lookup env i with
      | Inr ({d_decl={v=Enum _ _ _}}, _)
      | Inr ({d_decl={v=Record _ _ _ _ }}, _)
      | Inr ({d_decl={v=CaseType _ _ _}}, _)
      | Inr (_, Inl _) ->  //has decl-attributes
        e, tuint32
      | _ ->
        error "`sizeof` applied to a non-sized-typed" r
      end

    | App (Ext s) es ->
      //TODO: AR: not sure about this Ext node
      let m = lookup_macro_name env (with_range (to_ident' s) e.range) in
      let n_formals = List.length m.macro_arguments_t in
      let n_actuals = List.length es in
      if n_formals <> n_actuals
      then error (Printf.sprintf "%s expects %d arguments; got %d" s n_formals n_actuals) e.range;
      let check_arg e t : ML expr =
        let e, t' = check_expr env e in
        if not (eq_typ env t t')
        then error
               (Printf.sprintf
                  "%s expected argument of type %s; \
                  got argument %s of type %s"
                  s (print_typ t) (print_expr e) (print_typ t))
               e.range;
        e
      in
      let es = List.map2 check_arg es m.macro_arguments_t in
      with_range (App (Ext s) es) e.range,
      m.macro_result_t

    | App op es ->
      let ets = List.map (check_expr env) es in
      match ets with
      | [(e1, t1)] ->
        begin
        match op with
        | Not ->
          if not (eq_typ env t1 tbool)
          then error "Expected bool" e1.range;
          w (App Not [e1]), t1

        | BitwiseNot _ ->
          if typ_is_integral env t1
          then w (App (arith_op_t op t1) [e1]), t1
          else error (Printf.sprintf "Bitwise negation is only available on integral types; got %s"
                                     (print_typ t1))
                     e1.range
        | _ ->
          error "Not a unary op" e1.range
        end

      | [(e1,t1);(e2,t2)] ->
        begin
        match op with
        | Eq
        | Neq ->
          if not (eq_typ env t1 t2)
          then
          begin
            let err #a () : ML a =
                error
                     (Printf.sprintf "Equality on unequal types: %s and %s"
                       (print_typ t1)
                       (print_typ t2))
                     e.range
            in
            let it1 = typ_is_integral env t1 in
            let it2 = typ_is_integral env t2 in
            if it1 && it2
            then match try_retype_arith_exprs env (e1, t1) (e2, t2) e.range with
                 | Some (e1, e2, t) -> w (App op [e1; e2]), tbool
                 | _ -> err ()

            else err ()
          end
          else
            w (App op [e1; e2]), tbool

        | And
        | Or ->
          if not (eq_typs env [(t1,tbool); (t2,tbool)])
          then error "Binary boolean op on non booleans" e.range;
          w (App op [e1; e2]), tbool

        | ShiftLeft _
        | ShiftRight _ ->
          let t1_integral = typ_is_integral env t1 in
          let t2_integral = typ_is_integral env t2 in
          if not t1_integral || not t2_integral
          then error (Printf.sprintf "Bit shifts are only permissible on integral types: got %s and %s"
                                     (print_typ t1)
                                     (print_typ t2))
                     e.range;
          begin
          match try_cast_integer env (e2, t2) tuint32 with
          | None ->
            error (Printf.sprintf "Bit shift offset is too large: got type %s"
                                     (print_typ t2))
                  e2.range

          | Some e2 ->
            w (App (arith_op_t op t1) [e1; e2]), t1
          end

        | Plus _
        | Minus _
        | Mul _
        | Division _
        | Remainder _
        | LT _
        | GT _
        | LE _
        | GE _
        | BitwiseAnd _
        | BitwiseOr _
        | BitwiseXor _ ->
          let result_typ t =
              match op with
              | LT _ | GT _ | LE _ | GE _ -> tbool
              | _ -> t
          in
          let t1_integral = typ_is_integral env t1 in
          let t2_integral = typ_is_integral env t2 in
          if not t1_integral || not t2_integral
          then error (Printf.sprintf "Binary integer op on non-integral types: %s and %s"
                                     (print_typ t1)
                                     (print_typ t2))
               e.range;


          if not (eq_typs env [(t1,t2)])
          then match try_retype_arith_exprs env (e1, t1) (e2, t2) e.range with
               | Some (e1, e2, t) ->
                 w (App (arith_op_t op t) [e1; e2]), result_typ t

               | _ ->
                 error (Printf.sprintf "Binary integer operator (%s) on non-equal types: %s and %s"
                                     (print_expr e)
                                     (print_typ t1)
                                     (print_typ t2))
                     e.range
          else w (App (arith_op_t op t1) [e1; e2]), result_typ t1

        | _ ->
          error "Not a binary op" e.range
        end

      | [(e1, t1); (e2, t2); (e3, t3)] ->
        begin
        match op with
        | IfThenElse ->
          if not (eq_typ env t1 tbool)
          then error (Printf.sprintf "If-then-else expects a boolean guard, got %s" (print_typ t1))
                     e1.range;
          if not (eq_typ env t2 t3)
          then match try_retype_arith_exprs env (e2, t2) (e3, t3) e.range with
               | Some (e2, e3, t) ->
                 w (App IfThenElse [e1;e2;e3]), t
               | None ->
                 error (Printf.sprintf "then- and else-branch do not have the same type: got %s and %s"
                                       (print_typ t2)
                                       (print_typ t3))
                       e.range
          else
            w (App IfThenElse [e1;e2;e3]), t2

        | BitFieldOf n order ->
          let base_size = size_of_integral_typ env t1 e1.range in
          let size = 8 * base_size in
          if n <> size
          then error
                 (Printf.sprintf "BitFieldOf size %d is not equal to %d, i.e., the bit size %s"
                   n size (print_expr e1))
                 e1.range;
          begin
          match e2.v, e3.v with
          | Constant (Int UInt32 from), (Constant (Int UInt32 to)) ->
            if not
               (from <= size
            && from <= to
            && to <= size)
            then error "bitfield-of expresssions is out of bounds" e.range;
            w (App (BitFieldOf n order) [e1; e2; e3]), t1
          | _ ->
           error "bitfield-of with non-32-bit-consant indices" e.range
          end

        | _ ->
          error "Unexpected arity" e.range
        end
      | _ -> error "Unexpected arity" e.range

and check_typ_param (env:env) (p:typ_param) : ML (typ_param & typ) =
  match p with
  | Inl e ->
    let e, t = check_expr env e in
    Inl e, t
  | Inr o ->
    let o = check_out_expr env o in
    let { out_expr_t = t;
          out_expr_bit_width = bopt } = Some?.v o.out_expr_meta in
    (match bopt with
     | None ->
       Inr o, t
     | _ ->
       error ("Type parameter cannot be a bitfield") (range_of_typ_param p))

#pop-options
#push-options "--z3rlimit_factor 3"

let rec check_field_action (env:env) (f:atomic_field) (a:action)
  : ML (action & typ)
  = let check_atomic_action env (r:range) (a:atomic_action)
      : ML (atomic_action & typ)
      = match a with
        | Action_return e ->
          let e, t = check_expr env e in
          Action_return e, t

        | Action_abort ->
          Action_abort, tunit

        | Action_field_pos_64 ->
          Action_field_pos_64, tuint64

        | Action_field_pos_32 ->
          Action_field_pos_32, tuint32

        | Action_field_ptr ->
          Action_field_ptr, puint8

        | Action_field_ptr_after e write_to ->
          let e, t = check_expr env e in
          if not (eq_typ env t tuint64)
          then
            error (Printf.sprintf "Argument type mismatch, expected %s whereas %s has type %s"
              (Ast.print_typ tuint64)
              (Ast.print_expr e)
              (Ast.print_typ t)) e.range
          else
            let write_to = check_out_expr env write_to in
            let { out_expr_t = et } = Some?.v write_to.out_expr_meta in
            if not (eq_typ env et puint8)
            then
              error (Printf.sprintf "Pointee type mismatch, expected %s whereas %s points to %s"
                (Ast.print_typ puint8)
                (Ast.print_out_expr write_to)
                (Ast.print_typ et)) write_to.out_expr_node.range
            else
              Action_field_ptr_after e write_to, tbool

        | Action_deref i ->
          let t = lookup_expr_name env i in
          begin
          match t.v with
          | Pointer t -> Action_deref i, t
          | _ -> error "Dereferencing a non-pointer" i.range
          end

        | Action_assignment lhs rhs ->
          let lhs = check_out_expr env lhs in
          let { out_expr_t = t } = Some?.v lhs.out_expr_meta in
          let rhs, t' = check_expr env rhs in
          let def_ret = Action_assignment lhs rhs, tunit in
          if not (eq_typ env t t')
          then begin
            match try_cast_integer env (rhs, t') t with
            | Some rhs ->
              Action_assignment lhs rhs, tunit
            | None ->
              warning (Printf.sprintf
                        "Assigning to %s of type %s a value of incompatible type %s"
                        (print_out_expr lhs)
                        (print_typ t)
                        (print_typ t'))
                     rhs.range;
              def_ret
           end
           else def_ret

        | Action_call f args ->
          let ret_t, params = lookup_extern_fn (global_env_of_env env) f in
          if List.length params <> List.length args
          then error (Printf.sprintf "Insufficient arguments to extern function %s" (ident_to_string f)) f.range
          else let args = List.map2 (fun (t, _, _) arg ->
                 let arg, t_arg = check_expr env arg in
                 if not (eq_typ env t t_arg)
                 then error (Printf.sprintf "Argument type mismatch, expected %s whereas %s has type %s"
                               (Ast.print_typ t)
                               (Ast.print_expr arg)
                               (Ast.print_typ t_arg)) arg.range
                 else arg) params args in
               Action_call f args, ret_t
    in
    match a.v with
    | Atomic_action aa ->
      let aa, t = check_atomic_action env a.range aa in
      { a with v=Atomic_action aa }, t

    | Action_seq a0 rest ->
      let a0, _ = check_atomic_action env a.range a0 in
      let rest, t = check_field_action env f rest in
      { a with v=Action_seq a0 rest }, t

    | Action_ite hd then_ else_ ->
      let hd, t = check_expr env hd in
      if not (eq_typ env t tbool)
      then error (Printf.sprintf
                      "Branching is only permitted on boolean expressions, %s has type %s"
                        (print_expr hd)
                        (print_typ t))
                 hd.range;
      let then_, t = check_field_action env f then_ in
      let else_, t' =
        match else_ with
        | None -> None, tunit
        | Some else_ ->
          let else_, t = check_field_action env f else_ in
          Some else_, t
      in
      let branches_eq_t = eq_typ env t t' in
      let eq_t_unit = eq_typ env t tunit in
      if not branches_eq_t
      || (None? else_ && not eq_t_unit)
      then error (Printf.sprintf "The branches of a conditional must both have the same type; got %s and %s"
                                 (print_typ t)
                                 (print_typ t'))
                a.range;
      { a with v = Action_ite hd then_ else_ }, t

    | Action_let i aa k ->
      let aa, t = check_atomic_action env a.range aa in
      add_local env i t;
      let k, t = check_field_action env f k in
      remove_local env i;
      { a with v = Action_let i aa k }, t

    | Action_act a ->
      let a, t = check_field_action env f a in
      if eq_typ env t tunit
      then { a with v = Action_act a }, tbool
      else error (Printf.sprintf "This ':act' action returns %s instead of unit"
                                     (print_typ t))
                 a.range

#pop-options

#push-options "--z3rlimit_factor 4"
let check_atomic_field (env:env) (extend_scope: bool) (f:atomic_field)
  : ML atomic_field
  = let sf = f.v in
    let sf_field_type = check_typ (Some? sf.field_probe) env sf.field_type in
    let check_annot (e: expr) : ML expr =
        let e, t = check_expr env e in
        if not (eq_typ env t tuint32)
        then match try_cast_integer env (e, t) tuint32 with
             | Some e -> e
             | _ ->  error (Printf.sprintf "Array expression %s has type %s instead of UInt32"
                          (print_expr e)
                          (print_typ t))
                    e.range
        else e
    in
    let fa = match sf.field_array_opt with
    | FieldScalar -> FieldScalar
    | FieldArrayQualified (e, b) -> FieldArrayQualified (check_annot e, b)
    | FieldString sz -> FieldString (map_opt check_annot sz)
    | FieldConsumeAll ->
      if
        if eq_typ env sf.field_type tuint8
        then true
        else eq_typ env sf.field_type tuint8be
      then FieldConsumeAll
      else error (Printf.sprintf "This ':consume-all field returns %s instead of UINT8 or UINT8BE" (print_typ sf.field_type)) f.range
    in
    let fc = sf.field_constraint |> map_opt (fun e ->
        add_local env sf.field_ident sf.field_type;
        let e = fst (check_expr env e) in
        remove_local env sf.field_ident;
        e)
    in
    let f_act = sf.field_action |> map_opt (fun (a, _) ->
        add_local env sf.field_ident sf.field_type;
        let a, _ = check_field_action env f a in
        let dependent = is_used env sf.field_ident in
        remove_local env sf.field_ident;
        a, dependent)
    in
    let f_probe =
      match sf.field_probe with
      | None -> None
      | Some p ->
        let length, typ = check_expr env p.probe_length in
        let length =
          if not (eq_typ env typ tuint64)
          then match try_cast_integer env (length, typ) tuint64 with
              | Some e -> e
              | _ -> error (Printf.sprintf "Probe length expression %s has type %s instead of UInt64"
                            (print_expr length)
                            (print_typ typ))
                            length.range
          else length
        in
        let dest, dest_typ = check_ident env p.probe_dest in
        if not (eq_typ env dest_typ tcopybuffer)
        then error (Printf.sprintf "Probe destination expression %s has type %s instead of EVERPARSE_COPY_BUFFER_T"
                            (print_ident dest)
                            (print_typ dest_typ))
                            dest.range;
        let probe_fn =
          match p.probe_fn with
          | None -> (
            match GlobalEnv.default_probe_fn env.globals with
            | None -> 
              error (Printf.sprintf "Probe function not specified and no default probe function found")
                    p.probe_length.range
            | Some i -> i
          )
          | Some p -> (
            match GlobalEnv.resolve_probe_fn env.globals p with
            | None -> 
              error (Printf.sprintf "Probe function %s not found" (print_ident p))
                    p.range
            | Some i -> 
              i
          )
        in
        Some { probe_fn=Some probe_fn; probe_length=length; probe_dest=dest }
    in        
    if extend_scope then add_local env sf.field_ident sf.field_type;
    let sf = {
        sf with
        field_type = sf_field_type;
        field_array_opt = fa;
        field_constraint = fc;
        field_action = f_act;
        field_probe = f_probe;
    } in
    let _ = 
      match sf.field_type.v, sf.field_array_opt,
            sf.field_constraint, sf.field_bitwidth,
            sf.field_action, sf.field_probe
      with
      | Pointer _, FieldScalar,
        None, None,
        None, Some _ ->
        ()
      | _, _,
        _, _,
        _, Some _ ->
        error (Printf.sprintf "Probe annotation is only allowed on pointer fields with no other constraints")
              f.range
      | _ -> ()
    in
    Options.debug_print_string
      (Printf.sprintf "Field %s has comments <%s>\n"
                  (print_ident sf.field_ident)
                  (String.concat "\n" f.comments));
    { f with v = sf }

let is_strong_prefix_field_array (a: field_array_t) : Tot bool =
  not (FieldScalar? a)

let weak_kind_of_atomic_field (env: env) (f: atomic_field) : ML weak_kind =
  if is_strong_prefix_field_array f.v.field_array_opt
  then WeakKindStrongPrefix
  else match typ_weak_kind env f.v.field_type with
  | Some e -> e
  | None -> failwith (Printf.sprintf "cannot find the weak kind of field %s : %s" (print_ident f.v.field_ident) (print_typ f.v.field_type))

let weak_kind_of_list (wa:'a -> ML weak_kind) (xs:list 'a) : ML weak_kind =
  let k =
    List.fold_left 
      (fun out f -> 
        let fk = wa f in
        match out with
        | None -> Some fk
        | Some o -> Some (weak_kind_glb o fk))
      None
      xs
  in
  match k with
  | None -> WeakKindWeak
  | Some k -> k

let rec weak_kind_of_field (env: env) (f: field) : ML weak_kind =
  match f.v with
  | AtomicField f -> weak_kind_of_atomic_field env f
  | RecordField f _ -> weak_kind_of_record env f
  | SwitchCaseField f _ -> weak_kind_of_switch_case env f

and weak_kind_of_record env (fs:record) : ML weak_kind =
  match fs with
  | [] -> WeakKindStrongPrefix
  | [a] -> weak_kind_of_field env a
  | a :: q ->
    let wk = weak_kind_of_field env a in
    if wk <> WeakKindStrongPrefix
    then failwith
          (Printf.sprintf "weak_kind_of_fields: \
                           field %s should be of strong kind \
                           instead of %s"
                           (print_field a)
                           (print_weak_kind wk))
    else weak_kind_of_record env q

and weak_kind_of_switch_case env (s:switch_case) : ML weak_kind =
  let _, cases = s in
  weak_kind_of_list (weak_kind_of_case env) cases
  
and weak_kind_of_case (env: env) (c: case) : ML weak_kind =
  match c with
  | DefaultCase f
  | Case _ f -> weak_kind_of_field env f

#pop-options

let check_field_t = env -> field -> ML field

#push-options "--z3rlimit_factor 8"
let check_switch (check_field:check_field_t) (env:env) (s:switch_case)
  : ML switch_case
  = let head, cases = s in
    let head, scrutinee_t = check_expr env head in
    let fail_non_equality_type (#a:Type) ()  : ML (option a) =
        let integral = typ_is_integral env scrutinee_t in
        let is_bool = eq_typ env scrutinee_t tbool in
        if not integral
        && not is_bool
        then error (Printf.sprintf "Case analysis of a non-integral or non-boolean type (%s) is not supported"
                                     (print_typ scrutinee_t))
                     head.range;
        None
    in
    let tags_t_opt =
      match scrutinee_t.v with
      | Pointer _ -> fail_non_equality_type ()
      | Type_app hd KindSpec es ->
        (match try_lookup_enum_cases env hd with
         | Some enum -> Some enum
         | _ -> fail_non_equality_type ())
      | Type_app _ _ _ ->
        error "Impossible, check_switch is not supposed to typecheck output/extern types!" head.range

    in
    let check_case (c:case{Case? c}) : ML case =
      let Case pat f = c in
      let pat, pat_t = check_expr env pat in
      let f = check_field env f in
      let pat = //check type of patterns
        match tags_t_opt with
        | None ->
          //Not an enum; just check that its a valid u32
          if not (eq_typ env scrutinee_t pat_t)
          then match try_cast_integer env (pat, pat_t) scrutinee_t with
               | Some pat -> pat
               | _ ->
                 error (Printf.sprintf "Type of case (%s) does not match type of switch expression (%s)"
                                       (print_typ pat_t)
                                       (print_typ scrutinee_t))
                       pat.range
          else pat

        | Some (enum_tags, t) ->
          //expected an enumerated type;
          //check that patterns are valid cases of the enum
          let case_exists =
            match pat.v with
            | Identifier pat ->
              Some? (List.tryFind (fun (case:ident) -> case.v = pat.v) enum_tags)
            | _ ->
              false
          in
          if not (eq_typ env pat_t t)
          then error (Printf.sprintf "Type of case (%s) does not match type of switch expression (%s)"
                                     (print_typ pat_t)
                                     (print_typ t))
                     pat.range;

          if not case_exists
          then error (Printf.sprintf "Case (%s) is not in the enumerated type %s"
                                     (print_expr pat)
                                     (print_typ scrutinee_t))
                     pat.range;
          pat
      in
      Case pat f
    in
    let check_default_case (c:case{DefaultCase? c}) : ML case =
       let DefaultCase f = c in
       let f = check_field env f in
       DefaultCase f
    in
    let cases =
      List.map (fun (o:case) -> if Case? o then check_case o else check_default_case o) cases in
    let _ =
      List.fold_right
        (fun case default_ok ->
           match case with
           | Case _ _ -> false
           | DefaultCase f ->
              if default_ok then false
              else raise (error "default is only allowed in the last case"
                                f.range))
        cases
        true
    in
    (head, cases)
#pop-options

let is_bound_locally (env:env) (i:ident) = 
  match H.try_find env.locals i.v with
  | None -> false
  | Some _ -> true
  
let rec check_record (check_field:check_field_t) (env:env) (fs:record)
  : ML record
  = let env = copy_env env in //locals of a record do not escape the record
  
    (* Elaborate and check each field in order;
       Checking each field extends the local environment with the name of that field *)
    let fields = 
      List.map 
        (fun f ->
          match f.v with
          | AtomicField af ->
            let af = check_atomic_field env true af in
            { f with v = AtomicField af }

          | RecordField fs i ->
            let fs = check_record check_field env fs in
            {f with v = RecordField fs i }

          | SwitchCaseField swc i ->
            let swc = check_switch check_field env swc in
            { f with v = SwitchCaseField swc i})
        fs
    in
            
    (* Infer which of the fields are dependent by seeing which of them are used in refinements *)
    let nfields = List.length fields in
    let fields = fields |> List.mapi (fun i f ->
      match f.v with
      | RecordField _ _
      | SwitchCaseField _ _ -> f
      | AtomicField af ->
        let sf = af.v in
        let used = is_used env sf.field_ident in
        let last_field = i = (nfields - 1) in
        let dependent = used || (Some? sf.field_constraint && not last_field) in
        let af =
          with_range_and_comments
            ({ sf with field_dependence = dependent })
            af.range
            af.comments
        in
        let has_reader = typ_has_reader env af.v.field_type in
        let is_enum = is_enum env af.v.field_type in
        if af.v.field_dependence
        && not has_reader
        && not is_enum //if it's an enum, it can be inlined later to allow dependence
        then error "The type of this field does not have a reader, \
                    either because its values are too large \
                    or because reading it may incur a double fetch; \
                    subsequent fields cannot depend on it" af.range
        else { f with v = AtomicField af })
    in
    fields


let name_of_field (f:field) : ident =
    match f.v with
    | AtomicField af -> af.v.field_ident
    | RecordField _ i
    | SwitchCaseField _ i -> i

let check_field_names_unique (f:list field)
  : ML unit
  = match f with
    | [] 
    | [_] -> ()
    | hd::tl -> 
      let i = name_of_field hd in
      if List.for_all (fun f' -> not (eq_idents (name_of_field f') i)) tl
      then ()
      else error (Printf.sprintf "Field name %s is not unique" i.v.name) i.range

let rec check_field (env:env) (f:field) 
  : ML field
  = match f.v with
    | AtomicField af ->
      { f with v = AtomicField (check_atomic_field env false af) }

    | RecordField fs i ->
      check_field_names_unique fs;
      { f with v = RecordField (check_record check_field env fs) i }

    | SwitchCaseField swc i ->
      { f with v = SwitchCaseField (check_switch check_field env swc) i }    
  
(** Computes a layout for bit fields,
    decorating each field with a bitfield index
    and a bit range within that bitfield to store the given field.

    Collapsing adjacent bitfields into a single field is done in a
    separate phase, see BitFields.fst
 *)
let elaborate_bit_fields env (fields:list field)
  : ML (out:list field { List.length out == List.length fields })
  = let bf_index : ref int = ST.alloc 0 in
    let get_bf_index () = !bf_index in
    let next_bf_index () = bf_index := !bf_index + 1 in
    let new_bit_field (sf:atomic_field') bw r : ML (atomic_field & option (typ & int & int)) =
        let index = get_bf_index () in
        let size = size_of_integral_typ env sf.field_type r in
        let bit_size = 8 * size in
        let remaining_size = bit_size - bw.v in
        let from = 0 in
        let to = bw.v in
        let bf_attr = {
            bitfield_width = bw.v;
            bitfield_identifier = index;
            bitfield_type = sf.field_type;
            bitfield_from = from;
            bitfield_to = to
        } in
        let sf = { sf with field_bitwidth = Some (Inr (with_range bf_attr r)) } in
        with_range sf r,
        Some (sf.field_type, to, remaining_size)
    in
    let rec aux open_bit_field fields
      : ML (out:list field { List.length out == List.length fields } )
      = match fields with
        | [] ->
          []

        | hd::tl ->
          begin
          match hd.v with
          | RecordField fs hd_fieldname -> 
            next_bf_index();
            let fs = aux None fs in
            let hd = { hd with v = RecordField fs hd_fieldname } in
            next_bf_index();          
            hd :: aux None tl

          | SwitchCaseField (e, cases) hd_fieldname ->
            next_bf_index();          
            let cases = 
              List.map 
                (function 
                  | Case p f -> 
                    let [f] = aux None [f] in
                    Case p f
                    
                  | DefaultCase f ->
                    let [f] = aux None [f] in
                    DefaultCase f)
                cases
            in
            next_bf_index();          
            let hd = { hd with v = SwitchCaseField (e, cases) hd_fieldname } in
            hd :: aux None tl

         | AtomicField af ->
           let sf = af.v in
           match sf.field_bitwidth, open_bit_field with
           | None, None ->
             hd :: aux open_bit_field tl
  
           | None, Some _ ->  //end the bit field
             next_bf_index();
             hd :: aux None tl

           | Some (Inr _), _ ->
             failwith "Bitfield is already elaborated"

           | Some (Inl bw), None ->
             let af, open_bit_field = new_bit_field sf bw hd.range in
             let tl = aux open_bit_field tl in
             { hd with v = AtomicField af } :: tl

           | Some (Inl bw), Some (bit_field_typ, pos, remaining_size) ->
             Options.debug_print_string
               (Printf.sprintf
                 "Field type = %s; bit_field_type = %s\n"
                   (print_typ sf.field_type)
                   (print_typ bit_field_typ));

             let type_matches_current_open_field = eq_typ env sf.field_type bit_field_typ in
             if remaining_size < bw.v //not enough space in this bit field, start a new one
             || not type_matches_current_open_field
             then let _ = next_bf_index () in
                  let af, open_bit_field = new_bit_field sf bw hd.range in
                  let tl = aux open_bit_field tl in
                  { hd with v = AtomicField af } :: tl
             else //extend this bit field
                  begin
                   let remaining_size = remaining_size - bw.v in
                   let from = pos in
                   let to = pos + bw.v in
                   let index = get_bf_index() in
                   let bf_attr = {
                       bitfield_width = bw.v;
                       bitfield_identifier = index;
                       bitfield_type = bit_field_typ;
                       bitfield_from = from;
                       bitfield_to = to
                   } in
                   let sf = { sf with field_bitwidth = Some (Inr (with_range bf_attr bw.range)) } in
                   let af = { af with v = sf } in
                   let hd = { hd with v = AtomicField af } in
                   let open_bit_field = Some (bit_field_typ, to, remaining_size) in
                   let tl = aux open_bit_field tl in
                   hd :: tl
                 end
         end
      in
      aux None fields


let allowed_base_types_as_output_types = [
  "UINT8"; "UINT16"; "UINT32"; "UINT64";
  "UINT8BE"; "UINT16BE"; "UINT32BE"; "UINT64BE";
  "PUINT8";
  "Bool"
]

let rec check_mutable_param_type (env:env) (t:typ) : ML unit =
  let err iopt : ML unit =
    let otype = 
      match iopt with
      | None -> "None"
      | Some i ->
        match H.try_find env.globals.ge_out_t i.v with
        | Some d ->
          Printf.sprintf "(Some %s)" (print_decl d)
        | _ -> "None"
    in
    error (Printf.sprintf "%s is not an integer or output or extern type (found decl %s)" (print_typ t) otype) t.range in
  let t = unfold_typ_abbrev_only env t in
  match t.v with
  | Type_app i k [] ->
    if k = KindOutput || k = KindExtern ||
       (i.v.modul_name = None && List.Tot.mem i.v.name allowed_base_types_as_output_types)
    then ()
    else err (Some i)
  | Pointer t -> check_mutable_param_type env t
  | _ -> err None
    
let rec check_integer_or_output_type (env:env) (t:typ) : ML unit =
  let t = unfold_typ_abbrev_only env t in
  match t.v with
  | Type_app i k [] ->  //either it should be a base type, or an output type
    if i.v.modul_name = None && List.Tot.mem i.v.name allowed_base_types_as_output_types
    then ()
    else if not (k = KindOutput) then error (Printf.sprintf "%s is not an integer or output type" (print_typ t)) t.range
  | Pointer t -> check_integer_or_output_type env t
  | _ -> error (Printf.sprintf "%s is not an integer or output type" (print_typ t)) t.range

let check_mutable_param (env:env) (p:param) : ML unit =
  //a mutable parameter should have a pointer type
  //and the base type may be a base type or an output type
  let t, _, _ = p in
  match t.v with
  | Pointer bt ->
    check_mutable_param_type env bt
  | _ ->
    error (Printf.sprintf "%s is not a valid mutable parameter type, it is not a pointer type" (print_typ t)) t.range

let check_params (env:env) (ps:list param) : ML unit =
  ps |> List.iter (fun (t, p, q) ->
        if q = Mutable then check_mutable_param env (t, p, q)
        else ignore (check_typ true env t);
        add_local env p t)


let elaborate_record_decl (e:global_env)
                          (tdnames:Ast.typedef_names)
                          (params:list param)
                          (where:option expr)
                          (fields:list field)
                          (range:range)
                          (comments:comments)
                          (is_exported:bool)
  : ML decl
  = let env = { mk_env e with this=Some tdnames.typedef_name } in

    (* Check parameters, that their types are well-formed;
       extend the environments with them *)
    check_params env params;

    (* If a where-clause is present, elaborate it into a refined unit field *)
    let where, maybe_unit_field =
      match where with
      | None ->
        None, []
      | Some e ->
        let e, t = check_expr env e in
        if not (eq_typ env t tbool)
        then error (Printf.sprintf "Expected a boolean where clause; got %s"
                   (print_typ t))
                 e.range;
        let w = Some e in
        let field =
          { field_dependence = true;
            field_ident = with_range (to_ident' "__precondition") e.range;
            field_type = tunit;
            field_array_opt = FieldScalar;
            field_constraint = w;
            field_bitwidth = None;
            field_action = None;
            field_probe = None
          }
        in
        let af = with_range (AtomicField (with_range field e.range)) e.range in
        w, [af]
    in

    (* Elaborate and check each field in order;
       Checking each field extends the local environment with the name of that field *)
    let fields = check_record check_field env fields in

    let fields = maybe_unit_field@fields in

    let fields = elaborate_bit_fields env fields in

    let d = mk_decl (Record tdnames params where fields) range comments is_exported in

    let attrs = {
        may_fail = false; //only its fields may fail; not the struct itself
        integral = None;
        bit_order = None;
        has_reader = false;
        parser_weak_kind = weak_kind_of_record env fields;
        parser_kind_nz = None
      }
    in
    add_global e tdnames.typedef_name d (Inl attrs);
    d

(*
 * An output field type is either a base type or another output type
 *
 * TODO: check field name shadowing
 * TODO: check bit fields, do we check that the sum of bitwidths is ok etc.?
 *       as of now, we don't check anything here
 *)

let rec check_output_field (ge:global_env) (fld:out_field) : ML unit =
  match fld with
  | Out_field_named _ t _bopt -> check_integer_or_output_type (env_of_global_env ge) t
  | Out_field_anon l _ -> check_output_fields ge l

and check_output_fields (ge:global_env) (flds:list out_field) : ML unit =
  List.iter (check_output_field ge) flds

let check_entrypoint_probe_length_type
  (e: env)
  (t: typ)
: ML bool
= if eq_typ e t tuint8
  then true
  else if eq_typ e t tuint16
  then true
  else eq_typ e t tuint32

let is_sizeof (l: expr) : Tot bool =
  match l.v with
  | App SizeOf _ ->
      true
  | _ -> false

let check_entrypoint_probe_length
  (lenv: env)
  (l: expr)
: ML expr
= if
    Constant? l.v ||
    Identifier? l.v
  then
    let (l', t') = check_expr lenv l in
    if check_entrypoint_probe_length_type lenv t'
    then l'
    else error ("entrypoint probe: expected UINT32, got " ^ print_typ t') l.range
  else if is_sizeof l
  then
    let (l', t') = check_expr lenv l in
    l'
  else error ("entrypoint probe: expected a constant, #define'd identifier, or sizeof; got " ^ print_expr l) l.range

let check_attribute
  (e: env)
  (a: attribute)
: ML attribute
= match a with
  | Entrypoint (Some p) ->
    Entrypoint (Some ({
      p with probe_ep_length = check_entrypoint_probe_length e p.probe_ep_length
    }))
  | _ -> a

let check_typedef_names
  (e: global_env)
  (tdnames: Ast.typedef_names)
: ML Ast.typedef_names
= let env = { mk_env e with this=Some tdnames.typedef_name } in
  {
      tdnames with
        typedef_attributes = List.map (check_attribute env) tdnames.typedef_attributes
  }

let bind_decl (e:global_env) (d:decl) : ML decl =
  match d.d_decl.v with
  | ModuleAbbrev i m -> d
  | Define i None c ->
    let t = type_of_constant d.d_decl.range c in
    let d = decl_with_v d (Define i (Some t) c) in
    add_global e i d (Inr (nullary_macro t (Some (with_range (Constant c) d.d_decl.range))));
    d

  | Define i (Some t) c ->
    let env = mk_env e in
    let t = check_typ false env t in
    let t' = type_of_constant d.d_decl.range c in
    let d = decl_with_v d (Define i (Some t) c) in
    if eq_typ env t t'
    then (add_global e i d (Inr (nullary_macro (type_of_constant d.d_decl.range c)
                                               (Some (with_range (Constant c) d.d_decl.range))));
          d)
    else error "Ill-typed constant" d.d_decl.range

  | TypeAbbrev t i ->
    let env = mk_env e in
    let t = check_typ false env t in
    let wk =
      match typ_weak_kind env t with
      | None -> failwith (Printf.sprintf "Weak kind not found for type %s" (print_typ t))
      | Some wk -> wk
    in
    let integral, bit_order = tag_and_bit_order_of_integral_typ env t in
    let attrs =
      {
        may_fail = parser_may_fail env t;
        integral = integral;
        bit_order = bit_order;
        has_reader = typ_has_reader env t;
        parser_weak_kind = wk;
        parser_kind_nz = None
      }
    in
    let d = decl_with_v d (TypeAbbrev t i) in
    add_global e i d (Inl attrs);
    d

  | Enum t i cases ->
    let env = mk_env e in
    let t = check_typ false env t in
    let cases_idents = Desugar.check_desugared_enum_cases cases in
    cases_idents |> List.iter (fun i ->
      let _, t' = check_expr env (with_dummy_range (Identifier i)) in
      if not (eq_typ env t t')
      then error (Printf.sprintf "Inconsistent type of enumeration identifier: Expected %s, got %s"
                   (print_typ t)
                   (print_typ t'))
                 d.d_decl.range);
    let integral = typ_as_integer_type t in
    let bit_order = bit_order_of_typ t in
    let attrs =
      {
        may_fail = true;
        integral = Some integral;
        bit_order = Some bit_order;
        has_reader = false; //it's a refinement, so you can't read it again because of double fetches
        parser_weak_kind = WeakKindStrongPrefix;
        parser_kind_nz = None
      }
    in
    let d = decl_with_v d (Enum t i cases) in
    add_global e i d (Inl attrs);
    d

  | Record tdnames params where fields ->
    let tdnames = check_typedef_names e tdnames in
    elaborate_record_decl e tdnames params where fields d.d_decl.range d.d_decl.comments d.d_exported

  | CaseType tdnames params switch ->
    let tdnames = check_typedef_names e tdnames in
    let env = { mk_env e with this=Some tdnames.typedef_name } in
    check_params env params;
    let switch = check_switch check_field env switch in
    let wk = weak_kind_of_switch_case env switch in 
    let attrs = {
      may_fail = false;
      integral = None;
      bit_order = None;
      has_reader = false;
      parser_weak_kind = wk;
      parser_kind_nz = None
    } in
    let d = mk_decl (CaseType tdnames params switch) d.d_decl.range d.d_decl.comments d.d_exported in
    add_global e tdnames.typedef_name d (Inl attrs);
    d

  | OutputType out_t ->
    check_output_fields e out_t.out_typ_fields;
    add_output_type e out_t.out_typ_names.typedef_name d;
    d

  | ExternType tdnames ->
    add_extern_type e tdnames.typedef_name d;
    d

  | ExternFn f ret params ->
    let env = mk_env e in
    let ret = check_typ true env ret in
    check_params env params;
    let d = mk_decl (ExternFn f ret params) d.d_decl.range d.d_decl.comments d.d_exported in
    add_extern_fn e f d;
    d

  | ExternProbe i ->
    add_extern_probe e i d;
    d

let bind_decls (g:global_env) (p:list decl) : ML (list decl & global_env) =
  List.map (bind_decl g) p, g

let initial_global_env () =
  let cfg = Deps.get_config () in
  let e =
    {
      ge_h = H.create 10;
      ge_out_t = H.create 10;
      ge_extern_t = H.create 10;
      ge_extern_fn = H.create 10;
      ge_probe_fn = H.create 10;
      ge_cfg = cfg
    }
  in
  let nullary_decl i =
    let td_name =
      { typedef_name = i; typedef_abbrev = i; typedef_ptr_abbrev = i; typedef_attributes = [] }
    in
    mk_decl (Record td_name [] None []) dummy_range [] true
  in
  let _type_names =
    [
      ("unit",
        {
          may_fail = false;
          integral = None;
          bit_order = None;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some false
        });
      ("Bool",
        {
          may_fail = true;
          integral = None;
          bit_order = None;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("UINT8",
        {
          may_fail = true;
          integral = Some UInt8;
          bit_order = Some LSBFirst;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("UINT16",
        {
          may_fail = true;
          integral = Some UInt16;
          bit_order = Some LSBFirst;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("UINT32",
        {
          may_fail = true;
          integral = Some UInt32;
          bit_order = Some LSBFirst;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("UINT64",
        {
          may_fail = true;
          integral = Some UInt64;
          bit_order = Some LSBFirst;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("UINT8BE",
        {
          may_fail = true;
          integral = Some UInt8;
          bit_order = Some MSBFirst;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("UINT16BE",
        {
          may_fail = true;
          integral = Some UInt16;
          bit_order = Some MSBFirst;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("UINT32BE",
        {
          may_fail = true;
          integral = Some UInt32;
          bit_order = Some MSBFirst;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("UINT64BE",
        {
          may_fail = true;
          integral = Some UInt64;
          bit_order = Some MSBFirst;
          has_reader = true;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("field_id",
        {
          may_fail = true;
          integral = Some UInt32;
          bit_order = None;
          has_reader = false;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("all_bytes",
        {
          may_fail = false;
          integral = None;
          bit_order = None;
          has_reader = false;
          parser_weak_kind = WeakKindConsumesAll;
          parser_kind_nz = Some false
        });
      ("all_zeros",
        {
          may_fail = true;
          integral = None;
          bit_order = None;
          has_reader = false;
          parser_weak_kind = WeakKindConsumesAll;
          parser_kind_nz = Some false
        });
      ("PUINT8",
        {
          may_fail = true;
          integral = None;
          bit_order = None;
          has_reader = false;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
      ("EVERPARSE_COPY_BUFFER_T",
        {
          may_fail = true;
          integral = None;
          bit_order = None;
          has_reader = false;
          parser_weak_kind = WeakKindStrongPrefix;
          parser_kind_nz = Some true
        });
    ] |>
    List.iter (fun (i, attrs) ->
          let i = with_dummy_range (to_ident' i) in
          add_global e i (nullary_decl i) (Inl attrs))
  in
  let _operators =
    [
      ("is_range_okay",
        {
          macro_arguments_t = [tuint32; tuint32; tuint32];
          macro_result_t = tbool;
          macro_defn_t = None
        })
    ] |>
    List.iter (fun (i, d) ->
          let i = with_dummy_range (to_ident' i) in
          add_global e i (nullary_decl i) (Inr d))
  in
  let _void =
    let void_ident = with_dummy_range (to_ident' "void") in
    add_extern_type e
      void_ident
      (mk_decl (ExternType
            ({
                typedef_name = void_ident;
                typedef_abbrev = void_ident;
                typedef_ptr_abbrev = void_ident;
                typedef_attributes = []
              }))
          dummy_range
          []
          false)
  in
  let _ =
    match cfg with
    | None -> ()
    | Some (cfg, module_name) ->
      List.iter (fun flag ->
            let ms = nullary_macro tbool None in
            let i = with_dummy_range ({ to_ident' flag with modul_name = Some module_name }) in
            let d = mk_decl (ExternFn i tbool []) dummy_range [] false in
            add_global e i d (Inr ms))
        cfg.compile_time_flags.flags
  in
  e

let get_exported_decls ge mname =
  H.fold (fun k (d, _) (exported_decls, private_decls) ->
    if not (k.modul_name = Some mname)
    then exported_decls, private_decls
    else if d.d_exported
         then k::exported_decls, private_decls
         else exported_decls, k::private_decls) ge.ge_h ([], [])

let finish_module ge mname =
  let remove_private_decls (tbl:H.t ident' 'a) (f:'a -> decl) : ML unit =
    let pvt_decls = H.fold (fun k v idents ->
      if not (k.modul_name = Some mname)
      then idents
      else let d = f v in
           if d.d_exported
           then idents
           else k::idents) tbl [] in
    List.iter (H.remove tbl) pvt_decls in

  remove_private_decls ge.ge_h (fun (d, _) -> d);
  remove_private_decls ge.ge_out_t (fun d -> d);
  remove_private_decls ge.ge_extern_t (fun d -> d);
  remove_private_decls ge.ge_extern_fn (fun d -> d);
  ge
