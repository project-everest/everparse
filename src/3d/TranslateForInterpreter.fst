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
module TranslateForInterpreter
(* This module translates type definitions from the source Ast
   to types, parsers and validators in the Target language *)
open Ast
module A = Ast
module B = Binding
module T = Target
module H = Hashtable
module TS = TypeSizes
open FStar.All
open FStar.Pervasives
open FStar.List.Tot

noeq
type global_env = {
  benv:B.global_env;
  size_env: TS.env_t;
  has_reader: H.t ident' bool;
  parser_kind_nz: H.t ident' bool;
  parser_weak_kind: H.t ident' A.weak_kind;
  parser_kind_is_constant_size: H.t ident' bool;
}

let has_reader (env:global_env) (id:A.ident) : ML bool =
  if B.has_reader env.benv id
  then true
  else Some? (H.try_find env.has_reader id.v)

let add_reader (env:global_env) (id:A.ident) : ML unit =
  H.insert env.has_reader id.v true

let parser_kind_nz (env:global_env) (id:A.ident) : ML bool =
  match H.try_find env.parser_kind_nz id.v with
  | Some b -> b
  | None ->
    match B.parser_kind_nz env.benv id with
    | Some b -> b
    | None ->
      failwith (Printf.sprintf "Type %s has an unknown parser kind" (ident_to_string id))

let parser_weak_kind (env:global_env) (id:A.ident) : ML A.weak_kind =
  match H.try_find env.parser_weak_kind id.v with
  | Some b -> b
  | None ->
    match B.parser_weak_kind env.benv id with
    | Some b -> b
    | None ->
      failwith (Printf.sprintf "Type %s has an unknown weak kind" (ident_to_string id))

let parser_kind_is_constant_size
  (env: global_env) (id: A.ident)
: ML bool
= 
  match H.try_find env.parser_kind_is_constant_size id.v with
  | Some b -> b
  | None ->
    match TS.size_of_typename env.size_env id with
    | TS.Fixed _ -> true
    | _ -> false

let add_parser_kind_is_constant_size (genv:global_env) (id:A.ident) (is_constant_size:bool) =
  H.insert genv.parser_kind_is_constant_size id.v is_constant_size

/// gensym (top-level effect, safe to ignore)
#push-options "--warn_error -272"
let gen_ident : option string -> St ident =
  let open FStar.ST in
  let ctr : ref int = alloc 0 in
  let next base_name_opt =
    let v = !ctr in
    ctr := v + 1;
    let id =
      match base_name_opt with
      | None -> Printf.sprintf "_x_%d" v
      | Some n -> Printf.sprintf "_%s_%d" n v
    in
    with_dummy_range (to_ident' id)
  in
  next
#pop-options

let underscore_ident = with_dummy_range (to_ident' "_")

(** Some utilities **)
let mk_lam (f:(A.ident -> ML 'a)) : ML (T.lam 'a) =
  let x = gen_ident None in
  Some x, f x

let map_lam (x:T.lam 'a) (g: 'a -> ML 'b) : ML (T.lam 'b) =
  fst x, g (snd x)

let mk_parser k t typename fieldname p = T.({
  p_kind = k;
  p_typ = t;
  p_parser = p;
  p_typename = typename;
  p_fieldname = fieldname
})

// Kind constructors
let pk_return = T.({
  pk_kind = PK_return;
  pk_nz = false;
  pk_weak_kind = WeakKindStrongPrefix;
})
let pk_impos = T.({
  pk_kind = PK_impos;
  pk_nz = true;
  pk_weak_kind = WeakKindStrongPrefix;
})
let pk_base id nz wk = T.({
  pk_kind = PK_base id;
  pk_weak_kind = wk;
  pk_nz = nz
})
let pk_list k0 n = T.({
  pk_kind = PK_list k0 n;
  pk_weak_kind = WeakKindStrongPrefix;
  pk_nz = false
})
let pk_t_at_most = T.({
  pk_kind = PK_t_at_most;
  pk_weak_kind = WeakKindStrongPrefix;
  pk_nz = false
})
let pk_t_exact = T.({
  pk_kind = PK_t_exact;
  pk_weak_kind = WeakKindStrongPrefix;
  pk_nz = false
})
let pk_string = T.({
  pk_kind = PK_string;
  pk_weak_kind = WeakKindStrongPrefix;
  pk_nz = true
})
let pk_filter k = T.({
  pk_kind = PK_filter k;
  pk_weak_kind = k.pk_weak_kind;
  pk_nz = k.pk_nz
})
let pk_and_then k1 k2 = T.({
  pk_kind = PK_and_then k1 k2;
  pk_weak_kind = k2.pk_weak_kind;
  pk_nz = k1.pk_nz || k2.pk_nz
})
let pk_glb k1 k2 = T.({
  pk_kind = PK_glb k1 k2;
  pk_weak_kind = weak_kind_glb k1.pk_weak_kind k2.pk_weak_kind;
  pk_nz = k1.pk_nz && k2.pk_nz
})

let rec is_compile_time_fixed_size (env:global_env) (t:T.typ)
: ML bool
= match t with
  | T.T_false -> true
  | T.T_app hd _ _ ->
    begin
      try
        let size = TypeSizes.size_of_typename env.size_env hd in
        TS.Fixed? size
      with _ -> false
    end
  | T.T_pointer _ _ -> true
  | T.T_refine base _ -> is_compile_time_fixed_size env base
  | T.T_with_comment t _ -> is_compile_time_fixed_size env t
  | T.T_nlist elt n -> // this is the main reason why we need T.T_pair
    if Some? (T.as_constant n)
    then is_compile_time_fixed_size env elt
    else false
  | T.T_pair t1 t2 -> // this is the main reason why we need T.T_pair
    if is_compile_time_fixed_size env t1
    then is_compile_time_fixed_size env t2
    else false
  | _ -> false

let false_typ = T.T_false
let unit_typ =
    T.T_app (with_dummy_range (to_ident' "unit")) KindSpec []
let unit_val =
    T.(mk_expr (App (Ext "()") []))
let unit_parser =
    let unit_id = with_dummy_range (to_ident' "unit") in
    mk_parser pk_return unit_typ unit_id "none" (T.Parse_return unit_val)
let pair_typ t1 t2 =
    T.T_pair t1 t2
let pair_value x y =
    T.Record (with_dummy_range (to_ident' "tuple2"))
             [(with_dummy_range (to_ident' "fst"), T.mk_expr (T.Identifier x));
              (with_dummy_range (to_ident' "snd"), T.mk_expr (T.Identifier y))]  
let pair_parser env n1 p1 p2 =
    let open T in
    let pt = pair_typ p1.p_typ p2.p_typ in
    let t_id = with_dummy_range (to_ident' "tuple2") in
    let p1_is_const = is_compile_time_fixed_size env p1.p_typ in
    let p2_is_const = is_compile_time_fixed_size env p2.p_typ in
    mk_parser (pk_and_then p1.p_kind p2.p_kind)
              pt
              t_id
              (ident_to_string n1)
              (Parse_pair n1 p1_is_const p1 p2_is_const p2)
let dep_pair_typ t1 (t2:(A.ident & T.typ)) : T.typ =
    T.T_dep_pair t1 t2
let dep_pair_value x y : T.expr =
    T.mk_expr
      (T.Record (with_dummy_range (to_ident' "dtuple2"))
                [(with_dummy_range (to_ident' "fst"), T.mk_expr (T.Identifier x));
                 (with_dummy_range (to_ident' "snd"), T.mk_expr (T.Identifier y))])
let dep_pair_parser n1 p1 (p2:A.ident & T.parser) =
  let open T in
  let t = T_dep_pair p1.p_typ (fst p2, (snd p2).p_typ) in
  let t_id = with_dummy_range (to_ident' "dtuple2") in
  mk_parser
      (pk_and_then p1.p_kind (snd p2).p_kind) 
      t
      t_id
      (ident_to_string n1)
      (Parse_dep_pair n1 p1 (Some (fst p2), snd p2))
let dep_pair_with_refinement_parser n1 p1 (e:T.lam T.expr) (p2:A.ident & T.parser) =
  let open T in
  let t1 = T_refine p1.p_typ e in
  let t = T_dep_pair t1 (fst p2, (snd p2).p_typ) in
  let k1 = pk_filter p1.p_kind in
  let t_id = with_dummy_range (to_ident' "dtuple2") in
  mk_parser
      (pk_and_then k1 (snd p2).p_kind)
      t
      t_id
      (ident_to_string n1)
      (Parse_dep_pair_with_refinement n1 p1 e (Some (fst p2), snd p2))
let dep_pair_with_refinement_and_action_parser n1 p1 (e:T.lam T.expr) (a:T.lam T.action) (p2:A.ident & T.parser) =
  let open T in
  let t1 = T_refine p1.p_typ e in
  let t = T_dep_pair t1 (fst p2, (snd p2).p_typ) in
  let k1 = pk_filter p1.p_kind in
  let t_id = with_dummy_range (to_ident' "dtuple2") in  
  mk_parser
      (pk_and_then k1 (snd p2).p_kind)
      t
      t_id
      (ident_to_string n1)
      (Parse_dep_pair_with_refinement_and_action n1 p1 e a (Some (fst p2), snd p2))
let dep_pair_with_action_parser p1 (a:T.lam T.action) (p2:A.ident & T.parser) =
  let open T in
  let t1 = p1.p_typ in
  let t = T_dep_pair t1 (fst p2, (snd p2).p_typ) in
  let k1 = p1.p_kind in
  let t_id = with_dummy_range (to_ident' "dtuple2") in
  mk_parser
      (pk_and_then k1 (snd p2).p_kind)
      t
      t_id
      "none"
      (Parse_dep_pair_with_action p1 a (Some (fst p2), snd p2))
let extend_fieldname fieldname e = Printf.sprintf "%s.%s" fieldname e
let ite_parser typename fieldname (e:T.expr) (then_:T.parser) (else_:T.parser) : ML T.parser =      
    let k, p1, p2 =
      let k = pk_glb then_.p_kind else_.p_kind in
           k,
           mk_parser k then_.p_typ typename (extend_fieldname fieldname "case_left") (T.Parse_weaken_right then_ else_.p_kind),
           mk_parser k else_.p_typ typename (extend_fieldname fieldname "case_right") (T.Parse_weaken_left else_ then_.p_kind)
    in
    let t = T.T_if_else e then_.p_typ else_.p_typ in
    mk_parser k t typename fieldname (T.Parse_if_else e p1 p2)

let translate_op : A.op -> ML T.op = 
  let force_topt (o:option A.integer_type) 
    : ML integer_type
    = match o with
      | None -> failwith (Printf.sprintf "Unelaborated integer operator")
      | Some t -> t
  in
  fun op ->
  match op with
  | Eq -> T.Eq
  | Neq -> T.Neq
  | And -> T.And
  | Or -> T.Or
  | Not -> T.Not
  | Plus topt -> T.Plus (force_topt topt)
  | Minus topt -> T.Minus (force_topt topt)
  | Mul topt -> T.Mul (force_topt topt)
  | Division topt -> T.Division (force_topt topt)
  | Remainder topt -> T.Remainder (force_topt topt)
  | BitwiseAnd topt -> T.BitwiseAnd (force_topt topt)
  | BitwiseXor topt -> T.BitwiseXor (force_topt topt)
  | BitwiseOr topt -> T.BitwiseOr (force_topt topt)
  | BitwiseNot topt -> T.BitwiseNot (force_topt topt)
  | ShiftRight topt -> T.ShiftRight (force_topt topt)
  | ShiftLeft topt -> T.ShiftLeft (force_topt topt)
  | LT topt -> T.LT (force_topt topt)
  | GT topt -> T.GT (force_topt topt)
  | LE topt -> T.LE (force_topt topt)
  | GE topt -> T.GE (force_topt topt)
  | IfThenElse -> T.IfThenElse
  | BitFieldOf i order -> T.BitFieldOf i order
  | Cast (Some from) to -> T.Cast from to
  | Ext s -> T.Ext s
  | Cast None _
  | SizeOf -> failwith (Printf.sprintf "Operator `%s` should have been eliminated already"
                                  (Ast.print_op op))
  | ProbeFunctionName i -> T.ProbeFunctionName i
 
let rec translate_expr (e:A.expr) : ML T.expr =
  (match e.v with
   | Constant c -> T.Constant c
   | Identifier i -> T.Identifier i
   | App op exprs -> T.App (translate_op op) (List.map translate_expr exprs)
   | Static _ -> failwith "`static` should have been eliminated already"
   | This -> failwith "`this` should have been eliminated already"),
  e.A.range

(*
 * Straightforward 1-1 translation
 *)

let rec translate_output_type (t:A.typ) : ML T.typ =
  match t.v with
  | Pointer t (PQ A.UInt64 _ _) -> T.T_pointer (translate_output_type t) A.UInt64
  | Type_app id b [] [] -> T.T_app id b []
  | _ -> failwith "Impossible, translate_output_type did not get an output type!"

let rec translate_out_expr_node (oe:with_meta_t out_expr')
  : ML T.output_expr' =
  match oe.v with
  | OE_id id -> T.T_OE_id id
  | OE_star oe -> T.T_OE_star (translate_out_expr oe)
  | OE_addrof oe -> T.T_OE_addrof (translate_out_expr oe)
  | OE_deref oe id -> T.T_OE_deref (translate_out_expr oe) id
  | OE_dot oe id -> T.T_OE_dot (translate_out_expr oe) id

and translate_out_expr (oe:out_expr) : ML T.output_expr =
  let oe' = translate_out_expr_node oe.out_expr_node in
  match oe.out_expr_meta with
  | Some ({ out_expr_base_t = bt; out_expr_t = t; out_expr_bit_width = n }) ->
    { T.oe_expr = oe';
      T.oe_bt = translate_output_type bt;
      T.oe_t = translate_output_type t;
      T.oe_bitwidth = n}
  | None -> failwith "Impossible, translate_out_expr got an output expression node without metadata!"

(*
 * We create the Output_type_expr decl with these attributes,
 *   they are not used for output types
 *)

let output_types_attributes = {
  T.is_hoisted = false;
  T.is_entrypoint = false;
  T.is_if_def = false;
  T.is_exported = false;
  T.should_inline = false;
  T.comments = [] ;
}

(*
 * An output expression type parameter is translated to
 *   an external function call
 *
 * In addition we emit a top-level Output_type_expr decl
 *)

let translate_out_expr_typ_param (oe:out_expr) : ML (T.expr & T.decls) =
  let t_oe = translate_out_expr oe in
  let fn_name = T.output_getter_name t_oe in
  let base_var = T.output_base_var t_oe in
  let te =
    (T.App (T.Ext fn_name)
      [(T.Identifier base_var, oe.A.out_expr_node.A.range)]), oe.A.out_expr_node.A.range in
  te, [T.Output_type_expr t_oe true, output_types_attributes]
  
let translate_typ_param (p:typ_param) : ML (T.expr & T.decls) =
  match p with
  | A.Inl e  -> translate_expr e, []
  | A.Inr oe -> translate_out_expr_typ_param oe

let rec translate_typ (t:A.typ) : ML (T.typ & T.decls) =
  match t.v with
  | Pointer t (PQ a _ nullable) ->
    let t', decls = translate_typ t in
    T.T_pointer t' a, decls
  | Type_app hd b gs args ->
    let gs = gs |> List.map translate_expr |> List.map Inr in
    let args, decls = args |> List.map translate_typ_param |> List.split in
    T.T_app hd b (gs@List.map Inr args), List.flatten decls
  | Type_arrow ts t ->
    let ts, ds = ts |> List.map translate_typ |> List.split in
    let t, d = translate_typ t in
    T.T_arrow ts t, List.flatten ds @ d

let translate_probe_entrypoint
  (p: A.probe_entrypoint)
: ML T.probe_entrypoint
= {
    probe_ep_fn = p.probe_ep_fn;
    probe_ep_length = translate_expr p.probe_ep_length;
  }

let translate_params (params:list Ast.param)
: ML (list T.param & T.decls)
= let ps, ds =
    params
    |> List.map
        (fun (t, id, _) ->  //TODO: ignores qualifier
          let t, ds = translate_typ t in
          (id, t), ds)
    |> List.split
  in
  ps, List.flatten ds

 
let translate_typedef_name (tdn:A.typedef_names) (params:list Ast.param)
  : ML (T.typedef_name & T.decls) =

  let params, ds = translate_params params in
  let entrypoint_probes = List.map translate_probe_entrypoint (A.get_entrypoint_probes tdn.typedef_attributes) in

  let open T in
  { td_name = tdn.typedef_name;
    td_params = params;
    td_entrypoint_probes = entrypoint_probes;
    td_entrypoint = has_entrypoint tdn.typedef_attributes;
    td_noextract = List.existsb Noextract? tdn.typedef_attributes }, ds

let make_enum_typ (t:T.typ) (ids:list ident) =
  let refinement i =
    let x = T.Identifier i in
    List.fold_right
      (fun y e -> T.mk_expr (T.App T.Or [T.mk_expr (T.App T.Eq [T.mk_expr x; T.mk_expr (T.Identifier y);]); e]))
      ids
      (T.mk_expr (T.Constant (Bool false)))
  in
  T.T_refine t (mk_lam refinement)

let rec has_refinement_and_action (t:T.typ)
  : ML (option (T.typ &
                option (T.lam T.expr) &
                option (either T.action (T.lam T.action)) &
                option comments))
  = let open T in
    match t with
    | T_refine t e -> Some (t, Some e, None, None)
    | T_with_action t a ->
      begin
      match has_refinement_and_action t with
      | None ->
        Some(t, None, Some (Inl a), None)
      | Some (t, e, None, c) ->
        Some (t, e, Some (Inl a), c)
      | Some (_, _, Some _, _) ->
        failwith "Nested actions: impossible"
      end
    | T_with_dep_action t a ->
      begin
      match has_refinement_and_action t with
      | None ->
        Some (t, None, Some (Inr a), None)
      | Some (t, e, None, c) ->
        Some (t, e, Some (Inr a), c)
      | Some (_, _, Some _, _) ->
        failwith "Nested actions: impossible"
      end
    | T_with_comment t c ->
      begin
      match has_refinement_and_action t with
      | None -> None
      | Some (t, e, a, None) -> 
        Some (t, e, a, Some c)
      | Some (t, e, a, Some c') ->
        Some (t, e, a, Some (c @ c'))
      end
    | _ -> None

let maybe_add_comment t copt =
    match copt with
    | None -> t
    | Some c -> T.T_with_comment t c

let rec parse_typ (env:global_env)
                  (typename: A.ident) 
                  (fieldname:string)
                  (t:T.typ) : ML T.parser =
  let open T in
  let extend_fieldname e = Printf.sprintf "%s.%s" fieldname e in
  match t with
  | T_false ->
    mk_parser pk_impos T_false typename fieldname Parse_impos

  | T.T_app _ A.KindOutput _
  | T.T_app _ A.KindExtern _ ->
    failwith "Impossible, did not expect parse_typ to be called with an output/extern type!"

  | T.T_nlist telt e ->
    let pt = parse_typ env typename (extend_fieldname "element") telt in
    let t_size_constant = is_compile_time_fixed_size env telt in
    let n_is_const =
      match T.as_constant e with
      | Some (A.Int _ n) -> if n >= 0 then Some n else None
      | _ -> None
    in
    mk_parser (pk_list pt.p_kind n_is_const)
              t
              typename
              fieldname
              (T.Parse_nlist t_size_constant e pt)

  | T.T_app {v={name="t_at_most"}} KindSpec [Inr e; Inl t] ->
    let pt = parse_typ env typename (extend_fieldname "element") t in
    mk_parser pk_t_at_most
              t
              typename
              fieldname
              (T.Parse_t_at_most e pt)

  | T.T_app {v={name="t_exact"}} KindSpec [Inr e; Inl t] ->
    let pt = parse_typ env typename (extend_fieldname "element") t in
    mk_parser pk_t_exact
              t
              typename
              fieldname
              (T.Parse_t_exact e pt)

  | T.T_app {v={name="cstring"}} KindSpec [Inl t; Inr e] ->
    let pt = parse_typ env typename (extend_fieldname "element") t in
    mk_parser pk_string
              t
              typename
              fieldname
              (T.Parse_string pt e)

  | T.T_app hd KindSpec args ->
    mk_parser (pk_base hd (parser_kind_nz env hd) (parser_weak_kind env hd))
              t
              typename
              fieldname
              (T.Parse_app hd args)

  | T.T_refine t_base refinement ->
    let base = parse_typ env typename fieldname t_base in
    let refined = T.Parse_refinement typename base refinement in
    mk_parser (pk_filter base.p_kind) t typename (extend_fieldname "refinement") refined

  | T.T_if_else e t1 t2 ->
    let p1 = parse_typ env typename fieldname t1 in
    let p2 = parse_typ env typename fieldname t2 in
    ite_parser typename fieldname e p1 p2

  | T.T_pair t1 t2 ->
    pair_parser env typename
      (parse_typ env typename (extend_fieldname "first") t1)
      (parse_typ env typename (extend_fieldname "second") t1)

  | T.T_dep_pair t1 (x, t2) ->
    dep_pair_parser typename (parse_typ env typename (extend_fieldname "first") t1) 
                             (x, parse_typ env typename (extend_fieldname "second") t2)

  | T.T_with_action _ _
  | T.T_with_dep_action _ _ ->
    let ref_action = has_refinement_and_action t in
    begin
    match ref_action with
    | None
    | Some (_, _, None, _) ->
      failwith "Impossible"
    | Some (t, None, Some (Inl a), copt) ->
      let t = maybe_add_comment t copt in
      let p = parse_typ env typename (extend_fieldname "base") t in
      mk_parser p.p_kind t typename fieldname (T.Parse_with_action typename p a)
    | Some (t, None, Some (Inr a), copt) ->
      let t = maybe_add_comment t copt in    
      let p = parse_typ env typename (extend_fieldname "base") t in
      mk_parser p.p_kind t typename fieldname (T.Parse_with_dep_action typename p a)
    | Some (t, Some r, Some (Inl a), copt) ->
      let t = maybe_add_comment t copt in        
      let p = parse_typ env typename (extend_fieldname "base") t in
      mk_parser (pk_filter p.p_kind)
                (T.T_refine t r)
                typename
                fieldname
                (T.Parse_refinement_with_action typename p r (Some underscore_ident, a))
    | Some (t, Some r, Some (Inr a), copt) ->
      let t = maybe_add_comment t copt in            
      let p = parse_typ env typename (extend_fieldname "base") t in
      mk_parser (pk_filter p.p_kind)
                (T.T_refine t r)
                typename
                fieldname
                (T.Parse_refinement_with_action typename p r a)
    end
  | T.T_with_comment t c ->
    let p = parse_typ env typename fieldname t in
    { p with p_parser = T.Parse_with_comment p c }

  | T.T_pointer _ pointer_size ->
    let u64_or_u32, _ = translate_typ (A.type_of_integer_type pointer_size) in
    parse_typ env typename fieldname u64_or_u32

  | T.T_with_probe content_type integer_type pointer_nullable probe as_u64 dest init dest_sz -> 
    let p = parse_typ env typename fieldname content_type in
    let q = T.Parse_with_probe p integer_type pointer_nullable probe as_u64 dest init dest_sz in
    let u64_or_u32, _ = translate_typ (A.type_of_integer_type integer_type) in
    let u64_or_u32_parser = parse_typ env typename fieldname u64_or_u32 in
    { p_kind = u64_or_u32_parser.p_kind;
      p_typ = t;
      p_parser = q;
      p_typename = typename;
      p_fieldname = fieldname }
  
  | T.T_arrow _ _ ->
    failwith "Impossible, did not expect parse_typ to be called with an arrow type!"


let rec read_typ (env:global_env) (t:T.typ) : ML (option T.reader) =
  let open T in
  match t with
  | T_app ({v={name="UINT8"}}) _ [] -> Some Read_u8
  | T_app ({v={name="UINT16"}}) _ [] -> Some Read_u16
  | T_app ({v={name="UINT32"}}) _ [] -> Some Read_u32
  | T.T_app hd KindSpec args ->
    if has_reader env hd
    then Some (T.Read_app hd args)
    else None
  | T.T_with_comment t _
  | T.T_with_action t _ ->
    read_typ env t
  | _ -> None

let make_reader (env:global_env) (t:T.typ) : ML T.reader =
  match read_typ env t with
  | None ->
    failwith (Printf.sprintf "Unsupported reader type: %s\n" (T.print_typ "" t))  //AR: TODO: needs a module name
  | Some r ->
    r

/// To translate an assignment action, a star is translated as before
///
/// Other output expressions are translated to setters applied to the base variable and rhs
///
/// In addition a top-level Output_type_expr decl is emitted

let translate_action_assignment (lhs:A.out_expr) (rhs:A.expr)
  : ML (T.atomic_action & T.decls) =

  let open A in
  match lhs.out_expr_node.v with
  | OE_star ({out_expr_node={v=OE_id i}}) ->
    T.Action_assignment i (translate_expr rhs), []
  | _ ->
    let t_lhs = translate_out_expr lhs in
    let fn_name = T.output_setter_name t_lhs in
    let base_var = T.output_base_var t_lhs in
    let v = translate_expr rhs in
    let act = T.Action_call (Ast.with_dummy_range (Ast.to_ident' fn_name))
      [(T.Identifier base_var, rhs.A.range); v] in
    act, [T.Output_type_expr t_lhs false, output_types_attributes]

let translate_action_field_ptr_after (write_to:A.out_expr) (sz:A.expr)
  : ML (T.atomic_action & T.decls)
=
  let open A in
  match write_to.out_expr_node.v with
  | OE_star ({out_expr_node={v=OE_id i}}) ->
    T.Action_field_ptr_after (translate_expr sz) i, []
  | _ ->
    let t_write_to = translate_out_expr write_to in
    let fn_name = T.output_setter_name t_write_to in
    let base_var = T.output_base_var t_write_to in
    let v = translate_expr sz in
    let act = T.Action_field_ptr_after_with_setter v
      (Ast.with_dummy_range (Ast.to_ident' fn_name))
      (T.Identifier base_var, sz.A.range)
    in
    act, [T.Output_type_expr t_write_to false, output_types_attributes]

let rec translate_action (a:A.action) : ML (T.action & T.decls) =
  let translate_atomic_action (a:A.atomic_action)
    : ML (T.atomic_action & T.decls)
    = match a with
      | Action_return e ->
        T.Action_return (translate_expr e), []
      | Action_abort ->
        T.Action_abort, []
      | Action_field_pos_64 ->
        T.Action_field_pos_64, []
      | Action_field_pos_32 ->
        T.Action_field_pos_32, []
      | Action_field_ptr ->
        T.Action_field_ptr, []
      | Action_field_ptr_after sz write_to ->
        translate_action_field_ptr_after write_to sz
      | Action_deref i ->
        T.Action_deref i, []
      | Action_assignment lhs rhs ->
        translate_action_assignment lhs rhs
      | Action_call f args ->
        T.Action_call f (List.map translate_expr args), []
  in
  match a.v with
  | Atomic_action a ->
    let act, ds = translate_atomic_action a in
    T.Atomic_action act, ds

  | Action_seq hd tl ->
    let hd, ds1 = translate_atomic_action hd in
    let tl, ds2 = translate_action tl in
    T.Action_seq hd tl, ds1@ds2

  | Action_ite hd then_ (Some else_) ->
    let then_, ds_then = translate_action then_ in
    let else_, ds_else = translate_action else_ in
    T.Action_ite (translate_expr hd) then_ else_, ds_then @ ds_else

  | Action_ite hd then_ None ->
    let then_, ds_then = translate_action then_ in
    T.Action_ite (translate_expr hd)
                 then_
                 (T.Atomic_action (T.Action_return (T.mk_expr (T.Constant A.Unit)))),
    ds_then

  | Action_let i a k ->
    let a, ds1 = translate_atomic_action a in
    let k, ds2 = translate_action k in
    T.Action_let i a k, ds1 @ ds2

  | Action_act a ->
    let a, ds = translate_action a in
    T.Action_act a, ds

let rec parser_is_constant_size_without_actions
  (env: global_env)
  (p: T.parser)
: ML bool
= match p.T.p_parser with
  | T.Parse_return _
  | T.Parse_impos
    -> true
  | T.Parse_app hd _
    -> parser_kind_is_constant_size env hd
  | T.Parse_nlist _ array_size parse_elem
    -> begin match fst array_size with
      | T.Constant (A.Int _ array_size) -> parser_is_constant_size_without_actions env parse_elem
      | _ -> false
      end
  | T.Parse_pair _ _ hd _ tl
    -> if parser_is_constant_size_without_actions env hd
      then parser_is_constant_size_without_actions env tl
      else false
  | T.Parse_dep_pair _ parse_key (_, parse_value)
  | T.Parse_dep_pair_with_refinement _ parse_key _ (_, parse_value)
    -> (* the lambda identifier is not global, because the 3d syntax does not allow higher-order types *)
      if parser_is_constant_size_without_actions env parse_key
      then parser_is_constant_size_without_actions env parse_value
      else false
  | T.Parse_t_at_most _ _
  | T.Parse_t_exact _ _  
  | T.Parse_dep_pair_with_action _ _ _
  | T.Parse_dep_pair_with_refinement_and_action _ _ _ _ _
  | T.Parse_refinement_with_action _ _ _ _
  | T.Parse_with_dep_action _ _ _
  | T.Parse_with_action _ _ _
  | T.Parse_if_else _ _ _
  | T.Parse_string _ _
  | T.Parse_with_probe _ _ _ _ _ _ _ _
    -> false
  | T.Parse_map p _
  | T.Parse_refinement _ p _
  | T.Parse_weaken_left p _
  | T.Parse_weaken_right p _  
  | T.Parse_with_comment p _
    -> parser_is_constant_size_without_actions env p

let unknown_type_ident = 
  let open Ast in
  let id = {
    modul_name = None;
    name = "<unknown>"
  } in
  with_range id dummy_range

let make_zero (r: range) (t: typ) : ML T.expr =
  let it = typ_as_integer_type t in
  (T.Constant (Int it 0), r)

let rec translate_probe_action (a:A.probe_action) : ML (T.probe_action & T.decls) =
  let translate_atomic (a:A.probe_atomic_action) : ML T.atomic_probe_action =
    match a with
    | A.Probe_action_return e ->
      T.Atomic_probe_return (translate_expr e)
    | A.Probe_action_call f args ->
      T.Atomic_probe_call_pure f (List.map translate_expr args)
    | A.Probe_action_read f ->
      T.Atomic_probe_and_read f
    | A.Probe_action_write f v ->
      T.Atomic_probe_write_at_offset (translate_expr v) f
    | A.Probe_action_copy f v ->
      T.Atomic_probe_and_copy (translate_expr v) f
    | A.Probe_action_skip_read n ->
      T.Atomic_probe_skip_read (translate_expr n)
    | A.Probe_action_skip_write n ->
      T.Atomic_probe_skip_write (translate_expr n)
    | A.Probe_action_fail ->
      T.Atomic_probe_fail
  in
  match a.v with
  | A.Probe_atomic_action a ->
    T.Probe_action_atomic (translate_atomic a), []
  | A.Probe_action_var i ->
    T.Probe_action_var (translate_expr i), []
  | A.Probe_action_seq d hd tl ->
    let hd, ds1 = translate_probe_action hd in
    let tl, ds2 = translate_probe_action tl in
    T.Probe_action_seq (translate_expr d) hd tl, ds1@ds2
  | A.Probe_action_let d i a k ->
    let a = translate_atomic a in
    let tl, ds2 = translate_probe_action k in
    T.Probe_action_let (translate_expr d) i a tl, ds2
  | A.Probe_action_ite e th el ->
    let th, ds1 = translate_probe_action th in
    let el, ds2 = translate_probe_action el in
    T.Probe_action_ite (translate_expr e) th el, ds1@ds2
  | A.Probe_action_array len e ->
    let len = translate_expr len in
    let e, ds = translate_probe_action e in
    T.Probe_action_array len e, ds
  | A.Probe_action_copy_init_sz f ->
    T.Probe_action_copy_init_sz f, []

#push-options "--z3rlimit_factor 4"
let translate_atomic_field (f:A.atomic_field) : ML (T.struct_field & T.decls) =
  let sf = f.v in
  let translate_probe_call (p:probe_call) 
    : ML (T.probe_action & A.ident & T.decls & A.ident & T.expr) =
    let { probe_dest; probe_block; probe_init; probe_dest_sz } = p in
    let probe_block, ds = translate_probe_action probe_block in
    match probe_init with
    | None -> failwith "Impossible: probe_init should have been resolved"
    | Some probe_init ->
      probe_block, probe_dest, ds, probe_init, translate_expr probe_dest_sz
  in
  match f.v.field_probe with
  | Some probe_call -> (
    let as_u64 =
      match probe_call.probe_ptr_as_u64 with
      | None -> failwith "Impossible: probe_ptr_as_u64 should have been resolved"
      | Some i -> i
    in
    let probe_action, dest, ds, probe_init, dest_sz = translate_probe_call probe_call in
    match f.v.field_type.v with
    | Pointer t (PQ a _ nullable) ->
      let t, ds1 = translate_typ t in
      let sf_typ = T.T_with_probe t a nullable probe_action dest as_u64 probe_init dest_sz in
      T.({ sf_dependence=sf.field_dependence;
           sf_ident=sf.field_ident;
           sf_typ=sf_typ }), 
      ds@ds1
      
    | _ -> 
      failwith "Impossible: probed fields must be pointers and the probe function must be resolved"
  )
  
  | _ -> 
    let t, ds1 = translate_typ sf.field_type in
    let t =
        let mk_at_most t e : ML T.typ =
          let e = translate_expr e in
          T.T_app (with_range (to_ident' "t_at_most") sf.field_type.range) KindSpec [Inr e; Inl t]
        in
        match sf.field_array_opt with
        | FieldScalar -> t
        | FieldArrayQualified (e, ByteArrayByteSize)
        | FieldArrayQualified (e, ArrayByteSize) ->
          let e = translate_expr e in
          T.T_nlist t e
        | FieldArrayQualified (e, ArrayByteSizeAtMost) ->
          mk_at_most t e
        | FieldArrayQualified (e, ArrayByteSizeSingleElementArray) ->
          let e = translate_expr e in
          T.T_app (with_range (to_ident' "t_exact") sf.field_type.range) KindSpec [Inr e; Inl t]
        | FieldString sz ->
          let r = sf.field_type.range in
          let str = T.T_app (with_range (to_ident' "cstring") r) KindSpec [Inl t; Inr (make_zero r sf.field_type)] in
          begin match sz with
          | None -> str
          | Some e -> mk_at_most str e
          end
        | FieldConsumeAll -> T.T_app (with_range (to_ident' "all_bytes") sf.field_type.range) KindSpec []
    in
    let t =
      match sf.field_constraint with
      | None -> t
      | Some e ->
        T.T_refine t (Some sf.field_ident, translate_expr e)
    in
    let t, ds2 =
      match sf.field_action with
      | None -> t, []
      | Some (a, false) ->
        let a, ds2 = translate_action a in
        T.T_with_action t a, ds2
      | Some (a, _) ->
        let a, ds2 = translate_action a in
        T.T_with_dep_action t (Some sf.field_ident, a), ds2
    in
    let t : T.typ =
      match f.comments with
      | [] ->
        let c =
          Printf.sprintf "Validating field %s"
            (print_ident sf.field_ident)
        in
        T.T_with_comment t [c]
      | c -> T.T_with_comment t c
    in
    if T.T_pointer? t
    then failwith "Type-checking should have forbidden fields with pointer types"
    else
      T.({sf_dependence=sf.field_dependence;
          sf_ident=sf.field_ident;
          sf_typ=t}), ds1@ds2
#pop-options

noeq
type grouped_fields =
  // | Empty_grouped_field
  | DependentField    : hd:T.field -> tl:grouped_fields -> grouped_fields
  | NonDependentField : hd:T.field -> tl:option grouped_fields -> grouped_fields
  | ITEGroup          : e:T.expr -> then_:grouped_fields -> else_:grouped_fields -> grouped_fields
  | GroupThen         : id:A.ident -> struct:grouped_fields -> rest:option grouped_fields -> grouped_fields

let parse_grouped_fields (env:global_env) (typename:A.ident) (gfs:grouped_fields)
  : ML T.parser
  = let open T in
    let parse_typ (fieldname:A.ident) = parse_typ env typename Ast.(fieldname.v.name) in
    let rec aux (gfs:grouped_fields) : ML parser =
      match gfs with
      // | Empty_grouped_field ->
      //   failwith "Unexpected empty list of fields"
      | DependentField sf gfs ->
        //This a dependent pair, gfs cannot be empty
        let get_action = function
          | Inl a -> (Some sf.sf_ident, a)
          | Inr a -> a
        in
        begin
        match has_refinement_and_action sf.sf_typ with
        | None ->
          dep_pair_parser
            sf.sf_ident
            (parse_typ sf.sf_ident sf.sf_typ)
            (sf.sf_ident, aux gfs)
            
        | Some (_, None, None, copt) ->
          dep_pair_parser
            sf.sf_ident
            (parse_typ sf.sf_ident (maybe_add_comment sf.sf_typ copt))
            (sf.sf_ident, aux gfs)

        | Some (t, Some e, None, copt) ->
          dep_pair_with_refinement_parser
            sf.sf_ident
            (parse_typ sf.sf_ident (maybe_add_comment t copt))
            e
            (sf.sf_ident, aux gfs)

        | Some (t, Some e, Some a, copt) ->
          dep_pair_with_refinement_and_action_parser
            sf.sf_ident
            (parse_typ sf.sf_ident (maybe_add_comment t copt))
            e
            (get_action a)
            (sf.sf_ident, aux gfs)

        | Some (t, None, Some a, copt) ->
          dep_pair_with_action_parser
            (parse_typ sf.sf_ident (maybe_add_comment t copt))
            (get_action a)
            (sf.sf_ident, aux gfs)
        end

      | NonDependentField sf rest -> (
        match rest with
        | None ->
          parse_typ sf.sf_ident sf.sf_typ

        | Some rest -> 
          pair_parser env sf.sf_ident
            (parse_typ sf.sf_ident sf.sf_typ)
            (aux rest)
        )
        
      | ITEGroup e then_ else_ ->
        let id = gen_ident None in
        let then_ = aux then_ in
        let else_ = aux else_ in
        ite_parser typename id.v.name e then_ else_

      | GroupThen id gfs rest -> (
        match rest with
        | None ->
          aux gfs

        | Some rest -> 
          pair_parser env id
            (aux gfs)
            (aux rest)
        )

    in
    aux gfs


let make_tdn (i:A.ident) (attrs:list A.attribute) =
  {
    typedef_name = i;
    typedef_abbrev = with_dummy_range (to_ident' "");
    typedef_ptr_abbrev = None;
    typedef_attributes = attrs
  }

let env_t = list (A.ident * T.typ)

let check_in_global_env (env:global_env) (i:A.ident) =
  let _ = B.lookup_expr_name (B.mk_env env.benv) i in ()

let maybe_gen_ident (env:global_env) (s:string) : A.ident =
  with_dummy_range (to_ident' s)

let type_in_local_env (i:A.ident) (env:env_t)
  : ML (option T.typ) =
    match List.tryFind (fun (i', _) -> A.(i.v = i'.v)) env with
    | None -> None
    | Some (_, t) -> Some t

let rec free_vars_expr (genv:global_env)
                       (env:env_t)
                       (out:env_t)
                       (e:T.expr)
  : ML env_t
  = let open T in
    match fst e with
    | Constant _ -> out
    | Identifier i ->
      if Some? (type_in_local_env i out) then out
      else begin
        match type_in_local_env i env with
        | None ->
          check_in_global_env genv i;
          out
        | Some t -> (i, t) :: out
      end
    | App hd args ->
      List.fold_left (free_vars_expr genv env) out args
    | Record _ fields ->
      List.fold_left (fun out (_, e) -> free_vars_expr genv env out e) out fields

let with_attrs 
      (d:T.decl')
      (h:bool)
      (is_entrypoint: bool)
      (ifdef:bool)
      (e:bool)
      (i:bool)
      (c:list string)
  : T.decl
  = d, T.({ 
      is_hoisted = h;
      is_entrypoint;
      is_if_def = ifdef;
      is_exported = e;
      should_inline = i;
      comments = c
    } )

let with_comments (d:T.decl') (is_entrypoint: bool) (e:bool) (c:list string)
  : T.decl
  = d, T.({
      is_hoisted = false;
      is_entrypoint;
      is_if_def=false;
      is_exported = e;
      should_inline = false;
      comments = c;
    } )

let rec hoist_typ
          (fn:string)
          (genv:global_env)
          (env:env_t)
          (t:T.typ)
  : ML (list T.decl & T.typ)
  = let open T in
    match t with
    | T_false -> [], t
    | T_nlist _ _
    | T_app _ _ _ -> [], t
    | T_pair t1 t2 ->
      let ds, t1 = hoist_typ fn genv env t1 in
      let ds', t2 = hoist_typ fn genv env t2 in
      ds@ds', T_pair t1 t2
    | T_dep_pair t1 (x, t2) ->
      let ds, t1 = hoist_typ fn genv env t1 in
      let ds', t2 = hoist_typ fn genv ((x, t1)::env) t2 in
      ds@ds', T_dep_pair t1 (x, t2)
    | T_refine t1 (Some x, e) ->
      let ds, t1 = hoist_typ fn genv env t1 in
      // let fvs = env in //free_vars_expr genv env [] e in
      let params = List.rev env in
      let args = (List.map (fun (x, _) -> Identifier x) params) in
      let def, app =
        let params = params @ [x,t1] in
        let args = args in //@ [Identifier x] in
        let filter_name = fn ^ "_filter" in
        let id = maybe_gen_ident genv filter_name in
        let result_type = T_app (with_dummy_range (to_ident' "bool")) KindSpec [] in
        let body = e in
        let app = App (Ext id.A.v.name) (List.Tot.map (fun arg -> T.mk_expr arg) args) in
        (id, params, result_type, body),
        T.mk_expr app
      in
      let d = Definition def in
      let t = T_refine t1 (None, app) in
      ds@[with_attrs d true false false false true []],  //hoisted, not entrypoint, not exported, inlineable
      t

    | T_refine t1 (None, e) ->
      let ds, t1 = hoist_typ fn genv env t1 in
      ds, T_refine t1 (None, e)

    | T_if_else e t f ->
      let d1, t = hoist_typ fn genv env t in
      let d2, f = hoist_typ fn genv env f in
      d1@d2, T_if_else e t f

    | T_with_action t a ->
      let d, t = hoist_typ fn genv env t in
      d, T_with_action t a

    | T_with_dep_action t a ->
      let d, t = hoist_typ fn genv env t in
      d, T_with_dep_action t a

    | T_with_comment t c ->
      let d, t = hoist_typ fn genv env t in
      d, T_with_comment t c

    | T_pointer _ _
    | T_with_probe _ _ _ _ _ _ _ _
    | T_arrow _ _ ->
      [], t

let add_parser_kind_nz (genv:global_env) (id:A.ident) (nz:bool) (wk: weak_kind) =
  let _ = Options.debug_print_string
    (Printf.sprintf "For %s, adding parser kind %s\n"
      (ident_to_string id)
      (string_of_bool nz)) in
  H.insert genv.parser_weak_kind id.v wk;
  H.insert genv.parser_kind_nz id.v nz

let hoist_one_type_definition (should_inline:bool)
                              (genv:global_env) (env:env_t) (orig_tdn:T.typedef_name)
                              (prefix:string) (t:T.typ)
  : ML (T.decl & T.field_typ)
  =  let open T in
     let parse_typ = parse_typ genv in
     let type_name = prefix in //^ "_type" in
     let id = maybe_gen_ident genv type_name in
     let args = List.map (fun (x, _) -> Inr (T.mk_expr (Identifier x))) (List.rev env) in
     let tdef = T_app id KindSpec args in
     let tdef =
       if should_inline
       then tdef
       else T_with_comment tdef
                           [Printf.sprintf "Field %s"
                             prefix]
      in
      let body = t in
      let comment = Printf.sprintf "    Internal helper function:\n        Validator for field %s\n        of type %s"
                                   prefix
                                   (ident_to_string orig_tdn.td_name) in
      let tdn = {
        orig_tdn with
          td_name = id;
          td_params = List.rev env;
          td_entrypoint_probes = [];
          td_entrypoint = false;
      } in
      let t_parser = parse_typ orig_tdn.td_name type_name body in
      add_parser_kind_nz genv tdn.td_name t_parser.p_kind.pk_nz t_parser.p_kind.pk_weak_kind;
      add_parser_kind_is_constant_size genv tdn.td_name (parser_is_constant_size_without_actions genv t_parser);
      let td = {
        decl_name = tdn;
        decl_typ = TD_abbrev body;
        decl_parser = t_parser;
        decl_is_enum = false        
      } in
      let td = Type_decl td in
      with_attrs td true false false false should_inline [comment],  //hoisted, not entrypoint, not exported, should_inline
      tdef

let hoist_field (genv:global_env) (env:env_t) (tdn:T.typedef_name) (f:T.field)
  : ML (list T.decl & T.field)
  = let open T in
    let field_name = Printf.sprintf "%s_%s" (ident_name tdn.td_name) (ident_to_string f.sf_ident) in
    let d, t = hoist_typ field_name genv env f.sf_typ in
    let ref_action = has_refinement_and_action t in
    if (f.sf_dependence
     && Some? ref_action) //can't hoist it, otherwise we end up with double fetches
    || (match ref_action with
       | Some (_, Some _, Some (Inr _), _) -> //refinement and dependent action
         true
       | _ -> false)
    then let f = { f with sf_typ = t } in
         d, f
    else
      let td, tdef = hoist_one_type_definition false genv env tdn field_name t in
      let f = { f with sf_typ = tdef } in
      d@[td], f

let hoist_refinements (genv:global_env) (tdn:T.typedef_name) (fields:list T.field)
  : ML (list T.decl * list T.field)
  = let hoist_one_field edf (f:T.field)
        : ML _ =
        let open T in
        let (env, decls, fields) = edf in
        let decls', f = hoist_field genv env tdn f in
        let env = 
          if f.sf_dependence
          then (f.sf_ident, f.sf_typ)::env
          else env
        in
        env, decls@decls', f::fields
    in
    let _, decls, fields =
      List.fold_left
        hoist_one_field
        (List.rev tdn.T.td_params, [], [])
        fields
    in
    decls, List.rev fields

let rec field_as_grouped_fields (f:A.field)
  : ML (A.ident & grouped_fields & T.decls)
  = match f.v with
    | AtomicField af ->
      let sf, ds = translate_atomic_field af in
      sf.sf_ident, NonDependentField sf None, ds

    | RecordField fs field_name ->
      let gfs, ds =
        List.fold_right #_ #(option grouped_fields & T.decls)
          (fun f (gfs, ds_out) ->
            match f.v with
            | AtomicField af -> 
              let sf, ds = translate_atomic_field af in
              if sf.sf_dependence && Some? gfs
              then Some (DependentField sf (Some?.v gfs)), ds@ds_out
              else Some (NonDependentField sf gfs), ds@ds_out
  
            | RecordField _ _
            | SwitchCaseField _ _ ->
              let id, gf, ds = field_as_grouped_fields f in
              Some (GroupThen id gf gfs), ds@ds_out)
          fs
          (None, [])
      in
      let gfs, ds =
        if None? gfs
        then let sf, ds' = translate_atomic_field (unit_atomic_field f.range) in
             NonDependentField sf None, ds@ds'
        else Some?.v gfs, ds
      in
      field_name, gfs, ds

    | SwitchCaseField swc field_name ->
      let sc, cases = swc in
      let sc = translate_expr sc in
      let false_field =
        NonDependentField
          T.( { sf_typ = T.T_false;
                sf_ident = gen_ident None;
                sf_dependence = false } ) 
          None
      in
      let rest, default_group, decls =
        if List.length cases > 0
        then 
          let rest, last = List.splitAt (List.length cases - 1) cases in
          match last with
          | [DefaultCase f] ->
            let _, gfs, ds = field_as_grouped_fields f in
            rest, gfs, ds
          
          | _ -> 
            cases, false_field, []
          else
            cases, false_field, []
      in
      let gfs, ds =
        List.fold_right
          (fun case (else_group, decls') ->
            match case with
            | DefaultCase _ -> failwith "Impossible"
            | Case p f ->
              let _, gfs, decls = field_as_grouped_fields f in
              let guard =
                match p.v with
                | Constant (Bool true) ->
                  // simplify (sc == true) to just (sc)
                  sc
                | _ -> T.mk_expr (T.App T.Eq [sc; translate_expr p])
              in
              ITEGroup guard gfs else_group, decls@decls')
          rest
          (default_group, decls)
      in
      field_name, gfs, ds
    
let parse_field (env:global_env)
                (typename:A.ident)
                (f:A.field) 
  : ML (T.parser & T.decls)
  = let _, gfs, decls = field_as_grouped_fields f in
    parse_grouped_fields env typename gfs, decls

let generics_as_params (gs:list generic_param) =
  List.map (function GenericProbeFunction i ty _ -> ty, i, Immutable) gs

let translate_decl (env:global_env) (d:A.decl) : ML (list T.decl) =
  if A.is_noextract d then [] else
  match d.d_decl.v with
  | ModuleAbbrev _ _ -> []
  | Define i None s ->
    failwith (Printf.sprintf "Untyped definition remains after elaboration: %s" (ident_to_string i))

  | Define i (Some t) s ->
    let t, ds = translate_typ t in
    ds@[with_comments (T.Definition (i, [], t, T.mk_expr (T.Constant s))) (A.is_entrypoint d) d.d_exported d.d_decl.comments]

  | TypeAbbrev attrs t i gs ps ->
    let tdn = make_tdn i attrs in
    let t, ds1 = translate_typ t in
    let params =  generics_as_params gs @ ps in
    let tdn, ds2 = translate_typedef_name tdn params in
    let p = parse_typ env i "" t in
    let open T in
    add_parser_kind_nz env tdn.td_name p.p_kind.pk_nz p.p_kind.pk_weak_kind;
    add_parser_kind_is_constant_size env tdn.td_name (parser_is_constant_size_without_actions env p);
    let td = {
        decl_name = tdn;
        decl_typ = TD_abbrev t;
        decl_parser = p;
        decl_is_enum = false
    } in
    ds1@ds2@[with_comments (Type_decl td) (A.has_entrypoint attrs) d.d_exported A.(d.d_decl.comments)]

  | Enum t i ids ->
    let ids = Desugar.check_desugared_enum_cases ids in
    let tdn = make_tdn i [] in
    let typ, ds1 = translate_typ t in
    let tdn, ds2 = translate_typedef_name tdn [] in
    let refined_typ = make_enum_typ typ ids in
    let p = parse_typ env i "" refined_typ in
    let open T in
    add_parser_kind_nz env tdn.td_name p.p_kind.pk_nz p.p_kind.pk_weak_kind;
    add_parser_kind_is_constant_size env tdn.td_name (parser_is_constant_size_without_actions env p);
    let td = {
        decl_name = tdn;
        decl_typ = TD_abbrev refined_typ;
        decl_parser = p;
        decl_is_enum = true
    } in
    ds1@ds2@[with_comments (Type_decl td) (A.is_entrypoint d) d.d_exported A.(d.d_decl.comments)]

  | Record tdn gs params _ ast_fields ->
    let tdn, ds1 = translate_typedef_name tdn (generics_as_params gs @ params) in
    let dummy_ident = with_dummy_range (to_ident' "_") in
    let p, ds2 = parse_field env tdn.td_name (with_dummy_range (RecordField ast_fields dummy_ident)) in
    let open T in
    add_parser_kind_nz env tdn.td_name p.p_kind.pk_nz p.p_kind.pk_weak_kind;
    add_parser_kind_is_constant_size env tdn.td_name (parser_is_constant_size_without_actions env p);
    let decl_typ = TD_abbrev p.p_typ in
    let td = {
          decl_name = tdn;
          decl_typ = decl_typ;
          decl_parser = p;
          decl_is_enum = false
    } in
    ds1@ds2 @ [with_comments (Type_decl td) (A.is_entrypoint d) d.d_exported A.(d.d_decl.comments)]

  | CaseType tdn0 gs params switch_case ->
    let tdn, ds1 = translate_typedef_name tdn0 (generics_as_params gs @ params) in
    let dummy_ident = with_dummy_range (to_ident' "_") in    
    let p, ds2 = parse_field env tdn.td_name (with_dummy_range (SwitchCaseField switch_case dummy_ident)) in
    let open T in
    add_parser_kind_nz env tdn.td_name p.p_kind.pk_nz p.p_kind.pk_weak_kind;
    add_parser_kind_is_constant_size env tdn.td_name (parser_is_constant_size_without_actions env p);
    let t = p.p_typ in
    let td = {
        decl_name = tdn;
        decl_typ = TD_abbrev t;
        decl_parser = p;
        decl_is_enum = false
    } in
    ds1 @ ds2 @ [with_comments (Type_decl td) (A.is_entrypoint d) d.d_exported A.(d.d_decl.comments)]

  | ProbeFunction id ps pb _ ->
    let ps, ds = translate_params ps in
    let pb, ds' = translate_probe_action pb in
    ds@ds'@[with_comments (T.Probe_function id ps pb) false false A.(d.d_decl.comments)]

  | CoerceProbeFunctionStub _ _ _ ->
    failwith "Coerce probe function stub: should have been eliminated before translation"

  | Specialize _ _ _ ->
    failwith "Specialize: should have been eliminated before translation"

  | OutputType out_t -> [with_comments (T.Output_type out_t) (A.is_entrypoint d) false []]  //No decl for output type specifications

  | ExternType tdnames -> [with_comments (T.Extern_type tdnames.typedef_abbrev) (A.is_entrypoint d) false []]

  | ExternFn f ret params pure ->
    let ret, ds = translate_typ ret in
    let params, ds = List.fold_left (fun (params, ds) (t, i, _) ->
      let t, ds_t = translate_typ t in
      params@[i, t],ds@ds_t) ([], ds) params in
    ds @ [with_comments (T.Extern_fn f ret params pure) (A.is_entrypoint d) false []]

  | ExternProbe f pq ->
    let translate_qualifier (pq:A.probe_qualifier) : ML T.probe_qualifier =
      match pq with
      | A.PQWithOffsets -> T.PQWithOffsets
      | A.PQInit -> T.PQInit
      | A.PQRead t -> T.PQRead t
      | A.PQWrite t -> T.PQWrite t
    in
    let pq = translate_qualifier pq in
    [with_comments (T.Extern_probe f pq) (A.is_entrypoint d) false []]

noeq
type translate_env = {
  t_has_reader: H.t ident' bool;
  t_parser_kind_nz: H.t ident' bool;
  t_parser_weak_kind: H.t ident' A.weak_kind;
  t_parser_kind_is_constant_size: H.t ident' bool;
}

let initial_translate_env () = {
  t_has_reader = H.create 0;
  t_parser_kind_nz = H.create 0;
  t_parser_weak_kind = H.create 0;
  t_parser_kind_is_constant_size = H.create 0; }

let translate_decls benv senv tenv ds =
  let env = {
    benv = benv;
    size_env = (B.mk_env benv, senv);
    has_reader = tenv.t_has_reader;
    parser_kind_nz = tenv.t_parser_kind_nz;
    parser_weak_kind = tenv.t_parser_weak_kind;
    parser_kind_is_constant_size = tenv.t_parser_kind_is_constant_size;
  } in
  List.collect (translate_decl env) ds,
  { tenv with t_has_reader = env.has_reader;
              t_parser_kind_nz = env.parser_kind_nz;
              t_parser_weak_kind = env.parser_weak_kind;
              t_parser_kind_is_constant_size = env.parser_kind_is_constant_size }

let finish_module en mname e_and_p =
  e_and_p |> snd |> List.iter (fun k ->
    H.remove en.t_has_reader k;
    H.remove en.t_parser_kind_nz k;
    H.remove en.t_parser_weak_kind k;
    H.remove en.t_parser_kind_is_constant_size k);
  en