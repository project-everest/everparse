(*
   Copyright 2021 Microsoft Research

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
module InterpreterTarget
open Binding
(* The abstract syntax for the code produced by 3d, targeting prelude/Interpreter.fst *)
open FStar.All
open FStar.List.Tot
module A = Ast
module T = Target
module H = Hashtable

(* The boolean value to substitute for `use_error_handler` in generated F* code:
   `true` (the dynamic error handler) when the user did not pass
   `--use_error_handler_macro`, and `false` (the C macro `EverParse3dErrorHandlerMacro`)
   when they did. *)
let use_error_handler () : ML bool =
  not (Options.get_use_error_handler_macro ())

(* --pulse: generate code against the Pulse combinator backend
   (lib/everparse/3d) instead of the Low* one (src/3d/prelude). *)
let pulse () : ML bool = Options.get_pulse ()

(* The Pulse input-stream backend module selected by --input_stream. It is
   emitted as `module B = ...` in the generated module prefix. *)
let pulse_backend_module () : ML string = Options.pulse_backend_module ()

let pulse_inst () : ML string = Options.pulse_inst ()

(* The four leading arguments of every Pulse `typ`/`dtyp`/`action` former. *)
let pulse_inst_args () : ML string =
  Printf.sprintf "B.base_t B.len_t B.pos_t %s" (pulse_inst ())

(* The per-backend `[@@CMacro] error_handler_macro`, passed to `as_validator`
   and to the probe denotations. *)
let pulse_ehm () : ML string = "B.error_handler_macro"

(* Copy buffers (and hence probes) are supported for the `buffer` backend
   only, so the copy-buffer type class instance is always the buffer one.
   These arguments must be given explicitly: nothing else in a `state_dict`
   determines the input stream types. *)
let pulse_cb_inst_args () : ML string =
  " #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t #B.input_stream_buffer #B.copy_buffer_buffer"

let pulse_is_buffer () : ML bool =
  HashingOptions.InputStreamBuffer? (Options.get_input_stream_binding ())

(* `field_ptr_after` needs the client's Peep primitive, which both `extern` and
   `static` provide -- they are the same F* development, differing only in the
   C linkage of the stream primitives, exactly as in Low*. *)
let pulse_has_field_ptr_after () : ML bool =
  match Options.get_input_stream_binding () with
  | HashingOptions.InputStreamExtern _ -> true
  | HashingOptions.InputStreamStatic _ -> true
  | _ -> false


noeq
type inv =
  | Inv_conj : inv -> inv -> inv
  | Inv_ptr  : expr -> inv
  | Inv_copy_buf: expr -> inv
  (* --pulse only: the ambient state of the external actions generated for
     output types. In Low* this is carried by the Eloc_output location alone,
     but a Pulse state_dict fuses invariant and footprint. *)
  | Inv_output : inv

noeq
type eloc =
  | Eloc_output : eloc
  | Eloc_union  : eloc -> eloc -> eloc
  | Eloc_ptr    : expr -> eloc
  | Eloc_copy_buf: e:expr { T.Identifier? (fst e) } -> eloc

noeq
type disj =
  | Disj_pair : l:eloc{ Eloc_copy_buf? l } -> eloc -> disj
  | Disj_conj : disj -> disj -> disj

let index a = option a

let disj_pair l m : index disj =
  match l, m with
  | None, i
  | i, None -> None
  | Some l, Some m -> Some (Disj_pair l m)


let subst_index (s:'a -> ML 'a) (i:index 'a) =
  match i with
  | None -> None
  | Some i -> Some (s i)

let join_index j d0 d1 =
  match d0, d1 with
  | None, d
  | d, None -> d
  | Some d0, Some d1 -> Some (j d0 d1)

let join_inv = join_index Inv_conj
let join_eloc = join_index Eloc_union
let join_disj = join_index Disj_conj  

let rec subst_inv' subst (i:inv)
  : inv
  = match i with
    | Inv_conj i j ->
      Inv_conj (subst_inv' subst i)
               (subst_inv' subst j)
    | Inv_ptr x ->
      Inv_ptr (T.subst_expr subst x)
    | Inv_copy_buf x ->
      Inv_copy_buf (T.subst_expr subst x)
    | Inv_output -> i
let subst_inv s = subst_index (subst_inv' s)

let eq_tags e e' =
  match e, e' with
  | Eloc_output, Eloc_output
  | Eloc_union _ _, Eloc_union _ _ 
  | Eloc_ptr _, Eloc_ptr _ 
  | Eloc_copy_buf _, Eloc_copy_buf _ -> true
  | _ -> false

let rec subst_eloc' subst (e:eloc)
  : ML (e':eloc { eq_tags e e' })
  = match e with
    | Eloc_output -> e
    | Eloc_union i j ->
      Eloc_union (subst_eloc' subst i)
                 (subst_eloc' subst j)
    | Eloc_ptr x -> Eloc_ptr (T.subst_expr subst x)
    | Eloc_copy_buf x ->
      let y = T.subst_expr subst x in
      if not (T.Identifier? (fst y))
      then (
        Ast.error "Unexpected non-identifier in subst_eloc" (snd x)
      )
      else
        Eloc_copy_buf y
let subst_eloc s = subst_index (subst_eloc' s)

let rec subst_disj' subst (d:disj)
  : ML disj
  = match d with
    | Disj_pair e1 e2 -> 
      Disj_pair (subst_eloc' subst e1)
                (subst_eloc' subst e2)
    | Disj_conj d1 d2 ->
      Disj_conj (subst_disj' subst d1)
                (subst_disj' subst d2)
let subst_disj s = subst_index (subst_disj' s)

noeq
type on_success =
  | On_success : bool -> on_success
  | On_success_named : A.ident -> list expr -> on_success
  | On_success_union : on_success -> on_success -> on_success

let typ_indexes = index inv & index eloc & index disj & on_success
let typ_indexes_nil : typ_indexes = None, None, None, On_success false
let typ_indexes_union (i, e, d, b) (i', e', d', b') =
  join_inv i i',
  join_eloc e e',
  join_disj d d',
  On_success_union b b'

let env = H.t A.ident' type_decl
let create_env (_:unit) : ML env = H.create 100

let rec free_vars_of_expr (e:T.expr)
  : ML (list A.ident)
  = let open T in
    match fst e with
    | Constant _ -> []
    | Identifier i -> [i]
    | App _ args -> List.collect free_vars_of_expr args
    | Record _ args -> List.collect (fun (_, e) -> free_vars_of_expr e) args

let map_index (def:'b) (f:'a -> ML 'b) (i:index 'a) : ML 'b =
  match i with
  | None -> def
  | Some i -> f i

let rec free_vars_of_inv' (i:inv)
  : ML (list A.ident)
  = match i with
    | Inv_conj i j -> free_vars_of_inv' i @ free_vars_of_inv' j
    | Inv_ptr x -> free_vars_of_expr x
    | Inv_copy_buf x -> free_vars_of_expr x
    | Inv_output -> []
let free_vars_of_inv = map_index [] free_vars_of_inv'

let rec free_vars_of_eloc' (e:eloc)
  : ML (list A.ident)
  = match e with
    | Eloc_output -> []
    | Eloc_union i j -> free_vars_of_eloc' i @ free_vars_of_eloc' j
    | Eloc_ptr x -> free_vars_of_expr x
    | Eloc_copy_buf x -> free_vars_of_expr x
let free_vars_of_eloc = map_index [] free_vars_of_eloc'

let rec free_vars_of_disj' (d:disj)
  : ML (list A.ident)
  = match d with
    | Disj_conj d0 d1 -> free_vars_of_disj' d0 @ free_vars_of_disj' d1
    | Disj_pair i j -> free_vars_of_eloc' i @ free_vars_of_eloc' j
let free_vars_of_disj = map_index [] free_vars_of_disj'

let free_vars_of_typ_indexes (i:typ_indexes) =
  let i, j, d, _ = i in
  free_vars_of_inv i @
  free_vars_of_eloc j @
  free_vars_of_disj d

let filter_args_for_inv (args:list expr)
                        (td:type_decl)
  : ML (list expr)
  = let fvs = free_vars_of_typ_indexes td.typ_indexes in
    let args =
      List.map2
        (fun (b, _) a ->
          if Some? (List.tryFind (fun j -> A.ident_name b = A.ident_name j) fvs)
          then [a]
          else [])
        td.name.td_params
        args
    in
    List.flatten args

let itype_of_ident (hd:A.ident)
  : option itype
  = match hd.v.name with
    | "UINT8" -> Some UInt8
    | "UINT16" -> Some UInt16
    | "UINT32" -> Some UInt32
    | "UINT64" -> Some UInt64
    | "UINT8BE" -> Some UInt8BE
    | "UINT16BE" -> Some UInt16BE
    | "UINT32BE" -> Some UInt32BE
    | "UINT64BE" -> Some UInt64BE
    | "unit" -> Some Unit
    | "all_bytes" -> Some AllBytes
    | "all_zeros" -> Some AllZeros
    | _ -> None

let dtyp_of_app (en: env) (hd:A.ident) (args:list T.index)
  : ML dtyp
  = match itype_of_ident hd, args with
    | Some i, [] ->
      DT_IType i

    | _ ->
      let has_action, readable = match H.try_find en hd.v with
      | None -> failwith "type not found"
      | Some td -> td.has_action, td.allow_reading
      in
      DT_App has_action readable hd
        (List.map
          (function Inl _ -> failwith "Unexpected type application"
                  | Inr e -> e)
          args)

let tag_of_parser p
  = let open T in
    match p.p_parser with
    | Parse_return _ -> "Parse_return"
    | Parse_app _ _ -> "Parse_app"
    | Parse_nlist _ _ _ -> "Parse_nlist"
    | Parse_t_at_most _ _ -> "Parse_t_at_most"
    | Parse_t_exact _ _ -> "Parse_t_exact"
    | Parse_pair _ _ _ _ _ -> "Parse_pair"
    | Parse_dep_pair _ _ _ -> "Parse_dep_pair"
    | Parse_dep_pair_with_refinement _ _ _ _ -> "Parse_dep_pair_with_refinement"
    | Parse_dep_pair_with_action _ _ _ -> "Parse_dep_pair_with_action"
    | Parse_dep_pair_with_refinement_and_action _ _ _ _ _ -> "Parse_dep_pair_with_refinement_and_action"
    | Parse_map _ _ -> "Parse_map"
    | Parse_refinement _ _ _ -> "Parse_refinement"
    | Parse_refinement_with_action _ _ _ _ -> "Parse_refinement_with_action"
    | Parse_with_dep_action _ _ _ -> "Parse_with_dep_action"
    | Parse_with_action _ _ _ -> "Parse_with_action"
    | Parse_weaken_left _ _ -> "Parse_weaken_left"
    | Parse_weaken_right _ _ -> "Parse_weaken_right"
    | Parse_if_else _ _ _ -> "Parse_if_else"
    | Parse_impos -> "Parse_impos"
    | Parse_with_comment _ _ -> "Parse_with_comment"
    | Parse_string _ _ -> "Parse_string"
    | Parse_with_probe _ _ _ _ _ _ _ _ -> "Parse_with_probe"

let as_lam (x:T.lam 'a)
  : lam 'a
  = let i =
      match fst x with
      | None -> A.(with_dummy_range (to_ident' "_"))
      | Some i -> i
    in
    i, snd x

let id_as_expr (i:A.ident) = T.mk_expr (T.Identifier i)

let rec typ_indexes_of_action (a:T.action)
  : ML typ_indexes
  = let open T in
    let of_atomic_action (a:T.atomic_action)
      : ML typ_indexes
      = match a with
        | Action_return _
        | Action_abort
        | Action_field_pos_32
        | Action_field_pos_64 -> typ_indexes_nil
        | Action_field_ptr_after _ write_to ->
          Some (Inv_ptr (id_as_expr write_to)),
          Some (Eloc_ptr (id_as_expr write_to)),
          None,
          On_success false
        | Action_field_ptr_after_with_setter _ _ _ ->
          (if pulse () then Some Inv_output else None),
          Some Eloc_output,
          None,
          On_success false
        | Action_field_ptr ->
          None, None, None, On_success true
        | Action_deref x ->
          Some (Inv_ptr (id_as_expr x)), None, None, On_success false
        | Action_assignment x _ ->
          Some (Inv_ptr (id_as_expr x)),
          Some (Eloc_ptr (id_as_expr x)),
          None,
          On_success false
        | Action_call f args ->
          (if pulse () then Some Inv_output else None),
          Some Eloc_output,
          None,
          On_success false
    in
    match a with
    | Atomic_action aa -> of_atomic_action aa
    | Action_seq hd tl
    | Action_let _ hd tl ->
      typ_indexes_union (of_atomic_action hd) (typ_indexes_of_action tl)
    | Action_ite _ a0 a1 ->
      typ_indexes_union (typ_indexes_of_action a0) (typ_indexes_of_action a1)
    | Action_act a ->
      typ_indexes_of_action a

let rec inv_copy_buf_keys (i:inv)
  : ML (list string)
  = match i with
    | Inv_conj i j -> inv_copy_buf_keys i @ inv_copy_buf_keys j
    | Inv_ptr _ -> []
    | Inv_copy_buf x -> [T.print_expr "" x]
    | Inv_output -> []

let rec typ_indexes_of_parser (en:env) (p:T.parser)
  : ML typ_indexes
  = let typ_indexes_of_parser = typ_indexes_of_parser en in
    match p.p_parser with
    | T.Parse_impos ->
      typ_indexes_nil

    | T.Parse_app hd args ->
      let dt = dtyp_of_app en hd args in
      begin
      match dt with
      | DT_IType _ ->
        typ_indexes_nil
      | DT_App _ _ hd args ->
        let td =
          match H.try_find en hd.v with
          | Some td -> td
          | _ -> failwith (Printf.sprintf "Type decl not found for %s" (A.ident_to_string hd))
        in
        let inv, eloc, disj, _ = td.typ_indexes in
        let subst =
          match T.mk_subst td.name.td_params args with
          | None -> 
            failwith (Printf.sprintf "Unexpected number of arguments to type %s" (A.ident_to_string td.name.td_name))
          | Some s -> s
        in
        subst_inv subst inv,
        subst_eloc subst eloc,
        subst_disj subst disj,
        On_success_named hd args
      end

    | T.Parse_if_else _ p q
    | T.Parse_pair _ _ p _ q ->
      typ_indexes_union (typ_indexes_of_parser p) (typ_indexes_of_parser q)

    | T.Parse_dep_pair _ p (_, q)
    | T.Parse_dep_pair_with_refinement _ p _ (_, q) ->
      typ_indexes_union (typ_indexes_of_parser p) (typ_indexes_of_parser q)

    | T.Parse_weaken_left p _
    | T.Parse_weaken_right p _
    | T.Parse_refinement _ p _
    | T.Parse_with_comment p _
    | T.Parse_nlist _ _ p
    | T.Parse_t_at_most _ p
    | T.Parse_t_exact _ p ->
      typ_indexes_of_parser p

    | T.Parse_dep_pair_with_action p (_, a) (_, q)
    | T.Parse_dep_pair_with_refinement_and_action _ p _ (_, a) (_, q) ->
      typ_indexes_union
        (typ_indexes_of_parser p)
        (typ_indexes_union
          (typ_indexes_of_action a)
          (typ_indexes_of_parser q))

    | T.Parse_with_action _ p a ->
      typ_indexes_union
        (typ_indexes_of_parser p)
        (typ_indexes_of_action a)

    | T.Parse_with_dep_action _ p (_, a) ->
      typ_indexes_union
        (typ_indexes_of_parser p)
        (typ_indexes_of_action a)

    | T.Parse_string p _ ->
      typ_indexes_nil

    | T.Parse_refinement_with_action n p f (_, a) ->
      typ_indexes_union 
        (typ_indexes_of_parser p)
        (typ_indexes_of_action a)

    | T.Parse_with_probe p _ _ _ dest _ _ _ ->
      let i, l, d, s = typ_indexes_of_parser p in 
      typ_indexes_union
           (i, l, d, s)
           (Some (Inv_copy_buf (id_as_expr dest)),
            Some (Eloc_copy_buf (id_as_expr dest)),
            disj_pair (Some (Eloc_copy_buf (id_as_expr dest))) l, 
            On_success true)

    | T.Parse_map _ _
    | T.Parse_return _ -> failwith "Unnecessary"

let typ_of_parser (en: env) : Tot (T.parser -> ML typ)
= let rec typ_of_parser (p:T.parser)
    : ML typ
  = let rec dtyp_of_parser (p:T.parser)
      : ML dtyp
      = match p.p_parser with
        | T.Parse_app hd args ->
          dtyp_of_app en hd args

        | T.Parse_weaken_left p _
        | T.Parse_weaken_right p _
        | T.Parse_with_comment p _ ->
          dtyp_of_parser p

        | _ ->
          failwith
            (Printf.sprintf "Expected a named type, got %s"
              (tag_of_parser p))
    in
    let fn = nes p.p_fieldname in
    match p.p_parser with
    | T.Parse_impos ->
      T_false fn

    | T.Parse_app _ _ ->
      T_denoted fn (dtyp_of_parser p)

    | T.Parse_pair _ p_const p q_const q ->
      T_pair (nes p.p_fieldname) p_const (typ_of_parser p) q_const (typ_of_parser q)

    | T.Parse_with_comment p c ->
      T_with_comment fn (typ_of_parser p) (String.concat "; " c)

    | T.Parse_nlist fixed_size n p ->
      T_nlist fn fixed_size n (typ_of_parser p)

    | T.Parse_t_at_most n p ->
      T_at_most fn n (typ_of_parser p)

    | T.Parse_t_exact n p ->
      T_exact fn n (typ_of_parser p)

    | T.Parse_if_else e p1 p2 ->
      T_if_else e (typ_of_parser p1) (typ_of_parser p2)

    | T.Parse_dep_pair _ p k ->
      let i, k = as_lam k in
      let d = dtyp_of_parser p in
      if allow_reader_of_dtyp d
      then
        T_dep_pair (nes p.p_fieldname)
                   d
                   (i, typ_of_parser k)
      else
        failwith "typ_of_parser: Parse_dep_pair: tag not readable"

    | T.Parse_dep_pair_with_refinement _ p r k ->
      let i, r = as_lam r in
      let j, k = as_lam k in
      let d = dtyp_of_parser p in
      if allow_reader_of_dtyp d
      then
        T_dep_pair_with_refinement fn d (i, r) (j, typ_of_parser k)
      else
        failwith "typ_of_parser: Parse_dep_pair_with_refinement: tag not readable"

    | T.Parse_dep_pair_with_action p a k ->
      let (i, k) = as_lam k in
      let d = dtyp_of_parser p in
      if allow_reader_of_dtyp d
      then
        T_dep_pair_with_action fn d (i, typ_of_parser k) (as_lam a)
      else
        failwith "typ_of_parser: Parse_dep_pair_with_action: tag not readable"

    | T.Parse_dep_pair_with_refinement_and_action _ p r a k ->
      let a = as_lam a in
      let (i, k) = as_lam k in
      let r = as_lam r in
      let d = dtyp_of_parser p in
      if allow_reader_of_dtyp d
      then
        T_dep_pair_with_refinement_and_action fn d r (i, typ_of_parser k) a
      else
        failwith "typ_of_parser: Parse_dep_pair_with_refinement_and_action: tag not readable"

    | T.Parse_with_action _ p a ->
      T_with_action fn (typ_of_parser p) a

    | T.Parse_with_dep_action _ p a ->
      let a = as_lam a in
      let d = dtyp_of_parser p in
      if allow_reader_of_dtyp d
      then
        T_with_dep_action fn d a
      else
        failwith "typ_of_parser: Parse_with_dep_action: tag not readable"

    | T.Parse_string p z ->
      let d = dtyp_of_parser p in
      if allow_reader_of_dtyp d
      then
        T_string fn d z
      else
        failwith "typ_of_parser: Parse_string: element not readable"

    | T.Parse_refinement _ p f ->
      let d = dtyp_of_parser p in
      if allow_reader_of_dtyp d
      then
        T_refine fn d (as_lam f)
      else
        failwith "typ_of_parser: Parse_refinement: element not readable"

    | T.Parse_refinement_with_action _ p f a ->
      let d = dtyp_of_parser p in
      if allow_reader_of_dtyp d
      then
        T_refine_with_action fn d (as_lam f) (as_lam a)
      else
        failwith "typ_of_parser: Parse_refinement_with_action: element not readable"

    | T.Parse_weaken_left p _
    | T.Parse_weaken_right p _ ->
      typ_of_parser p

    | T.Parse_with_probe p sz nullable probe_fn dest as_u64 init dest_sz ->
      let d = dtyp_of_parser p in
      let probed_indexes = typ_indexes_of_parser en p in
      (* A copy buffer is a keyed `state_dict` entry that the probe combinator
         makes disjoint from the state of the probed type. Two probes at
         disjoint sites may therefore share a copy buffer, but a nested probe
         may not reuse the one it is already writing into. Reject that here
         rather than letting the key-disjointness obligation fail in the
         generated F* code. *)
      let dest_key = T.print_maybe_qualified_ident "" dest in
      let probed_inv, _, _, _ = probed_indexes in
      (match probed_inv with
       | Some i ->
         if List.mem dest_key (inv_copy_buf_keys i)
         then A.error
           (Printf.sprintf
             "The copy buffer %s cannot be reused by a probe nested inside a probe that already writes into it"
             dest_key)
           dest.A.range
       | None -> ());
      T_probe_then_validate fn d sz nullable probe_fn dest as_u64 init dest_sz
        probed_indexes

    | T.Parse_map _ _
    | T.Parse_return _ -> failwith "Unnecessary"

in typ_of_parser

let rec allow_reading_of_typ (t:typ)
  : Tot bool
  =
  match t with
  | T_with_comment _ t _ ->
    allow_reading_of_typ t

  | T_denoted _ dt ->
    begin
    match dt with
    | DT_IType i -> allow_reader_of_itype i
    | DT_App has_action readable _ _ -> readable
    end

  | _ ->
    false

let rec has_action_of_typ (t:typ)
  : Tot bool
  =
  match t with
  | T_false _ -> false
  | T_with_comment _ t _ -> has_action_of_typ t
  | T_denoted _ dt ->
    begin
    match dt with
    | DT_IType i -> false
    | DT_App has_action readable _ _ -> has_action
    end
  | T_pair _ _ t1 _ t2 ->
    has_action_of_typ t1 || has_action_of_typ t2
  | T_dep_pair _ t1 (_, t2) ->
    has_action_of_dtyp t1 || has_action_of_typ t2
  | T_refine _ t _ -> has_action_of_dtyp t
  | T_refine_with_action _ _ _ _ -> true
  | T_dep_pair_with_refinement _ t _ (_, t2) -> has_action_of_dtyp t || has_action_of_typ t2
  | T_dep_pair_with_action _ _ _ _ -> true
  | T_dep_pair_with_refinement_and_action _ _ _ _ _ -> true
  | T_if_else _ t1 t2 -> has_action_of_typ t1 || has_action_of_typ t2
  | T_with_action _ _ _ -> true
  | T_with_dep_action _ _ _ -> true
  | T_drop t -> has_action_of_typ t
  | T_with_comment _ t _ -> has_action_of_typ t
  | T_nlist _ _ _ t -> has_action_of_typ t
  | T_at_most _ _ t -> has_action_of_typ t
  | T_exact _ _ t -> has_action_of_typ t
  | T_string _ t _ -> has_action_of_dtyp t
  | T_probe_then_validate _ _ _ _ _ _ _ _ _ _ -> true

let check_validity_of_typ_indexes (td:T.type_decl) indexes =
  let rec atomic_locs_of l =
    match l with
    | Eloc_output -> [l]
    | Eloc_union l1 l2 -> atomic_locs_of l1 @ atomic_locs_of l2
    | Eloc_ptr _ -> [l]
    | Eloc_copy_buf _ -> [l]
  in
  let rec valid_disj (d:disj) : ML unit =
    match d with
    | Disj_conj d1 d2 ->
      valid_disj d1;
      valid_disj d2

    | Disj_pair (Eloc_copy_buf (T.Identifier x, rx)) l2 -> 
      let l2_locs = atomic_locs_of l2 in
      if List.existsb
          (function
            | Eloc_copy_buf (T.Identifier y, ry) -> A.eq_idents x y
            | _ -> false)
          l2_locs
      then (
        A.error (Printf.sprintf "Nested mutation of the copy buffer [%s]" (T.print_ident x))
                td.decl_name.td_name.range
      )
      else ()
    
  in
  let _, _, disj, _ = indexes in
  match disj with
  | None -> ()
  | Some disj -> valid_disj disj

let translate_decls (en:env) (ds:T.decls)
  : ML (list decl)
  = List.map
        (fun d ->
          match d with
          | (T.Type_decl td, attrs) ->
            let t = typ_of_parser en td.decl_parser in
            let ar = allow_reading_of_typ t in
            let ar =
              if attrs.T.is_entrypoint
              then false
              else ar
            in
            let refined =
              if td.decl_is_enum
              then match td.decl_typ with
                   | T.TD_abbrev t ->
                     if T.T_refine? t
                     then Some t
                     else None
                   | _ -> None
              else None
            in
            let typ_indexes = typ_indexes_of_parser en td.decl_parser in
            check_validity_of_typ_indexes td typ_indexes;
            let typ =
              if attrs.T.is_entrypoint
              then T_drop t
              else t
            in
            let td =
              { name = td.decl_name;
                typ = typ;
                kind = td.decl_parser.p_kind;
                typ_indexes;
                has_action = has_action_of_typ typ;
                allow_reading = ar;
                attrs = attrs;
                enum_typ = refined
                }
            in
            H.insert en td.name.td_name.v td;
            Inr td
        | d ->
          Inl (d <: not_type_decl))
      ds

let print_ityp (i:itype) =
  match i with
  | UInt8 -> "UInt8"
  | UInt16 -> "UInt16"
  | UInt32 -> "UInt32"
  | UInt64 -> "UInt64"
  | UInt8BE -> "UInt8BE"
  | UInt16BE -> "UInt16BE"
  | UInt32BE -> "UInt32BE"
  | UInt64BE -> "UInt64BE"
  | Unit -> "Unit"
  | AllBytes -> "AllBytes"
  | AllZeros -> "AllZeros"

let print_ident (mname:string) (i:A.ident) =
  T.print_maybe_qualified_ident mname i

let print_derived_name (mname:string) (tag:string) (i:A.ident) =
  Printf.sprintf "%s%s_%s"
    (T.maybe_mname_prefix mname i)
    tag
    (T.print_ident i)

(* --pulse: the parameters of the type declaration currently being printed.

   A copy buffer, or an output pointer, that a type receives as a parameter
   cannot be keyed in the `state_dict` by a literal derived from the name of
   that parameter: the very same buffer reaches different types under
   different parameter names, and two different keys for one resource would
   defeat the whole point of the keys. So every generated definition takes one
   `Ghost.erased string` key per parameter, and the key of a dictionary leaf
   that is a parameter is that erased string rather than a literal. Callers
   pass their own key for a parameter they forward, and `Ghost.hide` of a
   literal for anything else.

   The keys are erased so that they do not survive extraction: `validate_X`
   shares the binders of `def_X`, since its type mentions the dictionary.

   This ref holds the parameters in scope. It is set by `print_binding` before
   anything mentioning a `state_dict` is printed, which is the only context in
   which the key of a leaf can refer to a parameter. *)
let pulse_kenv : ref (list string) = alloc []

let set_pulse_kenv (l:list string) : ML unit =
  pulse_kenv := l

let get_pulse_kenv () : ML (list string) =
  !pulse_kenv

let pulse_key_binder_of (p:string) : string = Printf.sprintf "k__%s" p

let pulse_in_kenv (e:string) : ML bool =
  Some? (List.Tot.find (fun (x:string) -> x = e) (get_pulse_kenv ()))

(* Keys are string literals in generated F*, so anything that is not an
   identifier (an argument may be an arbitrary expression) has to be mangled.
   Only resources -- copy buffers and output pointers -- are ever dictionary
   leaves, and those are always plain identifiers, so mangling only ever
   applies to keys that go unused. *)
let pulse_sanitize_key (e:string) : ML string =
  let ok (c:FStar.Char.char) : ML bool =
    let n = FStar.Char.int_of_char c in
    if n >= 48 && n <= 57 then true
    else if n >= 65 && n <= 90 then true
    else if n >= 97 && n <= 122 then true
    else n = 95 || n = 46 || n = 39
  in
  FStar.String.string_of_list
    (List.map (fun c -> if ok c then c else FStar.Char.char_of_int 95)
      (FStar.String.list_of_string e))

(* The key of a dictionary leaf, as it appears inside the definition. *)
let pulse_key_of (e:string) : ML string =
  if pulse_in_kenv e
  then Printf.sprintf "(FStar.Ghost.reveal %s)" (pulse_key_binder_of e)
  else Printf.sprintf "\"%s\"" (pulse_sanitize_key e)

(* The key to pass for an argument, at a use site. *)
let pulse_key_arg_of (e:string) : ML string =
  if pulse_in_kenv e
  then pulse_key_binder_of e
  else Printf.sprintf "(FStar.Ghost.hide \"%s\")" (pulse_sanitize_key e)

(* --pulse: the `state_dict` of a type declaration.

   The Low* `inv` describes exactly the set of extra resources a type needs:
   the user-provided pointers it dereferences or assigns, and the copy buffers
   it probes into. In Pulse each of these becomes a keyed entry of a
   `state_dict`, the key being the printed name of the resource, so that
   disjointness is a decidable computation on string literals rather than an
   SMT obligation about memory footprints.

   `Inv_conj` may repeat the same resource (e.g. two fields writing the same
   pointer), whereas `state_dict_prod` requires disjoint key sets, so the
   leaves are deduplicated by key before being folded into a right-nested
   product. *)
let rec pulse_state_dict_leaves (mname:string) (i:inv)
  : ML (list (string & string))
  = match i with
    | Inv_conj i j ->
      pulse_state_dict_leaves mname i @ pulse_state_dict_leaves mname j
    | Inv_ptr x ->
      let e = T.print_expr mname x in
      [e, Printf.sprintf "(state_dict_singleton %s (pts_to %s #1.0R))" (pulse_key_of e) e]
    | Inv_copy_buf x ->
      let e = T.print_expr mname x in
      [e, Printf.sprintf "(A.copy_buffer_state_dict%s %s %s)" (pulse_cb_inst_args ()) (pulse_key_of e) e]
    | Inv_output -> ["output_state", "output_state"]

let rec pulse_dedup_leaves (l:list (string & string))
  : ML (list (string & string))
  = match l with
    | [] -> []
    | (k, v) :: tl ->
      let tl = pulse_dedup_leaves tl in
      if Some? (List.tryFind (fun (k', _) -> k = k') tl)
      then tl
      else (k, v) :: tl

let rec pulse_fold_prod (l:list (string & string))
  : ML string
  = match l with
    | [] -> "state_dict_empty"
    | [(_, v)] -> v
    | (_, v) :: tl -> Printf.sprintf "(state_dict_prod %s %s)" v (pulse_fold_prod tl)

let print_state_dict (mname:string) (i:index inv)
  : ML string
  = match i with
    | None -> "state_dict_empty"
    | Some i -> pulse_fold_prod (pulse_dedup_leaves (pulse_state_dict_leaves mname i))

(* The keys of the leaves of a declaration's own dictionary, in the order in
   which `pulse_fold_prod` combines them. *)
let pulse_state_dict_keys (mname:string) (i:index inv)
  : ML (list string)
  = match i with
    | None -> []
    | Some i ->
      List.map (fun (k, _) -> pulse_key_of k)
        (pulse_dedup_leaves (pulse_state_dict_leaves mname i))

(* `state_dict_prod` requires disjoint key sets, which for the singletons the
   frontend emits is pairwise disequality of the keys. When the keys are
   literals that is decided by normalization, but a key coming from a
   parameter is opaque, so the definition takes the disequalities it needs as
   a hypothesis, and its callers discharge them from their own. *)
let rec pulse_key_distinct_conj (l:list string)
  : ML string
  = match l with
    | [] -> ""
    | [_] -> ""
    | k :: tl ->
      let here =
        List.map (fun k' -> Printf.sprintf "%s =!= %s" k k') tl
        |> String.concat " /\\ "
      in
      let rest = pulse_key_distinct_conj tl in
      if rest = "" then here else Printf.sprintf "%s /\\ %s" here rest

let pulse_keys_binder (mname:string) (i:index inv)
  : ML string
  = let c = pulse_key_distinct_conj (pulse_state_dict_keys mname i) in
    if c = ""
    then "(sq_keys_: squash True)"
    else Printf.sprintf "(sq_keys_: squash (%s))" c

let print_dtyp_at (mname:string) (d:string) (dt:dtyp) =
  match dt with
  | DT_IType i ->
    Printf.sprintf "(DT_IType %s)" (print_ityp i)

  | DT_App _ _ hd args ->
    if pulse ()
    then
      (* In Pulse, all the nodes of a type live at a single, uniform
         `state_dict`. A referenced type is defined at its own, smaller
         dictionary, so `dtyp_X` is polymorphic in the ambient dictionary
         `d` (solved by unification from the enclosing `def_X` ascription)
         and takes the weakening proof, which is a decidable computation
         over the keys. The keys of the arguments are passed explicitly: a
         resource that the referenced type receives as a parameter has to be
         keyed by whatever key the caller uses for it. *)
      let pargs = List.map (T.print_expr mname) args in
      let keys = List.map pulse_key_arg_of pargs |> String.concat " " in
      Printf.sprintf "(%s %s %s () %s ())"
        (print_derived_name mname "dtyp" hd)
        keys
        (String.concat " " pargs)
        d
    else
    Printf.sprintf "(%s %s)"
      (print_derived_name mname "dtyp" hd)
      (List.map (T.print_expr mname) args |> String.concat " ")

let print_dtyp (mname:string) (dt:dtyp) = print_dtyp_at mname "_" dt

let print_lam (mname:string) (p:'a -> ML string) (x:lam 'a) =
  Printf.sprintf "(fun %s -> %s)"
    (print_ident mname (fst x))
    (p (snd x))

let print_lam2 (mname:string) (p:'a -> ML string) (x:lam 'a) =
  Printf.sprintf "(fun _ %s -> %s)"
    (print_ident mname (fst x))
    (p (snd x))

let rec print_action (mname:string) (a:T.action)
  : ML string
  = let print_atomic_action (a:T.atomic_action)
      : ML string
      = match a with
        | T.Action_return e -> (
          match fst e with
          | T.Constant (A.Bool true) ->
            "Action_return_true"
          | _ -> 
            Printf.sprintf "(Action_return %s)"
                            (T.print_expr mname e)
        )
        | T.Action_abort ->
          "Action_abort"

        | T.Action_field_pos_64 ->
          "Action_field_pos_64"

        | T.Action_field_pos_32 ->
          if pulse ()
          then "Action_field_pos_32"
          else "(Action_field_pos_32 EverParse3d.Actions.BackendFlagValue.backend_flag_value)"

        | T.Action_field_ptr ->
          if pulse ()
          then begin
            if not (pulse_is_buffer ())
            then A.error "The field_ptr action is only supported by the buffer backend" A.dummy_range;
            "(Action_field_ptr B.field_ptr ())"
          end
          else "(Action_field_ptr EverParse3d.Actions.BackendFlagValue.backend_flag_value)"

        | T.Action_field_ptr_after sz write_to ->
          if pulse ()
          then begin
            if not (pulse_has_field_ptr_after ())
            then A.error "The field_ptr_after action is only supported by the extern and static backends" A.dummy_range;
            Printf.sprintf
              "(Action_field_ptr_after B.field_ptr_after () %s %s %s ())"
              (pulse_key_arg_of (T.print_ident write_to))
              (T.print_expr mname sz)
              (T.print_ident write_to)
          end
          else
          Printf.sprintf
            "(Action_field_ptr_after EverParse3d.Actions.BackendFlagValue.backend_flag_value %s %s)"
            (T.print_expr mname sz)
            (T.print_ident write_to)

        | T.Action_field_ptr_after_with_setter sz write_to_field write_to_obj ->
          if pulse ()
          then begin
            if not (pulse_has_field_ptr_after ())
            then A.error "The field_ptr_after action is only supported by the extern and static backends" A.dummy_range;
            Printf.sprintf
              "(Action_field_ptr_after_with_setter (B.field_ptr_after_with_setter _) () %s (%s %s))"
              (T.print_expr mname sz)
              (T.print_ident write_to_field)
              (T.print_expr mname write_to_obj)
          end
          else
          Printf.sprintf
            "(Action_field_ptr_after_with_setter EverParse3d.Actions.BackendFlagValue.backend_flag_value %s (%s %s))"
            (T.print_expr mname sz)
            (T.print_ident write_to_field)
            (T.print_expr mname write_to_obj)

        | T.Action_deref i ->
          if pulse ()
          then Printf.sprintf "(Action_deref %s %s ())"
                              (pulse_key_arg_of (print_ident mname i))
                              (print_ident mname i)
          else
          Printf.sprintf "(Action_deref %s)"
                          (print_ident mname i)

        | T.Action_assignment lhs rhs ->
          if pulse ()
          then Printf.sprintf "(Action_assignment %s %s %s ())"
                              (pulse_key_arg_of (print_ident mname lhs))
                              (print_ident mname lhs)
                              (T.print_expr mname rhs)
          else
          Printf.sprintf "(Action_assignment %s %s)"
                         (print_ident mname lhs)
                         (T.print_expr mname rhs)

        | T.Action_call hd args ->
          if pulse ()
          then Printf.sprintf "(atomic_action_call_extern (mk_action_binding (%s %s) _ ()))"
                              (print_ident mname hd)
                              (List.map (T.print_expr mname) args |> String.concat " ")
          else
          Printf.sprintf "(Action_call (mk_action_binding (%s %s)))"
                          (print_ident mname hd)
                          (List.map (T.print_expr mname) args |> String.concat " ")
    in
    match a with
    | T.Atomic_action a ->
      Printf.sprintf "(Atomic_action %s)"
                     (print_atomic_action a)
    | T.Action_seq hd tl ->
      Printf.sprintf "(Action_seq %s %s)"
        (print_atomic_action hd)
        (print_action mname tl)
    | T.Action_ite hd then_ else_ ->
      Printf.sprintf "(Action_ite %s (fun _ -> %s) (fun _ -> %s))"
        (T.print_expr mname hd)
        (print_action mname then_)
        (print_action mname else_)
    | T.Action_let i a k ->
      Printf.sprintf "(Action_let %s %s)"
        (print_atomic_action a)
        (print_lam mname (print_action mname) (i, k))
    | T.Action_act a ->
      Printf.sprintf "(Action_act %s)"
        (print_action mname a)

let rec print_typ (mname:string) (t:typ)
  : ML string
  = match t with
    | T_false fn ->
      Printf.sprintf "(T_false \"%s\")" fn

    | T_denoted fn dt ->
      Printf.sprintf "(T_denoted \"%s\" %s)"
                     fn
                     (print_dtyp mname dt)

    | T_pair fn t1_const t1 t2_const t2 ->
      Printf.sprintf "(T_pair \"%s\" %s %s %s %s)"
                     fn
                     (if t1_const then "true" else "false")
                     (print_typ mname t1)
                     (if t2_const then "true" else "false")
                     (print_typ mname t2)

    | T_dep_pair fn t k ->
      Printf.sprintf "(T_dep_pair \"%s\" %s %s)"
                     fn
                     (print_dtyp mname t)
                     (print_lam mname (print_typ mname) k)

    | T_refine fn d r ->
      Printf.sprintf "(T_refine \"%s\" %s %s)"
                     fn
                     (print_dtyp mname d)
                     (print_lam mname (T.print_expr mname) r)

    | T_refine_with_action fn d r a ->
      Printf.sprintf "(T_refine_with_action \"%s\" %s %s %s)"
                     fn
                     (print_dtyp mname d)
                     (print_lam mname (T.print_expr mname) r)
                     (print_lam mname (print_action mname) a)

    | T_dep_pair_with_refinement fn d r k ->
      Printf.sprintf "(T_dep_pair_with_refinement \"%s\" %s %s %s)"
                     fn
                     (print_dtyp mname d)
                     (print_lam mname (T.print_expr mname) r)
                     (print_lam mname (print_typ mname) k)

    | T_dep_pair_with_action fn d k a ->
      Printf.sprintf "(T_dep_pair_with_action \"%s\" %s %s %s)"
                     fn
                     (print_dtyp mname d)
                     (print_lam mname (print_typ mname) k)
                     (print_lam mname (print_action mname) a)

    | T_dep_pair_with_refinement_and_action fn d r k a ->
      Printf.sprintf "(T_dep_pair_with_refinement_and_action \"%s\" %s %s %s %s)"
                     fn
                     (print_dtyp mname d)
                     (print_lam mname (T.print_expr mname) r)
                     (print_lam mname (print_typ mname) k)
                     (print_lam mname (print_action mname) a)

    | T_if_else e t1 t2 ->
      Printf.sprintf "(T_cases %s %s %s)"
                     (T.print_expr mname e)
                     (print_typ mname t1)
                     (print_typ mname t2)

    | T_with_action fn p a ->
      Printf.sprintf "(T_with_action \"%s\" %s %s)"
                     fn
                     (print_typ mname p)
                     (print_action mname a)

    | T_with_dep_action fn d a ->
      Printf.sprintf "(T_with_dep_action \"%s\" %s %s)"
                     fn
                     (print_dtyp mname d)
                     (print_lam2 mname (print_action mname) a)

    | T_drop t ->
      Printf.sprintf "(T_drop %s)"
                     (print_typ mname t)
    
    | T_with_comment fn t c ->
      Printf.sprintf "(T_with_comment \"%s\" %s \"%s\")"
                     fn
                     (print_typ mname t)
                     c

    | T_nlist fn fixed_size n t ->
      let is_const, n =
        match T.as_constant n with
        | None -> false, n
        | Some m -> true, (T.Constant m, snd n)
      in
      let n_is_const =
        if is_const
        then
          match fst n with
          | T.Constant (A.Int _ n) -> Printf.sprintf "(Some %d)" n
          | _ -> "None"
        else "None"
      in
      Printf.sprintf "(T_nlist \"%s\" %s %s %b %s)"
                     fn
                     (T.print_expr mname n)
                     n_is_const
                     fixed_size
                     (print_typ mname t)

    | T_at_most fn n t ->
      Printf.sprintf "(T_at_most \"%s\" %s %s)"
                     fn
                     (T.print_expr mname n)
                     (print_typ mname t)

    | T_exact fn n t ->
      Printf.sprintf "(T_exact \"%s\" %s %s)"
                     fn
                     (T.print_expr mname n)
                     (print_typ mname t)

    | T_string fn d z ->
      Printf.sprintf "(T_string \"%s\" %s %s)"
                     fn
                     (print_dtyp mname d)
                     (T.print_expr mname z)

    | T_probe_then_validate fn dt sz nullable (T.Probe_action_var probe_fn) dest as_u64 init dest_sz probed_indexes ->
      if pulse ()
      then begin
        if not (pulse_is_buffer ())
        then A.error "Probes are only supported by the buffer backend under --pulse" A.dummy_range;
        let probed_inv, _, _, _ = probed_indexes in
        let es = print_state_dict mname probed_inv in
        Printf.sprintf "(t_probe_then_validate_gen %s %s %b \"%s\" %s %s %s %s %s %s %s %s () _ ())"
                     (pulse_ehm ())
                     (match sz with | A.UInt32 -> "UInt32" | A.UInt64 -> "UInt64")
                     nullable
                     fn
                     (print_ident mname init)
                     (T.print_expr mname dest_sz)
                     (T.print_expr mname probe_fn)
                     (pulse_key_arg_of (T.print_maybe_qualified_ident mname dest))
                     (T.print_maybe_qualified_ident mname dest)
                     (print_ident mname as_u64)
                     es
                     (print_dtyp_at mname es dt)
      end
      else
      Printf.sprintf "(t_probe_then_validate %s %b \"%s\" %s %s %s %s %s %s)"
                     (match sz with | A.UInt32 -> "UInt32" | A.UInt64 -> "UInt64")
                     nullable
                     fn
                     (print_ident mname init)
                     (T.print_expr mname dest_sz)
                     (T.print_expr mname probe_fn)
                     (T.print_maybe_qualified_ident mname dest)
                     (print_ident mname as_u64)
                     (print_dtyp mname dt)

    | T_probe_then_validate fn dt sz nullable probe_fn dest as_u64 init dest_sz probed_indexes ->
      if pulse ()
      then begin
        if not (pulse_is_buffer ())
        then A.error "Probes are only supported by the buffer backend under --pulse" A.dummy_range;
        let probed_inv, _, _, _ = probed_indexes in
        let es = print_state_dict mname probed_inv in
        Printf.sprintf "(t_probe_then_validate_alt_gen %s %s %b \"%s\" %s %s %s %s %s %s %s %s () _ ())"
                     (pulse_ehm ())
                     (match sz with | A.UInt32 -> "UInt32" | A.UInt64 -> "UInt64")
                     nullable
                     fn
                     (print_ident mname init)
                     (T.print_expr mname dest_sz)
                     (T.print_probe_action mname probe_fn)
                     (pulse_key_arg_of (T.print_maybe_qualified_ident mname dest))
                     (T.print_maybe_qualified_ident mname dest)
                     (print_ident mname as_u64)
                     es
                     (print_dtyp_at mname es dt)
      end
      else
      Printf.sprintf "(t_probe_then_validate_alt %s %b \"%s\" %s %s %s %s %s %s)"
                     (match sz with | A.UInt32 -> "UInt32" | A.UInt64 -> "UInt64")
                     nullable
                     fn
                     (print_ident mname init)
                     (T.print_expr mname dest_sz)
                     (T.print_probe_action mname probe_fn)
                     (T.print_maybe_qualified_ident mname dest)
                     (print_ident mname as_u64)
                     (print_dtyp mname dt)

let print_param mname (p:T.param) =
  Printf.sprintf "(%s:%s)"
    (print_ident mname (fst p))
    (T.print_typ mname (snd p))

let print_typedef_name mname (n:T.typedef_name) =
  Printf.sprintf "%s %s"
    (print_ident mname n.td_name)
    (List.map (print_param mname) n.td_params |> String.concat " ")

(* --pulse: one erased key per parameter, in parameter order. *)
let pulse_key_binders mname (ps:list T.param) : ML string =
  List.map
    (fun p ->
      Printf.sprintf "(%s: FStar.Ghost.erased string)"
        (pulse_key_binder_of (print_ident mname (fst p))))
    ps
  |> String.concat " "

let pulse_key_binder_args mname (ps:list T.param) : ML string =
  List.map (fun p -> pulse_key_binder_of (print_ident mname (fst p))) ps
  |> String.concat " "

let state_dict_of_type_decl mname (td:type_decl) : ML string =
  let inv, _, _, _ = td.typ_indexes in
  print_state_dict mname inv

let print_type_decl mname (binders:string) (td:type_decl) =
  if pulse ()
  then
    FStar.Printf.sprintf
      "[@@specialize; noextract_to \"krml\"]\n\
       noextract\n\
       let def_%s %s = ( %s <: Tot (typ %s %s %b _ _ _))\n"
        (print_ident mname td.name.td_name)
        binders
        (print_typ mname td.typ)
        (pulse_inst_args ())
        (state_dict_of_type_decl mname td)
        (use_error_handler ())
  else
  FStar.Printf.sprintf
    "[@@specialize; noextract_to \"krml\"]\n\
     noextract\n\
     let def_%s = ( %s <: Tot (typ %b _ _ _ _ _ _) by (T.norm [delta_attr [`%%specialize]; zeta; iota; primops]; T.smt()))\n"
      (print_typedef_name mname td.name)
      (print_typ mname td.typ)
      (use_error_handler ())

let print_args mname (es:list expr) =
    List.map (T.print_expr mname) es |> String.concat " "

let print_index (f: 'a -> ML string) (i:index 'a)
  : ML string
  = map_index "Trivial" (fun s -> Printf.sprintf "(NonTrivial %s)" (f s)) i

let rec print_inv' mname (i:inv)
  : ML string
  = match i with
    | Inv_conj i j -> Printf.sprintf "(A.conj_inv %s %s)" (print_inv' mname i) (print_inv' mname j)
    | Inv_ptr x -> Printf.sprintf "(A.ptr_inv %s)" (T.print_expr mname x)
    | Inv_copy_buf x -> Printf.sprintf "(A.copy_buffer_inv %s)" (T.print_expr mname x)
    | Inv_output -> "A.true_inv"
let print_inv mname = print_index (print_inv' mname)

let rec print_eloc' mname (e:eloc)
  : ML string
  = match e with
    | Eloc_output -> "output_loc" //This is a bit sketchy
    | Eloc_union i j -> Printf.sprintf "(A.eloc_union %s %s)" (print_eloc' mname i) (print_eloc' mname j)
    | Eloc_ptr x -> Printf.sprintf "(A.ptr_loc %s)" (T.print_expr mname x)
    | Eloc_copy_buf x -> Printf.sprintf "(A.copy_buffer_loc %s)" (T.print_expr mname x)
let print_eloc mname = print_index (print_eloc' mname)

let rec print_disj' mname (d:disj)
  : ML string
  = match d with
    | Disj_pair i j -> Printf.sprintf "(NonTrivial <| A.disjoint %s %s)" (print_eloc' mname i) (print_eloc' mname j)
    | Disj_conj i j -> Printf.sprintf "(join_disj %s %s)" (print_disj' mname i) (print_disj' mname j)
let print_disj mname (i:index disj) =
  match i with
  | None -> "Trivial"
  | Some i -> print_disj' mname i

let print_td_iface_pulse is_entrypoint mname root_name binders args
                         sd ha ar pk_wk pk_nz =
  let ar = if is_entrypoint then false else ar in
  let kind_t =
    Printf.sprintf "[@@noextract_to \"krml\"]\n\
                    inline_for_extraction\n\
                    noextract\n\
                    val kind_%s : P.parser_kind %b P.%s"
      root_name
      pk_nz
      pk_wk
  in
  let def'_t =
    Printf.sprintf "[@@noextract_to \"krml\"]\n\
                    noextract\n\
                    val def'_%s %s: typ %s %s %b kind_%s %b %b"
      root_name
      binders
      (pulse_inst_args ())
      sd
      (use_error_handler ())
      root_name
      ha
      ar
  in
  let validator_t =
    Printf.sprintf "val validate_%s %s : validator_of %s %b (def'_%s %s)"
      root_name
      binders
      sd
      (use_error_handler ())
      root_name args
  in
  let dtyp_t =
    Printf.sprintf "[@@specialize; noextract_to \"krml\"]\n\
                    noextract\n\
                    val dtyp_%s %s (d: state_dict) (sq: squash (state_dict_weaken_prop %s d))\n\
                      : dtyp %s d %b kind_%s %b %b"
      root_name
      binders
      sd
      (pulse_inst_args ())
      (use_error_handler ())
      root_name
      ha
      ar
  in
  String.concat "\n\n" [kind_t; def'_t; validator_t; dtyp_t]

let print_td_iface is_entrypoint mname root_name binders args
                   inv eloc disj ha ar pk_wk pk_nz =
  let ar = if is_entrypoint then false else ar in
  let kind_t =
    Printf.sprintf "[@@noextract_to \"krml\"]\n\
                    inline_for_extraction\n\
                    noextract\n\
                    val kind_%s : P.parser_kind %b P.%s"
      root_name
      pk_nz
      pk_wk
  in
  let def'_t =
    Printf.sprintf "[@@noextract_to \"krml\"]\n\
                    noextract\n\
                    val def'_%s %s: typ %b kind_%s %s %s %s %b %b"
      root_name
      binders
      (use_error_handler ())
      root_name
      inv disj eloc
      ha
      ar
  in
  let validator_t =
    Printf.sprintf "val validate_%s %s : validator_of %b (def'_%s %s)"
      root_name
      binders
      (use_error_handler ())
      root_name args
  in
  let dtyp_t =
    Printf.sprintf "[@@specialize; noextract_to \"krml\"]\n\
                    noextract\n\
                    val dtyp_%s %s : dtyp_of %b (def'_%s %s)"
      root_name
      binders
      (use_error_handler ())
      root_name args
  in
  String.concat "\n\n" [kind_t; def'_t; validator_t; dtyp_t]

let print_binders mname binders =
    List.map (print_param mname) binders |>
    String.concat " "

let print_binders_as_args mname binders =
    List.map (fun (i, _) -> print_ident mname i) binders |>
    String.concat " "

// This large ML pretty-printer builds its result through ~20 chained
// `let` bindings, so its (trivial) verification condition is a deep
// continuation-passing term. The whole query verifies using ~8 rlimit,
// but the default budget of 5 makes F* cancel it and retry by splitting,
// and the split subquery then diverges into a quantifier cascade over the
// effect continuations ("incomplete quantifiers"). Raising the budget lets
// the whole query succeed in one shot, avoiding the split entirely.
#push-options "--z3rlimit 32"
let print_binding mname (td:type_decl)
: ML (string & string)
= let tdn = td.name in
  let k = td.kind in
  let typ = td.typ in
  let root_name = print_ident mname tdn.td_name in
  let print_binders = print_binders mname in
  let print_args = print_binders_as_args mname in
  (* Record the parameters in scope before printing anything that mentions a
     `state_dict`: a leaf that is a parameter is keyed by that parameter's
     erased key rather than by a literal. *)
  let _ = set_pulse_kenv (List.map (fun p -> print_ident mname (fst p)) tdn.td_params) in
  let binders, args =
    if pulse ()
    then
      let inv, _, _, _ = td.typ_indexes in
      Printf.sprintf "%s %s %s"
        (pulse_key_binders mname tdn.td_params)
        (print_binders tdn.td_params)
        (pulse_keys_binder mname inv),
      Printf.sprintf "%s %s sq_keys_"
        (pulse_key_binder_args mname tdn.td_params)
        (print_args tdn.td_params)
    else print_binders tdn.td_params, print_args tdn.td_params
  in
  let def = print_type_decl mname binders td in
  let weak_kind = A.print_weak_kind k.pk_weak_kind in
  let pk_of_binding =
      (* The kind expression is a nest of `and_then_kind`/`glb` applications,
         each of which mentions its arguments several times. Left unreduced,
         F* extraction unfolds them and the term grows exponentially with the
         nesting depth. Reduce the nest to a literal record here. *)
      let kind_expr =
        Printf.sprintf "coerce (_ by (T.norm [delta_only [`%%weak_kind_glb]; zeta; iota; primops]; T.trefl())) %s"
          (T.print_kind mname k)
      in
      let kind_expr =
        if pulse ()
        then Printf.sprintf "norm [delta_namespace [\"EverParse3d\"; \"LowParse\"]; zeta; iota; primops] (%s)" kind_expr
        else kind_expr
      in
      Printf.sprintf "[@@noextract_to \"krml\"]\n\
                    inline_for_extraction noextract\n\
                    let kind_%s : P.parser_kind %s %s = %s\n"
        root_name
        (string_of_bool k.pk_nz)
        weak_kind
        kind_expr
  in
  let inv, eloc, disj =
    let inv, eloc, disj, _ = td.typ_indexes in
    print_inv mname inv,
    print_eloc mname eloc,
    print_disj mname disj
  in
  let sd = state_dict_of_type_decl mname td in
  let def' =
    if pulse ()
    then
      Printf.sprintf
        "[@@specialize; noextract_to \"krml\"]\n\
          noextract\n\
          let def'_%s %s\n\
            : typ %s %s %b kind_%s %b %b\n\
            = coerce (_ by (coerce_validator [`%%kind_%s])) (def_%s %s)"
          root_name
          binders
          (pulse_inst_args ())
          sd
          (use_error_handler ())
          root_name
          td.has_action
          td.allow_reading
          root_name
          root_name
          args
    else
    Printf.sprintf
      "[@@specialize; noextract_to \"krml\"]\n\
        noextract\n\
        let def'_%s %s\n\
          : typ %b kind_%s %s %s %s %b %b\n\
          = coerce (_ by (coerce_validator [`%%kind_%s])) (def_%s %s)"
        root_name
        binders
        (use_error_handler ())
        root_name
        inv disj eloc
        td.has_action
        td.allow_reading
        root_name
        root_name
        args
  in
  let as_type_or_parser tag =
      Printf.sprintf "[@@noextract_to \"krml\"]\n\
                      noextract\n
                      let %s_%s %s = (as_%s (def'_%s %s))"
        tag
        root_name
        binders
        tag
        root_name
        args
  in
  let validate_binding =
    let attribs =
      // if tdn.td_noextract
      // then "[@@ specialize; noextract_to \"krml\"]\nnoextract\ninline_for_extraction"
      // else 
      (
        let cinline =
          if td.name.td_entrypoint
          || td.attrs.is_exported
          then ""
          else "; CInline"
        in
        Printf.sprintf "[@@normalize_for_extraction specialization_steps%s]" cinline
      )
    in
    if pulse ()
    then
      Printf.sprintf "%s\n\
                      let validate_%s %s = as_validator %s \"%s\" (def'_%s %s)\n"
                      attribs
                      root_name
                      binders
                      (pulse_ehm ())
                      root_name
                      root_name
                      args
    else
    Printf.sprintf "%s\n\
                    let validate_%s %s = as_validator \"%s\" (def'_%s %s)\n"
                    attribs
                    root_name
                    binders
                    root_name
                    root_name
                    args
  in
  let dtyp : string =
    let reader =
      if td.allow_reading
      then Printf.sprintf "(Some (as_reader (def_%s %s)))"
                        root_name
                        args
      else "None"
    in
    let coerce_validator =
      Printf.sprintf "(T.norm [delta_only [`%%parser_%s; `%%type_%s; `%%coerce]]; T.trefl())"
        root_name
        root_name
    in
    if pulse ()
    then
      Printf.sprintf "[@@specialize; noextract_to \"krml\"]\n\
                        noextract\n\
                        let dtyp_%s %s (d: state_dict) (sq: squash (state_dict_weaken_prop %s d))\n\
                          : dtyp %s d %b kind_%s %b %b\n\
                          = mk_dtyp_app\n\
                                    %s\n\
                                    d\n\
                                    %b\n\
                                    kind_%s\n\
                                    (type_%s %s)\n\
                                    (coerce (_ by (T.norm [delta_only [`%%type_%s]]; T.trefl())) (parser_%s %s))\n\
                                    %s\n\
                                    %b\n\
                                    %b\n\
                                    (A.validate_weaken_gen \"%s\" %b ((coerce (_ by %s) (validate_%s %s)) <: A.validate_with_action_t #B.base_t #B.len_t #B.pos_t #%s (parser_%s %s) %s %b %b %b) d sq)\n\
                                    (_ by (T.norm [delta_only [`%%Some?]; iota]; T.trefl()))\n"
                      root_name binders sd
                      (pulse_inst_args ())
                      (use_error_handler ())
                      root_name td.has_action td.allow_reading
                      (pulse_inst ())
                      (use_error_handler ())
                      root_name
                      root_name args
                      root_name
                      root_name args
                      reader
                      td.has_action
                      td.allow_reading
                      root_name
                      td.allow_reading
                      coerce_validator root_name args
                      (pulse_inst ())
                      root_name args
                      sd
                      td.has_action
                      td.allow_reading
                      (use_error_handler ())
    else
    Printf.sprintf "[@@specialize; noextract_to \"krml\"]\n\
                      noextract\n\
                      let dtyp_%s %s\n\
                        : dtyp %b kind_%s %b %b %s %s %s\n\
                        = mk_dtyp_app\n\
                                  %b\n\
                                  kind_%s\n\
                                  %s\n\
                                  %s\n\
                                  %s\n\
                                  (type_%s %s)\n\
                                  (coerce (_ by (T.norm [delta_only [`%%type_%s]]; T.trefl())) (parser_%s %s))\n\
                                  %s\n\
                                  %b\n\
                                  %b\n\
                                  (coerce (_ by %s) (validate_%s %s))\n\
                                  (_ by (T.norm [delta_only [`%%Some?]; iota]; T.trefl()))\n"
                      root_name binders
                      (use_error_handler ())
                      root_name td.has_action td.allow_reading
                      inv disj eloc
                      (use_error_handler ())
                      root_name
                      inv disj eloc
                      root_name args
                      root_name
                      root_name args
                      reader
                      td.has_action
                      td.allow_reading
                      coerce_validator root_name args
  in
  let enum_typ_of_binding =
    match td.enum_typ with
    | None -> ""
    | Some t ->
      Printf.sprintf "let %s = %s\n"
         root_name
         (T.print_typ mname t)
  in
  let impl =
    String.concat "\n"
      [def;
      pk_of_binding;
      def';
      (as_type_or_parser "type");
      (as_type_or_parser "parser");
      validate_binding;
      dtyp;
      enum_typ_of_binding]
  in
  // impl, ""
  if Some? td.enum_typ
  && (td.name.td_entrypoint || td.attrs.is_exported)
  then "", impl //exported enums are fully revealed
  else if td.name.td_entrypoint
      || td.attrs.is_exported
  then
    let iface =
      if pulse ()
      then
        print_td_iface_pulse td.name.td_entrypoint
                    mname root_name binders args
                    sd td.has_action td.allow_reading
                    weak_kind k.pk_nz
      else
      print_td_iface td.name.td_entrypoint
                    mname root_name binders args
                    inv eloc disj td.has_action td.allow_reading
                    weak_kind k.pk_nz
    in
    impl, iface
  else impl, ""
#pop-options

let print_decl mname (d:decl)
  : ML (string & string) =
  match d with
  | Inl d ->
    begin
    match fst d with
    | T.Assumption _ -> T.print_assumption mname d, ""
    | T.Definition _ -> "", T.print_definition mname d
    | T.Probe_function id params body ->
      //Fix `use_error_handler` on the emitted probe monad value to the
      //compile-time boolean chosen by --use_error_handler_macro, so the
      //probe function (which may be extracted as a standalone, shared
      //function, e.g. for type-specialized/coerce probes) either takes
      //the error-handler callback (dynamic) or drops it in favor of the
      //EVERPARSE_ERROR_HANDLER_MACRO C macro, consistently with the
      //validators that consume it.
      let impl =
        if pulse ()
        then
          Printf.sprintf "[@@ normalize_for_extraction specialization_steps]\nlet %s %s = probe_action_as_probe_m #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t #B.input_stream_buffer #B.copy_buffer_buffer #%b %s <| %s\n\n"
            (T.print_ident id)
            (T.print_params mname params)
            (use_error_handler ())
            (pulse_ehm ())
            (T.print_probe_action mname body)
        else
          Printf.sprintf "[@@ normalize_for_extraction specialization_steps]\nlet %s %s = probe_action_as_probe_m #%b <| %s\n\n"
            (T.print_ident id)
            (T.print_params mname params)
            (use_error_handler ())
            (T.print_probe_action mname body)
      in
      impl, ""
    | _ -> "", ""
    end
  | Inr td -> print_binding mname td

let rec unzip (x: list ('a & 'b))
  : list 'a & list 'b
  = match x with
    | [] -> [], []
    | (x,y)::tl ->
      let xs, ys = unzip tl in
      x::xs, y::ys

let print_decls en mname tds =
  let impl, iface =
    let impls, ifaces =
      List.map (print_decl mname) tds |>
      List.unzip
    in
    String.concat "\n\n" impls,
    String.concat "\n\n" ifaces
  in
  impl, iface
