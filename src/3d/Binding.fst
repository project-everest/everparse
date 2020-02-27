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
module Binding

(*
  This module implements a pass over the source AST
     -- checking that all names are properly bound
     -- well-typed
     -- computing the size of types
     -- computing which fields are dependent on others
*)
open FStar.Mul
open Ast
open FStar.All
module H = Hashtable

/// Generation of unique names for fields:
noeq
type field_num_ops_t = {
  next : (option ident & string) -> ML field_num; //generate an identifier for a field in a struct
  lookup : field_num -> ML (option (option ident & string)); //look up the identifier
  all_nums : unit -> ML (list (field_num & option ident & string)) //retrieve a table of identifier/field-name mappings
}

#push-options "--warn_error -272" //top-level effect; ok
let field_num_ops : field_num_ops_t =
  let open FStar.ST in
  let h : H.t field_num (option ident & string) = H.create 100 in
  let ctr : ref field_num = alloc 1 in
  let max_field_num = pow2 16 in
  let next s
    : ML field_num
    = let x = !ctr in
      H.insert h x s;
      begin
      if x + 1 = max_field_num
      then failwith "Exhausted field numbers"
      else ctr := x + 1
      end;
      x
  in
  let lookup (f:field_num)
    : ML (option (option ident & string))
    = H.try_find h f
  in
  let all_nums () =
    let entries = H.fold (fun k (i, s) out -> (k, i, s) :: out) h [] in
    List.sortWith #(field_num & _ & _) (fun (k, _, _) (k', _, _) -> k - k') entries
  in
  {
    next = next;
    lookup = lookup;
    all_nums = all_nums
  }
#pop-options

let field_error_code_variable_name_of_field
  (x: (option ident & string))
: Tot ident
= let (o, name) = x in
  match o with
  | None -> with_dummy_range name
  | Some this ->
    with_dummy_range (this.v ^ "__" ^ name)

let all_nums = field_num_ops.all_nums

let lookup_field_num x =
  match field_num_ops.lookup x with
  | None -> None
  | Some y -> Some (field_error_code_variable_name_of_field y)

/// Computed attributes for a decl:
///    -- its size in bytes
///    -- whether or not it ends with a variable-length field (suffix)
///    -- whether or not its validator may fail
///    -- whether the type is an integral type, i.e., can it be decomposed into bitfields
type decl_attributes = {
  size:size;
  has_suffix:bool;
  may_fail:bool;
  integral:bool;
  has_reader:bool;
  parser_kind_nz:option bool
}

noeq
type macro_signature = {
  macro_arguments_t: list typ;
  macro_result_t: typ
}

let nullary_macro t = { macro_arguments_t = []; macro_result_t = t }

(* Type-checking environments *)

/// global_env maps top-level identifiers to their corresponding declaration
///  -- maps type identifiers to decl_attributes
///  -- maps macro names to their types
let global_env = H.t ident' (decl & either decl_attributes macro_signature)

/// Maps locally bound names, i.e., a field name to its type
///  -- the bool signifies that this identifier has been used, and is
///     therefore marked as a dependent field
let local_env = H.t ident' (ident' & typ & bool)

/// `env` includes both a global and local env, together with a
/// binding for the `this` variable (bound to the name of a type) in
/// the current scope
noeq
type env = {
  this: option ident;
  locals: local_env;
  globals: global_env
}

let mk_env (g:global_env) =
  { this = None;
    locals = H.create 10;
    globals = g }

let params_of_decl (d:decl) : list param =
  match d.v with
  | Define _ _ _
  | TypeAbbrev _ _
  | Enum _ _ _ -> []
  | Record _ params _ _
  | CaseType _ params _ -> params

let check_shadow (e:H.t ident' 'a) (i:ident) (r:range) =
  match H.try_find e i.v with
  | Some j ->
    let msg = Printf.sprintf "Declaration %s clashes with previous declaration" i.v in
    error msg i.range
  | _ -> ()

let typedef_names (d:decl) : option typedef_names =
  match d.v with
  | Record td _ _ _
  | CaseType td _ _ -> Some td
  | _ -> None

let format_identifier (e:env) (i:ident) : ML ident =
  let j =
    match String.list_of_string i.v with
    | [] ->
      failwith "Impossible: empty identifier"
    | c0::cs ->
      if FStar.Char.lowercase c0 = c0
      then i //it starts with a lowercase symbol; that's ok
      else //otherwise, add an underscore
           {i with v =  Ast.reserved_prefix ^ i.v}
  in
  match H.try_find e.globals j.v, H.try_find e.locals j.v with
  | None, None -> j
  | _ ->
    let msg = Printf.sprintf
      "This name (%s) starts will clash with another name in scope (%s) as it is translated. \
       Please rename it"
       i.v j.v in
    error msg i.range

let add_global (e:global_env) (i:ident) (d:decl) (t:either decl_attributes macro_signature) : ML unit =
  check_shadow e i d.range;
  let env = mk_env e in
  let i' = format_identifier env i in
  H.insert e i.v (d, t);
  H.insert e i'.v (d, t);
  match typedef_names d with
  | None -> ()
  | Some td ->
    if td.typedef_abbrev.v <> i.v
    then begin
      check_shadow e td.typedef_abbrev d.range;
      let abbrev = format_identifier env td.typedef_abbrev in
      H.insert e td.typedef_abbrev.v (d, t);
      H.insert e abbrev.v (d, t)
    end

let add_local (e:env) (i:ident) (t:typ) : ML unit =
  check_shadow e.globals i t.range;
  check_shadow e.locals i t.range;
  let i' = format_identifier e i in
  H.insert e.locals i.v (i'.v, t, false);
  H.insert e.locals i'.v (i'.v, t, false)

let lookup (e:env) (i:ident) : ML (either typ (decl & either decl_attributes macro_signature)) =
  match H.try_find e.locals i.v with
  | Some (_, t, true) ->
    Inl t
  | Some (j, t, false) ->  //mark it as used
    H.remove e.locals i.v;
    H.insert e.locals i.v (j, t, true);
    Inl t
  | None ->
    match H.try_find e.globals i.v with
    | Some d -> Inr d
    | None -> error (Printf.sprintf "Variable %s not found" i.v) i.range

let remove_local (e:env) (i:ident) : ML unit =
  match H.try_find e.locals i.v with
  | Some (j, _, _) ->
    H.remove e.locals i.v;
    H.remove e.locals j
  | _ -> ()

let resolve_typedef_abbrev (env:env) (i:ident) =
    match lookup env i with
    | Inr ({v=Record names _ _ _}, _)
    | Inr ({v=CaseType names _ _}, _) ->
      names.typedef_name
    | _ -> i

let lookup_expr_name (e:env) (i:ident) : ML typ =
  match lookup e i with
  | Inl t -> t
  | Inr (_, Inr ({ macro_arguments_t=[]; macro_result_t=t })) -> t
  | Inr _ ->
    error (Printf.sprintf "Variable %s is not an expression identifier" i.v) i.range

let lookup_macro_name (e:env) (i:ident) : ML macro_signature =
  match lookup e i with
  | Inr (_, Inr m) -> m
  | _ -> error (Printf.sprintf "%s is an unknown operator" i.v) i.range

let try_lookup_enum_cases (e:env) (i:ident)
  : ML (option (list ident & typ))
  = match lookup e i with
    | Inr ({v=Enum t _ tags}, _) ->
      Some (Desugar.check_desugared_enum_cases tags, t)
    | _ -> None

let lookup_enum_cases (e:env) (i:ident)
  : ML (list ident & typ)
  = match try_lookup_enum_cases e i with
    | Some (tags, t) -> tags, t
    | _ -> error (Printf.sprintf "Type %s is not an enumeration" i.v) i.range

let is_used (e:env) (i:ident) : ML bool =
  match H.try_find e.locals i.v with
  | Some (_, t, b) -> b
  | _ ->  error (Printf.sprintf "Variable %s not found" i.v) i.range

let type_of_integer_type = function
  | UInt8  -> tuint8
  | UInt16 -> tuint16
  | UInt32 -> tuint32
  | UInt64 -> tuint64

let type_of_constant (c:constant) : typ =
  match c with
  | Unit -> tunit
  | Int UInt8 i -> tuint8
  | Int UInt16 i -> tuint16
  | Int UInt32 i -> tuint32
  | Int UInt64 i -> tuint64
  | XInt x -> tuint32
  | Bool _ -> tbool

let size_of_typ (env:env) (t:typ) : ML size =
  match t.v with
  | Type_app hd _ ->
    begin
    match lookup env hd with
    | Inr (_, Inl attrs) -> attrs.size
    | _ -> error (Printf.sprintf "Type %s not found" hd.v) t.range
    end
  | Pointer _ -> 4 //TODO

let typ_has_suffix env (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> false
  | Type_app hd _ ->
    match lookup env hd with
    | Inr (d, Inl attrs) -> attrs.has_suffix
    | _ -> false

let parser_may_fail (env:env) (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> true
  | Type_app hd _ ->
    match lookup env hd with
    | Inr (d, Inl attrs) -> attrs.may_fail
    | _ -> false

let typ_is_integral env (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> false
  | Type_app hd _ ->
    match lookup env hd with
    | Inr (d, Inl attrs) -> attrs.integral
    | _ -> false

let has_reader (env:global_env) (id:ident) : ML bool =
  match H.try_find env id.v with
  | Some (_, Inl attrs) -> attrs.has_reader
  | _ -> false

let parser_kind_nz (env:global_env) (id:ident) : ML (option bool) =
  match H.try_find env id.v with
  | Some (_, Inl attrs) -> attrs.parser_kind_nz
  | _ -> None

let has_suffix (env:global_env) (id:ident) : ML bool =
  match H.try_find env id.v with
  | Some (_, Inl attrs) -> attrs.has_suffix
  | _ -> false

let typ_has_reader env (t:typ) : ML bool =
  match t.v with
  | Pointer _ -> false
  | Type_app hd _ ->
    has_reader env.globals hd

let rec value_of_const_expr (env:env) (e:expr) : ML (option (either bool (integer_type & int))) =
  match e.v with
  | Constant (Int t n) -> Some (Inr (t, n))
  | Constant (Bool b) -> Some (Inl b)
  | App op [e1; e2] ->
    let v1 = value_of_const_expr env e1 in
    let v2 = value_of_const_expr env e2 in
    begin
    match op, v1, v2 with
    | Plus, Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 + n2))
    | Minus, Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 - n2))
    | Mul, Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 * n2))
    | Division, Some (Inr (t1, n1)), Some (Inr (t2, n2)) ->
      if n2 = 0
      then error ("Division by zero in constant expression") e2.range
      else Some (Inr (integer_type_lub t1 t2, n1 / n2))
    | GT, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 > n2))
    | LT, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 < n2))
    | GE, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 >= n2))
    | LE, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 <= n2))
    | And, Some (Inl b1), Some (Inl b2) -> Some (Inl (b1 && b2))
    | Or, Some (Inl b1), Some (Inl b2) -> Some (Inl (b1 || b2))
    | _ -> None
    end
  | App Not [e] ->
    let v = value_of_const_expr env e in
    begin
    match v with
    | Some (Inl b) -> Some (Inl (not b))
    | _ -> None
    end
  | App SizeOf [{v=Identifier t}] ->
    begin
    let n = size_of_typ env (with_range (Type_app t []) t.range) in
    Some (Inr (UInt32, n))
    end
  | App (Cast _ t) [e] ->
    let v = value_of_const_expr env e in
    begin
    match v with
    | Some (Inr (_, n)) ->
      Some (Inr (t, n))
    | _ -> None
    end
  | _ -> None

let map_opt (f:'a -> ML 'b) (o:option 'a) : ML (option 'b) =
  match o with
  | None -> None
  | Some x -> Some (f x)

let rec unfold_typ_abbrevs (env:env) (t:typ) : ML typ =
  match t.v with
  | Type_app hd [] -> //type abbreviations are not parameterized
    begin
    match lookup env hd with
    | Inr (d, _) ->
      begin
      match d.v with
      | TypeAbbrev t _ -> unfold_typ_abbrevs env t
      | Enum t _ _ -> unfold_typ_abbrevs env t
      | _ -> t
      end
    | _ -> t
    end
  | _ -> t

let eq_typ env t1 t2 =
  if Ast.eq_typ t1 t2 then true
  else Ast.eq_typ (unfold_typ_abbrevs env t1) (unfold_typ_abbrevs env t2)

let eq_typs env ts =
  List.for_all (fun (t1, t2) -> eq_typ env t1 t2) ts

let rec check_typ (pointer_ok:bool) (env:env) (t:typ)
  : ML unit
  = match t.v with
    | Pointer t0 ->
      if pointer_ok then check_typ pointer_ok env t0
      else error (Printf.sprintf "Pointer types are not permissible here; got %s" (print_typ t)) t.range

    | Type_app s es ->
      match lookup env s with
      | Inl _ ->
        error (Printf.sprintf "%s is not a type" s.v) s.range

      | Inr (d, _) ->
        let params = params_of_decl d in
        if List.length params <> List.length es
        then error (Printf.sprintf "Not enough arguments to %s" s.v) s.range;
        let _ =
          List.map2 (fun (t, _, _) e ->
            let e, t' = check_expr env e in
            if not (eq_typ env t t')
            then error "Argument type mismatch" e.range;
            e)
            params
            es
        in
        ()

and check_expr (env:env) (e:expr)
  : ML (expr & typ)
  = let w e' = with_range e' e.range in
    match e.v with
    | Constant c ->
      e, type_of_constant c

    | Identifier i ->
      let t = lookup_expr_name env i in
      e, t

    | This ->
      error "`this` is not a valid expression" e.range

    | App (Cast _ to) [n] ->
      let n, from = check_expr env n in
      begin
      if not (typ_is_integral env from)
      then error (Printf.sprintf "Casts are only supported on integral types; %s is not integral"
                    (print_typ from)) e.range
      else match from.v with
           | Type_app i _ ->
             let from_t = as_integer_typ i in
             if integer_type_lub to from_t <> to
             then error (Printf.sprintf "Only widening casts are supported; casting %s to %s loses precision"
                                (print_typ from)
                                (print_integer_type to))
                        e.range
             else
              let e = {e with v = App (Cast (Some from_t) to) [n]} in
              let t = type_of_integer_type to in
              Options.debug_print_string
                (Printf.sprintf "--------------- %s has type %s\n"
                             (print_expr e)
                             (print_typ t));
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
      | Inr ({v=Enum _ _ _}, _)
      | Inr ({v=Record _ _ _ _ }, _)
      | Inr ({v=CaseType _ _ _}, _)
      | Inr (_, Inl _) ->  //has decl-attributes
        e, tuint32
      | _ ->
        error "`sizeof` applied to a non-sized-typed" r
      end

    | App (Ext s) es ->
      let m = lookup_macro_name env (with_range s e.range) in
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

        | _ ->
          error "Not a unary op" e1.range
        end

      | [(e1,t1);(e2,t2)] ->
        begin
        match op with
        | Eq
        | Neq ->
          if not (eq_typ env t1 t2)
          then error
                 (Printf.sprintf "Equality on unequal types: %s and %s"
                   (print_typ t1)
                   (print_typ t2))
               e.range;
          w (App op [e1; e2]), tbool

        | And
        | Or ->
          if not (eq_typs env [(t1,tbool); (t2,tbool)])
          then error "Binary boolean op on non booleans" e.range;
          w (App op [e1; e2]), tbool

        | Plus
        | Minus
        | Mul
        | Division ->
          if not (eq_typs env [(t1,t2)])
          then error (Printf.sprintf "Binary integer operator (%s) on non-equal types: %s and %s"
                                     (print_expr e)
                                     (print_typ t1)
                                     (print_typ t2))
                     e.range;
          if not (typ_is_integral env t1)
          then error "Binary integer op on non-integral type" e.range;
          w (App op [e1; e2]), t1


        | LT
        | GT
        | LE
        | GE ->
          if not (eq_typs env [(t1,t2)])
          then error "Binary integer operator on non-equal types" e.range;
          if not (typ_is_integral env t1)
          then error "Binary integer op on non-integral type" e.range;
          w (App op [e1; e2]), tbool

        | _ ->
          error "Not a binary op" e.range
        end

      | [(e1, t1); (e2, t2); (e3, t3)] ->
        begin
        match op with
        | IfThenElse ->
          if not (eq_typ env t1 tbool)
          then error "If-then-else expects a boolean guard" e1.range;
          if not (eq_typ env t2 t3)
          then error "then- and else-branch do not have the same type" e.range;
          w (App IfThenElse [e1;e2;e3]), t2

        | BitFieldOf n ->
          let size = 8 * size_of_typ env t1 in
          if n <> size
          then error
                 (Printf.sprintf "BitFieldOf size %d is not equal to %d, i.e., the bit size %s"
                   n size (print_expr e1))
                 e1.range;
          begin
          match e2.v, e2.v with
          | Constant (Int UInt32 from), (Constant (Int UInt32 to)) ->
            if not
               (from <= size
            && from <= to
            && to <= size)
            then error "bitfield-of expresssions is out of bounds" e.range;
            w (App (BitFieldOf n) [e1; e2; e3]), t1
          | _ ->
           error "bitfield-of with non-32-bit-consant indices" e.range
          end

        | _ ->
          error "Unexpected arity" e.range
        end
      | _ -> error "Unexpected arity" e.range

let rec check_field_action (env:env) (f:field) (a:action)
  : ML (action & typ)
  = let check_atomic_action env (r:range) (a:atomic_action)
      : ML (atomic_action & typ)
      = match a with
        | Action_return e ->
          let e, t = check_expr env e in
          Action_return e, t

        | Action_abort ->
          Action_abort, tunit

        | Action_field_pos ->
          Action_field_pos, tuint32

        | Action_field_ptr ->
          Action_field_ptr, with_range (Pointer f.v.field_type) r

        | Action_deref i ->
          let t = lookup_expr_name env i in
          begin
          match t.v with
          | Pointer t -> Action_deref i, t
          | _ -> error "Dereferencing a non-pointer" i.range
          end

        | Action_assignment lhs rhs ->
          let t = lookup_expr_name env lhs in
          let rhs, t' = check_expr env rhs in
          begin
          match t.v with
          | Pointer t0 ->
            if not (eq_typ env t0 t')
            then warning (Printf.sprintf
                          "Assigning to pointer %s of type %s a value of incompatible type %s"
                          (print_ident lhs)
                          (print_typ t)
                          (print_typ t'))
                       rhs.range;
            Action_assignment lhs rhs, tunit
          | _ ->
            error "Assigning to a non-pointer" lhs.range
          end

        | Action_call f args ->
          error "Extern calls are not yet supported" r
    in
    match a.v with
    | Atomic_action aa ->
      let aa, t = check_atomic_action env a.range aa in
      { a with v=Atomic_action aa }, t

    | Action_seq a0 as ->
      let a0, _ = check_atomic_action env a.range a0 in
      let as, t = check_field_action env f as in
      { a with v=Action_seq a0 as }, t

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
      || not eq_t_unit
      then error (Printf.sprintf "The branches of a conditional must both have return type 'void'; got %s and %s"
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

#push-options "--z3rlimit_factor 2"
let check_field (env:env) (extend_scope: bool) (f:field)
  : ML field
  = let sf = f.v in
    check_typ false env sf.field_type;
    let fa = sf.field_array_opt |> map_opt (fun (e, b) ->
        let e, t = check_expr env e in
        if not (eq_typ env t tuint32)
        then error (Printf.sprintf "Array expression %s has type %s instead of UInt32"
                          (print_expr e)
                          (print_typ t))
                   e.range;
        e, b)
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
    let size = size_of_typ env sf.field_type in
    let size_opt =
        match sf.field_bitwidth with
        | None -> Some size

        | Some (Inl bw) ->
          if not (typ_is_integral env sf.field_type)
          then error (Printf.sprintf
                         "Bit-field annotations are only permitted on integral types; \
                          %s is not integral"
                          (print_typ sf.field_type))
                     bw.range;

          if Some? (sf.field_array_opt)
          then error "Bit-width annotations are not permitted on array fields" bw.range;

          let bitwidth_size = 8 * size in
          if not (0 <= bw.v && bw.v <= bitwidth_size)
          then error (Printf.sprintf "Expected a bit-width between 0 and %d" bitwidth_size)
                     bw.range;

          //we cannot compute the size of a bit field type in isolation
          //it requires information about adjacent bit fields
          //The size will be computed in a separate pass
          None

        | Some (Inr _) ->
          failwith "Impossible: this is an already elaborated bit field"
    in
    let size_opt =
        match sf.field_array_opt, size_opt with
        | _, None -> size_opt
        | None, _ -> size_opt
        | _, Some 0 -> size_opt //this is an opaque field
        | Some (e, ConstantSize), Some s ->
          begin
          match value_of_const_expr env e with
          | Some (Inr (_, n)) -> Some (n * s)
          | _ -> error "Variable-length array fields must be marked with the 'suffix' qualifier" f.range
          end
        | _ -> Some 0 //variable length
    in
    // Options.debug_print_string
    //   (Printf.sprintf "!!!Size of field %s is %s\n"
    //     sf.field_ident.v
    //     (match size_opt with | None -> "None" | Some s -> string_of_int s));
    if extend_scope then add_local env sf.field_ident sf.field_type;
    let field_number =
        let may_fail = parser_may_fail env sf.field_type in
        if may_fail
        || Some? fc //it has a refinement
        || Some? fa //it's an array
        then Some (field_num_ops.next (env.this, sf.field_ident.v))
        else None
    in
    let sf = {
        sf with
        field_array_opt = fa;
        field_constraint = fc;
        field_size = size_opt;
        field_number = field_number;
        field_action = f_act
    } in
    Options.debug_print_string
      (Printf.sprintf "Field %s has comments <%s>\n"
                  (print_ident sf.field_ident)
                  (String.concat "\n" f.comments));
    { f with v = sf }


let check_switch (env:env) (s:switch_case)
  : ML (switch_case & decl_attributes)
  = let head, cases = s in
    let head, maybe_enum_t = check_expr env head in
    let fail_non_integral (#a:Type) ()  : ML (option a) =
        if not (typ_is_integral env maybe_enum_t)
        then error (Printf.sprintf "Case analysis of a non-integral type (%s) is not supported"
                                     (print_typ maybe_enum_t))
                     head.range;
        None
    in
    let tags_t_opt =
      match maybe_enum_t.v with
      | Pointer _ -> fail_non_integral ()
      | Type_app hd es ->
        match try_lookup_enum_cases env hd with
        | Some enum -> Some enum
        | _ -> fail_non_integral ()
    in
    let check_case (c:case) : ML case =
      let pat, f = c in
      let pat, pat_t = check_expr env pat in
      let f = check_field env false f in
      let _ = //check type of patterns
        match tags_t_opt with
        | None ->
          //Not an enum; just check that its a valid u32
          if not (eq_typ env maybe_enum_t pat_t)
          then error (Printf.sprintf "Type of case (%s) does not match type of switch expression (%s)"
                                     (print_typ pat_t)
                                     (print_typ maybe_enum_t))
                     pat.range
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
                                     (print_typ maybe_enum_t))
                     pat.range
      in
      pat, f
    in
    let cases = List.map check_case cases in
    let size, suffix =
      List.fold_right
        (fun (_, f) (size, suffix) ->
          let sf = f.v in
          let size =
              match sf.field_size with
              | Some f -> if f > size then f else size
              | _ ->
                raise (error (Printf.sprintf "Size of union field %s cannot be computed"
                                             sf.field_ident.v)
                              sf.field_ident.range)
          in
          size, typ_has_suffix env sf.field_type)
        cases
        (0, false)
    in
    let attrs = {
      has_suffix = suffix;
      size = size;
      may_fail = false;
      integral = false;
      has_reader = false;
      parser_kind_nz = None
    } in
    (head, cases), attrs
#pop-options

let check_params (env:env) (ps:list param) : ML unit =
  ps |> List.iter (fun (t, p, _q) ->
      check_typ true env t;
      add_local env p t)

let rec elaborate_bit_fields env
                            (bf_index:int)
                            (open_bit_field: option (typ & int & int ))
                            (fields:list field)
  : ML (list field & size)
  = let new_bit_field index sf bw r : ML (field & option (typ & int & int) & int) =
        let size = size_of_typ env sf.field_type in
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
        Some (sf.field_type, to, remaining_size),
        size
    in
    let field_size hd : ML int =
      match hd.v.field_size with
      | None ->
        failwith (Printf.sprintf "Field size for %s should already have been computed"
                                 hd.v.field_ident.v)
      | Some n ->
        n
    in
    let aux hd tl_size : ML _ =
      hd::fst tl_size, snd tl_size + field_size hd
    in
    match fields with
    | [] ->
      [], 0

    | hd::tl ->
      let sf = hd.v in
      match sf.field_bitwidth, open_bit_field with
      | None, None ->
          aux hd (elaborate_bit_fields env bf_index open_bit_field tl)

      | None, Some _ ->  //end the bit field
          aux hd (elaborate_bit_fields env (bf_index + 1) None tl)

      | Some (Inr _), _ ->
          failwith "Bitfield is already elaborated"

      | Some (Inl bw), None ->
          let hd, open_bit_field, size = new_bit_field bf_index sf bw hd.range in
          let tl, size_tl = elaborate_bit_fields env bf_index open_bit_field tl in
          hd :: tl, size + size_tl

      | Some (Inl bw), Some (bit_field_typ, pos, remaining_size) ->
          Options.debug_print_string
            (Printf.sprintf
              "Field type = %s; bit_field_type = %s\n"
              (print_typ sf.field_type)
              (print_typ bit_field_typ));

          if remaining_size < bw.v //not enough space in this bit field, start a new one
          then let next_index = bf_index + 1 in
               let hd, open_bit_field, size = new_bit_field next_index sf bw hd.range in
               let tl, size_tl = elaborate_bit_fields env next_index open_bit_field tl in
               hd :: tl, size + size_tl
          else //extend this bit field
               begin
               if not (eq_typ env sf.field_type bit_field_typ)
               then raise (error "Packing fields of different types into the same bit field is not yet supported" hd.range);
               let remaining_size = remaining_size - bw.v in
               let from = pos in
               let to = pos + bw.v in
               let bf_attr = {
                       bitfield_width = bw.v;
                       bitfield_identifier = bf_index;
                       bitfield_type = bit_field_typ;
                       bitfield_from = from;
                       bitfield_to = to
               } in
               let sf = { sf with field_bitwidth = Some (Inr (with_range bf_attr bw.range)) } in
               let hd = { hd with v = sf } in
               let open_bit_field = Some (bit_field_typ, to, remaining_size) in
               let tl, size_tl = elaborate_bit_fields env bf_index open_bit_field tl in
               hd :: tl, size_tl
          end

let elaborate_record (e:global_env)
                     (tdnames:Ast.typedef_names)
                     (params:list param)
                     (where:option expr)
                     (fields:list field)
                     (range:range)
                     (comments:comments)
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
            field_size = Some 0;
            field_ident = with_range "__precondition" e.range;
            field_type = tunit;
            field_array_opt = None;
            field_constraint = w;
            field_number = Some (field_num_ops.next (env.this, "__precondition"));
            field_bitwidth = None;
            field_action = None
          }
        in
        w, [with_range field e.range]
    in

    (* Elaborate and check each field in order;
       Checking each field extends the local environment with the name of that field *)
    let fields = fields |> List.map (check_field env true) in

    (* Infer which of the fields are dependent by seeing which of them are used in refinements *)
    let nfields = List.length fields in
    let fields = fields |> List.mapi (fun i f ->
      let sf = f.v in
      let used = is_used env sf.field_ident in
      let last_field = i = (nfields - 1) in
      let dependent = used || (Some? sf.field_constraint && not last_field) in
      let f =
        with_range_and_comments
          ({ sf with field_dependence = dependent })
          f.range
          f.comments
      in
      let has_reader = typ_has_reader env f.v.field_type in
      if f.v.field_dependence
      && not has_reader
      then error "The type of this field does not have a reader, \
                  either because its values are too large \
                  or because reading it may incur a double fetch; \
                  subsequent fields cannot depend on it" f.range
      else f)
    in

    let fields = maybe_unit_field@fields in

    let fields, size = elaborate_bit_fields env 0 None fields in

    let d = with_range_and_comments (Record tdnames params where fields) range comments in

    let is_var_length (x:field) : ML bool =
      let sfx = typ_has_suffix env x.v.field_type in
      sfx ||
      (match x.v.field_array_opt with
       | None
       | Some (_, ConstantSize) -> false
       | _ -> true)
    in

    let check_suffix (fs:list field) : ML bool =
      let _, has_variable =
        List.fold_right
          (fun f (allow_variable, has_variable) ->
            let f_is_var = is_var_length f in
            let has_variable = has_variable || f_is_var in
            if f_is_var
            then if allow_variable then allow_variable, has_variable
                 else error "Variable-length fields can only be at the end of a struct" f.v.field_type.range
            else false, has_variable)
          fs
          (true, false)
      in
      has_variable
    in
    let has_suffix = check_suffix fields in
    Options.debug_print_string
      (Printf.sprintf "Size of record %s is %d\n"
        tdnames.typedef_name.v
        size
        );
    let attrs = {
        size = size;
        has_suffix = has_suffix;
        may_fail = false; //only its fields may fail; not the struct itself
        integral = false;
        has_reader = false;
        parser_kind_nz = None
      }
    in
    add_global e tdnames.typedef_name d (Inl attrs);
    d


let bind_decl (e:global_env) (d:decl) : ML decl =
  match d.v with
  | Define i None c ->
    add_global e i d (Inr (nullary_macro (type_of_constant c)));
    d

  | Define i (Some t) c ->
    let env = mk_env e in
    check_typ false env t;
    let t' = type_of_constant c in
    if eq_typ env t t'
    then (add_global e i d (Inr (nullary_macro (type_of_constant c))); d)
    else error "Ill-typed constant" d.range

  | TypeAbbrev t i ->
    let env = mk_env e in
    check_typ false env t;
    let attrs =
      {
        has_suffix = typ_has_suffix env t;
        size = size_of_typ env t;
        may_fail = parser_may_fail env t;
        integral = typ_is_integral env t;
        has_reader = typ_has_reader env t;
        parser_kind_nz = None
      }
    in
    add_global e i d (Inl attrs);
    d

  | Enum t i cases ->
    let env = mk_env e in
    check_typ false env t;
    let cases = Desugar.check_desugared_enum_cases cases in
    cases |> List.iter (fun i ->
      let _, t' = check_expr env (with_dummy_range (Identifier i)) in
      if not (eq_typ env t t')
      then error (Printf.sprintf "Inconsistent type of enumeration identifier: Expected %s, got %s"
                   (print_typ t)
                   (print_typ t'))
                 d.range);
    let attrs =
      {
        has_suffix = typ_has_suffix env t;
        size = size_of_typ env t;
        may_fail = true;
        integral = true;
        has_reader = false; //it's a refinement, so you can't read it again because of double fetches
        parser_kind_nz = None
      }
    in
    add_global e i d (Inl attrs);
    d

  | Record tdnames params where fields ->
    elaborate_record e tdnames params where fields d.range d.comments

  | CaseType tdnames params switch ->
    let env = { mk_env e with this=Some tdnames.typedef_name } in
    check_params env params;
    let switch, attrs = check_switch env switch in
    let d = with_range_and_comments (CaseType tdnames params switch) d.range d.comments in
    add_global e tdnames.typedef_name d (Inl attrs);
    d

let initial_global_env () =
  let e = H.create 10 in
  let nullary_decl i =
    let td_name = {
      typedef_name = i;
      typedef_abbrev = i;
      typedef_ptr_abbrev = i;
      typedef_entry_point = false
    }
    in
    with_dummy_range (Record td_name [] None [])
  in
  let _type_names =
    [ ("unit",    { size = 0; has_suffix = false; may_fail = false; integral = false; has_reader = true; parser_kind_nz=Some false});
      ("Bool",    { size = 1; has_suffix = false; may_fail = true;  integral = false; has_reader = true; parser_kind_nz=Some true});
      ("UINT8",   { size = 1; has_suffix = false; may_fail = true;  integral = true ; has_reader = true; parser_kind_nz=Some true });
      ("UINT16",  { size = 2; has_suffix = false; may_fail = true;  integral = true ; has_reader = true; parser_kind_nz=Some true });
      ("UINT32",  { size = 4; has_suffix = false; may_fail = true;  integral = true ; has_reader = true; parser_kind_nz=Some true});
      ("UINT64",  { size = 8; has_suffix = false; may_fail = true;  integral = true ; has_reader = true; parser_kind_nz=Some true});
      ("field_id",  { size = 4; has_suffix = false; may_fail = true;  integral = true ; has_reader = false; parser_kind_nz=Some true})]
    |> List.iter (fun (i, attrs) ->
      let i = with_dummy_range i in
      add_global e i (nullary_decl i) (Inl attrs))
  in
  let _operators =
    [ ("is_range_okay", { macro_arguments_t=[tuint32;tuint32;tuint32]; macro_result_t=tbool}) ]
    |> List.iter (fun (i, d) ->
        let i = with_dummy_range i in
        add_global e i (nullary_decl i) (Inr d))
  in
  e

let add_field_error_code_decls
  ()
: ML prog
= let l = all_nums () in
  List.map
    (fun (z: (field_num & option ident & string)) ->
      let (i, this, name) = z in
      let d =
        with_dummy_range (Define (field_error_code_variable_name_of_field (this, name))
                                 (Some tfield_id)
                                 (Int UInt64 i)) in
      { d with comments = ["Auto-generated field identifier for error reporting"] }
    )
    l

let bind_prog (p:prog) : ML (prog & global_env) =
  let e = initial_global_env() in
  let p' = List.map (bind_decl e) p in
  let fc = add_field_error_code_decls () in
  (fc @ p'), e
