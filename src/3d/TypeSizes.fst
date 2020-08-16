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
module TypeSizes
open FStar.All
open Ast
open FStar.Mul
module H = Hashtable
module B = Binding

let product_size (base:size) (n:int) =
  match base with
  | Variable
  | WithVariableSuffix _ ->
    Variable
  | Fixed k ->
    Fixed (k * n)

let typename = string

let size_env = H.t typename size

let initial_env (benv:B.global_env) : ML env_t =
  let i = [
       ("unit",     Fixed 0);
       ("Bool",     Fixed 1);
       ("UINT8",    Fixed 1);
       ("UINT16",   Fixed 2);
       ("UINT32",   Fixed 4);
       ("UINT64",   Fixed 8);
       ("field_id", Fixed 4);
       ("PUINT8",   Variable) //size of pointer is platform-dependent
  ]
  in
  let senv = H.create 17 in
  List.iter (fun (i, k) -> H.insert senv i k) i;
  B.mk_env benv,
  senv

let size_of_typename (env:env_t) (i:ident)
  : ML size
  = match H.try_find (snd env) i.v with
    | Some s -> s
    | None -> failwith (Printf.sprintf "size_of_typename: Identifier %s not found" i.v)

let print_size =
  function
  | Fixed n -> Printf.sprintf "(Fixed %d)" n
  | WithVariableSuffix n -> Printf.sprintf "(WithVariableSuffix %d)" n
  | Variable -> "Variable"

let extend_with_size_of_ident (env:env_t) (i:ident) (n:size)
  : ML unit
  = Options.debug_print_string
     (Printf.sprintf "***** Size of %s = %s\n"
                     i.v (print_size n));
    H.insert (snd env) i.v n

let extend_with_size_of_typedef_names (env:env_t) (names:typedef_names) (size:size)
  : ML unit
  = extend_with_size_of_ident env names.typedef_name size;
    extend_with_size_of_ident env names.typedef_abbrev size;
    extend_with_size_of_ident env names.typedef_ptr_abbrev Variable

let size_of_typ (env:env_t) (t:typ)
  : ML size
  = match t.v with
    | Type_app i _ -> size_of_typename env i
    | Pointer _ -> Variable

let rec value_of_const_expr (env:env_t) (e:expr)
  : ML (option (either bool (integer_type & int)))
  =
  match e.v with
  | Constant (Int t n) -> Some (Inr (t, n))
  | Constant (Bool b) -> Some (Inl b)
  | App op [e1; e2] ->
    let v1 = value_of_const_expr env e1 in
    let v2 = value_of_const_expr env e2 in
    begin
    match op, v1, v2 with
    | Plus _,  Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 + n2))
    | Minus _, Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 - n2))
    | Mul _,   Some (Inr (t1, n1)), Some (Inr (t2, n2)) -> Some (Inr (integer_type_lub t1 t2, n1 * n2))
    | Division _, Some (Inr (t1, n1)), Some (Inr (t2, n2)) ->
      if n2 = 0
      then error ("Division by zero in constant expression") e2.range
      else Some (Inr (integer_type_lub t1 t2, n1 / n2))
    | GT _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 > n2))
    | LT _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 < n2))
    | GE _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 >= n2))
    | LE _, Some (Inr (_, n1)), Some (Inr (_, n2)) -> Some (Inl (n1 <= n2))
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
    try
      match size_of_typ env (with_range (Type_app t []) t.range) with
      | Fixed n
      | WithVariableSuffix n -> Some (Inr (UInt32, n))
      | _ -> None
    with
      | _ -> None
    end
  | App (Cast _ t) [e] ->
    let v = value_of_const_expr env e in
    begin
    match v with
    | Some (Inr (_, n)) ->
      Some (Inr (t, n))
    | _ -> None
    end
  | Identifier i ->
    begin
    match B.lookup_macro_definition (fst env) i with
    | Some e ->
      value_of_const_expr env e
    | _ -> None
    end
  | _ -> None

let size_of_field (env:env_t) (f:field)
  : ML size
  = let base_size = size_of_typ env f.v.field_type in
    match f.v.field_array_opt with
    | None ->
      base_size

    | Some (e, ConstantSize) ->
      let n = value_of_const_expr env e in
      begin
      match n with
      | Some (Inr (_, k)) ->
        product_size base_size k

      | _ ->
        error (Printf.sprintf "Constant sized array expression %s could not be statically evaluated to a constant"
                                (print_expr e))
              f.range
      end

    | Some (n, VariableSizeEq)
    | Some (n, SingleElementVariableSizeEq) ->
      let n = value_of_const_expr env n in
      begin
      match n with
      | Some (Inr (_, k)) ->
        product_size base_size k

      | _ ->
        Variable
      end

    | _ -> Variable

let size_of_decl (env:env_t) (d:decl)
  : ML unit
  = match d.v with
    | Define _ _ _ -> ()

    | TypeAbbrev t i
    | Enum t i _ ->
      extend_with_size_of_ident env i (size_of_typ env t)

    | Record names params where fields ->
      let field_sizes = List.map (size_of_field env) fields in
      let rec sum (accum : size) (sizes:list size)
        : Tot size (decreases sizes)
        = match accum, sizes with
          | Variable, _
          | WithVariableSuffix _, _
          | _, [] -> accum
          | Fixed n, hd::tl ->
            match hd with
            | Fixed m -> sum (Fixed (n + m)) tl
            | WithVariableSuffix m -> WithVariableSuffix (n + m)
            | Variable -> WithVariableSuffix n
      in
      let size = sum (Fixed 0) field_sizes in
      extend_with_size_of_typedef_names env names size

    | CaseType names params cases ->
      let case_sizes =
        List.map
          (function
            | Case _ f
            | DefaultCase f ->
              size_of_field env f)
          (snd cases)
      in
      let size =
        List.fold_right
          (fun s accum ->
            match accum with
            | None -> Some s
            | Some s' ->
              if s = s'
              then Some s
              else Some Variable)
          case_sizes
          None
      in
      let size =
        match size with
        | None -> Fixed 0
        | Some s -> s
      in
      extend_with_size_of_typedef_names env names size

let size_of_decls (env:B.global_env) (d:list decl)
  : ML env_t
  = let env = initial_env env in
    List.iter (size_of_decl env) d;
    env
