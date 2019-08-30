module Binding
open Ast
open FStar.All
module H = Hashtable

noeq
type field_num_ops_t = {
  next : (option ident * string) -> ML field_num;
  lookup : field_num -> ML (option (option ident * string))
}

#push-options "--warn_error -272" //top-level effect; ok
let field_num_ops : field_num_ops_t =
  let open FStar.ST in
  let h : H.t field_num (option ident * string) = H.create 100 in
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
    : ML (option (option ident * string))
    = H.try_find h f
  in
  {
    next = next;
    lookup = lookup
  }
#pop-options


type decl_attributes = {
  size:option size;
  has_suffix:bool;
  may_fail:bool
}

let global_env = H.t ident' (decl * either decl_attributes typ)

//the bool signifies that this identifier has been used
let local_env = H.t ident' (typ * bool)

noeq
type env = {
  this: option ident;
  locals: local_env;
  globals: global_env
}

let params_of_decl (d:decl) : list param =
  match d.v with
  | Comment _
  | Define _ _
  | TypeAbbrev _ _
  | Enum _ _ _ -> []
  | Record _ params _
  | CaseType _ params _ -> params

let error #a msg (r:range) : ML a =
  failwith (Printf.sprintf "At %s: %s" (string_of_pos (fst r)) msg)

let check_shadow (e:H.t ident' 'a) (i:ident) (r:range) =
  match H.try_find e i.v with
  | Some j ->
    let msg = Printf.sprintf "Declaration %s clashes with previous declaration" i.v in
    error msg i.range

  | _ ->
    ()

let typedef_names (d:decl) : option typedef_names =
  match d.v with
  | Record td _ _
  | CaseType td _ _ -> Some td
  | _ -> None

let add_global (e:global_env) (i:ident) (d:decl) (t:either decl_attributes typ) =
  check_shadow e i d.range;
  H.insert e i.v (d, t);
  match typedef_names d with
  | None -> ()
  | Some td ->
    if td.typedef_abbrev.v <> i.v
    then begin
      check_shadow e td.typedef_abbrev d.range;
      H.insert e td.typedef_abbrev.v (d, t)
    end
//    check_shadow e td.typedef_ptr_abbrev d.range;

let add_local (e:env) (i:ident) (t:typ) =
  check_shadow e.globals i t.range;
  check_shadow e.locals i t.range;
  H.insert e.locals i.v (t, false)

let remove_local (e:env) (i:ident) =
  H.remove e.locals i.v

let lookup (e:env) (i:ident) : ML (either typ (decl & either decl_attributes typ)) =
  match H.try_find e.locals i.v with
  | Some (t, true) ->
    Inl t
  | Some (t, false) ->  //mark it as used
    H.remove e.locals i.v;
    H.insert e.locals i.v (t, true);
    Inl t
  | None ->
    match H.try_find e.globals i.v with
    | Some d -> Inr d
    | None -> error (Printf.sprintf "Variable %s not found" i.v) i.range

let lookup_expr_name (e:env) (i:ident) : ML typ =
  match lookup e i with
  | Inl t -> t
  | Inr (_, Inr t) -> t
  | Inr _ ->
    error (Printf.sprintf "Variable %s is not an expression identifier" i.v) i.range

let lookup_enum_cases (e:env) (i:ident)
  : ML (list ident * typ)
  = match lookup e i with
    | Inr ({v=Enum t _ tags}, _) -> tags, t
    | _ ->
      error (Printf.sprintf "Type %s is not an enumeration" i.v) i.range

let is_used (e:env) (i:ident) : ML bool =
  match H.try_find e.locals i.v with
  | Some (t, b) -> b
  | _ ->  error (Printf.sprintf "Variable %s not found" i.v) i.range

let type_of_constant (c:constant) : typ =
  match c with
  | Int i -> tuint32
  | XInt x -> tuint32
  | Bool _ -> tbool

let size_of_typ (env:env) (t:typ) : ML (option size) =
  let Type_app hd _ = t.v in
  match lookup env hd with
  | Inr (_, Inl attrs) -> attrs.size
  | _ -> None

let typ_has_suffix env (t:typ) : ML bool =
  let Type_app hd _ = t.v in
  match lookup env hd with
  | Inr (d, Inl attrs) -> attrs.has_suffix
  | _ -> false

let parser_may_fail (env:env) (t:typ) : ML bool =
  let Type_app hd _ = t.v in
  match lookup env hd with
  | Inr (d, Inl attrs) -> attrs.may_fail
  | _ -> false

let rec value_of_const_expr (env:env) (e:expr) : ML (option (either bool int)) =
  match e.v with
  | Constant (Int n) -> Some (Inr n)
  | Constant (Bool b) -> Some (Inl b)
  | App op [e1; e2] ->
    let v1 = value_of_const_expr env e1 in
    let v2 = value_of_const_expr env e2 in
    begin
    match op, v1, v2 with
    | Plus, Some (Inr n1), Some (Inr n2) -> Some (Inr (n1 + n2))
    | Minus, Some (Inr n1), Some (Inr n2) -> Some (Inr (n1 - n2))
    | GT, Some (Inr n1), Some (Inr n2) -> Some (Inl (n1 > n2))
    | LT, Some (Inr n1), Some (Inr n2) -> Some (Inl (n1 < n2))
    | GE, Some (Inr n1), Some (Inr n2) -> Some (Inl (n1 >= n2))
    | LE, Some (Inr n1), Some (Inr n2) -> Some (Inl (n1 <= n2))
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
    match size_of_typ env (with_range (Type_app t []) t.range) with
    | None -> None
    | Some n -> Some (Inr n)
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
  else Ast.eq_typ (unfold_typ_abbrevs env t1) (unfold_typ_abbrevs env t1)

let eq_typs env ts =
  List.for_all (fun (t1, t2) -> eq_typ env t1 t2) ts

let rec check_typ (env:env) (t:typ)
  : ML unit
  = match t.v with
    | Type_app s es ->
      match lookup env s with
      | Inl _ ->
        error (Printf.sprintf "%s is not a type" s.v) s.range

      | Inr (d, _) ->
        let params = params_of_decl d in
        if List.length params <> List.length es
        then error (Printf.sprintf "Not enough arguments to %s" s.v) s.range;
        let es =
          List.map2 (fun (t, _) e ->
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
      | Inr ({v=Record _ _ _ }, _)
      | Inr ({v=CaseType _ _ _}, _) ->
        e, tuint32
      | _ ->
        error "`sizeof` applied to a non-sized-typed" r
      end

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
        | Eq ->
          if not (eq_typ env t1 t2)
          then error
                 (Printf.sprintf "Equality on unequal types: %s and %s"
                   (print_typ t1)
                   (print_typ t2))
               e.range;
          w (App Eq [e1; e2]), tbool

        | And
        | Or ->
          if not (eq_typs env [(t1,tbool); (t2,tbool)])
          then error "Binary boolean op on non booleans" e.range;
          w (App op [e1; e2]), tbool

        | Plus
        | Minus ->
          if not (eq_typs env [(t1,tuint32); (t2,tuint32)])
          then error "Binary integer op on non-integers" e.range;
          w (App op [e1; e2]), tuint32


        | LT
        | GT
        | LE
        | GE ->
          if not (eq_typs env [(t1,tuint32); (t2,tuint32)])
          then error "Binary integer op on non integers" e.range;
          w (App op [e1; e2]), tbool

        | _ ->
          error "Not a binary op" e.range
        end

      | _ -> error "Unexpected arity" e.range

let check_field (env:env) (extend_scope: bool) (f:field)
  : ML field
  = match f.v with
    | FieldComment _ -> f
    | Field sf ->
      check_typ env sf.field_type;
      let fa = sf.field_array_opt |> map_opt (fun e ->
        let e, t = check_expr env e in
        if not (eq_typ env t tuint32)
        then error (Printf.sprintf "Array expression %s has type %s instead of UInt32"
                          (print_expr e)
                          (print_typ t))
                   e.range;
        e)
      in
      let fc = sf.field_constraint |> map_opt (fun e ->
        add_local env sf.field_ident sf.field_type;
        let e = fst (check_expr env e) in
        remove_local env sf.field_ident;
        e)
      in
      let size = size_of_typ env sf.field_type in
      let size =
        match sf.field_array_opt, size with
        | None, _ -> size
        | _, Some 0 -> size //this is an opaque field
        | Some e, Some s ->
          begin
          match value_of_const_expr env e with
          | Some (Inr n) -> Some (n `op_Multiply` s)
          | _ -> None
          end
        | _ -> None
      in
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
        field_size = size;
        field_number = field_number
      } in
      with_range (Field sf) f.range

let check_switch (env:env) (s:switch_case)
  : ML (switch_case * decl_attributes)
  = let head, cases = s in
    let head, enum_t = check_expr env head in
    let enum_tags, t = lookup_enum_cases env (Type_app?._0 enum_t.v) in
    let check_case (c:case) : ML case =
      let pat, f = c in
      let pat, pat_t = check_expr env pat in
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
                    (print_typ enum_t))
           pat.range;
      let f = check_field env false f in
      pat, f
    in
    let cases = List.map check_case cases in
    let size, suffix =
      List.fold_right
        (fun (_, f) (size, suffix) ->
          match f.v with
          | FieldComment _ -> size, suffix
          | Field sf ->
            let size =
              match size, sf.field_size with
              | Some n, Some f -> if f > n then Some f else Some n
              | _ -> None
            in
            size, typ_has_suffix env sf.field_type)
        cases
        (Some 0, false)
    in
    let attrs = { has_suffix = suffix; size = size; may_fail = false } in
    (head, cases), attrs

let mk_env (g:global_env) =
  { this = None;
    locals = H.create 10;
    globals = g }

let check_params (env:env) (ps:list param) : ML unit =
  ps |> List.iter (fun (t, p) ->
      check_typ env t;
      add_local env p t)

let bind_decl (e:global_env) (d:decl) : ML decl =
  match d.v with
  | Comment _ -> d

  | Define i c ->
    add_global e i d (Inr (type_of_constant c));
    d

  | TypeAbbrev t i ->
    let env = mk_env e in
    check_typ env t;
    let attrs =
      {
        has_suffix = typ_has_suffix env t;
        size = size_of_typ env t;
        may_fail = parser_may_fail env t
      }
    in
    add_global e i d (Inl attrs);
    d

  | Enum t i cases ->
    let env = mk_env e in
    check_typ env t;
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
        may_fail = true
      }
    in
    add_global e i d (Inl attrs);
    d

  | Record tdnames params fields ->
    let env = { mk_env e with this=Some tdnames.typedef_name } in
    check_params env params;
    let fields = fields |> List.map (check_field env true) in
    let fields = fields |> List.map (fun f ->
      match f.v with
      | FieldComment _ -> f
      | Field sf ->
        with_range
          (Field ({ sf with field_dependence = is_used env sf.field_ident }))
          f.range)
    in
    let d = with_range (Record tdnames params fields) d.range in
    let size =
      List.fold_right
        (fun f size ->
          match f.v with
          | FieldComment _ -> size
          | Field sf ->
            match size, sf.field_size with
            | Some size, Some fs -> Some (size + fs)
            | _ -> None)
        fields (Some 0)
    in
    let rec check_suffix (f:list struct_field) : ML bool =
      match f with
      | [] -> false
      | [last] ->
        typ_has_suffix env last.field_type
      | hd::tl ->
        if typ_has_suffix env hd.field_type
        then error "Variable-length fields can only be at the end of a struct" hd.field_type.range
        else check_suffix tl
    in
    let has_suffix =
      check_suffix
        (List.filter_map
          (function
            | {v=FieldComment _} -> None
            | {v=Field sf} -> Some sf)
          fields)
    in
    let attrs = {
        size = size;
        has_suffix = has_suffix;
        may_fail = false; //only its fields may fail; not the struct itself
      }
    in
    add_global e tdnames.typedef_name d (Inl attrs);
    d

  | CaseType tdnames params switch ->
    let env = { mk_env e with this=Some tdnames.typedef_name } in
    check_params env params;
    let switch, attrs = check_switch env switch in
    let d = with_range (CaseType tdnames params switch) d.range in
    add_global e tdnames.typedef_name d (Inl attrs);
    d

let prog = list decl

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
    { v = Record td_name [] [];
      range = dummy_range }
  in
  [ ("UINT8", { size = Some 1; has_suffix = false; may_fail = true});
    ("UINT32", { size = Some 4; has_suffix = false; may_fail = true});
    ("suffix", { size = Some 0; has_suffix = true; may_fail = true}) ]
  |> List.iter (fun (i, attrs) ->
    let i = { v = i; range=dummy_range} in
    add_global e i (nullary_decl i) (Inl attrs));
  e

let bind_prog (p:prog) : ML (prog * global_env) =
  let e = initial_global_env() in
  List.map (bind_decl e) p, e
