module Translate
open Ast
module A = Ast
module T = Target
open FStar.All

let translate_op : A.op -> ML T.op = function
  | Eq -> T.Eq
  | And -> T.And
  | Or -> T.Or
  | Not -> T.Not
  | Plus -> T.Plus
  | Minus -> T.Minus
  | LT -> T.LT
  | GT -> T.GT
  | LE -> T.LE
  | GE -> T.LE
  | _ -> failwith "Operator should have been eliminated already"

let rec translate_expr (e:A.expr) : ML T.expr =
  match e.v with
  | Constant c -> T.Constant c
  | Identifier i -> T.Identifier i
  | App op exprs -> T.App (translate_op op) (List.map translate_expr exprs)
  | This -> failwith "`this` should have been eliminated already"

let translate_typ (t:A.typ) : ML T.typ =
  let Type_app hd args = t.v in
  T.T_app hd (List.map (fun x -> Inr (translate_expr x)) args)

let translate_typedef_name (tdn:A.typedef_names) params : ML T.typedef_name =
  let params = List.map (fun (id, t) -> id, translate_typ t) params in
  tdn.typedef_name, params

let make_enum_typ (t:T.typ) (ids:list ident) =
  let refinement (x:A.ident) =
    let x = T.Identifier x in
    List.fold_right
      (fun y e -> T.App T.Or [T.App T.Eq [T.Identifier y; x]; e])
      ids
      (T.Constant (Bool false))
  in
  T.T_refine t refinement

let pk = ()

let mk_parser k t p = T.({
  p_kind = k;
  p_typ = t;
  p_parser = p
})

let rec parse_typ (t:T.typ) : ML T.parser =
  let open T in
  match t with
  | T.T_app hd args ->
    mk_parser pk (T.T_app hd args) (T.Parse_app hd args)

  | T.T_refine t_base refinement ->
    let base = parse_typ t_base in
    let refined = T.Parse_filter base refinement in
    mk_parser pk t refined

  | T.T_match head cases ->
    let cases =
      List.map
        (fun c -> c.pattern, parse_typ c.branch)
        cases
    in
    mk_parser pk t (T.Parse_cases head cases)

let pv p v = T.({
  v_parser = p;
  v_validator = v
})

let rec make_reader (t:T.typ) : ML T.reader =
  match t with
  | T.T_app {v="UInt8"} [] ->
    T.Read_u8

  | T.T_app {v="UInt16"} [] ->
    T.Read_u16

  | T.T_app {v="UInt32"} [] ->
    T.Read_u32

  | T.T_refine base refinement ->
    T.Read_filter (make_reader base) refinement

  | _ -> failwith "Unsupported reader type"

let rec make_validator (p:T.parser) : ML T.validator =
  let open T in
  match p.p_parser with
  | Parse_app hd args ->
    pv p (Validate_app hd args)

  | Parse_return e ->
    pv p Validate_return

  | Parse_seq p1 p2 ->
    pv p (Validate_seq (make_validator p1) (make_validator p2))

  | Parse_and_then p1 k ->
    pv p (Validate_and_read (make_validator p1) (make_reader p1.p_typ) (fun x -> make_validator (k x)))

  | Parse_map p1 f ->
    pv p (Validate_map (make_validator p1) f)

  | Parse_filter p1 f ->
    pv p (Validate_filter (make_validator p1) (make_reader p1.p_typ) f)

  | Parse_with_kind p1 k ->
    pv p (Validate_with_kind (make_validator p1))

  | Parse_cases hd cs ->
    pv p (Validate_cases hd (List.map (fun (e, p) -> e, make_validator p) cs))

let nondep_group = nat & list struct_field
let grouped_fields = list (either struct_field nondep_group)
let maked_grouped_fields (fs:list A.field) : ML grouped_fields =
  let sfs =
    List.filter_map
      (fun f ->
        match f.v with
        | Field sf -> Some sf
        | _ -> None)
      fs
  in
  let add_run (out, run) =
      match snd run with
      | [] -> out
      | _ -> Inr run :: out
  in
  let extend_run sf (run:nondep_group) : nondep_group =
    (fst run + 1, sf::snd run)
  in
  let group_non_dependent_fields
          (sf:struct_field)
          (out, run)
    : grouped_fields & nondep_group
    = if sf.field_dependence
      then Inl sf :: add_run (out, run), (0, [])
      else out, extend_run sf run
  in
  let gfs : grouped_fields =
    add_run (List.fold_right group_non_dependent_fields sfs ([], (0, [])))
  in
  gfs

// x:t1;
// t2;
// t3;
// y:t4;
// t5;
// t6

// (x <-- parse_t1 ;
//  (parse_t2 ;;
//   parse_t3 ;;
//   (y <-- parse_t4;
//     ((parse_t5 ;;
//       parse_t6) `map` (fun x56 -> y, x56))))
//  `map` (fun x_2_3_4_5_6 -> {x = x; y .... }))

let rec translate_grouped_fields
         (gfs:grouped_fields) =
  let translate_one_field sf =
      let t = translate_typ sf.field_typ in
      let t =
        match sf.field_array_opt with
        | None -> t
        | Some e ->
          let e = translate_expr e in
          T.T_app "lseq" [Inl t; Inr e]
      in
      let t =
        match sf.constraint with
        | None -> t
        | Some e ->
          T.T_refine t (fun x -> translate_expr e)
  in
  match gfs with
  | [] -> failwith "Empty fields"
  | Inl sf::tl ->




// let translate_fields (fs:list A.field) =
//   let gfs

//   ()

let translate_decl (d:A.decl) : ML T.decl =
  match d.v with
  | Comment s -> T.Comment s

  | Define i s -> T.Definition (i, s)

  | Enum t i ids ->
    let tdn = {
        typedef_name = i;
        typedef_abbrev = "";
        typedef_ptr_abbrev = "";
      }
    in
    let typ = translate_typ typ in
    let typedef_name = translate_typedef_name tdn [] in
    let refined_typ = make_enum_typ typ ids in
    let parser = parse_typ refined_typ in
    let open T in
    Type_decl (
      {
        decl_name = typedef_name;
        decl_typ = TD_abbrev refined_typ;
        decl_parser = parser;
        decl_validator = make_validator parser;
      }
    )

  | Record tdn params ast_fields ->
    let typedef_name = translate_typedef_name tdn params in
    let fields = translate_fields ast_fields in
    let parser = parse_fields ast_fields in
    let open T in
    Type_decl (
      {
        decl_name = typedef_name;
        decl_typ = TD_struct fields;
        decl_parser = parser;
        decl_validator = make_validator parser
      }
    )

  | CaseType tdn params switch_case ->
    let typedef_name = translate_typedef_name tdn params in
    let typ = translate_switch_case_type typ in
    let parser = parse_cases typ in
    let open T in
    Type_decl (
      {
        decl_name = typedef_name;
        decl_typ = TD_abbrev typ;
        decl_parser = parser;
        decl_validator = make_validator parser
      }
    )
