module Translate
open Ast
module A = Ast
module T = Target
open FStar.All

let gen_ident : unit -> St ident =
  let open FStar.ST in
  let ctr : ref int = alloc 0 in
  let next () =
    let v = !ctr in
    ctr := v + 1;
    let id = Printf.sprintf "_x_%d" v in
    with_dummy_range id
  in
  next

let mk_lam (f:(A.ident -> ML 'a)) : ML (T.lam 'a) =
  let x = gen_ident () in
  x, f x

let map_lam (x:T.lam 'a) (g: 'a -> ML 'b) : ML (T.lam 'b) =
  fst x, g (snd x)

let pk = ()

let mk_parser k t p = T.({
  p_kind = k;
  p_typ = t;
  p_parser = p
})

let unit_typ =
    T.T_app (with_dummy_range "unit") []
let unit_val =
    T.Record (with_dummy_range "unit") []
let unit_parser =
    mk_parser pk unit_typ (T.Parse_return unit_val)
let pair_typ t1 t2 =
    T.T_app (with_dummy_range "tuple2") [Inl t1; Inl t2]
let pair_value x y =
    T.Record (with_dummy_range "tuple2")
             [(with_dummy_range "fst", T.Identifier x);
              (with_dummy_range "snd", T.Identifier y)]
let pair_parser p1 p2 =
    let open T in
    let pt = pair_typ p1.p_typ p2.p_typ in
    mk_parser pk pt (Parse_seq p1 p2)
let dep_pair_typ t1 (t2:T.lam T.typ) : T.typ =
    T.T_dep_pair t1 t2
let dep_pair_value x y : T.expr =
    T.Record (with_dummy_range "dtuple2")
             [(with_dummy_range "fst", T.Identifier x);
              (with_dummy_range "snd", T.Identifier y)]
let dep_pair_parser p1 (p2:T.lam T.parser) =
  let open T in
  let x, p2 = p2 in
  let t = T_dep_pair p1.p_typ (x, p2.p_typ) in
  mk_parser pk t
      (Parse_and_then
        p1
        (x, mk_parser pk t (Parse_map p2 (mk_lam (dep_pair_value x)))))

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
  let params = List.map (fun (t, id) -> id, translate_typ t) params in
  tdn.typedef_name, params

let make_enum_typ (t:T.typ) (ids:list ident) =
  let refinement i =
    let x = T.Identifier i in
    List.fold_right
      (fun y e -> T.App T.Or [T.App T.Eq [T.Identifier y; x]; e])
      ids
      (T.Constant (Bool false))
  in
  T.T_refine t (mk_lam refinement)


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

  | T.T_dep_pair t1 (x, t2) ->
    dep_pair_parser (parse_typ t1) (x, parse_typ t2)

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
    pv p (Validate_and_read
            (make_validator p1)
            (make_reader p1.p_typ)
            (map_lam k make_validator))

  | Parse_map p1 f ->
    pv p (Validate_map (make_validator p1) f)

  | Parse_filter p1 f ->
    pv p (Validate_filter (make_validator p1) (make_reader p1.p_typ) f)

  | Parse_with_kind p1 k ->
    pv p (Validate_with_kind (make_validator p1))

  | Parse_cases hd cs ->
    pv p (Validate_cases hd (List.map (fun (e, p) -> e, make_validator p) cs))

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

// let rec translate_grouped_fields
//          (gfs:grouped_fields) =
//   let translate_one_field sf =
//       let t = translate_typ sf.field_typ in
//       let t =
//         match sf.field_array_opt with
//         | None -> t
//         | Some e ->
//           let e = translate_expr e in
//           T.T_app "lseq" [Inl t; Inr e]
//       in
//       let t =
//         match sf.constraint with
//         | None -> t
//         | Some e ->
//           T.T_refine t (fun x -> translate_expr e)
//   in
//   match gfs with
//   | [] -> failwith "Empty fields"
//   | Inl sf::tl ->


let translate_struct_field (sf:A.struct_field) : ML T.struct_field =
    let t = translate_typ sf.field_type in
    let t =
        match sf.field_array_opt with
        | None -> t
        | Some e ->
          let e = translate_expr e in
          T.T_app (with_range "lseq" sf.field_type.range) [Inl t; Inr e]
    in
    let t =
      match sf.field_constraint with
      | None -> t
      | Some e ->
        T.T_refine t (sf.field_ident, translate_expr e)
    in
    T.({sf_dependence=sf.field_dependence;
        sf_ident=sf.field_ident;
        sf_typ=t})

let translate_field (f:A.field) : ML T.field =
  match f.v with
  | FieldComment s ->
    T.FieldComment s
  | Field sf ->
    T.Field (translate_struct_field sf)

let nondep_group = nat & list T.struct_field
let grouped_fields = list (either T.struct_field nondep_group)
let make_grouped_fields (fs:list T.field) : ML grouped_fields =
  let open T in
  let sfs =
    List.filter_map
      (fun f ->
        match f with
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
    = if sf.sf_dependence
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
let parse_grouped_fields (gfs:grouped_fields)
  : ML T.parser
  = let open T in
    let rec aux (gfs:grouped_fields) : ML parser =
      match gfs with
      | [] ->
        unit_parser

      | Inl sf::gfs ->
        dep_pair_parser (parse_typ sf.sf_typ) (sf.sf_ident, aux gfs)

      | Inr (_, gf)::gfs ->
        List.fold_right
          (fun (sf:struct_field) (p_tl:parser) ->
            pair_parser (parse_typ sf.sf_typ) p_tl)
          gf
          (aux gfs)
    in
    aux gfs

let parse_fields (tdn:T.typedef_name) (fs:list T.field) =
  let open T in
  let td_name, td_params = tdn in
  let gfs = make_grouped_fields fs in
  let p = parse_grouped_fields gfs in
  let dfst (e:T.expr) = App (Ext "dfst") [e] in
  let dsnd (e:T.expr) = App (Ext "dsnd") [e] in
  let fst (e:T.expr) = App (Ext "fst") [e] in
  let snd (e:T.expr) = App (Ext "snd") [e] in
  let rec make_non_dep_record_fields (e:T.expr) (fs:list struct_field)
    : Tot  (list (A.ident * T.expr)) (decreases fs) =
    match fs with
    | [] -> []
    | [hd] -> [hd.sf_ident, e]
    | hd::tl -> (hd.sf_ident, fst e) :: make_non_dep_record_fields (snd e) tl
  in
  let rec make_record_fields (e:T.expr) (gfs:grouped_fields)
    : Tot  (list (A.ident * T.expr)) (decreases gfs) =
    match gfs with
    | [] -> []
    | Inl hd::gfs ->
      (hd.sf_ident, dfst e) :: make_record_fields (dsnd e) gfs
    | Inr (_,gf)::gfs ->
      let tl = make_record_fields (snd e) gfs in
      let head = make_non_dep_record_fields (fst e) gf in
      head @ tl
  in
  let make_record (x:A.ident) =
    let fields = make_record_fields (T.Identifier x) gfs in
    Record td_name fields
  in
  let t = T_app td_name (List.map (fun (x, _) -> Inr (T.Identifier x)) td_params) in
  mk_parser pk t (Parse_map p (mk_lam make_record))

let translate_switch_case_type (sw:Ast.switch_case) =
  let sc, cases = sw in
  let sc = translate_expr sc in
  let translate_case ef : ML (list T.case) =
    let e, f = ef in
    let pat = translate_expr e in
    match f.v with
    | FieldComment _ -> []
    | Field sf ->
      let sf = translate_struct_field sf in
      let open T in
      [{
        pattern = pat;
        branch = sf.sf_typ
       }]
  in
  let cases = List.collect translate_case cases in
  T.T_match sc cases

let translate_decl (d:A.decl) : ML T.decl =
  match d.v with
  | Comment s -> T.Comment s

  | Define i s -> T.Definition (i, s)

  | Enum t i ids ->
    let tdn = {
        typedef_name = i;
        typedef_abbrev = with_dummy_range "";
        typedef_ptr_abbrev = with_dummy_range "";
      }
    in
    let typ = translate_typ t in
    let tdn = translate_typedef_name tdn [] in
    let refined_typ = make_enum_typ typ ids in
    let p = parse_typ refined_typ in
    let open T in
    Type_decl (
      {
        decl_name = tdn;
        decl_typ = TD_abbrev refined_typ;
        decl_parser = p;
        decl_validator = make_validator p;
      }
    )

  | Record tdn params ast_fields ->
    let tdn = translate_typedef_name tdn params in
    let fields = List.map translate_field ast_fields in
    let p = parse_fields tdn fields in
    let open T in
    Type_decl (
      {
        decl_name = tdn;
        decl_typ = TD_struct fields;
        decl_parser = p;
        decl_validator = make_validator p
      }
    )

  | CaseType tdn params switch_case ->
    let tdn = translate_typedef_name tdn params in
    let t = translate_switch_case_type switch_case in
    let p = parse_typ t in
    let open T in
    Type_decl (
      {
        decl_name = tdn;
        decl_typ = TD_abbrev t;
        decl_parser = p;
        decl_validator = make_validator p
      }
    )
