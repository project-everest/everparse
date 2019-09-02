module Simplify
open Ast
open FStar.All
module B = Binding

let rec simplify_expr (env:B.env) (e:expr)
  : ML expr
  = match e.v with
    | This -> failwith "Impossible: should have been eliminated already"
    | App SizeOf _ ->
      begin
      match B.value_of_const_expr env e with
      | Some (Inr n) -> with_range (Constant (Int n)) e.range
      | _ -> B.error "Could not evaluate sizeof to a compile-time constant" e.range
      end
    | App op es ->
      let es = List.map (simplify_expr env) es in
      { e with v = App op es }

    | _ -> e

let simplify_typ (env:B.env) (t:typ)
  : ML typ
  = match t.v with
    | Type_app s es ->
      let es = List.map (simplify_expr env) es in
      { t with v = Type_app s es }

let simplify_field (env:B.env) (f:field)
  : ML field
  = match f.v with
    | FieldComment _ -> f
    | Field sf ->
      let ft = simplify_typ env sf.field_type in
      let fa = sf.field_array_opt |> B.map_opt (simplify_expr env) in
      let fc = sf.field_constraint |> B.map_opt (simplify_expr env) in
      let sf = { sf with field_type = ft;
                         field_array_opt = fa; 
                         field_constraint = fc } in
      with_range (Field sf) f.range

let simplify_decl (env:B.env) (d:decl) : ML decl =
  match d.v with
  | Comment _ -> d

  | Define i c -> d

  | TypeAbbrev t i ->
    { d with v = TypeAbbrev (simplify_typ env t) i }

  | Enum t i cases ->
    let t = simplify_typ env t in
    { d with v = Enum t i cases }

  | Record tdnames params fields ->
    let params = List.map (fun (t, i) -> simplify_typ env t, i) params in
    let fields = List.map (simplify_field env) fields in
    { d with v = Record tdnames params fields }

  | CaseType tdnames params switch ->
    let params = List.map (fun (t, i) -> simplify_typ env t, i) params in 
    let hd, cases = switch in
    let hd = simplify_expr env hd in
    let cases = List.map (fun (e, f) -> simplify_expr env e, simplify_field env f) cases in
    { d with v=CaseType tdnames params (hd, cases) }

let simplify_prog (env:B.global_env) (p:B.prog) =
  let env = B.mk_env env in
  List.map (simplify_decl env) p
