module COSE.AST
open CDDL.Interpreter
module Spec = COSE.Spec

#push-options "--fuel 0 --ifuel 0"

[@@  sem_attr]
let e0 = empty_total_env

[@@  sem_attr]
let generic_headers: group NMapGroup =
  GZeroOrOne (GMapElem () false (TElem (ELiteral (LInt CBOR.Spec.Constants.cbor_major_type_uint64 Spec.h_alg))) tint)

// expected: `option (either U64.t U64.t & ... )`



[@@  sem_attr]
let header_map = TMap generic_headers

let header_map_wf = // PLEASE normalize this
  compute_wf_typ
    e0.te_ast.ta_ast
    "header_map"
    (_ by (solve_by_norm ()))
    header_map
    (_ by (solve_mk_wf_typ_fuel_for ()))

inline_for_extraction noextract
let e1 = total_env_extend_typ
  e0
  "header_map"
  header_map
  header_map_wf
  _ (CDDL.Spec.bij_id _)
  _ (CDDL.Spec.bij_id _)

let header_map_validator = e1.te_impl_validate "header_map" //PLEASE normalize
let header_map_parser = e1.te_impl_parse "header_map" //PLEASE normalize
let header_map_serializer = e1.te_impl_serialize "header_map" //PLEASE normalize

inline_for_extraction noextract
let e2 = total_env_replace
  e1
  "header_map"
  () // (_ by (solve_by_norm ()))
  header_map_validator
  header_map_parser
  header_map_serializer


(*
1 => string
2 => int
* (int => any)


let header_map_wf = e0.te_impl_validate

l

irreducible let print (#t: Type) (x: t) : prop = False

// let _ : squash (print (e1.e_wf "header_map"))  = (_ by (solve_by_norm (); FStar.Tactics.fail "abc"))
