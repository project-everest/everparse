module COSE.AST.Old
open CDDL.Interpreter.Old
module Spec = COSE.Spec

#push-options "--fuel 0"

[@@ bounded_attr; sem_attr]
let e0 = empty_wf_ast_env

[@@ bounded_attr; sem_attr]
let e2 = wf_ast_env_extend_typ e0 "header_map"
  (_ by (solve_bounded ()))
  (TEscapeHatch Spec.header_map) // lem (TMap "header_map0"))
  (_ by (solve_bounded ()))
  (_ by (solve_spec_ast_env_elem_well_formed ()))

[@@ bounded_attr; sem_attr]
let e3 = wf_ast_env_extend_typ e2 "empty_or_serialized_map"
  (_ by (solve_bounded ()))
  (TEscapeHatch Spec.empty_or_serialized_map)
  (_ by (solve_bounded ()))
  (_ by (solve_spec_ast_env_elem_well_formed ()))

[@@ bounded_attr; sem_attr]
let e4 =
  wf_ast_env_extend_array_group e3 "headers"
    (_ by (solve_bounded ()))
    [
      "protected", TAAtom (TAElem (TDef "empty_or_serialized_map"));
      "unprotected", TAAtom (TAElem (TDef "header_map"));
    ]
    (_ by (solve_bounded ()))
    (_ by (solve_spec_ast_env_elem_well_formed ()))

let _ : squash (
  se_array_group e4.we_env.e_semenv "headers" `CDDL.Spec.array_group3_equiv` Spec.headers
) = 
  let a = (e4.we_env.e_env "headers") in
  assert (array_group_sem e4.we_env.e_semenv a `CDDL.Spec.array_group3_equiv` Spec.headers)
    by (solve_sem_equiv ())

[@@ bounded_attr; sem_attr]
let e5 = e4

[@@ bounded_attr; sem_attr]
let e6 =
  wf_ast_env_extend_typ e5 "cose_signature"
    (_ by (solve_bounded ()))
    (TArray [
      "headers", TAAtom (TADef "headers");
      "signature", TAAtom (TAElem (TByteString));
    ])
    (_ by (solve_bounded ()))
    (_ by (solve_spec_ast_env_elem_well_formed ()))

[@@ bounded_attr; sem_attr]
let e7 = e6

let _ : squash (
  se_typ e7.we_env.e_semenv "cose_signature" `CDDL.Spec.typ_equiv` Spec.cose_signature
) = 
  let a = (e7.we_env.e_env "cose_signature") in
  assert (typ_sem e7.we_env.e_semenv a `CDDL.Spec.typ_equiv` Spec.cose_signature)
    by (solve_sem_equiv ())

[@@ bounded_attr; sem_attr]
let e8 =
  wf_ast_env_extend_typ e7 "cose_sign_payload" 
    (_ by (solve_bounded ()))
    (TChoice [
      TByteString;
      (TLiteral (TLSimple CDDL.Spec.simple_value_nil));
    ])
    (_ by (solve_bounded ()))
    (_ by (solve_spec_ast_env_elem_well_formed ()))

[@@ bounded_attr; sem_attr]
let e9 = e8

[@@ bounded_attr; sem_attr]
let e10 = e9

[@@ bounded_attr; sem_attr]
let e11 =
  wf_ast_env_extend_typ e10 "cose_sign"
    (_ by (solve_bounded ()))
    (TArray [
      "headers", TAAtom (TADef "headers");
      "payload", TAAtom (TAElem (TDef "cose_sign_payload"));
      "signatures", TAAtom (TAElem (TElemArray (TAOneOrMore (TAElem (TDef "cose_signature")))));
    ])
    (_ by (solve_bounded ()))
    (_ by (solve_spec_ast_env_elem_well_formed ()))

#push-options "--z3rlimit 16" // cannot reason about typ_equiv

let _ : squash (
  se_typ e11.we_env.e_semenv "cose_sign" `CDDL.Spec.typ_equiv` Spec.cose_sign
) = 
  let a = (e11.we_env.e_env "cose_sign") in
  assert (typ_sem e11.we_env.e_semenv a `CDDL.Spec.typ_equiv` Spec.cose_sign)
    by (solve_sem_equiv ())

#pop-options

[@@ bounded_attr; sem_attr]
let e12 =
  wf_ast_env_extend_typ e11 "cose_sign_tagged"
    (_ by (solve_bounded ()))
    (TTag Spec.tag_cose_sign (TDef "cose_sign"))
    (_ by (solve_bounded ()))
    (_ by (solve_spec_ast_env_elem_well_formed ()))

#push-options "--z3rlimit 16" // cannot reason about typ_equiv

let _ : squash (
  se_typ e12.we_env.e_semenv "cose_sign_tagged" `CDDL.Spec.typ_equiv` Spec.cose_sign_tagged
) = 
  let a = (e12.we_env.e_env "cose_sign_tagged") in
  assert (typ_sem e12.we_env.e_semenv a `CDDL.Spec.typ_equiv` Spec.cose_sign_tagged)
    by (solve_sem_equiv ())

#pop-options

[@@ bounded_attr; sem_attr]
let e13 = e12

[@@ bounded_attr; sem_attr]
let e14 =
  wf_ast_env_extend_typ e13 "cose_sign1"
    (_ by (solve_bounded ()))
    (TArray [
      "headers", TAAtom (TADef "headers");
      "payload", TAAtom (TAElem (TDef "cose_sign_payload"));
      "signature", TAAtom (TAElem TByteString);
    ])
    (_ by (solve_bounded ()))
    (_ by (solve_spec_ast_env_elem_well_formed ()))

#push-options "--z3rlimit 16" // cannot reason about typ_equiv

let _ : squash (
  se_typ e14.we_env.e_semenv "cose_sign1" `CDDL.Spec.typ_equiv` Spec.cose_sign1
) = 
  let a = e14.we_env.e_env "cose_sign1" in
  assert (typ_sem e14.we_env.e_semenv a `CDDL.Spec.typ_equiv` Spec.cose_sign1)
    by (solve_sem_equiv ())

#pop-options

[@@ bounded_attr; sem_attr]
let e15 =
  wf_ast_env_extend_typ e14 "cose_sign1_tagged"
    (_ by (solve_bounded ()))
    (TTag Spec.tag_cose_sign1 (TDef "cose_sign1"))
    (_ by (solve_bounded ()))
    (_ by (solve_spec_ast_env_elem_well_formed ()))

#push-options "--z3rlimit 16" // cannot reason about typ_equiv

let _ : squash (
  se_typ e15.we_env.e_semenv "cose_sign1_tagged" `CDDL.Spec.typ_equiv` Spec.cose_sign1_tagged
) = 
  let a = (e15.we_env.e_env "cose_sign1_tagged") in
  assert (typ_sem e15.we_env.e_semenv a `CDDL.Spec.typ_equiv` Spec.cose_sign1_tagged)
    by (solve_sem_equiv ())

#pop-options

#pop-options
