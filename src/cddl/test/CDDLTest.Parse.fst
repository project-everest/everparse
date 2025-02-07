module CDDLTest.Parse
open CDDL.Pulse.AST.Env
open CDDL.Pulse.AST.GenValidators
module Det = CDDL.Pulse.AST.Det.C
module Impl = CDDL.Pulse.AST.Validate
module Parse = CDDL.Pulse.AST.Parse
module T = CDDL.Spec.AST.Tactics
module SZ = FStar.SizeT

  [@@ noextract_to "krml"; sem_attr]
  noextract
  let sorted_source0 =
    [
      "zint", DType (TChoice (TElem EUInt) (TElem ENInt))
    ]

[@@noextract_to "krml"] noextract
let env0 : spec_and_impl_env Det.cbor_det_impl = empty_spec_and_impl_env _

[@@noextract_to "krml"; sem_attr] noextract
let avenv0 : Parse.ancillary_validate_env Det.cbor_det_match env0.si_ast.e_sem_env =
  fun _ -> None

[@@noextract_to "krml"; sem_attr] noextract
let aenv0 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r env0.si_sp =
  fun _ _ -> None

[@@noextract_to "krml"; sem_attr] noextract
let aaenv0 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r env0.si_sp =
  fun _ _ -> None

let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64)

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let defs = produce_defs sorted_source0

let _ : unit = _ by (FStar.Tactics.print defs; FStar.Tactics.exact (`()))

(*
