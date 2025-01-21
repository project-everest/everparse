module CDDLTest
open CDDL.Pulse.AST.GenValidators
module Det = CDDL.Pulse.AST.Det.C
module Impl = CDDL.Pulse.AST.Validate
module T = CDDL.Spec.AST.Tactics
module SZ = FStar.SizeT

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let option_source = CDDL.Spec.AST.Plugin.parse ["cose.cddl"; "../spec/postlude.cddl"]

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let source = Some?.v option_source

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let option_sorted_source = topological_sort source

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source0 = Some?.v option_sorted_source

[@@noextract_to "krml"; sem_attr] noextract
let env0 : wf_ast_env = empty_ast_env

[@@noextract_to "krml"; sem_attr] noextract
let venv0 : Impl.validator_env Det.cbor_det_match env0.e_sem_env =
  Impl.empty_validator_env _

let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64)

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let defs = produce_defs 0 "" sorted_source0

let _ : unit = _ by (FStar.Tactics.print defs; FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("43 defs remaining. Producing definitions for bool"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf1 = compute_wf_typ env0 (T.pull_name sorted_source0) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source0) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf1' : ast0_wf_typ _ = wf1
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf1_eq : squash (wf1' == wf1) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_bool = Impl.validate_typ Det.cbor_det_impl venv0 true _ wf1'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env1 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env0 (T.pull_name sorted_source0) (T.pull_type sorted_source0) wf1
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv1 : Impl.validator_env Det.cbor_det_match env1.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv0 (T.pull_name sorted_source0) () _ validate_bool
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source1 = List.Tot.tl sorted_source0

let _ : unit = _ by (FStar.Tactics.print ("42 defs remaining. Producing definitions for everparse-no-match"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf2 = compute_wf_typ env1 (T.pull_name sorted_source1) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source1) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf2' : ast0_wf_typ _ = wf2
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf2_eq : squash (wf2' == wf2) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_everparsenomatch = Impl.validate_typ Det.cbor_det_impl venv1 true _ wf2'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env2 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env1 (T.pull_name sorted_source1) (T.pull_type sorted_source1) wf2
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv2 : Impl.validator_env Det.cbor_det_match env2.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv1 (T.pull_name sorted_source1) () _ validate_everparsenomatch
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source2 = List.Tot.tl sorted_source1

let _ : unit = _ by (FStar.Tactics.print ("41 defs remaining. Producing definitions for uint"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf3 = compute_wf_typ env2 (T.pull_name sorted_source2) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source2) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf3' : ast0_wf_typ _ = wf3
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf3_eq : squash (wf3' == wf3) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_uint = Impl.validate_typ Det.cbor_det_impl venv2 true _ wf3'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env3 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env2 (T.pull_name sorted_source2) (T.pull_type sorted_source2) wf3
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv3 : Impl.validator_env Det.cbor_det_match env3.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv2 (T.pull_name sorted_source2) () _ validate_uint
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source3 = List.Tot.tl sorted_source2

let _ : unit = _ by (FStar.Tactics.print ("40 defs remaining. Producing definitions for nint"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf4 = compute_wf_typ env3 (T.pull_name sorted_source3) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source3) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf4' : ast0_wf_typ _ = wf4
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf4_eq : squash (wf4' == wf4) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_nint = Impl.validate_typ Det.cbor_det_impl venv3 true _ wf4'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env4 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env3 (T.pull_name sorted_source3) (T.pull_type sorted_source3) wf4
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv4 : Impl.validator_env Det.cbor_det_match env4.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv3 (T.pull_name sorted_source3) () _ validate_nint
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source4 = List.Tot.tl sorted_source3

let _ : unit = _ by (FStar.Tactics.print ("39 defs remaining. Producing definitions for int"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf5 = compute_wf_typ env4 (T.pull_name sorted_source4) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source4) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf5' : ast0_wf_typ _ = wf5
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf5_eq : squash (wf5' == wf5) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_int = Impl.validate_typ Det.cbor_det_impl venv4 true _ wf5'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env5 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env4 (T.pull_name sorted_source4) (T.pull_type sorted_source4) wf5
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv5 : Impl.validator_env Det.cbor_det_match env5.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv4 (T.pull_name sorted_source4) () _ validate_int
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source5 = List.Tot.tl sorted_source4

let _ : unit = _ by (FStar.Tactics.print ("38 defs remaining. Producing definitions for bstr"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf6 = compute_wf_typ env5 (T.pull_name sorted_source5) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source5) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf6' : ast0_wf_typ _ = wf6
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf6_eq : squash (wf6' == wf6) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_bstr = Impl.validate_typ Det.cbor_det_impl venv5 true _ wf6'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env6 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env5 (T.pull_name sorted_source5) (T.pull_type sorted_source5) wf6
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv6 : Impl.validator_env Det.cbor_det_match env6.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv5 (T.pull_name sorted_source5) () _ validate_bstr
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source6 = List.Tot.tl sorted_source5

let _ : unit = _ by (FStar.Tactics.print ("37 defs remaining. Producing definitions for encoded-cbor"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf7 = compute_wf_typ env6 (T.pull_name sorted_source6) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source6) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf7' : ast0_wf_typ _ = wf7
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf7_eq : squash (wf7' == wf7) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_encodedcbor = Impl.validate_typ Det.cbor_det_impl venv6 true _ wf7'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env7 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env6 (T.pull_name sorted_source6) (T.pull_type sorted_source6) wf7
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv7 : Impl.validator_env Det.cbor_det_match env7.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv6 (T.pull_name sorted_source6) () _ validate_encodedcbor
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source7 = List.Tot.tl sorted_source6

let _ : unit = _ by (FStar.Tactics.print ("36 defs remaining. Producing definitions for bytes"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf8 = compute_wf_typ env7 (T.pull_name sorted_source7) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source7) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf8' : ast0_wf_typ _ = wf8
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf8_eq : squash (wf8' == wf8) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_bytes = Impl.validate_typ Det.cbor_det_impl venv7 true _ wf8'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env8 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env7 (T.pull_name sorted_source7) (T.pull_type sorted_source7) wf8
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv8 : Impl.validator_env Det.cbor_det_match env8.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv7 (T.pull_name sorted_source7) () _ validate_bytes
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source8 = List.Tot.tl sorted_source7

let _ : unit = _ by (FStar.Tactics.print ("35 defs remaining. Producing definitions for tstr"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf9 = compute_wf_typ env8 (T.pull_name sorted_source8) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source8) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf9' : ast0_wf_typ _ = wf9
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf9_eq : squash (wf9' == wf9) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_tstr = Impl.validate_typ Det.cbor_det_impl venv8 true _ wf9'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env9 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env8 (T.pull_name sorted_source8) (T.pull_type sorted_source8) wf9
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv9 : Impl.validator_env Det.cbor_det_match env9.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv8 (T.pull_name sorted_source8) () _ validate_tstr
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source9 = List.Tot.tl sorted_source8

let _ : unit = _ by (FStar.Tactics.print ("34 defs remaining. Producing definitions for label"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf10 = compute_wf_typ env9 (T.pull_name sorted_source9) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source9) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf10' : ast0_wf_typ _ = wf10
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf10_eq : squash (wf10' == wf10) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_label = Impl.validate_typ Det.cbor_det_impl venv9 true _ wf10'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env10 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env9 (T.pull_name sorted_source9) (T.pull_type sorted_source9) wf10
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv10 : Impl.validator_env Det.cbor_det_match env10.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv9 (T.pull_name sorted_source9) () _ validate_label
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source10 = List.Tot.tl sorted_source9

let _ : unit = _ by (FStar.Tactics.print ("33 defs remaining. Producing definitions for Generic_Headers"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env11 : wf_ast_env =
  wf_ast_env_extend_group env10 (T.pull_name sorted_source10) (T.pull_group sorted_source10) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ())) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ()))
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv11 : Impl.validator_env Det.cbor_det_match env11.e_sem_env =
  Impl.extend_validator_env_with_group venv10 (T.pull_name sorted_source10) (T.pull_group sorted_source10) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ())) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ()))
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source11 = List.Tot.tl sorted_source10

let _ : unit = _ by (FStar.Tactics.print ("32 defs remaining. Producing definitions for tdate"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf12 = compute_wf_typ env11 (T.pull_name sorted_source11) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source11) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf12' : ast0_wf_typ _ = wf12
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf12_eq : squash (wf12' == wf12) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_tdate = Impl.validate_typ Det.cbor_det_impl venv11 true _ wf12'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env12 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env11 (T.pull_name sorted_source11) (T.pull_type sorted_source11) wf12
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv12 : Impl.validator_env Det.cbor_det_match env12.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv11 (T.pull_name sorted_source11) () _ validate_tdate
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source12 = List.Tot.tl sorted_source11

let _ : unit = _ by (FStar.Tactics.print ("31 defs remaining. Producing definitions for uri"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf13 = compute_wf_typ env12 (T.pull_name sorted_source12) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source12) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf13' : ast0_wf_typ _ = wf13
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf13_eq : squash (wf13' == wf13) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_uri = Impl.validate_typ Det.cbor_det_impl venv12 true _ wf13'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env13 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env12 (T.pull_name sorted_source12) (T.pull_type sorted_source12) wf13
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv13 : Impl.validator_env Det.cbor_det_match env13.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv12 (T.pull_name sorted_source12) () _ validate_uri
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source13 = List.Tot.tl sorted_source12

let _ : unit = _ by (FStar.Tactics.print ("30 defs remaining. Producing definitions for b64url"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf14 = compute_wf_typ env13 (T.pull_name sorted_source13) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source13) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf14' : ast0_wf_typ _ = wf14
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf14_eq : squash (wf14' == wf14) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_b64url = Impl.validate_typ Det.cbor_det_impl venv13 true _ wf14'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env14 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env13 (T.pull_name sorted_source13) (T.pull_type sorted_source13) wf14
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv14 : Impl.validator_env Det.cbor_det_match env14.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv13 (T.pull_name sorted_source13) () _ validate_b64url
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source14 = List.Tot.tl sorted_source13

let _ : unit = _ by (FStar.Tactics.print ("29 defs remaining. Producing definitions for b64legacy"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf15 = compute_wf_typ env14 (T.pull_name sorted_source14) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source14) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf15' : ast0_wf_typ _ = wf15
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf15_eq : squash (wf15' == wf15) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_b64legacy = Impl.validate_typ Det.cbor_det_impl venv14 true _ wf15'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env15 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env14 (T.pull_name sorted_source14) (T.pull_type sorted_source14) wf15
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv15 : Impl.validator_env Det.cbor_det_match env15.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv14 (T.pull_name sorted_source14) () _ validate_b64legacy
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source15 = List.Tot.tl sorted_source14

let _ : unit = _ by (FStar.Tactics.print ("28 defs remaining. Producing definitions for regexp"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf16 = compute_wf_typ env15 (T.pull_name sorted_source15) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source15) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf16' : ast0_wf_typ _ = wf16
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf16_eq : squash (wf16' == wf16) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_regexp = Impl.validate_typ Det.cbor_det_impl venv15 true _ wf16'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env16 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env15 (T.pull_name sorted_source15) (T.pull_type sorted_source15) wf16
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv16 : Impl.validator_env Det.cbor_det_match env16.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv15 (T.pull_name sorted_source15) () _ validate_regexp
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source16 = List.Tot.tl sorted_source15

let _ : unit = _ by (FStar.Tactics.print ("27 defs remaining. Producing definitions for mime-message"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf17 = compute_wf_typ env16 (T.pull_name sorted_source16) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source16) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf17' : ast0_wf_typ _ = wf17
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf17_eq : squash (wf17' == wf17) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_mimemessage = Impl.validate_typ Det.cbor_det_impl venv16 true _ wf17'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env17 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env16 (T.pull_name sorted_source16) (T.pull_type sorted_source16) wf17
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv17 : Impl.validator_env Det.cbor_det_match env17.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv16 (T.pull_name sorted_source16) () _ validate_mimemessage
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source17 = List.Tot.tl sorted_source16

let _ : unit = _ by (FStar.Tactics.print ("26 defs remaining. Producing definitions for text"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf18 = compute_wf_typ env17 (T.pull_name sorted_source17) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source17) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf18' : ast0_wf_typ _ = wf18
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf18_eq : squash (wf18' == wf18) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_text = Impl.validate_typ Det.cbor_det_impl venv17 true _ wf18'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env18 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env17 (T.pull_name sorted_source17) (T.pull_type sorted_source17) wf18
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv18 : Impl.validator_env Det.cbor_det_match env18.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv17 (T.pull_name sorted_source17) () _ validate_text
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source18 = List.Tot.tl sorted_source17

let _ : unit = _ by (FStar.Tactics.print ("25 defs remaining. Producing definitions for false"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf19 = compute_wf_typ env18 (T.pull_name sorted_source18) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source18) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf19' : ast0_wf_typ _ = wf19
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf19_eq : squash (wf19' == wf19) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_false = Impl.validate_typ Det.cbor_det_impl venv18 true _ wf19'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env19 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env18 (T.pull_name sorted_source18) (T.pull_type sorted_source18) wf19
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv19 : Impl.validator_env Det.cbor_det_match env19.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv18 (T.pull_name sorted_source18) () _ validate_false
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source19 = List.Tot.tl sorted_source18

let _ : unit = _ by (FStar.Tactics.print ("24 defs remaining. Producing definitions for true"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf20 = compute_wf_typ env19 (T.pull_name sorted_source19) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source19) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf20' : ast0_wf_typ _ = wf20
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf20_eq : squash (wf20' == wf20) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_true = Impl.validate_typ Det.cbor_det_impl venv19 true _ wf20'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env20 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env19 (T.pull_name sorted_source19) (T.pull_type sorted_source19) wf20
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv20 : Impl.validator_env Det.cbor_det_match env20.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv19 (T.pull_name sorted_source19) () _ validate_true
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source20 = List.Tot.tl sorted_source19

let _ : unit = _ by (FStar.Tactics.print ("23 defs remaining. Producing definitions for nil"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf21 = compute_wf_typ env20 (T.pull_name sorted_source20) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source20) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf21' : ast0_wf_typ _ = wf21
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf21_eq : squash (wf21' == wf21) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_nil = Impl.validate_typ Det.cbor_det_impl venv20 true _ wf21'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env21 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env20 (T.pull_name sorted_source20) (T.pull_type sorted_source20) wf21
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv21 : Impl.validator_env Det.cbor_det_match env21.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv20 (T.pull_name sorted_source20) () _ validate_nil
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source21 = List.Tot.tl sorted_source20

let _ : unit = _ by (FStar.Tactics.print ("22 defs remaining. Producing definitions for null"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf22 = compute_wf_typ env21 (T.pull_name sorted_source21) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source21) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf22' : ast0_wf_typ _ = wf22
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf22_eq : squash (wf22' == wf22) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_null = Impl.validate_typ Det.cbor_det_impl venv21 true _ wf22'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env22 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env21 (T.pull_name sorted_source21) (T.pull_type sorted_source21) wf22
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv22 : Impl.validator_env Det.cbor_det_match env22.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv21 (T.pull_name sorted_source21) () _ validate_null
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source22 = List.Tot.tl sorted_source21

let _ : unit = _ by (FStar.Tactics.print ("21 defs remaining. Producing definitions for undefined"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf23 = compute_wf_typ env22 (T.pull_name sorted_source22) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source22) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf23' : ast0_wf_typ _ = wf23
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf23_eq : squash (wf23' == wf23) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_undefined = Impl.validate_typ Det.cbor_det_impl venv22 true _ wf23'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env23 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env22 (T.pull_name sorted_source22) (T.pull_type sorted_source22) wf23
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv23 : Impl.validator_env Det.cbor_det_match env23.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv22 (T.pull_name sorted_source22) () _ validate_undefined
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source23 = List.Tot.tl sorted_source22

let _ : unit = _ by (FStar.Tactics.print ("20 defs remaining. Producing definitions for any"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf24 = compute_wf_typ env23 (T.pull_name sorted_source23) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source23) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf24' : ast0_wf_typ _ = wf24
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf24_eq : squash (wf24' == wf24) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_any = Impl.validate_typ Det.cbor_det_impl venv23 true _ wf24'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env24 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env23 (T.pull_name sorted_source23) (T.pull_type sorted_source23) wf24
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv24 : Impl.validator_env Det.cbor_det_match env24.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv23 (T.pull_name sorted_source23) () _ validate_any
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source24 = List.Tot.tl sorted_source23

let _ : unit = _ by (FStar.Tactics.print ("19 defs remaining. Producing definitions for values"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf25 = compute_wf_typ env24 (T.pull_name sorted_source24) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source24) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf25' : ast0_wf_typ _ = wf25
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf25_eq : squash (wf25' == wf25) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_values = Impl.validate_typ Det.cbor_det_impl venv24 true _ wf25'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env25 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env24 (T.pull_name sorted_source24) (T.pull_type sorted_source24) wf25
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv25 : Impl.validator_env Det.cbor_det_match env25.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv24 (T.pull_name sorted_source24) () _ validate_values
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source25 = List.Tot.tl sorted_source24

let _ : unit = _ by (FStar.Tactics.print ("18 defs remaining. Producing definitions for header_map"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf26 = compute_wf_typ env25 (T.pull_name sorted_source25) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source25) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf26' : ast0_wf_typ _ = wf26
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf26_eq : squash (wf26' == wf26) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_header_map = Impl.validate_typ Det.cbor_det_impl venv25 true _ wf26'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env26 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env25 (T.pull_name sorted_source25) (T.pull_type sorted_source25) wf26
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv26 : Impl.validator_env Det.cbor_det_match env26.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv25 (T.pull_name sorted_source25) () _ validate_header_map
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source26 = List.Tot.tl sorted_source25

let _ : unit = _ by (FStar.Tactics.print ("17 defs remaining. Producing definitions for empty_or_serialized_map"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf27 = compute_wf_typ env26 (T.pull_name sorted_source26) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source26) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf27' : ast0_wf_typ _ = wf27
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf27_eq : squash (wf27' == wf27) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_empty_or_serialized_map = Impl.validate_typ Det.cbor_det_impl venv26 true _ wf27'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env27 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env26 (T.pull_name sorted_source26) (T.pull_type sorted_source26) wf27
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv27 : Impl.validator_env Det.cbor_det_match env27.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv26 (T.pull_name sorted_source26) () _ validate_empty_or_serialized_map
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source27 = List.Tot.tl sorted_source26

let _ : unit = _ by (FStar.Tactics.print ("16 defs remaining. Producing definitions for Headers"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env28 : wf_ast_env =
  wf_ast_env_extend_group env27 (T.pull_name sorted_source27) (T.pull_group sorted_source27) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ())) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ()))
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv28 : Impl.validator_env Det.cbor_det_match env28.e_sem_env =
  Impl.extend_validator_env_with_group venv27 (T.pull_name sorted_source27) (T.pull_group sorted_source27) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ())) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ()))
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source28 = List.Tot.tl sorted_source27

let _ : unit = _ by (FStar.Tactics.print ("15 defs remaining. Producing definitions for COSE_Signature"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf29 = compute_wf_typ env28 (T.pull_name sorted_source28) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source28) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf29' : ast0_wf_typ _ = wf29
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf29_eq : squash (wf29' == wf29) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_COSE_Signature = Impl.validate_typ Det.cbor_det_impl venv28 true _ wf29'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env29 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env28 (T.pull_name sorted_source28) (T.pull_type sorted_source28) wf29
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv29 : Impl.validator_env Det.cbor_det_match env29.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv28 (T.pull_name sorted_source28) () _ validate_COSE_Signature
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source29 = List.Tot.tl sorted_source28

let _ : unit = _ by (FStar.Tactics.print ("14 defs remaining. Producing definitions for COSE_Sign"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf30 = compute_wf_typ env29 (T.pull_name sorted_source29) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source29) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf30' : ast0_wf_typ _ = wf30
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf30_eq : squash (wf30' == wf30) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_COSE_Sign = Impl.validate_typ Det.cbor_det_impl venv29 true _ wf30'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env30 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env29 (T.pull_name sorted_source29) (T.pull_type sorted_source29) wf30
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv30 : Impl.validator_env Det.cbor_det_match env30.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv29 (T.pull_name sorted_source29) () _ validate_COSE_Sign
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source30 = List.Tot.tl sorted_source29

let _ : unit = _ by (FStar.Tactics.print ("13 defs remaining. Producing definitions for COSE_Sign_Tagged"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf31 = compute_wf_typ env30 (T.pull_name sorted_source30) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source30) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf31' : ast0_wf_typ _ = wf31
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf31_eq : squash (wf31' == wf31) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_COSE_Sign_Tagged = Impl.validate_typ Det.cbor_det_impl venv30 true _ wf31'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env31 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env30 (T.pull_name sorted_source30) (T.pull_type sorted_source30) wf31
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv31 : Impl.validator_env Det.cbor_det_match env31.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv30 (T.pull_name sorted_source30) () _ validate_COSE_Sign_Tagged
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source31 = List.Tot.tl sorted_source30

let _ : unit = _ by (FStar.Tactics.print ("12 defs remaining. Producing definitions for COSE_Sign1"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf32 = compute_wf_typ env31 (T.pull_name sorted_source31) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source31) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf32' : ast0_wf_typ _ = wf32
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf32_eq : squash (wf32' == wf32) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_COSE_Sign1 = Impl.validate_typ Det.cbor_det_impl venv31 true _ wf32'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env32 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env31 (T.pull_name sorted_source31) (T.pull_type sorted_source31) wf32
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv32 : Impl.validator_env Det.cbor_det_match env32.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv31 (T.pull_name sorted_source31) () _ validate_COSE_Sign1
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source32 = List.Tot.tl sorted_source31

let _ : unit = _ by (FStar.Tactics.print ("11 defs remaining. Producing definitions for COSE_Untagged_Message"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf33 = compute_wf_typ env32 (T.pull_name sorted_source32) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source32) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf33' : ast0_wf_typ _ = wf33
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf33_eq : squash (wf33' == wf33) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_COSE_Untagged_Message = Impl.validate_typ Det.cbor_det_impl venv32 true _ wf33'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env33 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env32 (T.pull_name sorted_source32) (T.pull_type sorted_source32) wf33
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv33 : Impl.validator_env Det.cbor_det_match env33.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv32 (T.pull_name sorted_source32) () _ validate_COSE_Untagged_Message
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source33 = List.Tot.tl sorted_source32

let _ : unit = _ by (FStar.Tactics.print ("10 defs remaining. Producing definitions for COSE_Sign1_Tagged"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf34 = compute_wf_typ env33 (T.pull_name sorted_source33) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source33) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf34' : ast0_wf_typ _ = wf34
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf34_eq : squash (wf34' == wf34) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_COSE_Sign1_Tagged = Impl.validate_typ Det.cbor_det_impl venv33 true _ wf34'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env34 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env33 (T.pull_name sorted_source33) (T.pull_type sorted_source33) wf34
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv34 : Impl.validator_env Det.cbor_det_match env34.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv33 (T.pull_name sorted_source33) () _ validate_COSE_Sign1_Tagged
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source34 = List.Tot.tl sorted_source33

let _ : unit = _ by (FStar.Tactics.print ("9 defs remaining. Producing definitions for COSE_Tagged_Message"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf35 = compute_wf_typ env34 (T.pull_name sorted_source34) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source34) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf35' : ast0_wf_typ _ = wf35
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf35_eq : squash (wf35' == wf35) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_COSE_Tagged_Message = Impl.validate_typ Det.cbor_det_impl venv34 true _ wf35'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env35 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env34 (T.pull_name sorted_source34) (T.pull_type sorted_source34) wf35
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv35 : Impl.validator_env Det.cbor_det_match env35.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv34 (T.pull_name sorted_source34) () _ validate_COSE_Tagged_Message
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source35 = List.Tot.tl sorted_source34

let _ : unit = _ by (FStar.Tactics.print ("8 defs remaining. Producing definitions for COSE_Messages"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf36 = compute_wf_typ env35 (T.pull_name sorted_source35) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source35) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf36' : ast0_wf_typ _ = wf36
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf36_eq : squash (wf36' == wf36) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_COSE_Messages = Impl.validate_typ Det.cbor_det_impl venv35 true _ wf36'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env36 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env35 (T.pull_name sorted_source35) (T.pull_type sorted_source35) wf36
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv36 : Impl.validator_env Det.cbor_det_match env36.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv35 (T.pull_name sorted_source35) () _ validate_COSE_Messages
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source36 = List.Tot.tl sorted_source35

let _ : unit = _ by (FStar.Tactics.print ("7 defs remaining. Producing definitions for Sig_structure"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf37 = compute_wf_typ env36 (T.pull_name sorted_source36) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source36) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf37' : ast0_wf_typ _ = wf37
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf37_eq : squash (wf37' == wf37) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_Sig_structure = Impl.validate_typ Det.cbor_det_impl venv36 true _ wf37'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env37 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env36 (T.pull_name sorted_source36) (T.pull_type sorted_source36) wf37
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv37 : Impl.validator_env Det.cbor_det_match env37.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv36 (T.pull_name sorted_source36) () _ validate_Sig_structure
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source37 = List.Tot.tl sorted_source36

let _ : unit = _ by (FStar.Tactics.print ("6 defs remaining. Producing definitions for Internal_Types"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf38 = compute_wf_typ env37 (T.pull_name sorted_source37) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source37) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf38' : ast0_wf_typ _ = wf38
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf38_eq : squash (wf38' == wf38) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_Internal_Types = Impl.validate_typ Det.cbor_det_impl venv37 true _ wf38'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env38 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env37 (T.pull_name sorted_source37) (T.pull_type sorted_source37) wf38
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv38 : Impl.validator_env Det.cbor_det_match env38.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv37 (T.pull_name sorted_source37) () _ validate_Internal_Types
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source38 = List.Tot.tl sorted_source37

let _ : unit = _ by (FStar.Tactics.print ("5 defs remaining. Producing definitions for start"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf39 = compute_wf_typ env38 (T.pull_name sorted_source38) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source38) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf39' : ast0_wf_typ _ = wf39
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf39_eq : squash (wf39' == wf39) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_start = Impl.validate_typ Det.cbor_det_impl venv38 true _ wf39'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env39 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env38 (T.pull_name sorted_source38) (T.pull_type sorted_source38) wf39
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv39 : Impl.validator_env Det.cbor_det_match env39.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv38 (T.pull_name sorted_source38) () _ validate_start
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source39 = List.Tot.tl sorted_source38

let _ : unit = _ by (FStar.Tactics.print ("4 defs remaining. Producing definitions for eb64url"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf40 = compute_wf_typ env39 (T.pull_name sorted_source39) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source39) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf40' : ast0_wf_typ _ = wf40
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf40_eq : squash (wf40' == wf40) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_eb64url = Impl.validate_typ Det.cbor_det_impl venv39 true _ wf40'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env40 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env39 (T.pull_name sorted_source39) (T.pull_type sorted_source39) wf40
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv40 : Impl.validator_env Det.cbor_det_match env40.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv39 (T.pull_name sorted_source39) () _ validate_eb64url
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source40 = List.Tot.tl sorted_source39

let _ : unit = _ by (FStar.Tactics.print ("3 defs remaining. Producing definitions for eb64legacy"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf41 = compute_wf_typ env40 (T.pull_name sorted_source40) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source40) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf41' : ast0_wf_typ _ = wf41
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf41_eq : squash (wf41' == wf41) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_eb64legacy = Impl.validate_typ Det.cbor_det_impl venv40 true _ wf41'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env41 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env40 (T.pull_name sorted_source40) (T.pull_type sorted_source40) wf41
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv41 : Impl.validator_env Det.cbor_det_match env41.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv40 (T.pull_name sorted_source40) () _ validate_eb64legacy
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source41 = List.Tot.tl sorted_source40

let _ : unit = _ by (FStar.Tactics.print ("2 defs remaining. Producing definitions for eb16"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf42 = compute_wf_typ env41 (T.pull_name sorted_source41) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source41) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf42' : ast0_wf_typ _ = wf42
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf42_eq : squash (wf42' == wf42) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_eb16 = Impl.validate_typ Det.cbor_det_impl venv41 true _ wf42'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env42 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env41 (T.pull_name sorted_source41) (T.pull_type sorted_source41) wf42
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv42 : Impl.validator_env Det.cbor_det_match env42.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv41 (T.pull_name sorted_source41) () _ validate_eb16
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source42 = List.Tot.tl sorted_source41

let _ : unit = _ by (FStar.Tactics.print ("1 defs remaining. Producing definitions for cbor-any"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf43 = compute_wf_typ env42 (T.pull_name sorted_source42) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source42) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf43' : ast0_wf_typ _ = wf43
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf43_eq : squash (wf43' == wf43) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate_cborany = Impl.validate_typ Det.cbor_det_impl venv42 true _ wf43'
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env43 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env42 (T.pull_name sorted_source42) (T.pull_type sorted_source42) wf43
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv43 : Impl.validator_env Det.cbor_det_match env43.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv42 (T.pull_name sorted_source42) () _ validate_cborany
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source43 = List.Tot.tl sorted_source42
