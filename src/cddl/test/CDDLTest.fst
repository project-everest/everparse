module CDDLTest
open CDDL.Spec.AST.Driver
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

[@@noextract_to "krml"] noextract
let wf1 = compute_wf_typ env0 (T.pull_name sorted_source0) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source0) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf1' : ast0_wf_typ _ = wf1

[@@noextract_to "krml"] noextract
let wf1_eq : squash (wf1' == wf1) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate1 = Impl.validate_typ Det.cbor_det_impl venv0 true _ wf1'

[@@noextract_to "krml"; sem_attr] noextract
let env1 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env0 (T.pull_name sorted_source0) (T.pull_type sorted_source0) wf1

[@@noextract_to "krml"; sem_attr] noextract
let venv1 : Impl.validator_env Det.cbor_det_match env1.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv0 (T.pull_name sorted_source0) () _ validate1

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source1 = List.Tot.tl sorted_source0


[@@noextract_to "krml"] noextract
let wf2 = compute_wf_typ env1 (T.pull_name sorted_source1) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source1) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf2' : ast0_wf_typ _ = wf2

[@@noextract_to "krml"] noextract
let wf2_eq : squash (wf2' == wf2) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate2 = Impl.validate_typ Det.cbor_det_impl venv1 true _ wf2'

[@@noextract_to "krml"; sem_attr] noextract
let env2 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env1 (T.pull_name sorted_source1) (T.pull_type sorted_source1) wf2

[@@noextract_to "krml"; sem_attr] noextract
let venv2 : Impl.validator_env Det.cbor_det_match env2.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv1 (T.pull_name sorted_source1) () _ validate2

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source2 = List.Tot.tl sorted_source1


[@@noextract_to "krml"] noextract
let wf3 = compute_wf_typ env2 (T.pull_name sorted_source2) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source2) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf3' : ast0_wf_typ _ = wf3

[@@noextract_to "krml"] noextract
let wf3_eq : squash (wf3' == wf3) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate3 = Impl.validate_typ Det.cbor_det_impl venv2 true _ wf3'

[@@noextract_to "krml"; sem_attr] noextract
let env3 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env2 (T.pull_name sorted_source2) (T.pull_type sorted_source2) wf3

[@@noextract_to "krml"; sem_attr] noextract
let venv3 : Impl.validator_env Det.cbor_det_match env3.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv2 (T.pull_name sorted_source2) () _ validate3

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source3 = List.Tot.tl sorted_source2


[@@noextract_to "krml"] noextract
let wf4 = compute_wf_typ env3 (T.pull_name sorted_source3) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source3) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf4' : ast0_wf_typ _ = wf4

[@@noextract_to "krml"] noextract
let wf4_eq : squash (wf4' == wf4) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate4 = Impl.validate_typ Det.cbor_det_impl venv3 true _ wf4'

[@@noextract_to "krml"; sem_attr] noextract
let env4 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env3 (T.pull_name sorted_source3) (T.pull_type sorted_source3) wf4

[@@noextract_to "krml"; sem_attr] noextract
let venv4 : Impl.validator_env Det.cbor_det_match env4.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv3 (T.pull_name sorted_source3) () _ validate4

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source4 = List.Tot.tl sorted_source3


[@@noextract_to "krml"] noextract
let wf5 = compute_wf_typ env4 (T.pull_name sorted_source4) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source4) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf5' : ast0_wf_typ _ = wf5

[@@noextract_to "krml"] noextract
let wf5_eq : squash (wf5' == wf5) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate5 = Impl.validate_typ Det.cbor_det_impl venv4 true _ wf5'

[@@noextract_to "krml"; sem_attr] noextract
let env5 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env4 (T.pull_name sorted_source4) (T.pull_type sorted_source4) wf5

[@@noextract_to "krml"; sem_attr] noextract
let venv5 : Impl.validator_env Det.cbor_det_match env5.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv4 (T.pull_name sorted_source4) () _ validate5

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source5 = List.Tot.tl sorted_source4


[@@noextract_to "krml"] noextract
let wf6 = compute_wf_typ env5 (T.pull_name sorted_source5) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source5) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf6' : ast0_wf_typ _ = wf6

[@@noextract_to "krml"] noextract
let wf6_eq : squash (wf6' == wf6) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate6 = Impl.validate_typ Det.cbor_det_impl venv5 true _ wf6'

[@@noextract_to "krml"; sem_attr] noextract
let env6 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env5 (T.pull_name sorted_source5) (T.pull_type sorted_source5) wf6

[@@noextract_to "krml"; sem_attr] noextract
let venv6 : Impl.validator_env Det.cbor_det_match env6.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv5 (T.pull_name sorted_source5) () _ validate6

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source6 = List.Tot.tl sorted_source5


[@@noextract_to "krml"] noextract
let wf7 = compute_wf_typ env6 (T.pull_name sorted_source6) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source6) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf7' : ast0_wf_typ _ = wf7

[@@noextract_to "krml"] noextract
let wf7_eq : squash (wf7' == wf7) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate7 = Impl.validate_typ Det.cbor_det_impl venv6 true _ wf7'

[@@noextract_to "krml"; sem_attr] noextract
let env7 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env6 (T.pull_name sorted_source6) (T.pull_type sorted_source6) wf7

[@@noextract_to "krml"; sem_attr] noextract
let venv7 : Impl.validator_env Det.cbor_det_match env7.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv6 (T.pull_name sorted_source6) () _ validate7

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source7 = List.Tot.tl sorted_source6



[@@noextract_to "krml"] noextract
let wf8 = compute_wf_typ env7 (T.pull_name sorted_source7) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source7) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf8' : ast0_wf_typ _ = wf8

[@@noextract_to "krml"] noextract
let wf8_eq : squash (wf8' == wf8) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate8 = Impl.validate_typ Det.cbor_det_impl venv7 true _ wf8'

[@@noextract_to "krml"; sem_attr] noextract
let env8 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env7 (T.pull_name sorted_source7) (T.pull_type sorted_source7) wf8

[@@noextract_to "krml"; sem_attr] noextract
let venv8 : Impl.validator_env Det.cbor_det_match env8.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv7 (T.pull_name sorted_source7) () _ validate8

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source8 = List.Tot.tl sorted_source7


[@@noextract_to "krml"] noextract
let wf9 = compute_wf_typ env8 (T.pull_name sorted_source8) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source8) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf9' : ast0_wf_typ _ = wf9

[@@noextract_to "krml"] noextract
let wf9_eq : squash (wf9' == wf9) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate9 = Impl.validate_typ Det.cbor_det_impl venv8 true _ wf9'

[@@noextract_to "krml"; sem_attr] noextract
let env9 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env8 (T.pull_name sorted_source8) (T.pull_type sorted_source8) wf9

[@@noextract_to "krml"; sem_attr] noextract
let venv9 : Impl.validator_env Det.cbor_det_match env9.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv8 (T.pull_name sorted_source8) () _ validate9

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source9 = List.Tot.tl sorted_source8


[@@noextract_to "krml"] noextract
let wf10 = compute_wf_typ env9 (T.pull_name sorted_source9) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source9) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf10' : ast0_wf_typ _ = wf10

[@@noextract_to "krml"] noextract
let wf10_eq : squash (wf10' == wf10) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate10 = Impl.validate_typ Det.cbor_det_impl venv9 true _ wf10'

[@@noextract_to "krml"; sem_attr] noextract
let env10 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env9 (T.pull_name sorted_source9) (T.pull_type sorted_source9) wf10

[@@noextract_to "krml"; sem_attr] noextract
let venv10 : Impl.validator_env Det.cbor_det_match env10.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv9 (T.pull_name sorted_source9) () _ validate10

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source10 = List.Tot.tl sorted_source9


[@@noextract_to "krml"; sem_attr] noextract
let env11 : wf_ast_env =
  wf_ast_env_extend_group env10 (T.pull_name sorted_source10) (T.pull_group sorted_source10) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ())) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ()))

[@@noextract_to "krml"; sem_attr] noextract
let venv11 : Impl.validator_env Det.cbor_det_match env11.e_sem_env =
  Impl.extend_validator_env_with_group venv10 (T.pull_name sorted_source10) (T.pull_group sorted_source10) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ())) (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source11 = List.Tot.tl sorted_source10


[@@noextract_to "krml"] noextract
let wf12 = compute_wf_typ env11 (T.pull_name sorted_source11) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source11) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf12' : ast0_wf_typ _ = wf12

[@@noextract_to "krml"] noextract
let wf12_eq : squash (wf12' == wf12) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate12 = Impl.validate_typ Det.cbor_det_impl venv11 true _ wf12'

[@@noextract_to "krml"; sem_attr] noextract
let env12 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env11 (T.pull_name sorted_source11) (T.pull_type sorted_source11) wf12

[@@noextract_to "krml"; sem_attr] noextract
let venv12 : Impl.validator_env Det.cbor_det_match env12.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv11 (T.pull_name sorted_source11) () _ validate12

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source12 = List.Tot.tl sorted_source11


[@@noextract_to "krml"] noextract
let wf13 = compute_wf_typ env12 (T.pull_name sorted_source12) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source12) (_ by (T.solve_mk_wf_typ_fuel_for ()))

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf13' : ast0_wf_typ _ = wf13

[@@noextract_to "krml"] noextract
let wf13_eq : squash (wf13' == wf13) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())

// TODO: extract the name of the type into the name of the validator
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ())]
let validate13 = Impl.validate_typ Det.cbor_det_impl venv12 true _ wf13'

[@@noextract_to "krml"; sem_attr] noextract
let env13 : wf_ast_env =
  wf_ast_env_extend_typ_with_weak env12 (T.pull_name sorted_source12) (T.pull_type sorted_source12) wf13

[@@noextract_to "krml"; sem_attr] noextract
let venv13 : Impl.validator_env Det.cbor_det_match env13.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv12 (T.pull_name sorted_source12) () _ validate13

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source13 = List.Tot.tl sorted_source12
