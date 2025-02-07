module CDDLTest.Validate
open CDDL.Pulse.AST.Env
open CDDL.Pulse.AST.GenValidators
module Det = CDDL.Pulse.AST.Det.C
module Impl = CDDL.Pulse.AST.Validate
module Parse = CDDL.Pulse.AST.Parse
module T = CDDL.Spec.AST.Tactics
module SZ = FStar.SizeT

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let option_source = CDDL.Spec.AST.Plugin.parse ["cose.cddl"; "../spec/postlude.cddl"]
(*
    Some
    [
      "int", DType (TChoice (TDef "uint") (TDef "nint"));
      "uint", DType (TElem EUInt);
      "nint", DType (TElem ENInt)
    ]
*)

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let source = Some?.v option_source

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let option_sorted_source = topological_sort source

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source0 = Some?.v option_sorted_source

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
fstar.exe  --load_cmxs evercddl_lib --load_cmxs evercddl_plugin --warn_error -342 --odir _output   --include /home/tahina/everest/everparse/src/cbor/spec --include /home/tahina/everest/everparse/src/cddl/spec --include /home/tahina/everest/everparse/lib/evercddl/lib --include /home/tahina/everest/everparse/lib/evercddl/plugin --include /home/tahina/everest/everparse/src/cbor/pulse --include /home/tahina/everest/everparse/src/cddl/pulse --include /home/tahina/everest/karamel/krmllib --include /home/tahina/everest/karamel/krmllib/obj --include /home/tahina/everest/pulse/out/lib/pulse --include . --cache_checked_modules --warn_error @241 --already_cached PulseCore,Pulse,C,LowStar,*,-CDDLTest,Prims,FStar,LowStar --cmi --ext context_pruning   CDDLTest.Validate.fst
TAC>> 
*)

let _ : unit = _ by (FStar.Tactics.print ("43 defs remaining. Producing definitions for bool"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf1 = compute_wf_typ env0.si_ast (T.pull_name sorted_source0) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source0) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf1' : ast0_wf_typ _ = wf1
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf1_eq : squash (wf1' == wf1) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_bool = Impl.validate_typ Det.cbor_det_impl env0.si_v true _ wf1'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_bool' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r (target_type_of_wf_typ wf1')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_bool = impltype_bool'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_bool : squash (impltype_bool' == impltype_bool) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_bool' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env0.si_sp wf1').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r (target_type_of_wf_typ wf1')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_bool = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env0.si_sp wf1').parser #impltype_bool (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r (target_type_of_wf_typ wf1')).sem_rel impltype_bool eqimpltype_bool)
let eqparsertype_bool : squash (parsertype_bool' == parsertype_bool) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env0.si_sp wf1').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r (target_type_of_wf_typ wf1')).sem_rel impltype_bool eqimpltype_bool
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_bool : parsertype_bool = T.inline_coerce_eq eqparsertype_bool (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env0.si_v env0.si_r env0.si_sp env0.si_p avenv0 aenv0 aaenv0 wf1' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_bool' : parsertype_bool' = T.inline_coerce_eq_reverse eqparsertype_bool parse_bool
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env1 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env0 (T.pull_name sorted_source0) (T.pull_type sorted_source0) wf1' validate_bool parse_bool'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv1 : Parse.ancillary_validate_env Det.cbor_det_match env1.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv0 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv1 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env1.si_r env1.si_sp =
  Parse.ancillary_parse_env_extend aenv0 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv1 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env1.si_r env1.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv0 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source1 = List.Tot.tl sorted_source0

let _ : unit = _ by (FStar.Tactics.print ("42 defs remaining. Producing definitions for everparse-no-match"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf2 = compute_wf_typ env1.si_ast (T.pull_name sorted_source1) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source1) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf2' : ast0_wf_typ _ = wf2
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf2_eq : squash (wf2' == wf2) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_everparsenomatch = Impl.validate_typ Det.cbor_det_impl env1.si_v true _ wf2'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_everparsenomatch' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env1.si_r (target_type_of_wf_typ wf2')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_everparsenomatch = impltype_everparsenomatch'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_everparsenomatch : squash (impltype_everparsenomatch' == impltype_everparsenomatch) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_everparsenomatch' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env1.si_sp wf2').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env1.si_r (target_type_of_wf_typ wf2')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_everparsenomatch = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env1.si_sp wf2').parser #impltype_everparsenomatch (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env1.si_r (target_type_of_wf_typ wf2')).sem_rel impltype_everparsenomatch eqimpltype_everparsenomatch)
let eqparsertype_everparsenomatch : squash (parsertype_everparsenomatch' == parsertype_everparsenomatch) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env1.si_sp wf2').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env1.si_r (target_type_of_wf_typ wf2')).sem_rel impltype_everparsenomatch eqimpltype_everparsenomatch
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_everparsenomatch : parsertype_everparsenomatch = T.inline_coerce_eq eqparsertype_everparsenomatch (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env1.si_v env1.si_r env1.si_sp env1.si_p avenv1 aenv1 aaenv1 wf2' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_everparsenomatch' : parsertype_everparsenomatch' = T.inline_coerce_eq_reverse eqparsertype_everparsenomatch parse_everparsenomatch
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env2 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env1 (T.pull_name sorted_source1) (T.pull_type sorted_source1) wf2' validate_everparsenomatch parse_everparsenomatch'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv2 : Parse.ancillary_validate_env Det.cbor_det_match env2.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv1 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv2 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env2.si_r env2.si_sp =
  Parse.ancillary_parse_env_extend aenv1 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv2 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env2.si_r env2.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv1 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source2 = List.Tot.tl sorted_source1

let _ : unit = _ by (FStar.Tactics.print ("41 defs remaining. Producing definitions for uint"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf3 = compute_wf_typ env2.si_ast (T.pull_name sorted_source2) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source2) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf3' : ast0_wf_typ _ = wf3
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf3_eq : squash (wf3' == wf3) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_uint = Impl.validate_typ Det.cbor_det_impl env2.si_v true _ wf3'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_uint' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env2.si_r (target_type_of_wf_typ wf3')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_uint = impltype_uint'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_uint : squash (impltype_uint' == impltype_uint) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_uint' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env2.si_sp wf3').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env2.si_r (target_type_of_wf_typ wf3')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_uint = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env2.si_sp wf3').parser #impltype_uint (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env2.si_r (target_type_of_wf_typ wf3')).sem_rel impltype_uint eqimpltype_uint)
let eqparsertype_uint : squash (parsertype_uint' == parsertype_uint) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env2.si_sp wf3').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env2.si_r (target_type_of_wf_typ wf3')).sem_rel impltype_uint eqimpltype_uint
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_uint : parsertype_uint = T.inline_coerce_eq eqparsertype_uint (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env2.si_v env2.si_r env2.si_sp env2.si_p avenv2 aenv2 aaenv2 wf3' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_uint' : parsertype_uint' = T.inline_coerce_eq_reverse eqparsertype_uint parse_uint
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env3 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env2 (T.pull_name sorted_source2) (T.pull_type sorted_source2) wf3' validate_uint parse_uint'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv3 : Parse.ancillary_validate_env Det.cbor_det_match env3.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv2 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv3 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env3.si_r env3.si_sp =
  Parse.ancillary_parse_env_extend aenv2 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv3 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env3.si_r env3.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv2 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source3 = List.Tot.tl sorted_source2

let _ : unit = _ by (FStar.Tactics.print ("40 defs remaining. Producing definitions for nint"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf4 = compute_wf_typ env3.si_ast (T.pull_name sorted_source3) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source3) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf4' : ast0_wf_typ _ = wf4
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf4_eq : squash (wf4' == wf4) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_nint = Impl.validate_typ Det.cbor_det_impl env3.si_v true _ wf4'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_nint' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env3.si_r (target_type_of_wf_typ wf4')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_nint = impltype_nint'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_nint : squash (impltype_nint' == impltype_nint) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_nint' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env3.si_sp wf4').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env3.si_r (target_type_of_wf_typ wf4')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_nint = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env3.si_sp wf4').parser #impltype_nint (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env3.si_r (target_type_of_wf_typ wf4')).sem_rel impltype_nint eqimpltype_nint)
let eqparsertype_nint : squash (parsertype_nint' == parsertype_nint) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env3.si_sp wf4').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env3.si_r (target_type_of_wf_typ wf4')).sem_rel impltype_nint eqimpltype_nint
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_nint : parsertype_nint = T.inline_coerce_eq eqparsertype_nint (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env3.si_v env3.si_r env3.si_sp env3.si_p avenv3 aenv3 aaenv3 wf4' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_nint' : parsertype_nint' = T.inline_coerce_eq_reverse eqparsertype_nint parse_nint
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env4 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env3 (T.pull_name sorted_source3) (T.pull_type sorted_source3) wf4' validate_nint parse_nint'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv4 : Parse.ancillary_validate_env Det.cbor_det_match env4.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv3 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv4 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env4.si_r env4.si_sp =
  Parse.ancillary_parse_env_extend aenv3 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv4 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env4.si_r env4.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv3 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source4 = List.Tot.tl sorted_source3

let _ : unit = _ by (FStar.Tactics.print ("39 defs remaining. Producing definitions for int"); FStar.Tactics.exact (`()))

(*
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf5 = compute_wf_typ env4.si_ast (T.pull_name sorted_source4) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source4) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf5' : ast0_wf_typ _ = wf5
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf5_eq : squash (wf5' == wf5) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_int = Impl.validate_typ Det.cbor_det_impl env4.si_v true _ wf5'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_int' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env4.si_r (target_type_of_wf_typ wf5')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_int = impltype_int'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_int : squash (impltype_int' == impltype_int) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_int' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env4.si_sp wf5').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env4.si_r (target_type_of_wf_typ wf5')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_int = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env4.si_sp wf5').parser #impltype_int (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env4.si_r (target_type_of_wf_typ wf5')).sem_rel impltype_int eqimpltype_int)
let eqparsertype_int : squash (parsertype_int' == parsertype_int) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env4.si_sp wf5').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env4.si_r (target_type_of_wf_typ wf5')).sem_rel impltype_int eqimpltype_int
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_int : parsertype_int = T.inline_coerce_eq eqparsertype_int (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env4.si_v env4.si_r env4.si_sp env4.si_p avenv4 aenv4 aaenv4 wf5' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_int' : parsertype_int' = T.inline_coerce_eq_reverse eqparsertype_int parse_int
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env5 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env4 (T.pull_name sorted_source4) (T.pull_type sorted_source4) wf5' validate_int parse_int'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv5 : Parse.ancillary_validate_env Det.cbor_det_match env5.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv4 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv5 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env5.si_r env5.si_sp =
  Parse.ancillary_parse_env_extend aenv4 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv5 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env5.si_r env5.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv4 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source5 = List.Tot.tl sorted_source4

let _ : unit = _ by (FStar.Tactics.print ("38 defs remaining. Producing definitions for bstr"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf6 = compute_wf_typ env5.si_ast (T.pull_name sorted_source5) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source5) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf6' : ast0_wf_typ _ = wf6
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf6_eq : squash (wf6' == wf6) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_bstr = Impl.validate_typ Det.cbor_det_impl env5.si_v true _ wf6'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_bstr' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env5.si_r (target_type_of_wf_typ wf6')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_bstr = impltype_bstr'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_bstr : squash (impltype_bstr' == impltype_bstr) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_bstr' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env5.si_sp wf6').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env5.si_r (target_type_of_wf_typ wf6')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_bstr = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env5.si_sp wf6').parser #impltype_bstr (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env5.si_r (target_type_of_wf_typ wf6')).sem_rel impltype_bstr eqimpltype_bstr)
let eqparsertype_bstr : squash (parsertype_bstr' == parsertype_bstr) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env5.si_sp wf6').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env5.si_r (target_type_of_wf_typ wf6')).sem_rel impltype_bstr eqimpltype_bstr
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_bstr : parsertype_bstr = T.inline_coerce_eq eqparsertype_bstr (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env5.si_v env5.si_r env5.si_sp env5.si_p avenv5 aenv5 aaenv5 wf6' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_bstr' : parsertype_bstr' = T.inline_coerce_eq_reverse eqparsertype_bstr parse_bstr
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env6 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env5 (T.pull_name sorted_source5) (T.pull_type sorted_source5) wf6' validate_bstr parse_bstr'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv6 : Parse.ancillary_validate_env Det.cbor_det_match env6.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv5 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv6 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env6.si_r env6.si_sp =
  Parse.ancillary_parse_env_extend aenv5 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv6 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env6.si_r env6.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv5 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source6 = List.Tot.tl sorted_source5

let _ : unit = _ by (FStar.Tactics.print ("37 defs remaining. Producing definitions for encoded-cbor"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf7 = compute_wf_typ env6.si_ast (T.pull_name sorted_source6) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source6) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf7' : ast0_wf_typ _ = wf7
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf7_eq : squash (wf7' == wf7) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_encodedcbor = Impl.validate_typ Det.cbor_det_impl env6.si_v true _ wf7'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_encodedcbor' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env6.si_r (target_type_of_wf_typ wf7')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_encodedcbor = impltype_encodedcbor'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_encodedcbor : squash (impltype_encodedcbor' == impltype_encodedcbor) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_encodedcbor' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env6.si_sp wf7').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env6.si_r (target_type_of_wf_typ wf7')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_encodedcbor = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env6.si_sp wf7').parser #impltype_encodedcbor (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env6.si_r (target_type_of_wf_typ wf7')).sem_rel impltype_encodedcbor eqimpltype_encodedcbor)
let eqparsertype_encodedcbor : squash (parsertype_encodedcbor' == parsertype_encodedcbor) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env6.si_sp wf7').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env6.si_r (target_type_of_wf_typ wf7')).sem_rel impltype_encodedcbor eqimpltype_encodedcbor
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_encodedcbor : parsertype_encodedcbor = T.inline_coerce_eq eqparsertype_encodedcbor (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env6.si_v env6.si_r env6.si_sp env6.si_p avenv6 aenv6 aaenv6 wf7' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_encodedcbor' : parsertype_encodedcbor' = T.inline_coerce_eq_reverse eqparsertype_encodedcbor parse_encodedcbor
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env7 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env6 (T.pull_name sorted_source6) (T.pull_type sorted_source6) wf7' validate_encodedcbor parse_encodedcbor'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv7 : Parse.ancillary_validate_env Det.cbor_det_match env7.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv6 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv7 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env7.si_r env7.si_sp =
  Parse.ancillary_parse_env_extend aenv6 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv7 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env7.si_r env7.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv6 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source7 = List.Tot.tl sorted_source6

let _ : unit = _ by (FStar.Tactics.print ("36 defs remaining. Producing definitions for bytes"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf8 = compute_wf_typ env7.si_ast (T.pull_name sorted_source7) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source7) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf8' : ast0_wf_typ _ = wf8
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf8_eq : squash (wf8' == wf8) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_bytes = Impl.validate_typ Det.cbor_det_impl env7.si_v true _ wf8'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_bytes' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env7.si_r (target_type_of_wf_typ wf8')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_bytes = impltype_bytes'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_bytes : squash (impltype_bytes' == impltype_bytes) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_bytes' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env7.si_sp wf8').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env7.si_r (target_type_of_wf_typ wf8')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_bytes = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env7.si_sp wf8').parser #impltype_bytes (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env7.si_r (target_type_of_wf_typ wf8')).sem_rel impltype_bytes eqimpltype_bytes)
let eqparsertype_bytes : squash (parsertype_bytes' == parsertype_bytes) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env7.si_sp wf8').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env7.si_r (target_type_of_wf_typ wf8')).sem_rel impltype_bytes eqimpltype_bytes
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_bytes : parsertype_bytes = T.inline_coerce_eq eqparsertype_bytes (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env7.si_v env7.si_r env7.si_sp env7.si_p avenv7 aenv7 aaenv7 wf8' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_bytes' : parsertype_bytes' = T.inline_coerce_eq_reverse eqparsertype_bytes parse_bytes
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env8 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env7 (T.pull_name sorted_source7) (T.pull_type sorted_source7) wf8' validate_bytes parse_bytes'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv8 : Parse.ancillary_validate_env Det.cbor_det_match env8.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv7 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv8 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env8.si_r env8.si_sp =
  Parse.ancillary_parse_env_extend aenv7 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv8 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env8.si_r env8.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv7 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source8 = List.Tot.tl sorted_source7

let _ : unit = _ by (FStar.Tactics.print ("35 defs remaining. Producing definitions for tstr"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf9 = compute_wf_typ env8.si_ast (T.pull_name sorted_source8) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source8) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf9' : ast0_wf_typ _ = wf9
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf9_eq : squash (wf9' == wf9) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_tstr = Impl.validate_typ Det.cbor_det_impl env8.si_v true _ wf9'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_tstr' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env8.si_r (target_type_of_wf_typ wf9')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_tstr = impltype_tstr'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_tstr : squash (impltype_tstr' == impltype_tstr) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_tstr' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env8.si_sp wf9').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env8.si_r (target_type_of_wf_typ wf9')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_tstr = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env8.si_sp wf9').parser #impltype_tstr (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env8.si_r (target_type_of_wf_typ wf9')).sem_rel impltype_tstr eqimpltype_tstr)
let eqparsertype_tstr : squash (parsertype_tstr' == parsertype_tstr) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env8.si_sp wf9').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env8.si_r (target_type_of_wf_typ wf9')).sem_rel impltype_tstr eqimpltype_tstr
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_tstr : parsertype_tstr = T.inline_coerce_eq eqparsertype_tstr (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env8.si_v env8.si_r env8.si_sp env8.si_p avenv8 aenv8 aaenv8 wf9' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_tstr' : parsertype_tstr' = T.inline_coerce_eq_reverse eqparsertype_tstr parse_tstr
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env9 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env8 (T.pull_name sorted_source8) (T.pull_type sorted_source8) wf9' validate_tstr parse_tstr'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv9 : Parse.ancillary_validate_env Det.cbor_det_match env9.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv8 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv9 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env9.si_r env9.si_sp =
  Parse.ancillary_parse_env_extend aenv8 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv9 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env9.si_r env9.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv8 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source9 = List.Tot.tl sorted_source8

let _ : unit = _ by (FStar.Tactics.print ("34 defs remaining. Producing definitions for label"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf10 = compute_wf_typ env9.si_ast (T.pull_name sorted_source9) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source9) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf10' : ast0_wf_typ _ = wf10
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf10_eq : squash (wf10' == wf10) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_label = Impl.validate_typ Det.cbor_det_impl env9.si_v true _ wf10'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_label' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env9.si_r (target_type_of_wf_typ wf10')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_label = impltype_label'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_label : squash (impltype_label' == impltype_label) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_label' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env9.si_sp wf10').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env9.si_r (target_type_of_wf_typ wf10')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_label = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env9.si_sp wf10').parser #impltype_label (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env9.si_r (target_type_of_wf_typ wf10')).sem_rel impltype_label eqimpltype_label)
let eqparsertype_label : squash (parsertype_label' == parsertype_label) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env9.si_sp wf10').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env9.si_r (target_type_of_wf_typ wf10')).sem_rel impltype_label eqimpltype_label
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_label : parsertype_label = T.inline_coerce_eq eqparsertype_label (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env9.si_v env9.si_r env9.si_sp env9.si_p avenv9 aenv9 aaenv9 wf10' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_label' : parsertype_label' = T.inline_coerce_eq_reverse eqparsertype_label parse_label
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env10 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env9 (T.pull_name sorted_source9) (T.pull_type sorted_source9) wf10' validate_label parse_label'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv10 : Parse.ancillary_validate_env Det.cbor_det_match env10.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv9 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv10 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env10.si_r env10.si_sp =
  Parse.ancillary_parse_env_extend aenv9 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv10 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env10.si_r env10.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv9 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source10 = List.Tot.tl sorted_source9

let _ : unit = _ by (FStar.Tactics.print ("33 defs remaining. Producing definitions for Generic_Headers"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env11 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_group env10 (T.pull_name sorted_source10) (T.pull_group sorted_source10) (_ by (T.trefl_or_norm ())) (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv11 : Parse.ancillary_validate_env Det.cbor_det_match env11.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv10 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv11 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env11.si_r env11.si_sp =
  Parse.ancillary_parse_env_extend aenv10 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv11 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env11.si_r env11.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv10 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source11 = List.Tot.tl sorted_source10

let _ : unit = _ by (FStar.Tactics.print ("32 defs remaining. Producing definitions for tdate"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf12 = compute_wf_typ env11.si_ast (T.pull_name sorted_source11) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source11) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf12' : ast0_wf_typ _ = wf12
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf12_eq : squash (wf12' == wf12) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_tdate = Impl.validate_typ Det.cbor_det_impl env11.si_v true _ wf12'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_tdate' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env11.si_r (target_type_of_wf_typ wf12')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_tdate = impltype_tdate'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_tdate : squash (impltype_tdate' == impltype_tdate) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_tdate' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env11.si_sp wf12').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env11.si_r (target_type_of_wf_typ wf12')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_tdate = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env11.si_sp wf12').parser #impltype_tdate (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env11.si_r (target_type_of_wf_typ wf12')).sem_rel impltype_tdate eqimpltype_tdate)
let eqparsertype_tdate : squash (parsertype_tdate' == parsertype_tdate) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env11.si_sp wf12').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env11.si_r (target_type_of_wf_typ wf12')).sem_rel impltype_tdate eqimpltype_tdate
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_tdate : parsertype_tdate = T.inline_coerce_eq eqparsertype_tdate (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env11.si_v env11.si_r env11.si_sp env11.si_p avenv11 aenv11 aaenv11 wf12' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_tdate' : parsertype_tdate' = T.inline_coerce_eq_reverse eqparsertype_tdate parse_tdate
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env12 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env11 (T.pull_name sorted_source11) (T.pull_type sorted_source11) wf12' validate_tdate parse_tdate'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv12 : Parse.ancillary_validate_env Det.cbor_det_match env12.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv11 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv12 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env12.si_r env12.si_sp =
  Parse.ancillary_parse_env_extend aenv11 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv12 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env12.si_r env12.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv11 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source12 = List.Tot.tl sorted_source11

let _ : unit = _ by (FStar.Tactics.print ("31 defs remaining. Producing definitions for uri"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf13 = compute_wf_typ env12.si_ast (T.pull_name sorted_source12) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source12) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf13' : ast0_wf_typ _ = wf13
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf13_eq : squash (wf13' == wf13) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_uri = Impl.validate_typ Det.cbor_det_impl env12.si_v true _ wf13'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_uri' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env12.si_r (target_type_of_wf_typ wf13')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_uri = impltype_uri'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_uri : squash (impltype_uri' == impltype_uri) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_uri' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env12.si_sp wf13').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env12.si_r (target_type_of_wf_typ wf13')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_uri = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env12.si_sp wf13').parser #impltype_uri (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env12.si_r (target_type_of_wf_typ wf13')).sem_rel impltype_uri eqimpltype_uri)
let eqparsertype_uri : squash (parsertype_uri' == parsertype_uri) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env12.si_sp wf13').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env12.si_r (target_type_of_wf_typ wf13')).sem_rel impltype_uri eqimpltype_uri
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_uri : parsertype_uri = T.inline_coerce_eq eqparsertype_uri (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env12.si_v env12.si_r env12.si_sp env12.si_p avenv12 aenv12 aaenv12 wf13' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_uri' : parsertype_uri' = T.inline_coerce_eq_reverse eqparsertype_uri parse_uri
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env13 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env12 (T.pull_name sorted_source12) (T.pull_type sorted_source12) wf13' validate_uri parse_uri'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv13 : Parse.ancillary_validate_env Det.cbor_det_match env13.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv12 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv13 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env13.si_r env13.si_sp =
  Parse.ancillary_parse_env_extend aenv12 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv13 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env13.si_r env13.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv12 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source13 = List.Tot.tl sorted_source12

let _ : unit = _ by (FStar.Tactics.print ("30 defs remaining. Producing definitions for b64url"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf14 = compute_wf_typ env13.si_ast (T.pull_name sorted_source13) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source13) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf14' : ast0_wf_typ _ = wf14
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf14_eq : squash (wf14' == wf14) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_b64url = Impl.validate_typ Det.cbor_det_impl env13.si_v true _ wf14'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_b64url' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env13.si_r (target_type_of_wf_typ wf14')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_b64url = impltype_b64url'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_b64url : squash (impltype_b64url' == impltype_b64url) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_b64url' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env13.si_sp wf14').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env13.si_r (target_type_of_wf_typ wf14')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_b64url = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env13.si_sp wf14').parser #impltype_b64url (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env13.si_r (target_type_of_wf_typ wf14')).sem_rel impltype_b64url eqimpltype_b64url)
let eqparsertype_b64url : squash (parsertype_b64url' == parsertype_b64url) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env13.si_sp wf14').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env13.si_r (target_type_of_wf_typ wf14')).sem_rel impltype_b64url eqimpltype_b64url
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_b64url : parsertype_b64url = T.inline_coerce_eq eqparsertype_b64url (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env13.si_v env13.si_r env13.si_sp env13.si_p avenv13 aenv13 aaenv13 wf14' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_b64url' : parsertype_b64url' = T.inline_coerce_eq_reverse eqparsertype_b64url parse_b64url
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env14 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env13 (T.pull_name sorted_source13) (T.pull_type sorted_source13) wf14' validate_b64url parse_b64url'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv14 : Parse.ancillary_validate_env Det.cbor_det_match env14.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv13 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv14 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env14.si_r env14.si_sp =
  Parse.ancillary_parse_env_extend aenv13 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv14 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env14.si_r env14.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv13 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source14 = List.Tot.tl sorted_source13

let _ : unit = _ by (FStar.Tactics.print ("29 defs remaining. Producing definitions for b64legacy"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf15 = compute_wf_typ env14.si_ast (T.pull_name sorted_source14) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source14) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf15' : ast0_wf_typ _ = wf15
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf15_eq : squash (wf15' == wf15) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_b64legacy = Impl.validate_typ Det.cbor_det_impl env14.si_v true _ wf15'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_b64legacy' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env14.si_r (target_type_of_wf_typ wf15')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_b64legacy = impltype_b64legacy'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_b64legacy : squash (impltype_b64legacy' == impltype_b64legacy) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_b64legacy' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env14.si_sp wf15').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env14.si_r (target_type_of_wf_typ wf15')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_b64legacy = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env14.si_sp wf15').parser #impltype_b64legacy (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env14.si_r (target_type_of_wf_typ wf15')).sem_rel impltype_b64legacy eqimpltype_b64legacy)
let eqparsertype_b64legacy : squash (parsertype_b64legacy' == parsertype_b64legacy) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env14.si_sp wf15').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env14.si_r (target_type_of_wf_typ wf15')).sem_rel impltype_b64legacy eqimpltype_b64legacy
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_b64legacy : parsertype_b64legacy = T.inline_coerce_eq eqparsertype_b64legacy (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env14.si_v env14.si_r env14.si_sp env14.si_p avenv14 aenv14 aaenv14 wf15' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_b64legacy' : parsertype_b64legacy' = T.inline_coerce_eq_reverse eqparsertype_b64legacy parse_b64legacy
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env15 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env14 (T.pull_name sorted_source14) (T.pull_type sorted_source14) wf15' validate_b64legacy parse_b64legacy'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv15 : Parse.ancillary_validate_env Det.cbor_det_match env15.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv14 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv15 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env15.si_r env15.si_sp =
  Parse.ancillary_parse_env_extend aenv14 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv15 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env15.si_r env15.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv14 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source15 = List.Tot.tl sorted_source14

let _ : unit = _ by (FStar.Tactics.print ("28 defs remaining. Producing definitions for regexp"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf16 = compute_wf_typ env15.si_ast (T.pull_name sorted_source15) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source15) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf16' : ast0_wf_typ _ = wf16
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf16_eq : squash (wf16' == wf16) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_regexp = Impl.validate_typ Det.cbor_det_impl env15.si_v true _ wf16'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_regexp' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env15.si_r (target_type_of_wf_typ wf16')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_regexp = impltype_regexp'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_regexp : squash (impltype_regexp' == impltype_regexp) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_regexp' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env15.si_sp wf16').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env15.si_r (target_type_of_wf_typ wf16')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_regexp = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env15.si_sp wf16').parser #impltype_regexp (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env15.si_r (target_type_of_wf_typ wf16')).sem_rel impltype_regexp eqimpltype_regexp)
let eqparsertype_regexp : squash (parsertype_regexp' == parsertype_regexp) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env15.si_sp wf16').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env15.si_r (target_type_of_wf_typ wf16')).sem_rel impltype_regexp eqimpltype_regexp
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_regexp : parsertype_regexp = T.inline_coerce_eq eqparsertype_regexp (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env15.si_v env15.si_r env15.si_sp env15.si_p avenv15 aenv15 aaenv15 wf16' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_regexp' : parsertype_regexp' = T.inline_coerce_eq_reverse eqparsertype_regexp parse_regexp
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env16 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env15 (T.pull_name sorted_source15) (T.pull_type sorted_source15) wf16' validate_regexp parse_regexp'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv16 : Parse.ancillary_validate_env Det.cbor_det_match env16.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv15 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv16 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env16.si_r env16.si_sp =
  Parse.ancillary_parse_env_extend aenv15 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv16 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env16.si_r env16.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv15 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source16 = List.Tot.tl sorted_source15

let _ : unit = _ by (FStar.Tactics.print ("27 defs remaining. Producing definitions for mime-message"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf17 = compute_wf_typ env16.si_ast (T.pull_name sorted_source16) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source16) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf17' : ast0_wf_typ _ = wf17
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf17_eq : squash (wf17' == wf17) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_mimemessage = Impl.validate_typ Det.cbor_det_impl env16.si_v true _ wf17'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_mimemessage' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env16.si_r (target_type_of_wf_typ wf17')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_mimemessage = impltype_mimemessage'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_mimemessage : squash (impltype_mimemessage' == impltype_mimemessage) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_mimemessage' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env16.si_sp wf17').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env16.si_r (target_type_of_wf_typ wf17')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_mimemessage = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env16.si_sp wf17').parser #impltype_mimemessage (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env16.si_r (target_type_of_wf_typ wf17')).sem_rel impltype_mimemessage eqimpltype_mimemessage)
let eqparsertype_mimemessage : squash (parsertype_mimemessage' == parsertype_mimemessage) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env16.si_sp wf17').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env16.si_r (target_type_of_wf_typ wf17')).sem_rel impltype_mimemessage eqimpltype_mimemessage
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_mimemessage : parsertype_mimemessage = T.inline_coerce_eq eqparsertype_mimemessage (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env16.si_v env16.si_r env16.si_sp env16.si_p avenv16 aenv16 aaenv16 wf17' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_mimemessage' : parsertype_mimemessage' = T.inline_coerce_eq_reverse eqparsertype_mimemessage parse_mimemessage
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env17 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env16 (T.pull_name sorted_source16) (T.pull_type sorted_source16) wf17' validate_mimemessage parse_mimemessage'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv17 : Parse.ancillary_validate_env Det.cbor_det_match env17.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv16 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv17 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env17.si_r env17.si_sp =
  Parse.ancillary_parse_env_extend aenv16 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv17 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env17.si_r env17.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv16 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source17 = List.Tot.tl sorted_source16

let _ : unit = _ by (FStar.Tactics.print ("26 defs remaining. Producing definitions for text"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf18 = compute_wf_typ env17.si_ast (T.pull_name sorted_source17) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source17) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf18' : ast0_wf_typ _ = wf18
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf18_eq : squash (wf18' == wf18) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_text = Impl.validate_typ Det.cbor_det_impl env17.si_v true _ wf18'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_text' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env17.si_r (target_type_of_wf_typ wf18')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_text = impltype_text'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_text : squash (impltype_text' == impltype_text) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_text' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env17.si_sp wf18').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env17.si_r (target_type_of_wf_typ wf18')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_text = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env17.si_sp wf18').parser #impltype_text (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env17.si_r (target_type_of_wf_typ wf18')).sem_rel impltype_text eqimpltype_text)
let eqparsertype_text : squash (parsertype_text' == parsertype_text) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env17.si_sp wf18').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env17.si_r (target_type_of_wf_typ wf18')).sem_rel impltype_text eqimpltype_text
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_text : parsertype_text = T.inline_coerce_eq eqparsertype_text (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env17.si_v env17.si_r env17.si_sp env17.si_p avenv17 aenv17 aaenv17 wf18' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_text' : parsertype_text' = T.inline_coerce_eq_reverse eqparsertype_text parse_text
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env18 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env17 (T.pull_name sorted_source17) (T.pull_type sorted_source17) wf18' validate_text parse_text'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv18 : Parse.ancillary_validate_env Det.cbor_det_match env18.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv17 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv18 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env18.si_r env18.si_sp =
  Parse.ancillary_parse_env_extend aenv17 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv18 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env18.si_r env18.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv17 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source18 = List.Tot.tl sorted_source17

let _ : unit = _ by (FStar.Tactics.print ("25 defs remaining. Producing definitions for false"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf19 = compute_wf_typ env18.si_ast (T.pull_name sorted_source18) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source18) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf19' : ast0_wf_typ _ = wf19
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf19_eq : squash (wf19' == wf19) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_false = Impl.validate_typ Det.cbor_det_impl env18.si_v true _ wf19'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_false' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env18.si_r (target_type_of_wf_typ wf19')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_false = impltype_false'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_false : squash (impltype_false' == impltype_false) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_false' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env18.si_sp wf19').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env18.si_r (target_type_of_wf_typ wf19')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_false = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env18.si_sp wf19').parser #impltype_false (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env18.si_r (target_type_of_wf_typ wf19')).sem_rel impltype_false eqimpltype_false)
let eqparsertype_false : squash (parsertype_false' == parsertype_false) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env18.si_sp wf19').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env18.si_r (target_type_of_wf_typ wf19')).sem_rel impltype_false eqimpltype_false
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_false : parsertype_false = T.inline_coerce_eq eqparsertype_false (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env18.si_v env18.si_r env18.si_sp env18.si_p avenv18 aenv18 aaenv18 wf19' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_false' : parsertype_false' = T.inline_coerce_eq_reverse eqparsertype_false parse_false
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env19 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env18 (T.pull_name sorted_source18) (T.pull_type sorted_source18) wf19' validate_false parse_false'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv19 : Parse.ancillary_validate_env Det.cbor_det_match env19.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv18 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv19 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env19.si_r env19.si_sp =
  Parse.ancillary_parse_env_extend aenv18 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv19 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env19.si_r env19.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv18 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source19 = List.Tot.tl sorted_source18

let _ : unit = _ by (FStar.Tactics.print ("24 defs remaining. Producing definitions for true"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf20 = compute_wf_typ env19.si_ast (T.pull_name sorted_source19) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source19) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf20' : ast0_wf_typ _ = wf20
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf20_eq : squash (wf20' == wf20) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_true = Impl.validate_typ Det.cbor_det_impl env19.si_v true _ wf20'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_true' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env19.si_r (target_type_of_wf_typ wf20')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_true = impltype_true'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_true : squash (impltype_true' == impltype_true) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_true' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env19.si_sp wf20').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env19.si_r (target_type_of_wf_typ wf20')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_true = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env19.si_sp wf20').parser #impltype_true (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env19.si_r (target_type_of_wf_typ wf20')).sem_rel impltype_true eqimpltype_true)
let eqparsertype_true : squash (parsertype_true' == parsertype_true) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env19.si_sp wf20').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env19.si_r (target_type_of_wf_typ wf20')).sem_rel impltype_true eqimpltype_true
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_true : parsertype_true = T.inline_coerce_eq eqparsertype_true (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env19.si_v env19.si_r env19.si_sp env19.si_p avenv19 aenv19 aaenv19 wf20' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_true' : parsertype_true' = T.inline_coerce_eq_reverse eqparsertype_true parse_true
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env20 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env19 (T.pull_name sorted_source19) (T.pull_type sorted_source19) wf20' validate_true parse_true'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv20 : Parse.ancillary_validate_env Det.cbor_det_match env20.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv19 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv20 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env20.si_r env20.si_sp =
  Parse.ancillary_parse_env_extend aenv19 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv20 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env20.si_r env20.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv19 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source20 = List.Tot.tl sorted_source19

let _ : unit = _ by (FStar.Tactics.print ("23 defs remaining. Producing definitions for nil"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf21 = compute_wf_typ env20.si_ast (T.pull_name sorted_source20) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source20) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf21' : ast0_wf_typ _ = wf21
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf21_eq : squash (wf21' == wf21) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_nil = Impl.validate_typ Det.cbor_det_impl env20.si_v true _ wf21'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_nil' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env20.si_r (target_type_of_wf_typ wf21')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_nil = impltype_nil'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_nil : squash (impltype_nil' == impltype_nil) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_nil' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env20.si_sp wf21').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env20.si_r (target_type_of_wf_typ wf21')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_nil = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env20.si_sp wf21').parser #impltype_nil (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env20.si_r (target_type_of_wf_typ wf21')).sem_rel impltype_nil eqimpltype_nil)
let eqparsertype_nil : squash (parsertype_nil' == parsertype_nil) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env20.si_sp wf21').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env20.si_r (target_type_of_wf_typ wf21')).sem_rel impltype_nil eqimpltype_nil
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_nil : parsertype_nil = T.inline_coerce_eq eqparsertype_nil (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env20.si_v env20.si_r env20.si_sp env20.si_p avenv20 aenv20 aaenv20 wf21' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_nil' : parsertype_nil' = T.inline_coerce_eq_reverse eqparsertype_nil parse_nil
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env21 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env20 (T.pull_name sorted_source20) (T.pull_type sorted_source20) wf21' validate_nil parse_nil'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv21 : Parse.ancillary_validate_env Det.cbor_det_match env21.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv20 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv21 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env21.si_r env21.si_sp =
  Parse.ancillary_parse_env_extend aenv20 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv21 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env21.si_r env21.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv20 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source21 = List.Tot.tl sorted_source20

let _ : unit = _ by (FStar.Tactics.print ("22 defs remaining. Producing definitions for null"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf22 = compute_wf_typ env21.si_ast (T.pull_name sorted_source21) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source21) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf22' : ast0_wf_typ _ = wf22
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf22_eq : squash (wf22' == wf22) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_null = Impl.validate_typ Det.cbor_det_impl env21.si_v true _ wf22'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_null' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env21.si_r (target_type_of_wf_typ wf22')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_null = impltype_null'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_null : squash (impltype_null' == impltype_null) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_null' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env21.si_sp wf22').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env21.si_r (target_type_of_wf_typ wf22')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_null = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env21.si_sp wf22').parser #impltype_null (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env21.si_r (target_type_of_wf_typ wf22')).sem_rel impltype_null eqimpltype_null)
let eqparsertype_null : squash (parsertype_null' == parsertype_null) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env21.si_sp wf22').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env21.si_r (target_type_of_wf_typ wf22')).sem_rel impltype_null eqimpltype_null
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_null : parsertype_null = T.inline_coerce_eq eqparsertype_null (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env21.si_v env21.si_r env21.si_sp env21.si_p avenv21 aenv21 aaenv21 wf22' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_null' : parsertype_null' = T.inline_coerce_eq_reverse eqparsertype_null parse_null
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env22 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env21 (T.pull_name sorted_source21) (T.pull_type sorted_source21) wf22' validate_null parse_null'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv22 : Parse.ancillary_validate_env Det.cbor_det_match env22.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv21 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv22 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env22.si_r env22.si_sp =
  Parse.ancillary_parse_env_extend aenv21 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv22 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env22.si_r env22.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv21 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source22 = List.Tot.tl sorted_source21

let _ : unit = _ by (FStar.Tactics.print ("21 defs remaining. Producing definitions for undefined"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf23 = compute_wf_typ env22.si_ast (T.pull_name sorted_source22) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source22) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf23' : ast0_wf_typ _ = wf23
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf23_eq : squash (wf23' == wf23) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_undefined = Impl.validate_typ Det.cbor_det_impl env22.si_v true _ wf23'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_undefined' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env22.si_r (target_type_of_wf_typ wf23')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_undefined = impltype_undefined'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_undefined : squash (impltype_undefined' == impltype_undefined) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_undefined' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env22.si_sp wf23').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env22.si_r (target_type_of_wf_typ wf23')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_undefined = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env22.si_sp wf23').parser #impltype_undefined (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env22.si_r (target_type_of_wf_typ wf23')).sem_rel impltype_undefined eqimpltype_undefined)
let eqparsertype_undefined : squash (parsertype_undefined' == parsertype_undefined) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env22.si_sp wf23').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env22.si_r (target_type_of_wf_typ wf23')).sem_rel impltype_undefined eqimpltype_undefined
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_undefined : parsertype_undefined = T.inline_coerce_eq eqparsertype_undefined (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env22.si_v env22.si_r env22.si_sp env22.si_p avenv22 aenv22 aaenv22 wf23' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_undefined' : parsertype_undefined' = T.inline_coerce_eq_reverse eqparsertype_undefined parse_undefined
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env23 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env22 (T.pull_name sorted_source22) (T.pull_type sorted_source22) wf23' validate_undefined parse_undefined'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv23 : Parse.ancillary_validate_env Det.cbor_det_match env23.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv22 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv23 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env23.si_r env23.si_sp =
  Parse.ancillary_parse_env_extend aenv22 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv23 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env23.si_r env23.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv22 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source23 = List.Tot.tl sorted_source22

let _ : unit = _ by (FStar.Tactics.print ("20 defs remaining. Producing definitions for any"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf24 = compute_wf_typ env23.si_ast (T.pull_name sorted_source23) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source23) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf24' : ast0_wf_typ _ = wf24
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf24_eq : squash (wf24' == wf24) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_any = Impl.validate_typ Det.cbor_det_impl env23.si_v true _ wf24'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_any' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env23.si_r (target_type_of_wf_typ wf24')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_any = impltype_any'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_any : squash (impltype_any' == impltype_any) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_any' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env23.si_sp wf24').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env23.si_r (target_type_of_wf_typ wf24')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_any = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env23.si_sp wf24').parser #impltype_any (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env23.si_r (target_type_of_wf_typ wf24')).sem_rel impltype_any eqimpltype_any)
let eqparsertype_any : squash (parsertype_any' == parsertype_any) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env23.si_sp wf24').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env23.si_r (target_type_of_wf_typ wf24')).sem_rel impltype_any eqimpltype_any
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_any : parsertype_any = T.inline_coerce_eq eqparsertype_any (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env23.si_v env23.si_r env23.si_sp env23.si_p avenv23 aenv23 aaenv23 wf24' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_any' : parsertype_any' = T.inline_coerce_eq_reverse eqparsertype_any parse_any
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env24 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env23 (T.pull_name sorted_source23) (T.pull_type sorted_source23) wf24' validate_any parse_any'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv24 : Parse.ancillary_validate_env Det.cbor_det_match env24.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv23 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv24 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env24.si_r env24.si_sp =
  Parse.ancillary_parse_env_extend aenv23 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv24 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env24.si_r env24.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv23 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source24 = List.Tot.tl sorted_source23

let _ : unit = _ by (FStar.Tactics.print ("19 defs remaining. Producing definitions for values"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf25 = compute_wf_typ env24.si_ast (T.pull_name sorted_source24) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source24) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf25' : ast0_wf_typ _ = wf25
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf25_eq : squash (wf25' == wf25) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_values = Impl.validate_typ Det.cbor_det_impl env24.si_v true _ wf25'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_values' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env24.si_r (target_type_of_wf_typ wf25')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_values = impltype_values'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_values : squash (impltype_values' == impltype_values) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_values' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env24.si_sp wf25').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env24.si_r (target_type_of_wf_typ wf25')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_values = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env24.si_sp wf25').parser #impltype_values (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env24.si_r (target_type_of_wf_typ wf25')).sem_rel impltype_values eqimpltype_values)
let eqparsertype_values : squash (parsertype_values' == parsertype_values) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env24.si_sp wf25').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env24.si_r (target_type_of_wf_typ wf25')).sem_rel impltype_values eqimpltype_values
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_values : parsertype_values = T.inline_coerce_eq eqparsertype_values (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env24.si_v env24.si_r env24.si_sp env24.si_p avenv24 aenv24 aaenv24 wf25' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_values' : parsertype_values' = T.inline_coerce_eq_reverse eqparsertype_values parse_values
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env25 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env24 (T.pull_name sorted_source24) (T.pull_type sorted_source24) wf25' validate_values parse_values'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv25 : Parse.ancillary_validate_env Det.cbor_det_match env25.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv24 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv25 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env25.si_r env25.si_sp =
  Parse.ancillary_parse_env_extend aenv24 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv25 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env25.si_r env25.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv24 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source25 = List.Tot.tl sorted_source24

(*
let _ : unit = _ by (FStar.Tactics.print ("18 defs remaining. Producing definitions for header_map"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf26 = compute_wf_typ env25.si_ast (T.pull_name sorted_source25) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source25) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf26' : ast0_wf_typ _ = wf26
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf26_eq : squash (wf26' == wf26) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_header_map = Impl.validate_typ Det.cbor_det_impl env25.si_v true _ wf26'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_header_map' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env25.si_r (target_type_of_wf_typ wf26')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_header_map = impltype_header_map'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_header_map : squash (impltype_header_map' == impltype_header_map) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_header_map' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env25.si_sp wf26').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env25.si_r (target_type_of_wf_typ wf26')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_header_map = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env25.si_sp wf26').parser #impltype_header_map (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env25.si_r (target_type_of_wf_typ wf26')).sem_rel impltype_header_map eqimpltype_header_map)
let eqparsertype_header_map : squash (parsertype_header_map' == parsertype_header_map) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env25.si_sp wf26').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env25.si_r (target_type_of_wf_typ wf26')).sem_rel impltype_header_map eqimpltype_header_map
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_header_map : parsertype_header_map = T.inline_coerce_eq eqparsertype_header_map (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env25.si_v env25.si_r env25.si_sp env25.si_p avenv25 aenv25 aaenv25 wf26' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_header_map' : parsertype_header_map' = T.inline_coerce_eq_reverse eqparsertype_header_map parse_header_map
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env26 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env25 (T.pull_name sorted_source25) (T.pull_type sorted_source25) wf26' validate_header_map parse_header_map'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv26 : Parse.ancillary_validate_env Det.cbor_det_match env26.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv25 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv26 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env26.si_r env26.si_sp =
  Parse.ancillary_parse_env_extend aenv25 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv26 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env26.si_r env26.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv25 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source26 = List.Tot.tl sorted_source25

let _ : unit = _ by (FStar.Tactics.print ("17 defs remaining. Producing definitions for empty_or_serialized_map"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf27 = compute_wf_typ env26.si_ast (T.pull_name sorted_source26) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source26) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf27' : ast0_wf_typ _ = wf27
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf27_eq : squash (wf27' == wf27) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_empty_or_serialized_map = Impl.validate_typ Det.cbor_det_impl env26.si_v true _ wf27'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_empty_or_serialized_map' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env26.si_r (target_type_of_wf_typ wf27')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_empty_or_serialized_map = impltype_empty_or_serialized_map'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_empty_or_serialized_map : squash (impltype_empty_or_serialized_map' == impltype_empty_or_serialized_map) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_empty_or_serialized_map' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env26.si_sp wf27').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env26.si_r (target_type_of_wf_typ wf27')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_empty_or_serialized_map = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env26.si_sp wf27').parser #impltype_empty_or_serialized_map (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env26.si_r (target_type_of_wf_typ wf27')).sem_rel impltype_empty_or_serialized_map eqimpltype_empty_or_serialized_map)
let eqparsertype_empty_or_serialized_map : squash (parsertype_empty_or_serialized_map' == parsertype_empty_or_serialized_map) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env26.si_sp wf27').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env26.si_r (target_type_of_wf_typ wf27')).sem_rel impltype_empty_or_serialized_map eqimpltype_empty_or_serialized_map
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_empty_or_serialized_map : parsertype_empty_or_serialized_map = T.inline_coerce_eq eqparsertype_empty_or_serialized_map (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env26.si_v env26.si_r env26.si_sp env26.si_p avenv26 aenv26 aaenv26 wf27' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_empty_or_serialized_map' : parsertype_empty_or_serialized_map' = T.inline_coerce_eq_reverse eqparsertype_empty_or_serialized_map parse_empty_or_serialized_map
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env27 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env26 (T.pull_name sorted_source26) (T.pull_type sorted_source26) wf27' validate_empty_or_serialized_map parse_empty_or_serialized_map'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv27 : Parse.ancillary_validate_env Det.cbor_det_match env27.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv26 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv27 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env27.si_r env27.si_sp =
  Parse.ancillary_parse_env_extend aenv26 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv27 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env27.si_r env27.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv26 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source27 = List.Tot.tl sorted_source26

let _ : unit = _ by (FStar.Tactics.print ("16 defs remaining. Producing definitions for Headers"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env28 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_group env27 (T.pull_name sorted_source27) (T.pull_group sorted_source27) (_ by (T.trefl_or_norm ())) (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv28 : Parse.ancillary_validate_env Det.cbor_det_match env28.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv27 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv28 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env28.si_r env28.si_sp =
  Parse.ancillary_parse_env_extend aenv27 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv28 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env28.si_r env28.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv27 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source28 = List.Tot.tl sorted_source27

let _ : unit = _ by (FStar.Tactics.print ("15 defs remaining. Producing definitions for COSE_Signature"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf29 = compute_wf_typ env28.si_ast (T.pull_name sorted_source28) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source28) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf29' : ast0_wf_typ _ = wf29
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf29_eq : squash (wf29' == wf29) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Signature = Impl.validate_typ Det.cbor_det_impl env28.si_v true _ wf29'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_COSE_Signature' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env28.si_r (target_type_of_wf_typ wf29')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_COSE_Signature = impltype_COSE_Signature'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_COSE_Signature : squash (impltype_COSE_Signature' == impltype_COSE_Signature) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_COSE_Signature' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env28.si_sp wf29').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env28.si_r (target_type_of_wf_typ wf29')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_COSE_Signature = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env28.si_sp wf29').parser #impltype_COSE_Signature (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env28.si_r (target_type_of_wf_typ wf29')).sem_rel impltype_COSE_Signature eqimpltype_COSE_Signature)
let eqparsertype_COSE_Signature : squash (parsertype_COSE_Signature' == parsertype_COSE_Signature) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env28.si_sp wf29').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env28.si_r (target_type_of_wf_typ wf29')).sem_rel impltype_COSE_Signature eqimpltype_COSE_Signature
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_COSE_Signature : parsertype_COSE_Signature = T.inline_coerce_eq eqparsertype_COSE_Signature (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env28.si_v env28.si_r env28.si_sp env28.si_p avenv28 aenv28 aaenv28 wf29' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_COSE_Signature' : parsertype_COSE_Signature' = T.inline_coerce_eq_reverse eqparsertype_COSE_Signature parse_COSE_Signature
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env29 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env28 (T.pull_name sorted_source28) (T.pull_type sorted_source28) wf29' validate_COSE_Signature parse_COSE_Signature'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv29 : Parse.ancillary_validate_env Det.cbor_det_match env29.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv28 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv29 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env29.si_r env29.si_sp =
  Parse.ancillary_parse_env_extend aenv28 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv29 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env29.si_r env29.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv28 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source29 = List.Tot.tl sorted_source28

let _ : unit = _ by (FStar.Tactics.print ("14 defs remaining. Producing definitions for COSE_Sign"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf30 = compute_wf_typ env29.si_ast (T.pull_name sorted_source29) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source29) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf30' : ast0_wf_typ _ = wf30
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf30_eq : squash (wf30' == wf30) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign = Impl.validate_typ Det.cbor_det_impl env29.si_v true _ wf30'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_COSE_Sign' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env29.si_r (target_type_of_wf_typ wf30')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_COSE_Sign = impltype_COSE_Sign'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_COSE_Sign : squash (impltype_COSE_Sign' == impltype_COSE_Sign) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_COSE_Sign' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env29.si_sp wf30').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env29.si_r (target_type_of_wf_typ wf30')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_COSE_Sign = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env29.si_sp wf30').parser #impltype_COSE_Sign (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env29.si_r (target_type_of_wf_typ wf30')).sem_rel impltype_COSE_Sign eqimpltype_COSE_Sign)
let eqparsertype_COSE_Sign : squash (parsertype_COSE_Sign' == parsertype_COSE_Sign) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env29.si_sp wf30').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env29.si_r (target_type_of_wf_typ wf30')).sem_rel impltype_COSE_Sign eqimpltype_COSE_Sign
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_COSE_Sign : parsertype_COSE_Sign = T.inline_coerce_eq eqparsertype_COSE_Sign (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env29.si_v env29.si_r env29.si_sp env29.si_p avenv29 aenv29 aaenv29 wf30' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_COSE_Sign' : parsertype_COSE_Sign' = T.inline_coerce_eq_reverse eqparsertype_COSE_Sign parse_COSE_Sign
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env30 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env29 (T.pull_name sorted_source29) (T.pull_type sorted_source29) wf30' validate_COSE_Sign parse_COSE_Sign'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv30 : Parse.ancillary_validate_env Det.cbor_det_match env30.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv29 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv30 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env30.si_r env30.si_sp =
  Parse.ancillary_parse_env_extend aenv29 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv30 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env30.si_r env30.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv29 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source30 = List.Tot.tl sorted_source29

let _ : unit = _ by (FStar.Tactics.print ("13 defs remaining. Producing definitions for COSE_Sign_Tagged"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf31 = compute_wf_typ env30.si_ast (T.pull_name sorted_source30) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source30) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf31' : ast0_wf_typ _ = wf31
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf31_eq : squash (wf31' == wf31) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign_Tagged = Impl.validate_typ Det.cbor_det_impl env30.si_v true _ wf31'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_COSE_Sign_Tagged' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env30.si_r (target_type_of_wf_typ wf31')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_COSE_Sign_Tagged = impltype_COSE_Sign_Tagged'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_COSE_Sign_Tagged : squash (impltype_COSE_Sign_Tagged' == impltype_COSE_Sign_Tagged) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_COSE_Sign_Tagged' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env30.si_sp wf31').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env30.si_r (target_type_of_wf_typ wf31')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_COSE_Sign_Tagged = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env30.si_sp wf31').parser #impltype_COSE_Sign_Tagged (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env30.si_r (target_type_of_wf_typ wf31')).sem_rel impltype_COSE_Sign_Tagged eqimpltype_COSE_Sign_Tagged)
let eqparsertype_COSE_Sign_Tagged : squash (parsertype_COSE_Sign_Tagged' == parsertype_COSE_Sign_Tagged) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env30.si_sp wf31').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env30.si_r (target_type_of_wf_typ wf31')).sem_rel impltype_COSE_Sign_Tagged eqimpltype_COSE_Sign_Tagged
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_COSE_Sign_Tagged : parsertype_COSE_Sign_Tagged = T.inline_coerce_eq eqparsertype_COSE_Sign_Tagged (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env30.si_v env30.si_r env30.si_sp env30.si_p avenv30 aenv30 aaenv30 wf31' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_COSE_Sign_Tagged' : parsertype_COSE_Sign_Tagged' = T.inline_coerce_eq_reverse eqparsertype_COSE_Sign_Tagged parse_COSE_Sign_Tagged
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env31 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env30 (T.pull_name sorted_source30) (T.pull_type sorted_source30) wf31' validate_COSE_Sign_Tagged parse_COSE_Sign_Tagged'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv31 : Parse.ancillary_validate_env Det.cbor_det_match env31.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv30 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv31 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env31.si_r env31.si_sp =
  Parse.ancillary_parse_env_extend aenv30 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv31 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env31.si_r env31.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv30 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source31 = List.Tot.tl sorted_source30

let _ : unit = _ by (FStar.Tactics.print ("12 defs remaining. Producing definitions for COSE_Sign1"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf32 = compute_wf_typ env31.si_ast (T.pull_name sorted_source31) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source31) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf32' : ast0_wf_typ _ = wf32
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf32_eq : squash (wf32' == wf32) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign1 = Impl.validate_typ Det.cbor_det_impl env31.si_v true _ wf32'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_COSE_Sign1' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env31.si_r (target_type_of_wf_typ wf32')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_COSE_Sign1 = impltype_COSE_Sign1'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_COSE_Sign1 : squash (impltype_COSE_Sign1' == impltype_COSE_Sign1) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_COSE_Sign1' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env31.si_sp wf32').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env31.si_r (target_type_of_wf_typ wf32')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_COSE_Sign1 = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env31.si_sp wf32').parser #impltype_COSE_Sign1 (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env31.si_r (target_type_of_wf_typ wf32')).sem_rel impltype_COSE_Sign1 eqimpltype_COSE_Sign1)
let eqparsertype_COSE_Sign1 : squash (parsertype_COSE_Sign1' == parsertype_COSE_Sign1) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env31.si_sp wf32').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env31.si_r (target_type_of_wf_typ wf32')).sem_rel impltype_COSE_Sign1 eqimpltype_COSE_Sign1
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_COSE_Sign1 : parsertype_COSE_Sign1 = T.inline_coerce_eq eqparsertype_COSE_Sign1 (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env31.si_v env31.si_r env31.si_sp env31.si_p avenv31 aenv31 aaenv31 wf32' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_COSE_Sign1' : parsertype_COSE_Sign1' = T.inline_coerce_eq_reverse eqparsertype_COSE_Sign1 parse_COSE_Sign1
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env32 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env31 (T.pull_name sorted_source31) (T.pull_type sorted_source31) wf32' validate_COSE_Sign1 parse_COSE_Sign1'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv32 : Parse.ancillary_validate_env Det.cbor_det_match env32.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv31 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv32 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env32.si_r env32.si_sp =
  Parse.ancillary_parse_env_extend aenv31 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv32 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env32.si_r env32.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv31 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source32 = List.Tot.tl sorted_source31

let _ : unit = _ by (FStar.Tactics.print ("11 defs remaining. Producing definitions for COSE_Untagged_Message"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf33 = compute_wf_typ env32.si_ast (T.pull_name sorted_source32) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source32) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf33' : ast0_wf_typ _ = wf33
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf33_eq : squash (wf33' == wf33) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Untagged_Message = Impl.validate_typ Det.cbor_det_impl env32.si_v true _ wf33'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_COSE_Untagged_Message' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env32.si_r (target_type_of_wf_typ wf33')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_COSE_Untagged_Message = impltype_COSE_Untagged_Message'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_COSE_Untagged_Message : squash (impltype_COSE_Untagged_Message' == impltype_COSE_Untagged_Message) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_COSE_Untagged_Message' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env32.si_sp wf33').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env32.si_r (target_type_of_wf_typ wf33')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_COSE_Untagged_Message = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env32.si_sp wf33').parser #impltype_COSE_Untagged_Message (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env32.si_r (target_type_of_wf_typ wf33')).sem_rel impltype_COSE_Untagged_Message eqimpltype_COSE_Untagged_Message)
let eqparsertype_COSE_Untagged_Message : squash (parsertype_COSE_Untagged_Message' == parsertype_COSE_Untagged_Message) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env32.si_sp wf33').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env32.si_r (target_type_of_wf_typ wf33')).sem_rel impltype_COSE_Untagged_Message eqimpltype_COSE_Untagged_Message
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_COSE_Untagged_Message : parsertype_COSE_Untagged_Message = T.inline_coerce_eq eqparsertype_COSE_Untagged_Message (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env32.si_v env32.si_r env32.si_sp env32.si_p avenv32 aenv32 aaenv32 wf33' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_COSE_Untagged_Message' : parsertype_COSE_Untagged_Message' = T.inline_coerce_eq_reverse eqparsertype_COSE_Untagged_Message parse_COSE_Untagged_Message
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env33 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env32 (T.pull_name sorted_source32) (T.pull_type sorted_source32) wf33' validate_COSE_Untagged_Message parse_COSE_Untagged_Message'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv33 : Parse.ancillary_validate_env Det.cbor_det_match env33.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv32 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv33 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env33.si_r env33.si_sp =
  Parse.ancillary_parse_env_extend aenv32 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv33 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env33.si_r env33.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv32 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source33 = List.Tot.tl sorted_source32

let _ : unit = _ by (FStar.Tactics.print ("10 defs remaining. Producing definitions for COSE_Sign1_Tagged"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf34 = compute_wf_typ env33.si_ast (T.pull_name sorted_source33) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source33) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf34' : ast0_wf_typ _ = wf34
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf34_eq : squash (wf34' == wf34) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign1_Tagged = Impl.validate_typ Det.cbor_det_impl env33.si_v true _ wf34'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_COSE_Sign1_Tagged' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env33.si_r (target_type_of_wf_typ wf34')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_COSE_Sign1_Tagged = impltype_COSE_Sign1_Tagged'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_COSE_Sign1_Tagged : squash (impltype_COSE_Sign1_Tagged' == impltype_COSE_Sign1_Tagged) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_COSE_Sign1_Tagged' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env33.si_sp wf34').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env33.si_r (target_type_of_wf_typ wf34')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_COSE_Sign1_Tagged = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env33.si_sp wf34').parser #impltype_COSE_Sign1_Tagged (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env33.si_r (target_type_of_wf_typ wf34')).sem_rel impltype_COSE_Sign1_Tagged eqimpltype_COSE_Sign1_Tagged)
let eqparsertype_COSE_Sign1_Tagged : squash (parsertype_COSE_Sign1_Tagged' == parsertype_COSE_Sign1_Tagged) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env33.si_sp wf34').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env33.si_r (target_type_of_wf_typ wf34')).sem_rel impltype_COSE_Sign1_Tagged eqimpltype_COSE_Sign1_Tagged
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_COSE_Sign1_Tagged : parsertype_COSE_Sign1_Tagged = T.inline_coerce_eq eqparsertype_COSE_Sign1_Tagged (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env33.si_v env33.si_r env33.si_sp env33.si_p avenv33 aenv33 aaenv33 wf34' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_COSE_Sign1_Tagged' : parsertype_COSE_Sign1_Tagged' = T.inline_coerce_eq_reverse eqparsertype_COSE_Sign1_Tagged parse_COSE_Sign1_Tagged
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env34 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env33 (T.pull_name sorted_source33) (T.pull_type sorted_source33) wf34' validate_COSE_Sign1_Tagged parse_COSE_Sign1_Tagged'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv34 : Parse.ancillary_validate_env Det.cbor_det_match env34.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv33 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv34 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env34.si_r env34.si_sp =
  Parse.ancillary_parse_env_extend aenv33 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv34 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env34.si_r env34.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv33 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source34 = List.Tot.tl sorted_source33

let _ : unit = _ by (FStar.Tactics.print ("9 defs remaining. Producing definitions for COSE_Tagged_Message"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf35 = compute_wf_typ env34.si_ast (T.pull_name sorted_source34) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source34) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf35' : ast0_wf_typ _ = wf35
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf35_eq : squash (wf35' == wf35) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Tagged_Message = Impl.validate_typ Det.cbor_det_impl env34.si_v true _ wf35'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_COSE_Tagged_Message' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env34.si_r (target_type_of_wf_typ wf35')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_COSE_Tagged_Message = impltype_COSE_Tagged_Message'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_COSE_Tagged_Message : squash (impltype_COSE_Tagged_Message' == impltype_COSE_Tagged_Message) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_COSE_Tagged_Message' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env34.si_sp wf35').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env34.si_r (target_type_of_wf_typ wf35')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_COSE_Tagged_Message = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env34.si_sp wf35').parser #impltype_COSE_Tagged_Message (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env34.si_r (target_type_of_wf_typ wf35')).sem_rel impltype_COSE_Tagged_Message eqimpltype_COSE_Tagged_Message)
let eqparsertype_COSE_Tagged_Message : squash (parsertype_COSE_Tagged_Message' == parsertype_COSE_Tagged_Message) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env34.si_sp wf35').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env34.si_r (target_type_of_wf_typ wf35')).sem_rel impltype_COSE_Tagged_Message eqimpltype_COSE_Tagged_Message
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_COSE_Tagged_Message : parsertype_COSE_Tagged_Message = T.inline_coerce_eq eqparsertype_COSE_Tagged_Message (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env34.si_v env34.si_r env34.si_sp env34.si_p avenv34 aenv34 aaenv34 wf35' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_COSE_Tagged_Message' : parsertype_COSE_Tagged_Message' = T.inline_coerce_eq_reverse eqparsertype_COSE_Tagged_Message parse_COSE_Tagged_Message
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env35 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env34 (T.pull_name sorted_source34) (T.pull_type sorted_source34) wf35' validate_COSE_Tagged_Message parse_COSE_Tagged_Message'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv35 : Parse.ancillary_validate_env Det.cbor_det_match env35.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv34 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv35 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env35.si_r env35.si_sp =
  Parse.ancillary_parse_env_extend aenv34 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv35 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env35.si_r env35.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv34 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source35 = List.Tot.tl sorted_source34

let _ : unit = _ by (FStar.Tactics.print ("8 defs remaining. Producing definitions for COSE_Messages"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf36 = compute_wf_typ env35.si_ast (T.pull_name sorted_source35) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source35) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf36' : ast0_wf_typ _ = wf36
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf36_eq : squash (wf36' == wf36) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Messages = Impl.validate_typ Det.cbor_det_impl env35.si_v true _ wf36'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_COSE_Messages' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env35.si_r (target_type_of_wf_typ wf36')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_COSE_Messages = impltype_COSE_Messages'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_COSE_Messages : squash (impltype_COSE_Messages' == impltype_COSE_Messages) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_COSE_Messages' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env35.si_sp wf36').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env35.si_r (target_type_of_wf_typ wf36')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_COSE_Messages = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env35.si_sp wf36').parser #impltype_COSE_Messages (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env35.si_r (target_type_of_wf_typ wf36')).sem_rel impltype_COSE_Messages eqimpltype_COSE_Messages)
let eqparsertype_COSE_Messages : squash (parsertype_COSE_Messages' == parsertype_COSE_Messages) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env35.si_sp wf36').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env35.si_r (target_type_of_wf_typ wf36')).sem_rel impltype_COSE_Messages eqimpltype_COSE_Messages
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_COSE_Messages : parsertype_COSE_Messages = T.inline_coerce_eq eqparsertype_COSE_Messages (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env35.si_v env35.si_r env35.si_sp env35.si_p avenv35 aenv35 aaenv35 wf36' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_COSE_Messages' : parsertype_COSE_Messages' = T.inline_coerce_eq_reverse eqparsertype_COSE_Messages parse_COSE_Messages
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env36 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env35 (T.pull_name sorted_source35) (T.pull_type sorted_source35) wf36' validate_COSE_Messages parse_COSE_Messages'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv36 : Parse.ancillary_validate_env Det.cbor_det_match env36.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv35 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv36 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env36.si_r env36.si_sp =
  Parse.ancillary_parse_env_extend aenv35 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv36 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env36.si_r env36.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv35 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source36 = List.Tot.tl sorted_source35

let _ : unit = _ by (FStar.Tactics.print ("7 defs remaining. Producing definitions for Sig_structure"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf37 = compute_wf_typ env36.si_ast (T.pull_name sorted_source36) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source36) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf37' : ast0_wf_typ _ = wf37
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf37_eq : squash (wf37' == wf37) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_Sig_structure = Impl.validate_typ Det.cbor_det_impl env36.si_v true _ wf37'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_Sig_structure' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env36.si_r (target_type_of_wf_typ wf37')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_Sig_structure = impltype_Sig_structure'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_Sig_structure : squash (impltype_Sig_structure' == impltype_Sig_structure) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_Sig_structure' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env36.si_sp wf37').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env36.si_r (target_type_of_wf_typ wf37')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_Sig_structure = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env36.si_sp wf37').parser #impltype_Sig_structure (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env36.si_r (target_type_of_wf_typ wf37')).sem_rel impltype_Sig_structure eqimpltype_Sig_structure)
let eqparsertype_Sig_structure : squash (parsertype_Sig_structure' == parsertype_Sig_structure) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env36.si_sp wf37').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env36.si_r (target_type_of_wf_typ wf37')).sem_rel impltype_Sig_structure eqimpltype_Sig_structure
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_Sig_structure : parsertype_Sig_structure = T.inline_coerce_eq eqparsertype_Sig_structure (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env36.si_v env36.si_r env36.si_sp env36.si_p avenv36 aenv36 aaenv36 wf37' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_Sig_structure' : parsertype_Sig_structure' = T.inline_coerce_eq_reverse eqparsertype_Sig_structure parse_Sig_structure
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env37 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env36 (T.pull_name sorted_source36) (T.pull_type sorted_source36) wf37' validate_Sig_structure parse_Sig_structure'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv37 : Parse.ancillary_validate_env Det.cbor_det_match env37.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv36 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv37 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env37.si_r env37.si_sp =
  Parse.ancillary_parse_env_extend aenv36 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv37 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env37.si_r env37.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv36 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source37 = List.Tot.tl sorted_source36

let _ : unit = _ by (FStar.Tactics.print ("6 defs remaining. Producing definitions for Internal_Types"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf38 = compute_wf_typ env37.si_ast (T.pull_name sorted_source37) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source37) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf38' : ast0_wf_typ _ = wf38
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf38_eq : squash (wf38' == wf38) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_Internal_Types = Impl.validate_typ Det.cbor_det_impl env37.si_v true _ wf38'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_Internal_Types' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env37.si_r (target_type_of_wf_typ wf38')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_Internal_Types = impltype_Internal_Types'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_Internal_Types : squash (impltype_Internal_Types' == impltype_Internal_Types) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_Internal_Types' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env37.si_sp wf38').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env37.si_r (target_type_of_wf_typ wf38')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_Internal_Types = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env37.si_sp wf38').parser #impltype_Internal_Types (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env37.si_r (target_type_of_wf_typ wf38')).sem_rel impltype_Internal_Types eqimpltype_Internal_Types)
let eqparsertype_Internal_Types : squash (parsertype_Internal_Types' == parsertype_Internal_Types) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env37.si_sp wf38').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env37.si_r (target_type_of_wf_typ wf38')).sem_rel impltype_Internal_Types eqimpltype_Internal_Types
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_Internal_Types : parsertype_Internal_Types = T.inline_coerce_eq eqparsertype_Internal_Types (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env37.si_v env37.si_r env37.si_sp env37.si_p avenv37 aenv37 aaenv37 wf38' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_Internal_Types' : parsertype_Internal_Types' = T.inline_coerce_eq_reverse eqparsertype_Internal_Types parse_Internal_Types
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env38 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env37 (T.pull_name sorted_source37) (T.pull_type sorted_source37) wf38' validate_Internal_Types parse_Internal_Types'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv38 : Parse.ancillary_validate_env Det.cbor_det_match env38.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv37 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv38 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env38.si_r env38.si_sp =
  Parse.ancillary_parse_env_extend aenv37 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv38 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env38.si_r env38.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv37 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source38 = List.Tot.tl sorted_source37

let _ : unit = _ by (FStar.Tactics.print ("5 defs remaining. Producing definitions for start"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf39 = compute_wf_typ env38.si_ast (T.pull_name sorted_source38) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source38) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf39' : ast0_wf_typ _ = wf39
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf39_eq : squash (wf39' == wf39) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_start = Impl.validate_typ Det.cbor_det_impl env38.si_v true _ wf39'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_start' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env38.si_r (target_type_of_wf_typ wf39')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_start = impltype_start'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_start : squash (impltype_start' == impltype_start) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_start' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env38.si_sp wf39').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env38.si_r (target_type_of_wf_typ wf39')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_start = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env38.si_sp wf39').parser #impltype_start (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env38.si_r (target_type_of_wf_typ wf39')).sem_rel impltype_start eqimpltype_start)
let eqparsertype_start : squash (parsertype_start' == parsertype_start) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env38.si_sp wf39').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env38.si_r (target_type_of_wf_typ wf39')).sem_rel impltype_start eqimpltype_start
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_start : parsertype_start = T.inline_coerce_eq eqparsertype_start (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env38.si_v env38.si_r env38.si_sp env38.si_p avenv38 aenv38 aaenv38 wf39' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_start' : parsertype_start' = T.inline_coerce_eq_reverse eqparsertype_start parse_start
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env39 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env38 (T.pull_name sorted_source38) (T.pull_type sorted_source38) wf39' validate_start parse_start'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv39 : Parse.ancillary_validate_env Det.cbor_det_match env39.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv38 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv39 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env39.si_r env39.si_sp =
  Parse.ancillary_parse_env_extend aenv38 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv39 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env39.si_r env39.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv38 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source39 = List.Tot.tl sorted_source38

let _ : unit = _ by (FStar.Tactics.print ("4 defs remaining. Producing definitions for eb64url"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf40 = compute_wf_typ env39.si_ast (T.pull_name sorted_source39) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source39) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf40' : ast0_wf_typ _ = wf40
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf40_eq : squash (wf40' == wf40) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_eb64url = Impl.validate_typ Det.cbor_det_impl env39.si_v true _ wf40'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_eb64url' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env39.si_r (target_type_of_wf_typ wf40')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_eb64url = impltype_eb64url'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_eb64url : squash (impltype_eb64url' == impltype_eb64url) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_eb64url' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env39.si_sp wf40').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env39.si_r (target_type_of_wf_typ wf40')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_eb64url = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env39.si_sp wf40').parser #impltype_eb64url (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env39.si_r (target_type_of_wf_typ wf40')).sem_rel impltype_eb64url eqimpltype_eb64url)
let eqparsertype_eb64url : squash (parsertype_eb64url' == parsertype_eb64url) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env39.si_sp wf40').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env39.si_r (target_type_of_wf_typ wf40')).sem_rel impltype_eb64url eqimpltype_eb64url
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_eb64url : parsertype_eb64url = T.inline_coerce_eq eqparsertype_eb64url (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env39.si_v env39.si_r env39.si_sp env39.si_p avenv39 aenv39 aaenv39 wf40' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_eb64url' : parsertype_eb64url' = T.inline_coerce_eq_reverse eqparsertype_eb64url parse_eb64url
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env40 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env39 (T.pull_name sorted_source39) (T.pull_type sorted_source39) wf40' validate_eb64url parse_eb64url'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv40 : Parse.ancillary_validate_env Det.cbor_det_match env40.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv39 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv40 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env40.si_r env40.si_sp =
  Parse.ancillary_parse_env_extend aenv39 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv40 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env40.si_r env40.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv39 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source40 = List.Tot.tl sorted_source39

let _ : unit = _ by (FStar.Tactics.print ("3 defs remaining. Producing definitions for eb64legacy"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf41 = compute_wf_typ env40.si_ast (T.pull_name sorted_source40) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source40) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf41' : ast0_wf_typ _ = wf41
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf41_eq : squash (wf41' == wf41) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_eb64legacy = Impl.validate_typ Det.cbor_det_impl env40.si_v true _ wf41'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_eb64legacy' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env40.si_r (target_type_of_wf_typ wf41')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_eb64legacy = impltype_eb64legacy'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_eb64legacy : squash (impltype_eb64legacy' == impltype_eb64legacy) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_eb64legacy' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env40.si_sp wf41').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env40.si_r (target_type_of_wf_typ wf41')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_eb64legacy = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env40.si_sp wf41').parser #impltype_eb64legacy (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env40.si_r (target_type_of_wf_typ wf41')).sem_rel impltype_eb64legacy eqimpltype_eb64legacy)
let eqparsertype_eb64legacy : squash (parsertype_eb64legacy' == parsertype_eb64legacy) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env40.si_sp wf41').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env40.si_r (target_type_of_wf_typ wf41')).sem_rel impltype_eb64legacy eqimpltype_eb64legacy
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_eb64legacy : parsertype_eb64legacy = T.inline_coerce_eq eqparsertype_eb64legacy (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env40.si_v env40.si_r env40.si_sp env40.si_p avenv40 aenv40 aaenv40 wf41' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_eb64legacy' : parsertype_eb64legacy' = T.inline_coerce_eq_reverse eqparsertype_eb64legacy parse_eb64legacy
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env41 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env40 (T.pull_name sorted_source40) (T.pull_type sorted_source40) wf41' validate_eb64legacy parse_eb64legacy'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv41 : Parse.ancillary_validate_env Det.cbor_det_match env41.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv40 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv41 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env41.si_r env41.si_sp =
  Parse.ancillary_parse_env_extend aenv40 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv41 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env41.si_r env41.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv40 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source41 = List.Tot.tl sorted_source40

let _ : unit = _ by (FStar.Tactics.print ("2 defs remaining. Producing definitions for eb16"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf42 = compute_wf_typ env41.si_ast (T.pull_name sorted_source41) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source41) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf42' : ast0_wf_typ _ = wf42
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf42_eq : squash (wf42' == wf42) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_eb16 = Impl.validate_typ Det.cbor_det_impl env41.si_v true _ wf42'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_eb16' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env41.si_r (target_type_of_wf_typ wf42')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_eb16 = impltype_eb16'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_eb16 : squash (impltype_eb16' == impltype_eb16) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_eb16' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env41.si_sp wf42').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env41.si_r (target_type_of_wf_typ wf42')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_eb16 = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env41.si_sp wf42').parser #impltype_eb16 (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env41.si_r (target_type_of_wf_typ wf42')).sem_rel impltype_eb16 eqimpltype_eb16)
let eqparsertype_eb16 : squash (parsertype_eb16' == parsertype_eb16) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env41.si_sp wf42').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env41.si_r (target_type_of_wf_typ wf42')).sem_rel impltype_eb16 eqimpltype_eb16
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_eb16 : parsertype_eb16 = T.inline_coerce_eq eqparsertype_eb16 (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env41.si_v env41.si_r env41.si_sp env41.si_p avenv41 aenv41 aaenv41 wf42' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_eb16' : parsertype_eb16' = T.inline_coerce_eq_reverse eqparsertype_eb16 parse_eb16
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env42 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env41 (T.pull_name sorted_source41) (T.pull_type sorted_source41) wf42' validate_eb16 parse_eb16'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv42 : Parse.ancillary_validate_env Det.cbor_det_match env42.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv41 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv42 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env42.si_r env42.si_sp =
  Parse.ancillary_parse_env_extend aenv41 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv42 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env42.si_r env42.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv41 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source42 = List.Tot.tl sorted_source41

let _ : unit = _ by (FStar.Tactics.print ("1 defs remaining. Producing definitions for cbor-any"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf43 = compute_wf_typ env42.si_ast (T.pull_name sorted_source42) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source42) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf43' : ast0_wf_typ _ = wf43
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf43_eq : squash (wf43' == wf43) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_cborany = Impl.validate_typ Det.cbor_det_impl env42.si_v true _ wf43'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_cborany' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env42.si_r (target_type_of_wf_typ wf43')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_cborany = impltype_cborany'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_cborany : squash (impltype_cborany' == impltype_cborany) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_cborany' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env42.si_sp wf43').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env42.si_r (target_type_of_wf_typ wf43')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_cborany = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env42.si_sp wf43').parser #impltype_cborany (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env42.si_r (target_type_of_wf_typ wf43')).sem_rel impltype_cborany eqimpltype_cborany)
let eqparsertype_cborany : squash (parsertype_cborany' == parsertype_cborany) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env42.si_sp wf43').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env42.si_r (target_type_of_wf_typ wf43')).sem_rel impltype_cborany eqimpltype_cborany
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_cborany : parsertype_cborany = T.inline_coerce_eq eqparsertype_cborany (Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env42.si_v env42.si_r env42.si_sp env42.si_p avenv42 aenv42 aaenv42 wf43' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_cborany' : parsertype_cborany' = T.inline_coerce_eq_reverse eqparsertype_cborany parse_cborany
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env43 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env42 (T.pull_name sorted_source42) (T.pull_type sorted_source42) wf43' validate_cborany parse_cborany'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let avenv43 : Parse.ancillary_validate_env Det.cbor_det_match env43.si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv42 _
[@@noextract_to "krml"; sem_attr] noextract
let aenv43 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env43.si_r env43.si_sp =
  Parse.ancillary_parse_env_extend aenv42 _ _
[@@noextract_to "krml"; sem_attr] noextract
let aaenv43 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env43.si_r env43.si_sp =
  Parse.ancillary_parse_array_group_env_extend aaenv42 _ _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source43 = List.Tot.tl sorted_source42

(*

Verified module: CDDLTest.Validate
All verification conditions discharged successfully
touch -c CDDLTest.Validate.fst.checked
