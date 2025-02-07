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
fstar.exe  --load_cmxs evercddl_lib --load_cmxs evercddl_plugin --warn_error -342 --odir _output   --include /home/tahina/everest/everparse/src/cbor/spec --include /home/tahina/everest/everparse/src/cddl/spec --include /home/tahina/everest/everparse/lib/evercddl/lib --include /home/tahina/everest/everparse/lib/evercddl/plugin --include /home/tahina/everest/everparse/src/cbor/pulse --include /home/tahina/everest/everparse/src/cddl/pulse --include /home/tahina/everest/karamel/krmllib --include /home/tahina/everest/karamel/krmllib/obj --include /home/tahina/everest/pulse/out/lib/pulse --include . --cache_checked_modules --warn_error @241 --already_cached PulseCore,Pulse,C,LowStar,*,-CDDLTest,Prims,FStar,LowStar --cmi --ext context_pruning   CDDLTest.Parse.fst
TAC>> 
*)

let _ : unit = _ by (FStar.Tactics.print ("1 defs remaining. Producing definitions for zint"); FStar.Tactics.exact (`()))

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
let validate_zint = Impl.validate_typ Det.cbor_det_impl env0.si_v true _ wf1'
let _ : unit = _ by (FStar.Tactics.print ("impltype'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let impltype_zint' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r (target_type_of_wf_typ wf1')).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print ("impltype"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let impltype_zint = impltype_zint'
let _ : unit = _ by (FStar.Tactics.print ("eqimpltype"); FStar.Tactics.exact (`()))
let eqimpltype_zint : squash (impltype_zint' == impltype_zint) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parsertype_zint' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env0.si_sp wf1').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r (target_type_of_wf_typ wf1')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parsertype_zint = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env0.si_sp wf1').parser #impltype_zint (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r (target_type_of_wf_typ wf1')).sem_rel impltype_zint eqimpltype_zint)
let eqparsertype_zint : squash (parsertype_zint' == parsertype_zint) = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ env0.si_sp wf1').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r (target_type_of_wf_typ wf1')).sem_rel impltype_zint eqimpltype_zint
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())] // FIXME: WHY WHY WHY is `nbe` looping here?
let parse_zint : parsertype_zint = T.inline_coerce_eq eqparsertype_zint
(Parse.impl_zero_copy_wf_type' Det.cbor_det_impl env0.si_v env0.si_r env0.si_sp env0.si_p avenv0 aenv0 aaenv0 wf1' (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_zint' : parsertype_zint' = T.inline_coerce_eq_reverse eqparsertype_zint parse_zint
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env1 (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak env0 (T.pull_name sorted_source0) (T.pull_type sorted_source0) wf1' validate_zint parse_zint'
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

(*

Verified module: CDDLTest.Parse
All verification conditions discharged successfully
touch -c CDDLTest.Parse.fst.checked
