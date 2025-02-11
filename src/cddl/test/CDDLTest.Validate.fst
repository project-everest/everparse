module CDDLTest.Validate
open CDDL.Pulse.AST.Bundle
open CDDL.Pulse.AST.Gen
module Det = CDDL.Pulse.AST.Det.C
module Impl = CDDL.Pulse.AST.Validate
module Env = CDDL.Pulse.AST.Env
module Parse = CDDL.Pulse.AST.Parse
module T = CDDL.Pulse.AST.Tactics
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

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source0 = Some?.v option_sorted_source

[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env0 : bundle_env Det.cbor_det_match = empty_bundle_env _

[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv0_0 : Parse.ancillary_validate_env Det.cbor_det_match env0.be_ast.e_sem_env =
  fun _ -> None

[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv0_0 : ancillary_bundle_env Det.cbor_det_match env0.be_ast.e_sem_env =
  fun _ _ -> None

[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv0_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env0.be_ast.e_sem_env =
  fun _ _ -> None

let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64)

[@@noextract_to "krml"] noextract
let _ : unit = _ by (produce_defs sorted_source0)

(*
mkdir -p _output
true    
/home/tahina/everest/master/FStar/bin/fstar.exe  --load_cmxs evercddl_lib --load_cmxs evercddl_plugin --warn_error -342 --odir _output   --include /home/tahina/everest/master/everparse/src/cbor/spec --include /home/tahina/everest/master/everparse/src/cddl/spec --include /home/tahina/everest/master/everparse/lib/evercddl/lib --include /home/tahina/everest/master/everparse/lib/evercddl/plugin --include /home/tahina/everest/master/everparse/src/cbor/pulse --include /home/tahina/everest/master/everparse/src/cddl/pulse --include /home/tahina/everest/master/karamel/krmllib --include /home/tahina/everest/master/karamel/krmllib/obj --include /home/tahina/everest/master/pulse/out/lib/pulse --include . --cache_checked_modules --warn_error @241 --already_cached PulseCore,Pulse,C,LowStar,*,-CDDLTest,Prims,FStar,LowStar --cmi --ext context_pruning --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice' --dep full @.depend.rsp --output_deps_to .depend.aux
mv .depend.aux .depend
/home/tahina/everest/master/FStar/bin/fstar.exe  --load_cmxs evercddl_lib --load_cmxs evercddl_plugin --warn_error -342 --odir _output   --include /home/tahina/everest/master/everparse/src/cbor/spec --include /home/tahina/everest/master/everparse/src/cddl/spec --include /home/tahina/everest/master/everparse/lib/evercddl/lib --include /home/tahina/everest/master/everparse/lib/evercddl/plugin --include /home/tahina/everest/master/everparse/src/cbor/pulse --include /home/tahina/everest/master/everparse/src/cddl/pulse --include /home/tahina/everest/master/karamel/krmllib --include /home/tahina/everest/master/karamel/krmllib/obj --include /home/tahina/everest/master/pulse/out/lib/pulse --include . --cache_checked_modules --warn_error @241 --already_cached PulseCore,Pulse,C,LowStar,*,-CDDLTest,Prims,FStar,LowStar --cmi --ext context_pruning   CDDLTest.Validate.fst
TAC>> 
*)

let _ : unit = _ by (FStar.Tactics.print ("43 defs remaining. Producing definitions for bool"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf1' = compute_wf_typ' env0.be_ast (T.pull_name sorted_source0) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source0) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf1 = owf1'
let owf1_eq : squash (owf1 == owf1') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf1' = extract_computed_wf_typ' env0.be_ast (T.pull_name sorted_source0) (T.pull_type sorted_source0) 1 owf1 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf1 = wf1'
let _ : squash (wf1 == wf1') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_bool = Impl.validate_typ Det.cbor_det_impl env0.be_v true _ wf1
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b1' = impl_bundle_wf_type' Det.cbor_det_impl env0 avenv0_0 aenv0_0 aaenv0_0 wf1 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_bool = b1'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b1 = bundle_set_parser b1' parse_bool
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env1 =
  bundle_env_extend_typ_with_weak env0 (T.pull_name sorted_source0) (T.pull_type sorted_source0) wf1 validate_bool b1
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv1_0 : Parse.ancillary_validate_env Det.cbor_det_match env1.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv0_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv1_0 : ancillary_bundle_env Det.cbor_det_match env1.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv0_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv1_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env1.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv0_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source1 = List.Tot.tl sorted_source0
let _ : unit = _ by (FStar.Tactics.print ("42 defs remaining. Producing definitions for everparse-no-match"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf2' = compute_wf_typ' env1.be_ast (T.pull_name sorted_source1) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source1) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf2 = owf2'
let owf2_eq : squash (owf2 == owf2') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf2' = extract_computed_wf_typ' env1.be_ast (T.pull_name sorted_source1) (T.pull_type sorted_source1) 1 owf2 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf2 = wf2'
let _ : squash (wf2 == wf2') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_everparsenomatch = Impl.validate_typ Det.cbor_det_impl env1.be_v true _ wf2
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b2' = impl_bundle_wf_type' Det.cbor_det_impl env1 avenv1_0 aenv1_0 aaenv1_0 wf2 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_everparsenomatch = b2'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b2 = bundle_set_parser b2' parse_everparsenomatch
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env2 =
  bundle_env_extend_typ_with_weak env1 (T.pull_name sorted_source1) (T.pull_type sorted_source1) wf2 validate_everparsenomatch b2
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv2_0 : Parse.ancillary_validate_env Det.cbor_det_match env2.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv1_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv2_0 : ancillary_bundle_env Det.cbor_det_match env2.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv1_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv2_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env2.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv1_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source2 = List.Tot.tl sorted_source1
let _ : unit = _ by (FStar.Tactics.print ("41 defs remaining. Producing definitions for uint"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf3' = compute_wf_typ' env2.be_ast (T.pull_name sorted_source2) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source2) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf3 = owf3'
let owf3_eq : squash (owf3 == owf3') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf3' = extract_computed_wf_typ' env2.be_ast (T.pull_name sorted_source2) (T.pull_type sorted_source2) 1 owf3 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf3 = wf3'
let _ : squash (wf3 == wf3') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_uint = Impl.validate_typ Det.cbor_det_impl env2.be_v true _ wf3
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b3' = impl_bundle_wf_type' Det.cbor_det_impl env2 avenv2_0 aenv2_0 aaenv2_0 wf3 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_uint = b3'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b3 = bundle_set_parser b3' parse_uint
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env3 =
  bundle_env_extend_typ_with_weak env2 (T.pull_name sorted_source2) (T.pull_type sorted_source2) wf3 validate_uint b3
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv3_0 : Parse.ancillary_validate_env Det.cbor_det_match env3.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv2_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv3_0 : ancillary_bundle_env Det.cbor_det_match env3.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv2_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv3_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env3.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv2_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source3 = List.Tot.tl sorted_source2
let _ : unit = _ by (FStar.Tactics.print ("40 defs remaining. Producing definitions for nint"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf4' = compute_wf_typ' env3.be_ast (T.pull_name sorted_source3) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source3) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf4 = owf4'
let owf4_eq : squash (owf4 == owf4') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf4' = extract_computed_wf_typ' env3.be_ast (T.pull_name sorted_source3) (T.pull_type sorted_source3) 1 owf4 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf4 = wf4'
let _ : squash (wf4 == wf4') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_nint = Impl.validate_typ Det.cbor_det_impl env3.be_v true _ wf4
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b4' = impl_bundle_wf_type' Det.cbor_det_impl env3 avenv3_0 aenv3_0 aaenv3_0 wf4 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_nint = b4'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b4 = bundle_set_parser b4' parse_nint
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env4 =
  bundle_env_extend_typ_with_weak env3 (T.pull_name sorted_source3) (T.pull_type sorted_source3) wf4 validate_nint b4
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv4_0 : Parse.ancillary_validate_env Det.cbor_det_match env4.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv3_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv4_0 : ancillary_bundle_env Det.cbor_det_match env4.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv3_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv4_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env4.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv3_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source4 = List.Tot.tl sorted_source3
let _ : unit = _ by (FStar.Tactics.print ("39 defs remaining. Producing definitions for int"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf5' = compute_wf_typ' env4.be_ast (T.pull_name sorted_source4) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source4) 3
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf5 = owf5'
let owf5_eq : squash (owf5 == owf5') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf5' = extract_computed_wf_typ' env4.be_ast (T.pull_name sorted_source4) (T.pull_type sorted_source4) 3 owf5 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf5 = wf5'
let _ : squash (wf5 == wf5') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_int = Impl.validate_typ Det.cbor_det_impl env4.be_v true _ wf5
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b5' = impl_bundle_wf_type' Det.cbor_det_impl env4 avenv4_0 aenv4_0 aaenv4_0 wf5 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_int = b5'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b5 = bundle_set_parser b5' parse_int
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env5 =
  bundle_env_extend_typ_with_weak env4 (T.pull_name sorted_source4) (T.pull_type sorted_source4) wf5 validate_int b5
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv5_0 : Parse.ancillary_validate_env Det.cbor_det_match env5.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv4_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv5_0 : ancillary_bundle_env Det.cbor_det_match env5.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv4_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv5_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env5.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv4_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source5 = List.Tot.tl sorted_source4
let _ : unit = _ by (FStar.Tactics.print ("38 defs remaining. Producing definitions for bstr"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf6' = compute_wf_typ' env5.be_ast (T.pull_name sorted_source5) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source5) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf6 = owf6'
let owf6_eq : squash (owf6 == owf6') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf6' = extract_computed_wf_typ' env5.be_ast (T.pull_name sorted_source5) (T.pull_type sorted_source5) 1 owf6 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf6 = wf6'
let _ : squash (wf6 == wf6') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_bstr = Impl.validate_typ Det.cbor_det_impl env5.be_v true _ wf6
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b6' = impl_bundle_wf_type' Det.cbor_det_impl env5 avenv5_0 aenv5_0 aaenv5_0 wf6 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_bstr = b6'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b6 = bundle_set_parser b6' parse_bstr
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env6 =
  bundle_env_extend_typ_with_weak env5 (T.pull_name sorted_source5) (T.pull_type sorted_source5) wf6 validate_bstr b6
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv6_0 : Parse.ancillary_validate_env Det.cbor_det_match env6.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv5_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv6_0 : ancillary_bundle_env Det.cbor_det_match env6.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv5_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv6_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env6.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv5_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source6 = List.Tot.tl sorted_source5
let _ : unit = _ by (FStar.Tactics.print ("37 defs remaining. Producing definitions for encoded-cbor"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf7' = compute_wf_typ' env6.be_ast (T.pull_name sorted_source6) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source6) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf7 = owf7'
let owf7_eq : squash (owf7 == owf7') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf7' = extract_computed_wf_typ' env6.be_ast (T.pull_name sorted_source6) (T.pull_type sorted_source6) 2 owf7 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf7 = wf7'
let _ : squash (wf7 == wf7') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_encodedcbor = Impl.validate_typ Det.cbor_det_impl env6.be_v true _ wf7
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b7' = impl_bundle_wf_type' Det.cbor_det_impl env6 avenv6_0 aenv6_0 aaenv6_0 wf7 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_encodedcbor = b7'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b7 = bundle_set_parser b7' parse_encodedcbor
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env7 =
  bundle_env_extend_typ_with_weak env6 (T.pull_name sorted_source6) (T.pull_type sorted_source6) wf7 validate_encodedcbor b7
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv7_0 : Parse.ancillary_validate_env Det.cbor_det_match env7.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv6_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv7_0 : ancillary_bundle_env Det.cbor_det_match env7.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv6_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv7_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env7.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv6_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source7 = List.Tot.tl sorted_source6
let _ : unit = _ by (FStar.Tactics.print ("36 defs remaining. Producing definitions for bytes"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf8' = compute_wf_typ' env7.be_ast (T.pull_name sorted_source7) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source7) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf8 = owf8'
let owf8_eq : squash (owf8 == owf8') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf8' = extract_computed_wf_typ' env7.be_ast (T.pull_name sorted_source7) (T.pull_type sorted_source7) 1 owf8 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf8 = wf8'
let _ : squash (wf8 == wf8') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_bytes = Impl.validate_typ Det.cbor_det_impl env7.be_v true _ wf8
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b8' = impl_bundle_wf_type' Det.cbor_det_impl env7 avenv7_0 aenv7_0 aaenv7_0 wf8 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_bytes = b8'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b8 = bundle_set_parser b8' parse_bytes
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env8 =
  bundle_env_extend_typ_with_weak env7 (T.pull_name sorted_source7) (T.pull_type sorted_source7) wf8 validate_bytes b8
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv8_0 : Parse.ancillary_validate_env Det.cbor_det_match env8.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv7_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv8_0 : ancillary_bundle_env Det.cbor_det_match env8.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv7_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv8_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env8.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv7_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source8 = List.Tot.tl sorted_source7
let _ : unit = _ by (FStar.Tactics.print ("35 defs remaining. Producing definitions for tstr"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf9' = compute_wf_typ' env8.be_ast (T.pull_name sorted_source8) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source8) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf9 = owf9'
let owf9_eq : squash (owf9 == owf9') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf9' = extract_computed_wf_typ' env8.be_ast (T.pull_name sorted_source8) (T.pull_type sorted_source8) 1 owf9 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf9 = wf9'
let _ : squash (wf9 == wf9') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_tstr = Impl.validate_typ Det.cbor_det_impl env8.be_v true _ wf9
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b9' = impl_bundle_wf_type' Det.cbor_det_impl env8 avenv8_0 aenv8_0 aaenv8_0 wf9 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_tstr = b9'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b9 = bundle_set_parser b9' parse_tstr
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env9 =
  bundle_env_extend_typ_with_weak env8 (T.pull_name sorted_source8) (T.pull_type sorted_source8) wf9 validate_tstr b9
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv9_0 : Parse.ancillary_validate_env Det.cbor_det_match env9.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv8_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv9_0 : ancillary_bundle_env Det.cbor_det_match env9.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv8_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv9_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env9.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv8_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source9 = List.Tot.tl sorted_source8
let _ : unit = _ by (FStar.Tactics.print ("34 defs remaining. Producing definitions for label"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf10' = compute_wf_typ' env9.be_ast (T.pull_name sorted_source9) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source9) 5
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf10 = owf10'
let owf10_eq : squash (owf10 == owf10') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf10' = extract_computed_wf_typ' env9.be_ast (T.pull_name sorted_source9) (T.pull_type sorted_source9) 5 owf10 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf10 = wf10'
let _ : squash (wf10 == wf10') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_label = Impl.validate_typ Det.cbor_det_impl env9.be_v true _ wf10
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b10' = impl_bundle_wf_type' Det.cbor_det_impl env9 avenv9_0 aenv9_0 aaenv9_0 wf10 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_label = b10'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b10 = bundle_set_parser b10' parse_label
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env10 =
  bundle_env_extend_typ_with_weak env9 (T.pull_name sorted_source9) (T.pull_type sorted_source9) wf10 validate_label b10
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv10_0 : Parse.ancillary_validate_env Det.cbor_det_match env10.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv9_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv10_0 : ancillary_bundle_env Det.cbor_det_match env10.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv9_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv10_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env10.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv9_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source10 = List.Tot.tl sorted_source9
let _ : unit = _ by (FStar.Tactics.print ("33 defs remaining. Producing definitions for Generic_Headers"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env11 =
  bundle_env_extend_group env10 (T.pull_name sorted_source10) (T.pull_group sorted_source10) (_ by (T.trefl_or_norm ())) (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv11_0 : Parse.ancillary_validate_env Det.cbor_det_match env11.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv10_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv11_0 : ancillary_bundle_env Det.cbor_det_match env11.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv10_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv11_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env11.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv10_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source11 = List.Tot.tl sorted_source10
let _ : unit = _ by (FStar.Tactics.print ("32 defs remaining. Producing definitions for tdate"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf12' = compute_wf_typ' env11.be_ast (T.pull_name sorted_source11) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source11) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf12 = owf12'
let owf12_eq : squash (owf12 == owf12') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf12' = extract_computed_wf_typ' env11.be_ast (T.pull_name sorted_source11) (T.pull_type sorted_source11) 2 owf12 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf12 = wf12'
let _ : squash (wf12 == wf12') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_tdate = Impl.validate_typ Det.cbor_det_impl env11.be_v true _ wf12
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b12' = impl_bundle_wf_type' Det.cbor_det_impl env11 avenv11_0 aenv11_0 aaenv11_0 wf12 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_tdate = b12'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b12 = bundle_set_parser b12' parse_tdate
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env12 =
  bundle_env_extend_typ_with_weak env11 (T.pull_name sorted_source11) (T.pull_type sorted_source11) wf12 validate_tdate b12
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv12_0 : Parse.ancillary_validate_env Det.cbor_det_match env12.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv11_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv12_0 : ancillary_bundle_env Det.cbor_det_match env12.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv11_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv12_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env12.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv11_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source12 = List.Tot.tl sorted_source11
let _ : unit = _ by (FStar.Tactics.print ("31 defs remaining. Producing definitions for uri"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf13' = compute_wf_typ' env12.be_ast (T.pull_name sorted_source12) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source12) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf13 = owf13'
let owf13_eq : squash (owf13 == owf13') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf13' = extract_computed_wf_typ' env12.be_ast (T.pull_name sorted_source12) (T.pull_type sorted_source12) 2 owf13 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf13 = wf13'
let _ : squash (wf13 == wf13') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_uri = Impl.validate_typ Det.cbor_det_impl env12.be_v true _ wf13
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b13' = impl_bundle_wf_type' Det.cbor_det_impl env12 avenv12_0 aenv12_0 aaenv12_0 wf13 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_uri = b13'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b13 = bundle_set_parser b13' parse_uri
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env13 =
  bundle_env_extend_typ_with_weak env12 (T.pull_name sorted_source12) (T.pull_type sorted_source12) wf13 validate_uri b13
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv13_0 : Parse.ancillary_validate_env Det.cbor_det_match env13.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv12_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv13_0 : ancillary_bundle_env Det.cbor_det_match env13.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv12_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv13_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env13.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv12_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source13 = List.Tot.tl sorted_source12
let _ : unit = _ by (FStar.Tactics.print ("30 defs remaining. Producing definitions for b64url"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf14' = compute_wf_typ' env13.be_ast (T.pull_name sorted_source13) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source13) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf14 = owf14'
let owf14_eq : squash (owf14 == owf14') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf14' = extract_computed_wf_typ' env13.be_ast (T.pull_name sorted_source13) (T.pull_type sorted_source13) 2 owf14 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf14 = wf14'
let _ : squash (wf14 == wf14') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_b64url = Impl.validate_typ Det.cbor_det_impl env13.be_v true _ wf14
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b14' = impl_bundle_wf_type' Det.cbor_det_impl env13 avenv13_0 aenv13_0 aaenv13_0 wf14 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_b64url = b14'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b14 = bundle_set_parser b14' parse_b64url
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env14 =
  bundle_env_extend_typ_with_weak env13 (T.pull_name sorted_source13) (T.pull_type sorted_source13) wf14 validate_b64url b14
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv14_0 : Parse.ancillary_validate_env Det.cbor_det_match env14.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv13_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv14_0 : ancillary_bundle_env Det.cbor_det_match env14.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv13_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv14_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env14.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv13_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source14 = List.Tot.tl sorted_source13
let _ : unit = _ by (FStar.Tactics.print ("29 defs remaining. Producing definitions for b64legacy"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf15' = compute_wf_typ' env14.be_ast (T.pull_name sorted_source14) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source14) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf15 = owf15'
let owf15_eq : squash (owf15 == owf15') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf15' = extract_computed_wf_typ' env14.be_ast (T.pull_name sorted_source14) (T.pull_type sorted_source14) 2 owf15 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf15 = wf15'
let _ : squash (wf15 == wf15') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_b64legacy = Impl.validate_typ Det.cbor_det_impl env14.be_v true _ wf15
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b15' = impl_bundle_wf_type' Det.cbor_det_impl env14 avenv14_0 aenv14_0 aaenv14_0 wf15 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_b64legacy = b15'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b15 = bundle_set_parser b15' parse_b64legacy
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env15 =
  bundle_env_extend_typ_with_weak env14 (T.pull_name sorted_source14) (T.pull_type sorted_source14) wf15 validate_b64legacy b15
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv15_0 : Parse.ancillary_validate_env Det.cbor_det_match env15.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv14_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv15_0 : ancillary_bundle_env Det.cbor_det_match env15.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv14_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv15_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env15.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv14_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source15 = List.Tot.tl sorted_source14
let _ : unit = _ by (FStar.Tactics.print ("28 defs remaining. Producing definitions for regexp"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf16' = compute_wf_typ' env15.be_ast (T.pull_name sorted_source15) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source15) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf16 = owf16'
let owf16_eq : squash (owf16 == owf16') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf16' = extract_computed_wf_typ' env15.be_ast (T.pull_name sorted_source15) (T.pull_type sorted_source15) 2 owf16 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf16 = wf16'
let _ : squash (wf16 == wf16') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_regexp = Impl.validate_typ Det.cbor_det_impl env15.be_v true _ wf16
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b16' = impl_bundle_wf_type' Det.cbor_det_impl env15 avenv15_0 aenv15_0 aaenv15_0 wf16 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_regexp = b16'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b16 = bundle_set_parser b16' parse_regexp
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env16 =
  bundle_env_extend_typ_with_weak env15 (T.pull_name sorted_source15) (T.pull_type sorted_source15) wf16 validate_regexp b16
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv16_0 : Parse.ancillary_validate_env Det.cbor_det_match env16.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv15_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv16_0 : ancillary_bundle_env Det.cbor_det_match env16.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv15_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv16_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env16.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv15_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source16 = List.Tot.tl sorted_source15
let _ : unit = _ by (FStar.Tactics.print ("27 defs remaining. Producing definitions for mime-message"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf17' = compute_wf_typ' env16.be_ast (T.pull_name sorted_source16) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source16) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf17 = owf17'
let owf17_eq : squash (owf17 == owf17') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf17' = extract_computed_wf_typ' env16.be_ast (T.pull_name sorted_source16) (T.pull_type sorted_source16) 2 owf17 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf17 = wf17'
let _ : squash (wf17 == wf17') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_mimemessage = Impl.validate_typ Det.cbor_det_impl env16.be_v true _ wf17
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b17' = impl_bundle_wf_type' Det.cbor_det_impl env16 avenv16_0 aenv16_0 aaenv16_0 wf17 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_mimemessage = b17'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b17 = bundle_set_parser b17' parse_mimemessage
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env17 =
  bundle_env_extend_typ_with_weak env16 (T.pull_name sorted_source16) (T.pull_type sorted_source16) wf17 validate_mimemessage b17
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv17_0 : Parse.ancillary_validate_env Det.cbor_det_match env17.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv16_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv17_0 : ancillary_bundle_env Det.cbor_det_match env17.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv16_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv17_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env17.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv16_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source17 = List.Tot.tl sorted_source16
let _ : unit = _ by (FStar.Tactics.print ("26 defs remaining. Producing definitions for text"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf18' = compute_wf_typ' env17.be_ast (T.pull_name sorted_source17) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source17) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf18 = owf18'
let owf18_eq : squash (owf18 == owf18') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf18' = extract_computed_wf_typ' env17.be_ast (T.pull_name sorted_source17) (T.pull_type sorted_source17) 1 owf18 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf18 = wf18'
let _ : squash (wf18 == wf18') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_text = Impl.validate_typ Det.cbor_det_impl env17.be_v true _ wf18
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b18' = impl_bundle_wf_type' Det.cbor_det_impl env17 avenv17_0 aenv17_0 aaenv17_0 wf18 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_text = b18'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b18 = bundle_set_parser b18' parse_text
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env18 =
  bundle_env_extend_typ_with_weak env17 (T.pull_name sorted_source17) (T.pull_type sorted_source17) wf18 validate_text b18
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv18_0 : Parse.ancillary_validate_env Det.cbor_det_match env18.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv17_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv18_0 : ancillary_bundle_env Det.cbor_det_match env18.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv17_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv18_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env18.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv17_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source18 = List.Tot.tl sorted_source17
let _ : unit = _ by (FStar.Tactics.print ("25 defs remaining. Producing definitions for false"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf19' = compute_wf_typ' env18.be_ast (T.pull_name sorted_source18) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source18) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf19 = owf19'
let owf19_eq : squash (owf19 == owf19') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf19' = extract_computed_wf_typ' env18.be_ast (T.pull_name sorted_source18) (T.pull_type sorted_source18) 1 owf19 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf19 = wf19'
let _ : squash (wf19 == wf19') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_false = Impl.validate_typ Det.cbor_det_impl env18.be_v true _ wf19
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b19' = impl_bundle_wf_type' Det.cbor_det_impl env18 avenv18_0 aenv18_0 aaenv18_0 wf19 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_false = b19'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b19 = bundle_set_parser b19' parse_false
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env19 =
  bundle_env_extend_typ_with_weak env18 (T.pull_name sorted_source18) (T.pull_type sorted_source18) wf19 validate_false b19
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv19_0 : Parse.ancillary_validate_env Det.cbor_det_match env19.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv18_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv19_0 : ancillary_bundle_env Det.cbor_det_match env19.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv18_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv19_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env19.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv18_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source19 = List.Tot.tl sorted_source18
let _ : unit = _ by (FStar.Tactics.print ("24 defs remaining. Producing definitions for true"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf20' = compute_wf_typ' env19.be_ast (T.pull_name sorted_source19) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source19) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf20 = owf20'
let owf20_eq : squash (owf20 == owf20') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf20' = extract_computed_wf_typ' env19.be_ast (T.pull_name sorted_source19) (T.pull_type sorted_source19) 1 owf20 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf20 = wf20'
let _ : squash (wf20 == wf20') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_true = Impl.validate_typ Det.cbor_det_impl env19.be_v true _ wf20
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b20' = impl_bundle_wf_type' Det.cbor_det_impl env19 avenv19_0 aenv19_0 aaenv19_0 wf20 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_true = b20'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b20 = bundle_set_parser b20' parse_true
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env20 =
  bundle_env_extend_typ_with_weak env19 (T.pull_name sorted_source19) (T.pull_type sorted_source19) wf20 validate_true b20
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv20_0 : Parse.ancillary_validate_env Det.cbor_det_match env20.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv19_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv20_0 : ancillary_bundle_env Det.cbor_det_match env20.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv19_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv20_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env20.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv19_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source20 = List.Tot.tl sorted_source19
let _ : unit = _ by (FStar.Tactics.print ("23 defs remaining. Producing definitions for nil"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf21' = compute_wf_typ' env20.be_ast (T.pull_name sorted_source20) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source20) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf21 = owf21'
let owf21_eq : squash (owf21 == owf21') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf21' = extract_computed_wf_typ' env20.be_ast (T.pull_name sorted_source20) (T.pull_type sorted_source20) 1 owf21 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf21 = wf21'
let _ : squash (wf21 == wf21') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_nil = Impl.validate_typ Det.cbor_det_impl env20.be_v true _ wf21
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b21' = impl_bundle_wf_type' Det.cbor_det_impl env20 avenv20_0 aenv20_0 aaenv20_0 wf21 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_nil = b21'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b21 = bundle_set_parser b21' parse_nil
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env21 =
  bundle_env_extend_typ_with_weak env20 (T.pull_name sorted_source20) (T.pull_type sorted_source20) wf21 validate_nil b21
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv21_0 : Parse.ancillary_validate_env Det.cbor_det_match env21.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv20_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv21_0 : ancillary_bundle_env Det.cbor_det_match env21.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv20_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv21_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env21.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv20_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source21 = List.Tot.tl sorted_source20
let _ : unit = _ by (FStar.Tactics.print ("22 defs remaining. Producing definitions for null"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf22' = compute_wf_typ' env21.be_ast (T.pull_name sorted_source21) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source21) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf22 = owf22'
let owf22_eq : squash (owf22 == owf22') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf22' = extract_computed_wf_typ' env21.be_ast (T.pull_name sorted_source21) (T.pull_type sorted_source21) 1 owf22 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf22 = wf22'
let _ : squash (wf22 == wf22') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_null = Impl.validate_typ Det.cbor_det_impl env21.be_v true _ wf22
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b22' = impl_bundle_wf_type' Det.cbor_det_impl env21 avenv21_0 aenv21_0 aaenv21_0 wf22 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_null = b22'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b22 = bundle_set_parser b22' parse_null
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env22 =
  bundle_env_extend_typ_with_weak env21 (T.pull_name sorted_source21) (T.pull_type sorted_source21) wf22 validate_null b22
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv22_0 : Parse.ancillary_validate_env Det.cbor_det_match env22.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv21_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv22_0 : ancillary_bundle_env Det.cbor_det_match env22.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv21_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv22_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env22.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv21_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source22 = List.Tot.tl sorted_source21
let _ : unit = _ by (FStar.Tactics.print ("21 defs remaining. Producing definitions for undefined"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf23' = compute_wf_typ' env22.be_ast (T.pull_name sorted_source22) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source22) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf23 = owf23'
let owf23_eq : squash (owf23 == owf23') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf23' = extract_computed_wf_typ' env22.be_ast (T.pull_name sorted_source22) (T.pull_type sorted_source22) 1 owf23 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf23 = wf23'
let _ : squash (wf23 == wf23') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_undefined = Impl.validate_typ Det.cbor_det_impl env22.be_v true _ wf23
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b23' = impl_bundle_wf_type' Det.cbor_det_impl env22 avenv22_0 aenv22_0 aaenv22_0 wf23 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_undefined = b23'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b23 = bundle_set_parser b23' parse_undefined
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env23 =
  bundle_env_extend_typ_with_weak env22 (T.pull_name sorted_source22) (T.pull_type sorted_source22) wf23 validate_undefined b23
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv23_0 : Parse.ancillary_validate_env Det.cbor_det_match env23.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv22_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv23_0 : ancillary_bundle_env Det.cbor_det_match env23.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv22_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv23_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env23.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv22_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source23 = List.Tot.tl sorted_source22
let _ : unit = _ by (FStar.Tactics.print ("20 defs remaining. Producing definitions for any"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf24' = compute_wf_typ' env23.be_ast (T.pull_name sorted_source23) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source23) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf24 = owf24'
let owf24_eq : squash (owf24 == owf24') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf24' = extract_computed_wf_typ' env23.be_ast (T.pull_name sorted_source23) (T.pull_type sorted_source23) 1 owf24 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf24 = wf24'
let _ : squash (wf24 == wf24') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_any = Impl.validate_typ Det.cbor_det_impl env23.be_v true _ wf24
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b24' = impl_bundle_wf_type' Det.cbor_det_impl env23 avenv23_0 aenv23_0 aaenv23_0 wf24 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_any = b24'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b24 = bundle_set_parser b24' parse_any
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env24 =
  bundle_env_extend_typ_with_weak env23 (T.pull_name sorted_source23) (T.pull_type sorted_source23) wf24 validate_any b24
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv24_0 : Parse.ancillary_validate_env Det.cbor_det_match env24.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv23_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv24_0 : ancillary_bundle_env Det.cbor_det_match env24.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv23_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv24_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env24.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv23_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source24 = List.Tot.tl sorted_source23
let _ : unit = _ by (FStar.Tactics.print ("19 defs remaining. Producing definitions for values"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf25' = compute_wf_typ' env24.be_ast (T.pull_name sorted_source24) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source24) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf25 = owf25'
let owf25_eq : squash (owf25 == owf25') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf25' = extract_computed_wf_typ' env24.be_ast (T.pull_name sorted_source24) (T.pull_type sorted_source24) 1 owf25 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf25 = wf25'
let _ : squash (wf25 == wf25') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_values = Impl.validate_typ Det.cbor_det_impl env24.be_v true _ wf25
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b25' = impl_bundle_wf_type' Det.cbor_det_impl env24 avenv24_0 aenv24_0 aaenv24_0 wf25 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_values = b25'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b25 = bundle_set_parser b25' parse_values
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env25 =
  bundle_env_extend_typ_with_weak env24 (T.pull_name sorted_source24) (T.pull_type sorted_source24) wf25 validate_values b25
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv25_0 : Parse.ancillary_validate_env Det.cbor_det_match env25.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv24_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv25_0 : ancillary_bundle_env Det.cbor_det_match env25.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv24_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv25_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env25.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv24_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source25 = List.Tot.tl sorted_source24
let _ : unit = _ by (FStar.Tactics.print ("18 defs remaining. Producing definitions for header_map"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf26' = compute_wf_typ' env25.be_ast (T.pull_name sorted_source25) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source25) 22
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf26 = owf26'
let owf26_eq : squash (owf26 == owf26') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf26' = extract_computed_wf_typ' env25.be_ast (T.pull_name sorted_source25) (T.pull_type sorted_source25) 22 owf26 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf26 = wf26'
let _ : squash (wf26 == wf26') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_1'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; bundle_attr] noextract
let aux_env25_wf_1' = Parse.ask_zero_copy_wf_type (Parse.ancillary_validate_env_is_some avenv25_0) (ancillary_bundle_env_is_some aenv25_0) (ancillary_array_bundle_env_is_some aaenv25_0) wf26
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_1"); FStar.Tactics.exact (`()))
[@@base_attr; noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ())] noextract
let aux_env25_wf_1 = aux_env25_wf_1'
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_1_eq"); FStar.Tactics.exact (`()))
let _ : squash (aux_env25_wf_1 == aux_env25_wf_1') = (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let aux_env25_validate_1 = Parse.validate_ask_for_array_group Det.cbor_det_impl env25.be_v aux_env25_wf_1 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let aux_env25_bundle_1' = impl_bundle_wf_ask_for_array_group Det.cbor_det_impl env25 avenv25_0 aenv25_0 aaenv25_0 aux_env25_wf_1 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let aux_env25_parse_1 = aux_env25_bundle_1'.ab_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let aux_env25_bundle_1 = array_bundle_set_parser aux_env25_bundle_1' aux_env25_parse_1
let _ : unit = _ by (FStar.Tactics.print ("ancillary env'"); FStar.Tactics.exact (`()))
[@@bundle_attr; sem_attr; noextract_to "krml"] noextract
let avenv25_1 = avenv25_0
[@@bundle_attr; noextract_to "krml"] noextract
let aenv25_1 = aenv25_0
[@@bundle_attr; noextract_to "krml"] noextract
let aaenv25_1 = ancillary_array_bundle_env_set_ask_for aaenv25_0 aux_env25_wf_1 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) aux_env25_validate_1 aux_env25_bundle_1
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_2'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; bundle_attr] noextract
let aux_env25_wf_2' = Parse.ask_zero_copy_wf_type (Parse.ancillary_validate_env_is_some avenv25_1) (ancillary_bundle_env_is_some aenv25_1) (ancillary_array_bundle_env_is_some aaenv25_1) wf26
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_2"); FStar.Tactics.exact (`()))
[@@base_attr; noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ())] noextract
let aux_env25_wf_2 = aux_env25_wf_2'
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_2_eq"); FStar.Tactics.exact (`()))
let _ : squash (aux_env25_wf_2 == aux_env25_wf_2') = (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let aux_env25_validate_2 = Parse.validate_ask_for_type Det.cbor_det_impl env25.be_v aux_env25_wf_2 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let aux_env25_bundle_2' = impl_bundle_wf_ask_for_guarded_type Det.cbor_det_impl env25 avenv25_1 aenv25_1 aaenv25_1 aux_env25_wf_2 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let aux_env25_parse_2 = aux_env25_bundle_2'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let aux_env25_bundle_2 = bundle_set_parser aux_env25_bundle_2' aux_env25_parse_2
let _ : unit = _ by (FStar.Tactics.print ("ancillary env'"); FStar.Tactics.exact (`()))
[@@bundle_attr; sem_attr; noextract_to "krml"] noextract
let avenv25_2 = avenv25_1
[@@bundle_attr; noextract_to "krml"] noextract
let aenv25_2 = ancillary_bundle_env_set_ask_for aenv25_1 aux_env25_wf_2 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) aux_env25_validate_2 aux_env25_bundle_2
[@@bundle_attr; noextract_to "krml"] noextract
let aaenv25_2 = aaenv25_1
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_3'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; bundle_attr] noextract
let aux_env25_wf_3' = Parse.ask_zero_copy_wf_type (Parse.ancillary_validate_env_is_some avenv25_2) (ancillary_bundle_env_is_some aenv25_2) (ancillary_array_bundle_env_is_some aaenv25_2) wf26
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_3"); FStar.Tactics.exact (`()))
[@@base_attr; noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ())] noextract
let aux_env25_wf_3 = aux_env25_wf_3'
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_3_eq"); FStar.Tactics.exact (`()))
let _ : squash (aux_env25_wf_3 == aux_env25_wf_3') = (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let aux_env25_validate_3 = Parse.validate_ask_for_type Det.cbor_det_impl env25.be_v aux_env25_wf_3 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("ancillary env'"); FStar.Tactics.exact (`()))
[@@bundle_attr; sem_attr; noextract_to "krml"] noextract
let avenv25_3 = Parse.ancillary_validate_env_set_ask_for avenv25_2 aux_env25_wf_3 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) aux_env25_validate_3
[@@bundle_attr; noextract_to "krml"] noextract
let aenv25_3 = aenv25_2
[@@bundle_attr; noextract_to "krml"] noextract
let aaenv25_3 = aaenv25_2
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_4'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; bundle_attr] noextract
let aux_env25_wf_4' = Parse.ask_zero_copy_wf_type (Parse.ancillary_validate_env_is_some avenv25_3) (ancillary_bundle_env_is_some aenv25_3) (ancillary_array_bundle_env_is_some aaenv25_3) wf26
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_4"); FStar.Tactics.exact (`()))
[@@base_attr; noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ())] noextract
let aux_env25_wf_4 = aux_env25_wf_4'
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env25_wf_4_eq"); FStar.Tactics.exact (`()))
let _ : squash (aux_env25_wf_4 == aux_env25_wf_4') = (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let aux_env25_validate_4 = Parse.validate_ask_for_type Det.cbor_det_impl env25.be_v aux_env25_wf_4 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let aux_env25_bundle_4' = impl_bundle_wf_ask_for_guarded_type Det.cbor_det_impl env25 avenv25_3 aenv25_3 aaenv25_3 aux_env25_wf_4 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let aux_env25_parse_4 = aux_env25_bundle_4'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let aux_env25_bundle_4 = bundle_set_parser aux_env25_bundle_4' aux_env25_parse_4
let _ : unit = _ by (FStar.Tactics.print ("ancillary env'"); FStar.Tactics.exact (`()))
[@@bundle_attr; sem_attr; noextract_to "krml"] noextract
let avenv25_4 = avenv25_3
[@@bundle_attr; noextract_to "krml"] noextract
let aenv25_4 = ancillary_bundle_env_set_ask_for aenv25_3 aux_env25_wf_4 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) aux_env25_validate_4 aux_env25_bundle_4
[@@bundle_attr; noextract_to "krml"] noextract
let aaenv25_4 = aaenv25_3
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_header_map = Impl.validate_typ Det.cbor_det_impl env25.be_v true _ wf26
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b26' = impl_bundle_wf_type' Det.cbor_det_impl env25 avenv25_4 aenv25_4 aaenv25_4 wf26 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_header_map = b26'.b_parser
(*
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b26 = bundle_set_parser b26' parse_header_map
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env26 =
  bundle_env_extend_typ_with_weak env25 (T.pull_name sorted_source25) (T.pull_type sorted_source25) wf26 validate_header_map b26
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv26_0 : Parse.ancillary_validate_env Det.cbor_det_match env26.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv25_4 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv26_0 : ancillary_bundle_env Det.cbor_det_match env26.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv25_4 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv26_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env26.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv25_4 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source26 = List.Tot.tl sorted_source25
let _ : unit = _ by (FStar.Tactics.print ("17 defs remaining. Producing definitions for empty_or_serialized_map"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf27' = compute_wf_typ' env26.be_ast (T.pull_name sorted_source26) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source26) 5
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf27 = owf27'
let owf27_eq : squash (owf27 == owf27') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf27' = extract_computed_wf_typ' env26.be_ast (T.pull_name sorted_source26) (T.pull_type sorted_source26) 5 owf27 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf27 = wf27'
let _ : squash (wf27 == wf27') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_empty_or_serialized_map = Impl.validate_typ Det.cbor_det_impl env26.be_v true _ wf27
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b27' = impl_bundle_wf_type' Det.cbor_det_impl env26 avenv26_0 aenv26_0 aaenv26_0 wf27 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_empty_or_serialized_map = b27'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b27 = bundle_set_parser b27' parse_empty_or_serialized_map
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env27 =
  bundle_env_extend_typ_with_weak env26 (T.pull_name sorted_source26) (T.pull_type sorted_source26) wf27 validate_empty_or_serialized_map b27
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv27_0 : Parse.ancillary_validate_env Det.cbor_det_match env27.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv26_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv27_0 : ancillary_bundle_env Det.cbor_det_match env27.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv26_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv27_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env27.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv26_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source27 = List.Tot.tl sorted_source26
let _ : unit = _ by (FStar.Tactics.print ("16 defs remaining. Producing definitions for Headers"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env28 =
  bundle_env_extend_group env27 (T.pull_name sorted_source27) (T.pull_group sorted_source27) (_ by (T.trefl_or_norm ())) (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv28_0 : Parse.ancillary_validate_env Det.cbor_det_match env28.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv27_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv28_0 : ancillary_bundle_env Det.cbor_det_match env28.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv27_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv28_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env28.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv27_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source28 = List.Tot.tl sorted_source27
let _ : unit = _ by (FStar.Tactics.print ("15 defs remaining. Producing definitions for COSE_Signature"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf29' = compute_wf_typ' env28.be_ast (T.pull_name sorted_source28) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source28) 6
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf29 = owf29'
let owf29_eq : squash (owf29 == owf29') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf29' = extract_computed_wf_typ' env28.be_ast (T.pull_name sorted_source28) (T.pull_type sorted_source28) 6 owf29 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf29 = wf29'
let _ : squash (wf29 == wf29') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Signature = Impl.validate_typ Det.cbor_det_impl env28.be_v true _ wf29
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b29' = impl_bundle_wf_type' Det.cbor_det_impl env28 avenv28_0 aenv28_0 aaenv28_0 wf29 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Signature = b29'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b29 = bundle_set_parser b29' parse_COSE_Signature
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env29 =
  bundle_env_extend_typ_with_weak env28 (T.pull_name sorted_source28) (T.pull_type sorted_source28) wf29 validate_COSE_Signature b29
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv29_0 : Parse.ancillary_validate_env Det.cbor_det_match env29.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv28_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv29_0 : ancillary_bundle_env Det.cbor_det_match env29.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv28_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv29_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env29.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv28_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source29 = List.Tot.tl sorted_source28
let _ : unit = _ by (FStar.Tactics.print ("14 defs remaining. Producing definitions for COSE_Sign"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf30' = compute_wf_typ' env29.be_ast (T.pull_name sorted_source29) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source29) 8
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf30 = owf30'
let owf30_eq : squash (owf30 == owf30') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf30' = extract_computed_wf_typ' env29.be_ast (T.pull_name sorted_source29) (T.pull_type sorted_source29) 8 owf30 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf30 = wf30'
let _ : squash (wf30 == wf30') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env29_wf_1'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; bundle_attr] noextract
let aux_env29_wf_1' = Parse.ask_zero_copy_wf_type (Parse.ancillary_validate_env_is_some avenv29_0) (ancillary_bundle_env_is_some aenv29_0) (ancillary_array_bundle_env_is_some aaenv29_0) wf30
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env29_wf_1"); FStar.Tactics.exact (`()))
[@@base_attr; noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ())] noextract
let aux_env29_wf_1 = aux_env29_wf_1'
let _ : unit = _ by (FStar.Tactics.print ("ancillary aux_env29_wf_1_eq"); FStar.Tactics.exact (`()))
let _ : squash (aux_env29_wf_1 == aux_env29_wf_1') = (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let aux_env29_validate_1 = Parse.validate_ask_for_array_group Det.cbor_det_impl env29.be_v aux_env29_wf_1 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let aux_env29_bundle_1' = impl_bundle_wf_ask_for_array_group Det.cbor_det_impl env29 avenv29_0 aenv29_0 aaenv29_0 aux_env29_wf_1 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let aux_env29_parse_1 = aux_env29_bundle_1'.ab_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let aux_env29_bundle_1 = array_bundle_set_parser aux_env29_bundle_1' aux_env29_parse_1
let _ : unit = _ by (FStar.Tactics.print ("ancillary env'"); FStar.Tactics.exact (`()))
[@@bundle_attr; sem_attr; noextract_to "krml"] noextract
let avenv29_1 = avenv29_0
[@@bundle_attr; noextract_to "krml"] noextract
let aenv29_1 = aenv29_0
[@@bundle_attr; noextract_to "krml"] noextract
let aaenv29_1 = ancillary_array_bundle_env_set_ask_for aaenv29_0 aux_env29_wf_1 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) aux_env29_validate_1 aux_env29_bundle_1
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign = Impl.validate_typ Det.cbor_det_impl env29.be_v true _ wf30
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b30' = impl_bundle_wf_type' Det.cbor_det_impl env29 avenv29_1 aenv29_1 aaenv29_1 wf30 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Sign = b30'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b30 = bundle_set_parser b30' parse_COSE_Sign
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env30 =
  bundle_env_extend_typ_with_weak env29 (T.pull_name sorted_source29) (T.pull_type sorted_source29) wf30 validate_COSE_Sign b30
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv30_0 : Parse.ancillary_validate_env Det.cbor_det_match env30.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv29_1 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv30_0 : ancillary_bundle_env Det.cbor_det_match env30.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv29_1 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv30_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env30.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv29_1 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source30 = List.Tot.tl sorted_source29
let _ : unit = _ by (FStar.Tactics.print ("13 defs remaining. Producing definitions for COSE_Sign_Tagged"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf31' = compute_wf_typ' env30.be_ast (T.pull_name sorted_source30) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source30) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf31 = owf31'
let owf31_eq : squash (owf31 == owf31') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf31' = extract_computed_wf_typ' env30.be_ast (T.pull_name sorted_source30) (T.pull_type sorted_source30) 2 owf31 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf31 = wf31'
let _ : squash (wf31 == wf31') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign_Tagged = Impl.validate_typ Det.cbor_det_impl env30.be_v true _ wf31
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b31' = impl_bundle_wf_type' Det.cbor_det_impl env30 avenv30_0 aenv30_0 aaenv30_0 wf31 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Sign_Tagged = b31'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b31 = bundle_set_parser b31' parse_COSE_Sign_Tagged
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env31 =
  bundle_env_extend_typ_with_weak env30 (T.pull_name sorted_source30) (T.pull_type sorted_source30) wf31 validate_COSE_Sign_Tagged b31
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv31_0 : Parse.ancillary_validate_env Det.cbor_det_match env31.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv30_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv31_0 : ancillary_bundle_env Det.cbor_det_match env31.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv30_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv31_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env31.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv30_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source31 = List.Tot.tl sorted_source30
let _ : unit = _ by (FStar.Tactics.print ("12 defs remaining. Producing definitions for COSE_Sign1"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf32' = compute_wf_typ' env31.be_ast (T.pull_name sorted_source31) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source31) 7
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf32 = owf32'
let owf32_eq : squash (owf32 == owf32') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf32' = extract_computed_wf_typ' env31.be_ast (T.pull_name sorted_source31) (T.pull_type sorted_source31) 7 owf32 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf32 = wf32'
let _ : squash (wf32 == wf32') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign1 = Impl.validate_typ Det.cbor_det_impl env31.be_v true _ wf32
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b32' = impl_bundle_wf_type' Det.cbor_det_impl env31 avenv31_0 aenv31_0 aaenv31_0 wf32 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Sign1 = b32'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b32 = bundle_set_parser b32' parse_COSE_Sign1
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env32 =
  bundle_env_extend_typ_with_weak env31 (T.pull_name sorted_source31) (T.pull_type sorted_source31) wf32 validate_COSE_Sign1 b32
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv32_0 : Parse.ancillary_validate_env Det.cbor_det_match env32.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv31_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv32_0 : ancillary_bundle_env Det.cbor_det_match env32.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv31_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv32_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env32.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv31_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source32 = List.Tot.tl sorted_source31
let _ : unit = _ by (FStar.Tactics.print ("11 defs remaining. Producing definitions for COSE_Untagged_Message"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf33' = compute_wf_typ' env32.be_ast (T.pull_name sorted_source32) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source32) 13
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf33 = owf33'
let owf33_eq : squash (owf33 == owf33') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf33' = extract_computed_wf_typ' env32.be_ast (T.pull_name sorted_source32) (T.pull_type sorted_source32) 13 owf33 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf33 = wf33'
let _ : squash (wf33 == wf33') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Untagged_Message = Impl.validate_typ Det.cbor_det_impl env32.be_v true _ wf33
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b33' = impl_bundle_wf_type' Det.cbor_det_impl env32 avenv32_0 aenv32_0 aaenv32_0 wf33 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Untagged_Message = b33'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b33 = bundle_set_parser b33' parse_COSE_Untagged_Message
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env33 =
  bundle_env_extend_typ_with_weak env32 (T.pull_name sorted_source32) (T.pull_type sorted_source32) wf33 validate_COSE_Untagged_Message b33
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv33_0 : Parse.ancillary_validate_env Det.cbor_det_match env33.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv32_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv33_0 : ancillary_bundle_env Det.cbor_det_match env33.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv32_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv33_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env33.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv32_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source33 = List.Tot.tl sorted_source32
let _ : unit = _ by (FStar.Tactics.print ("10 defs remaining. Producing definitions for COSE_Sign1_Tagged"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf34' = compute_wf_typ' env33.be_ast (T.pull_name sorted_source33) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source33) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf34 = owf34'
let owf34_eq : squash (owf34 == owf34') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf34' = extract_computed_wf_typ' env33.be_ast (T.pull_name sorted_source33) (T.pull_type sorted_source33) 2 owf34 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf34 = wf34'
let _ : squash (wf34 == wf34') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign1_Tagged = Impl.validate_typ Det.cbor_det_impl env33.be_v true _ wf34
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b34' = impl_bundle_wf_type' Det.cbor_det_impl env33 avenv33_0 aenv33_0 aaenv33_0 wf34 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Sign1_Tagged = b34'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b34 = bundle_set_parser b34' parse_COSE_Sign1_Tagged
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env34 =
  bundle_env_extend_typ_with_weak env33 (T.pull_name sorted_source33) (T.pull_type sorted_source33) wf34 validate_COSE_Sign1_Tagged b34
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv34_0 : Parse.ancillary_validate_env Det.cbor_det_match env34.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv33_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv34_0 : ancillary_bundle_env Det.cbor_det_match env34.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv33_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv34_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env34.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv33_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source34 = List.Tot.tl sorted_source33
let _ : unit = _ by (FStar.Tactics.print ("9 defs remaining. Producing definitions for COSE_Tagged_Message"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf35' = compute_wf_typ' env34.be_ast (T.pull_name sorted_source34) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source34) 3
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf35 = owf35'
let owf35_eq : squash (owf35 == owf35') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf35' = extract_computed_wf_typ' env34.be_ast (T.pull_name sorted_source34) (T.pull_type sorted_source34) 3 owf35 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf35 = wf35'
let _ : squash (wf35 == wf35') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Tagged_Message = Impl.validate_typ Det.cbor_det_impl env34.be_v true _ wf35
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b35' = impl_bundle_wf_type' Det.cbor_det_impl env34 avenv34_0 aenv34_0 aaenv34_0 wf35 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Tagged_Message = b35'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b35 = bundle_set_parser b35' parse_COSE_Tagged_Message
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env35 =
  bundle_env_extend_typ_with_weak env34 (T.pull_name sorted_source34) (T.pull_type sorted_source34) wf35 validate_COSE_Tagged_Message b35
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv35_0 : Parse.ancillary_validate_env Det.cbor_det_match env35.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv34_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv35_0 : ancillary_bundle_env Det.cbor_det_match env35.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv34_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv35_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env35.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv34_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source35 = List.Tot.tl sorted_source34
let _ : unit = _ by (FStar.Tactics.print ("8 defs remaining. Producing definitions for COSE_Messages"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf36' = compute_wf_typ' env35.be_ast (T.pull_name sorted_source35) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source35) 7
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf36 = owf36'
let owf36_eq : squash (owf36 == owf36') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf36' = extract_computed_wf_typ' env35.be_ast (T.pull_name sorted_source35) (T.pull_type sorted_source35) 7 owf36 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf36 = wf36'
let _ : squash (wf36 == wf36') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Messages = Impl.validate_typ Det.cbor_det_impl env35.be_v true _ wf36
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b36' = impl_bundle_wf_type' Det.cbor_det_impl env35 avenv35_0 aenv35_0 aaenv35_0 wf36 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Messages = b36'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b36 = bundle_set_parser b36' parse_COSE_Messages
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env36 =
  bundle_env_extend_typ_with_weak env35 (T.pull_name sorted_source35) (T.pull_type sorted_source35) wf36 validate_COSE_Messages b36
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv36_0 : Parse.ancillary_validate_env Det.cbor_det_match env36.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv35_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv36_0 : ancillary_bundle_env Det.cbor_det_match env36.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv35_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv36_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env36.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv35_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source36 = List.Tot.tl sorted_source35
let _ : unit = _ by (FStar.Tactics.print ("7 defs remaining. Producing definitions for Sig_structure"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf37' = compute_wf_typ' env36.be_ast (T.pull_name sorted_source36) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source36) 9
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf37 = owf37'
let owf37_eq : squash (owf37 == owf37') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf37' = extract_computed_wf_typ' env36.be_ast (T.pull_name sorted_source36) (T.pull_type sorted_source36) 9 owf37 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf37 = wf37'
let _ : squash (wf37 == wf37') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_Sig_structure = Impl.validate_typ Det.cbor_det_impl env36.be_v true _ wf37
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b37' = impl_bundle_wf_type' Det.cbor_det_impl env36 avenv36_0 aenv36_0 aaenv36_0 wf37 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_Sig_structure = b37'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b37 = bundle_set_parser b37' parse_Sig_structure
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env37 =
  bundle_env_extend_typ_with_weak env36 (T.pull_name sorted_source36) (T.pull_type sorted_source36) wf37 validate_Sig_structure b37
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv37_0 : Parse.ancillary_validate_env Det.cbor_det_match env37.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv36_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv37_0 : ancillary_bundle_env Det.cbor_det_match env37.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv36_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv37_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env37.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv36_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source37 = List.Tot.tl sorted_source36
let _ : unit = _ by (FStar.Tactics.print ("6 defs remaining. Producing definitions for Internal_Types"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf38' = compute_wf_typ' env37.be_ast (T.pull_name sorted_source37) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source37) 1
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf38 = owf38'
let owf38_eq : squash (owf38 == owf38') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf38' = extract_computed_wf_typ' env37.be_ast (T.pull_name sorted_source37) (T.pull_type sorted_source37) 1 owf38 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf38 = wf38'
let _ : squash (wf38 == wf38') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_Internal_Types = Impl.validate_typ Det.cbor_det_impl env37.be_v true _ wf38
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b38' = impl_bundle_wf_type' Det.cbor_det_impl env37 avenv37_0 aenv37_0 aaenv37_0 wf38 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_Internal_Types = b38'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b38 = bundle_set_parser b38' parse_Internal_Types
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env38 =
  bundle_env_extend_typ_with_weak env37 (T.pull_name sorted_source37) (T.pull_type sorted_source37) wf38 validate_Internal_Types b38
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv38_0 : Parse.ancillary_validate_env Det.cbor_det_match env38.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv37_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv38_0 : ancillary_bundle_env Det.cbor_det_match env38.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv37_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv38_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env38.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv37_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source38 = List.Tot.tl sorted_source37
let _ : unit = _ by (FStar.Tactics.print ("5 defs remaining. Producing definitions for start"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf39' = compute_wf_typ' env38.be_ast (T.pull_name sorted_source38) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source38) 18
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf39 = owf39'
let owf39_eq : squash (owf39 == owf39') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf39' = extract_computed_wf_typ' env38.be_ast (T.pull_name sorted_source38) (T.pull_type sorted_source38) 18 owf39 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf39 = wf39'
let _ : squash (wf39 == wf39') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_start = Impl.validate_typ Det.cbor_det_impl env38.be_v true _ wf39
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b39' = impl_bundle_wf_type' Det.cbor_det_impl env38 avenv38_0 aenv38_0 aaenv38_0 wf39 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_start = b39'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b39 = bundle_set_parser b39' parse_start
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env39 =
  bundle_env_extend_typ_with_weak env38 (T.pull_name sorted_source38) (T.pull_type sorted_source38) wf39 validate_start b39
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv39_0 : Parse.ancillary_validate_env Det.cbor_det_match env39.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv38_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv39_0 : ancillary_bundle_env Det.cbor_det_match env39.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv38_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv39_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env39.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv38_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source39 = List.Tot.tl sorted_source38
let _ : unit = _ by (FStar.Tactics.print ("4 defs remaining. Producing definitions for eb64url"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf40' = compute_wf_typ' env39.be_ast (T.pull_name sorted_source39) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source39) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf40 = owf40'
let owf40_eq : squash (owf40 == owf40') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf40' = extract_computed_wf_typ' env39.be_ast (T.pull_name sorted_source39) (T.pull_type sorted_source39) 2 owf40 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf40 = wf40'
let _ : squash (wf40 == wf40') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_eb64url = Impl.validate_typ Det.cbor_det_impl env39.be_v true _ wf40
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b40' = impl_bundle_wf_type' Det.cbor_det_impl env39 avenv39_0 aenv39_0 aaenv39_0 wf40 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_eb64url = b40'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b40 = bundle_set_parser b40' parse_eb64url
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env40 =
  bundle_env_extend_typ_with_weak env39 (T.pull_name sorted_source39) (T.pull_type sorted_source39) wf40 validate_eb64url b40
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv40_0 : Parse.ancillary_validate_env Det.cbor_det_match env40.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv39_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv40_0 : ancillary_bundle_env Det.cbor_det_match env40.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv39_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv40_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env40.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv39_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source40 = List.Tot.tl sorted_source39
let _ : unit = _ by (FStar.Tactics.print ("3 defs remaining. Producing definitions for eb64legacy"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf41' = compute_wf_typ' env40.be_ast (T.pull_name sorted_source40) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source40) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf41 = owf41'
let owf41_eq : squash (owf41 == owf41') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf41' = extract_computed_wf_typ' env40.be_ast (T.pull_name sorted_source40) (T.pull_type sorted_source40) 2 owf41 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf41 = wf41'
let _ : squash (wf41 == wf41') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_eb64legacy = Impl.validate_typ Det.cbor_det_impl env40.be_v true _ wf41
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b41' = impl_bundle_wf_type' Det.cbor_det_impl env40 avenv40_0 aenv40_0 aaenv40_0 wf41 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_eb64legacy = b41'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b41 = bundle_set_parser b41' parse_eb64legacy
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env41 =
  bundle_env_extend_typ_with_weak env40 (T.pull_name sorted_source40) (T.pull_type sorted_source40) wf41 validate_eb64legacy b41
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv41_0 : Parse.ancillary_validate_env Det.cbor_det_match env41.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv40_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv41_0 : ancillary_bundle_env Det.cbor_det_match env41.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv40_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv41_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env41.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv40_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source41 = List.Tot.tl sorted_source40
let _ : unit = _ by (FStar.Tactics.print ("2 defs remaining. Producing definitions for eb16"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf42' = compute_wf_typ' env41.be_ast (T.pull_name sorted_source41) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source41) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf42 = owf42'
let owf42_eq : squash (owf42 == owf42') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf42' = extract_computed_wf_typ' env41.be_ast (T.pull_name sorted_source41) (T.pull_type sorted_source41) 2 owf42 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf42 = wf42'
let _ : squash (wf42 == wf42') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_eb16 = Impl.validate_typ Det.cbor_det_impl env41.be_v true _ wf42
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b42' = impl_bundle_wf_type' Det.cbor_det_impl env41 avenv41_0 aenv41_0 aaenv41_0 wf42 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_eb16 = b42'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b42 = bundle_set_parser b42' parse_eb16
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env42 =
  bundle_env_extend_typ_with_weak env41 (T.pull_name sorted_source41) (T.pull_type sorted_source41) wf42 validate_eb16 b42
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv42_0 : Parse.ancillary_validate_env Det.cbor_det_match env42.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv41_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv42_0 : ancillary_bundle_env Det.cbor_det_match env42.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv41_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv42_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env42.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv41_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source42 = List.Tot.tl sorted_source41
let _ : unit = _ by (FStar.Tactics.print ("1 defs remaining. Producing definitions for cbor-any"); FStar.Tactics.exact (`()))
let _ : unit = _ by (FStar.Tactics.print ("owf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let owf43' = compute_wf_typ' env42.be_ast (T.pull_name sorted_source42) (_ by (T.trefl_or_norm ())) (T.pull_type sorted_source42) 2
let _ : unit = _ by (FStar.Tactics.print ("owf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let owf43 = owf43'
let owf43_eq : squash (owf43 == owf43') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf43' = extract_computed_wf_typ' env42.be_ast (T.pull_name sorted_source42) (T.pull_type sorted_source42) 2 owf43 (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf43 = wf43'
let _ : squash (wf43 == wf43') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_cborany = Impl.validate_typ Det.cbor_det_impl env42.be_v true _ wf43
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b43' = impl_bundle_wf_type' Det.cbor_det_impl env42 avenv42_0 aenv42_0 aaenv42_0 wf43 (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_cborany = b43'.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b43 = bundle_set_parser b43' parse_cborany
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env43 =
  bundle_env_extend_typ_with_weak env42 (T.pull_name sorted_source42) (T.pull_type sorted_source42) wf43 validate_cborany b43
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv43_0 : Parse.ancillary_validate_env Det.cbor_det_match env43.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv42_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv43_0 : ancillary_bundle_env Det.cbor_det_match env43.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv42_0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv43_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env43.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv42_0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source43 = List.Tot.tl sorted_source42
(*

Verified module: CDDLTest.Validate
All verification conditions discharged successfully
touch -c CDDLTest.Validate.fst.checked
