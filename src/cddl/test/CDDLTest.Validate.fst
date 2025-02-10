module CDDLTest.Validate
open CDDL.Pulse.AST.Bundle
open CDDL.Pulse.AST.GenValidators
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

[@@noextract_to "krml"] noextract
let env0 : bundle_env Det.cbor_det_match = empty_bundle_env _

[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv0 : Parse.ancillary_validate_env Det.cbor_det_match env0.be_ast.e_sem_env =
  fun _ -> None

[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv0 : ancillary_bundle_env Det.cbor_det_match env0.be_ast.e_sem_env =
  fun _ _ -> None

[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env0.be_ast.e_sem_env =
  fun _ _ -> None

let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64)

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let defs = produce_defs sorted_source0

let _ : unit = _ by (FStar.Tactics.print defs; FStar.Tactics.exact (`()))

(*
mkdir -p _output
true    
fstar.exe  --load_cmxs evercddl_lib --load_cmxs evercddl_plugin --warn_error -342 --odir _output   --include /home/tahina/everest/everparse/src/cbor/spec --include /home/tahina/everest/everparse/src/cddl/spec --include /home/tahina/everest/everparse/lib/evercddl/lib --include /home/tahina/everest/everparse/lib/evercddl/plugin --include /home/tahina/everest/everparse/src/cbor/pulse --include /home/tahina/everest/everparse/src/cddl/pulse --include /home/tahina/everest/karamel/krmllib --include /home/tahina/everest/karamel/krmllib/obj --include /home/tahina/everest/pulse/out/lib/pulse --include . --cache_checked_modules --warn_error @241 --already_cached PulseCore,Pulse,C,LowStar,*,-CDDLTest,Prims,FStar,LowStar --cmi --ext context_pruning --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice' --dep full @.depend.rsp --output_deps_to .depend.aux
mv .depend.aux .depend
fstar.exe  --load_cmxs evercddl_lib --load_cmxs evercddl_plugin --warn_error -342 --odir _output   --include /home/tahina/everest/everparse/src/cbor/spec --include /home/tahina/everest/everparse/src/cddl/spec --include /home/tahina/everest/everparse/lib/evercddl/lib --include /home/tahina/everest/everparse/lib/evercddl/plugin --include /home/tahina/everest/everparse/src/cbor/pulse --include /home/tahina/everest/everparse/src/cddl/pulse --include /home/tahina/everest/karamel/krmllib --include /home/tahina/everest/karamel/krmllib/obj --include /home/tahina/everest/pulse/out/lib/pulse --include . --cache_checked_modules --warn_error @241 --already_cached PulseCore,Pulse,C,LowStar,*,-CDDLTest,Prims,FStar,LowStar --cmi --ext context_pruning   CDDLTest.Validate.fst
TAC>> 
*)

let _ : unit = _ by (FStar.Tactics.print ("43 defs remaining. Producing definitions for bool"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf1 = compute_wf_typ env0.be_ast (T.pull_name sorted_source0) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source0) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf1' : ast0_wf_typ _ = wf1
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf1_eq : squash (wf1' == wf1) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_bool = Impl.validate_typ Det.cbor_det_impl env0.be_v true _ wf1'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b1 = impl_bundle_wf_type' Det.cbor_det_impl env0 avenv0 aenv0 aaenv0 wf1' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_bool = b1.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b1' = { b1 with b_parser = parse_bool }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env1 =
  bundle_env_extend_typ_with_weak env0 (T.pull_name sorted_source0) (T.pull_type sorted_source0) wf1' validate_bool b1'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv1 : Parse.ancillary_validate_env Det.cbor_det_match env1.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv1 : ancillary_bundle_env Det.cbor_det_match env1.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv0 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv1 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env1.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv0 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source1 = List.Tot.tl sorted_source0

let _ : unit = _ by (FStar.Tactics.print ("42 defs remaining. Producing definitions for everparse-no-match"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf2 = compute_wf_typ env1.be_ast (T.pull_name sorted_source1) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source1) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf2' : ast0_wf_typ _ = wf2
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf2_eq : squash (wf2' == wf2) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_everparsenomatch = Impl.validate_typ Det.cbor_det_impl env1.be_v true _ wf2'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b2 = impl_bundle_wf_type' Det.cbor_det_impl env1 avenv1 aenv1 aaenv1 wf2' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_everparsenomatch = b2.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b2' = { b2 with b_parser = parse_everparsenomatch }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env2 =
  bundle_env_extend_typ_with_weak env1 (T.pull_name sorted_source1) (T.pull_type sorted_source1) wf2' validate_everparsenomatch b2'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv2 : Parse.ancillary_validate_env Det.cbor_det_match env2.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv1 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv2 : ancillary_bundle_env Det.cbor_det_match env2.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv1 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv2 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env2.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv1 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source2 = List.Tot.tl sorted_source1

let _ : unit = _ by (FStar.Tactics.print ("41 defs remaining. Producing definitions for uint"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf3 = compute_wf_typ env2.be_ast (T.pull_name sorted_source2) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source2) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf3' : ast0_wf_typ _ = wf3
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf3_eq : squash (wf3' == wf3) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_uint = Impl.validate_typ Det.cbor_det_impl env2.be_v true _ wf3'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b3 = impl_bundle_wf_type' Det.cbor_det_impl env2 avenv2 aenv2 aaenv2 wf3' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_uint = b3.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b3' = { b3 with b_parser = parse_uint }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env3 =
  bundle_env_extend_typ_with_weak env2 (T.pull_name sorted_source2) (T.pull_type sorted_source2) wf3' validate_uint b3'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv3 : Parse.ancillary_validate_env Det.cbor_det_match env3.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv2 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv3 : ancillary_bundle_env Det.cbor_det_match env3.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv2 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv3 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env3.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv2 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source3 = List.Tot.tl sorted_source2

let _ : unit = _ by (FStar.Tactics.print ("40 defs remaining. Producing definitions for nint"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf4 = compute_wf_typ env3.be_ast (T.pull_name sorted_source3) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source3) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf4' : ast0_wf_typ _ = wf4
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf4_eq : squash (wf4' == wf4) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_nint = Impl.validate_typ Det.cbor_det_impl env3.be_v true _ wf4'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b4 = impl_bundle_wf_type' Det.cbor_det_impl env3 avenv3 aenv3 aaenv3 wf4' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_nint = b4.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b4' = { b4 with b_parser = parse_nint }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env4 =
  bundle_env_extend_typ_with_weak env3 (T.pull_name sorted_source3) (T.pull_type sorted_source3) wf4' validate_nint b4'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv4 : Parse.ancillary_validate_env Det.cbor_det_match env4.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv3 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv4 : ancillary_bundle_env Det.cbor_det_match env4.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv3 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv4 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env4.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv3 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source4 = List.Tot.tl sorted_source3

let _ : unit = _ by (FStar.Tactics.print ("39 defs remaining. Producing definitions for int"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf5 = compute_wf_typ env4.be_ast (T.pull_name sorted_source4) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source4) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf5' : ast0_wf_typ _ = wf5
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf5_eq : squash (wf5' == wf5) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_int = Impl.validate_typ Det.cbor_det_impl env4.be_v true _ wf5'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b5 = impl_bundle_wf_type' Det.cbor_det_impl env4 avenv4 aenv4 aaenv4 wf5' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_int = b5.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b5' = { b5 with b_parser = parse_int }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env5 =
  bundle_env_extend_typ_with_weak env4 (T.pull_name sorted_source4) (T.pull_type sorted_source4) wf5' validate_int b5'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv5 : Parse.ancillary_validate_env Det.cbor_det_match env5.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv4 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv5 : ancillary_bundle_env Det.cbor_det_match env5.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv4 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv5 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env5.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv4 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source5 = List.Tot.tl sorted_source4

let _ : unit = _ by (FStar.Tactics.print ("38 defs remaining. Producing definitions for bstr"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf6 = compute_wf_typ env5.be_ast (T.pull_name sorted_source5) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source5) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf6' : ast0_wf_typ _ = wf6
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf6_eq : squash (wf6' == wf6) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_bstr = Impl.validate_typ Det.cbor_det_impl env5.be_v true _ wf6'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b6 = impl_bundle_wf_type' Det.cbor_det_impl env5 avenv5 aenv5 aaenv5 wf6' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_bstr = b6.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b6' = { b6 with b_parser = parse_bstr }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env6 =
  bundle_env_extend_typ_with_weak env5 (T.pull_name sorted_source5) (T.pull_type sorted_source5) wf6' validate_bstr b6'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv6 : Parse.ancillary_validate_env Det.cbor_det_match env6.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv5 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv6 : ancillary_bundle_env Det.cbor_det_match env6.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv5 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv6 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env6.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv5 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source6 = List.Tot.tl sorted_source5

let _ : unit = _ by (FStar.Tactics.print ("37 defs remaining. Producing definitions for encoded-cbor"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf7 = compute_wf_typ env6.be_ast (T.pull_name sorted_source6) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source6) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf7' : ast0_wf_typ _ = wf7
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf7_eq : squash (wf7' == wf7) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_encodedcbor = Impl.validate_typ Det.cbor_det_impl env6.be_v true _ wf7'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b7 = impl_bundle_wf_type' Det.cbor_det_impl env6 avenv6 aenv6 aaenv6 wf7' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_encodedcbor = b7.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b7' = { b7 with b_parser = parse_encodedcbor }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env7 =
  bundle_env_extend_typ_with_weak env6 (T.pull_name sorted_source6) (T.pull_type sorted_source6) wf7' validate_encodedcbor b7'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv7 : Parse.ancillary_validate_env Det.cbor_det_match env7.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv6 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv7 : ancillary_bundle_env Det.cbor_det_match env7.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv6 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv7 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env7.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv6 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source7 = List.Tot.tl sorted_source6

let _ : unit = _ by (FStar.Tactics.print ("36 defs remaining. Producing definitions for bytes"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf8 = compute_wf_typ env7.be_ast (T.pull_name sorted_source7) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source7) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf8' : ast0_wf_typ _ = wf8
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf8_eq : squash (wf8' == wf8) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_bytes = Impl.validate_typ Det.cbor_det_impl env7.be_v true _ wf8'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b8 = impl_bundle_wf_type' Det.cbor_det_impl env7 avenv7 aenv7 aaenv7 wf8' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_bytes = b8.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b8' = { b8 with b_parser = parse_bytes }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env8 =
  bundle_env_extend_typ_with_weak env7 (T.pull_name sorted_source7) (T.pull_type sorted_source7) wf8' validate_bytes b8'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv8 : Parse.ancillary_validate_env Det.cbor_det_match env8.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv7 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv8 : ancillary_bundle_env Det.cbor_det_match env8.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv7 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv8 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env8.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv7 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source8 = List.Tot.tl sorted_source7

let _ : unit = _ by (FStar.Tactics.print ("35 defs remaining. Producing definitions for tstr"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf9 = compute_wf_typ env8.be_ast (T.pull_name sorted_source8) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source8) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf9' : ast0_wf_typ _ = wf9
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf9_eq : squash (wf9' == wf9) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_tstr = Impl.validate_typ Det.cbor_det_impl env8.be_v true _ wf9'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b9 = impl_bundle_wf_type' Det.cbor_det_impl env8 avenv8 aenv8 aaenv8 wf9' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_tstr = b9.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b9' = { b9 with b_parser = parse_tstr }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env9 =
  bundle_env_extend_typ_with_weak env8 (T.pull_name sorted_source8) (T.pull_type sorted_source8) wf9' validate_tstr b9'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv9 : Parse.ancillary_validate_env Det.cbor_det_match env9.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv8 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv9 : ancillary_bundle_env Det.cbor_det_match env9.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv8 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv9 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env9.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv8 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source9 = List.Tot.tl sorted_source8

let _ : unit = _ by (FStar.Tactics.print ("34 defs remaining. Producing definitions for label"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf10 = compute_wf_typ env9.be_ast (T.pull_name sorted_source9) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source9) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf10' : ast0_wf_typ _ = wf10
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf10_eq : squash (wf10' == wf10) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_label = Impl.validate_typ Det.cbor_det_impl env9.be_v true _ wf10'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b10 = impl_bundle_wf_type' Det.cbor_det_impl env9 avenv9 aenv9 aaenv9 wf10' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_label = b10.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b10' = { b10 with b_parser = parse_label }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env10 =
  bundle_env_extend_typ_with_weak env9 (T.pull_name sorted_source9) (T.pull_type sorted_source9) wf10' validate_label b10'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv10 : Parse.ancillary_validate_env Det.cbor_det_match env10.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv9 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv10 : ancillary_bundle_env Det.cbor_det_match env10.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv9 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv10 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env10.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv9 _
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
let avenv11 : Parse.ancillary_validate_env Det.cbor_det_match env11.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv10 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv11 : ancillary_bundle_env Det.cbor_det_match env11.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv10 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv11 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env11.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv10 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source11 = List.Tot.tl sorted_source10

let _ : unit = _ by (FStar.Tactics.print ("32 defs remaining. Producing definitions for tdate"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf12 = compute_wf_typ env11.be_ast (T.pull_name sorted_source11) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source11) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf12' : ast0_wf_typ _ = wf12
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf12_eq : squash (wf12' == wf12) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_tdate = Impl.validate_typ Det.cbor_det_impl env11.be_v true _ wf12'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b12 = impl_bundle_wf_type' Det.cbor_det_impl env11 avenv11 aenv11 aaenv11 wf12' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_tdate = b12.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b12' = { b12 with b_parser = parse_tdate }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env12 =
  bundle_env_extend_typ_with_weak env11 (T.pull_name sorted_source11) (T.pull_type sorted_source11) wf12' validate_tdate b12'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv12 : Parse.ancillary_validate_env Det.cbor_det_match env12.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv11 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv12 : ancillary_bundle_env Det.cbor_det_match env12.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv11 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv12 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env12.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv11 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source12 = List.Tot.tl sorted_source11

let _ : unit = _ by (FStar.Tactics.print ("31 defs remaining. Producing definitions for uri"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf13 = compute_wf_typ env12.be_ast (T.pull_name sorted_source12) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source12) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf13' : ast0_wf_typ _ = wf13
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf13_eq : squash (wf13' == wf13) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_uri = Impl.validate_typ Det.cbor_det_impl env12.be_v true _ wf13'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b13 = impl_bundle_wf_type' Det.cbor_det_impl env12 avenv12 aenv12 aaenv12 wf13' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_uri = b13.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b13' = { b13 with b_parser = parse_uri }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env13 =
  bundle_env_extend_typ_with_weak env12 (T.pull_name sorted_source12) (T.pull_type sorted_source12) wf13' validate_uri b13'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv13 : Parse.ancillary_validate_env Det.cbor_det_match env13.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv12 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv13 : ancillary_bundle_env Det.cbor_det_match env13.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv12 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv13 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env13.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv12 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source13 = List.Tot.tl sorted_source12

let _ : unit = _ by (FStar.Tactics.print ("30 defs remaining. Producing definitions for b64url"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf14 = compute_wf_typ env13.be_ast (T.pull_name sorted_source13) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source13) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf14' : ast0_wf_typ _ = wf14
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf14_eq : squash (wf14' == wf14) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_b64url = Impl.validate_typ Det.cbor_det_impl env13.be_v true _ wf14'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b14 = impl_bundle_wf_type' Det.cbor_det_impl env13 avenv13 aenv13 aaenv13 wf14' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_b64url = b14.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b14' = { b14 with b_parser = parse_b64url }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env14 =
  bundle_env_extend_typ_with_weak env13 (T.pull_name sorted_source13) (T.pull_type sorted_source13) wf14' validate_b64url b14'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv14 : Parse.ancillary_validate_env Det.cbor_det_match env14.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv13 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv14 : ancillary_bundle_env Det.cbor_det_match env14.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv13 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv14 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env14.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv13 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source14 = List.Tot.tl sorted_source13

let _ : unit = _ by (FStar.Tactics.print ("29 defs remaining. Producing definitions for b64legacy"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf15 = compute_wf_typ env14.be_ast (T.pull_name sorted_source14) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source14) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf15' : ast0_wf_typ _ = wf15
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf15_eq : squash (wf15' == wf15) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_b64legacy = Impl.validate_typ Det.cbor_det_impl env14.be_v true _ wf15'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b15 = impl_bundle_wf_type' Det.cbor_det_impl env14 avenv14 aenv14 aaenv14 wf15' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_b64legacy = b15.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b15' = { b15 with b_parser = parse_b64legacy }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env15 =
  bundle_env_extend_typ_with_weak env14 (T.pull_name sorted_source14) (T.pull_type sorted_source14) wf15' validate_b64legacy b15'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv15 : Parse.ancillary_validate_env Det.cbor_det_match env15.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv14 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv15 : ancillary_bundle_env Det.cbor_det_match env15.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv14 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv15 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env15.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv14 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source15 = List.Tot.tl sorted_source14

let _ : unit = _ by (FStar.Tactics.print ("28 defs remaining. Producing definitions for regexp"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf16 = compute_wf_typ env15.be_ast (T.pull_name sorted_source15) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source15) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf16' : ast0_wf_typ _ = wf16
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf16_eq : squash (wf16' == wf16) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_regexp = Impl.validate_typ Det.cbor_det_impl env15.be_v true _ wf16'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b16 = impl_bundle_wf_type' Det.cbor_det_impl env15 avenv15 aenv15 aaenv15 wf16' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_regexp = b16.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b16' = { b16 with b_parser = parse_regexp }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env16 =
  bundle_env_extend_typ_with_weak env15 (T.pull_name sorted_source15) (T.pull_type sorted_source15) wf16' validate_regexp b16'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv16 : Parse.ancillary_validate_env Det.cbor_det_match env16.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv15 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv16 : ancillary_bundle_env Det.cbor_det_match env16.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv15 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv16 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env16.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv15 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source16 = List.Tot.tl sorted_source15

let _ : unit = _ by (FStar.Tactics.print ("27 defs remaining. Producing definitions for mime-message"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf17 = compute_wf_typ env16.be_ast (T.pull_name sorted_source16) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source16) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf17' : ast0_wf_typ _ = wf17
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf17_eq : squash (wf17' == wf17) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_mimemessage = Impl.validate_typ Det.cbor_det_impl env16.be_v true _ wf17'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b17 = impl_bundle_wf_type' Det.cbor_det_impl env16 avenv16 aenv16 aaenv16 wf17' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_mimemessage = b17.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b17' = { b17 with b_parser = parse_mimemessage }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env17 =
  bundle_env_extend_typ_with_weak env16 (T.pull_name sorted_source16) (T.pull_type sorted_source16) wf17' validate_mimemessage b17'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv17 : Parse.ancillary_validate_env Det.cbor_det_match env17.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv16 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv17 : ancillary_bundle_env Det.cbor_det_match env17.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv16 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv17 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env17.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv16 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source17 = List.Tot.tl sorted_source16

let _ : unit = _ by (FStar.Tactics.print ("26 defs remaining. Producing definitions for text"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf18 = compute_wf_typ env17.be_ast (T.pull_name sorted_source17) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source17) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf18' : ast0_wf_typ _ = wf18
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf18_eq : squash (wf18' == wf18) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_text = Impl.validate_typ Det.cbor_det_impl env17.be_v true _ wf18'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b18 = impl_bundle_wf_type' Det.cbor_det_impl env17 avenv17 aenv17 aaenv17 wf18' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_text = b18.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b18' = { b18 with b_parser = parse_text }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env18 =
  bundle_env_extend_typ_with_weak env17 (T.pull_name sorted_source17) (T.pull_type sorted_source17) wf18' validate_text b18'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv18 : Parse.ancillary_validate_env Det.cbor_det_match env18.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv17 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv18 : ancillary_bundle_env Det.cbor_det_match env18.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv17 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv18 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env18.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv17 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source18 = List.Tot.tl sorted_source17

let _ : unit = _ by (FStar.Tactics.print ("25 defs remaining. Producing definitions for false"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf19 = compute_wf_typ env18.be_ast (T.pull_name sorted_source18) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source18) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf19' : ast0_wf_typ _ = wf19
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf19_eq : squash (wf19' == wf19) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_false = Impl.validate_typ Det.cbor_det_impl env18.be_v true _ wf19'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b19 = impl_bundle_wf_type' Det.cbor_det_impl env18 avenv18 aenv18 aaenv18 wf19' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_false = b19.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b19' = { b19 with b_parser = parse_false }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env19 =
  bundle_env_extend_typ_with_weak env18 (T.pull_name sorted_source18) (T.pull_type sorted_source18) wf19' validate_false b19'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv19 : Parse.ancillary_validate_env Det.cbor_det_match env19.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv18 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv19 : ancillary_bundle_env Det.cbor_det_match env19.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv18 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv19 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env19.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv18 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source19 = List.Tot.tl sorted_source18

let _ : unit = _ by (FStar.Tactics.print ("24 defs remaining. Producing definitions for true"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf20 = compute_wf_typ env19.be_ast (T.pull_name sorted_source19) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source19) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf20' : ast0_wf_typ _ = wf20
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf20_eq : squash (wf20' == wf20) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_true = Impl.validate_typ Det.cbor_det_impl env19.be_v true _ wf20'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b20 = impl_bundle_wf_type' Det.cbor_det_impl env19 avenv19 aenv19 aaenv19 wf20' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_true = b20.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b20' = { b20 with b_parser = parse_true }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env20 =
  bundle_env_extend_typ_with_weak env19 (T.pull_name sorted_source19) (T.pull_type sorted_source19) wf20' validate_true b20'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv20 : Parse.ancillary_validate_env Det.cbor_det_match env20.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv19 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv20 : ancillary_bundle_env Det.cbor_det_match env20.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv19 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv20 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env20.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv19 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source20 = List.Tot.tl sorted_source19

let _ : unit = _ by (FStar.Tactics.print ("23 defs remaining. Producing definitions for nil"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf21 = compute_wf_typ env20.be_ast (T.pull_name sorted_source20) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source20) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf21' : ast0_wf_typ _ = wf21
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf21_eq : squash (wf21' == wf21) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_nil = Impl.validate_typ Det.cbor_det_impl env20.be_v true _ wf21'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b21 = impl_bundle_wf_type' Det.cbor_det_impl env20 avenv20 aenv20 aaenv20 wf21' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_nil = b21.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b21' = { b21 with b_parser = parse_nil }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env21 =
  bundle_env_extend_typ_with_weak env20 (T.pull_name sorted_source20) (T.pull_type sorted_source20) wf21' validate_nil b21'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv21 : Parse.ancillary_validate_env Det.cbor_det_match env21.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv20 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv21 : ancillary_bundle_env Det.cbor_det_match env21.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv20 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv21 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env21.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv20 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source21 = List.Tot.tl sorted_source20

let _ : unit = _ by (FStar.Tactics.print ("22 defs remaining. Producing definitions for null"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf22 = compute_wf_typ env21.be_ast (T.pull_name sorted_source21) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source21) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf22' : ast0_wf_typ _ = wf22
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf22_eq : squash (wf22' == wf22) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_null = Impl.validate_typ Det.cbor_det_impl env21.be_v true _ wf22'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b22 = impl_bundle_wf_type' Det.cbor_det_impl env21 avenv21 aenv21 aaenv21 wf22' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_null = b22.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b22' = { b22 with b_parser = parse_null }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env22 =
  bundle_env_extend_typ_with_weak env21 (T.pull_name sorted_source21) (T.pull_type sorted_source21) wf22' validate_null b22'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv22 : Parse.ancillary_validate_env Det.cbor_det_match env22.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv21 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv22 : ancillary_bundle_env Det.cbor_det_match env22.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv21 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv22 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env22.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv21 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source22 = List.Tot.tl sorted_source21

let _ : unit = _ by (FStar.Tactics.print ("21 defs remaining. Producing definitions for undefined"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf23 = compute_wf_typ env22.be_ast (T.pull_name sorted_source22) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source22) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf23' : ast0_wf_typ _ = wf23
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf23_eq : squash (wf23' == wf23) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_undefined = Impl.validate_typ Det.cbor_det_impl env22.be_v true _ wf23'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b23 = impl_bundle_wf_type' Det.cbor_det_impl env22 avenv22 aenv22 aaenv22 wf23' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_undefined = b23.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b23' = { b23 with b_parser = parse_undefined }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env23 =
  bundle_env_extend_typ_with_weak env22 (T.pull_name sorted_source22) (T.pull_type sorted_source22) wf23' validate_undefined b23'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv23 : Parse.ancillary_validate_env Det.cbor_det_match env23.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv22 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv23 : ancillary_bundle_env Det.cbor_det_match env23.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv22 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv23 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env23.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv22 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source23 = List.Tot.tl sorted_source22

let _ : unit = _ by (FStar.Tactics.print ("20 defs remaining. Producing definitions for any"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf24 = compute_wf_typ env23.be_ast (T.pull_name sorted_source23) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source23) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf24' : ast0_wf_typ _ = wf24
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf24_eq : squash (wf24' == wf24) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_any = Impl.validate_typ Det.cbor_det_impl env23.be_v true _ wf24'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b24 = impl_bundle_wf_type' Det.cbor_det_impl env23 avenv23 aenv23 aaenv23 wf24' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_any = b24.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b24' = { b24 with b_parser = parse_any }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env24 =
  bundle_env_extend_typ_with_weak env23 (T.pull_name sorted_source23) (T.pull_type sorted_source23) wf24' validate_any b24'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv24 : Parse.ancillary_validate_env Det.cbor_det_match env24.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv23 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv24 : ancillary_bundle_env Det.cbor_det_match env24.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv23 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv24 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env24.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv23 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source24 = List.Tot.tl sorted_source23

let _ : unit = _ by (FStar.Tactics.print ("19 defs remaining. Producing definitions for values"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf25 = compute_wf_typ env24.be_ast (T.pull_name sorted_source24) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source24) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf25' : ast0_wf_typ _ = wf25
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf25_eq : squash (wf25' == wf25) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_values = Impl.validate_typ Det.cbor_det_impl env24.be_v true _ wf25'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b25 = impl_bundle_wf_type' Det.cbor_det_impl env24 avenv24 aenv24 aaenv24 wf25' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_values = b25.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b25' = { b25 with b_parser = parse_values }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env25 =
  bundle_env_extend_typ_with_weak env24 (T.pull_name sorted_source24) (T.pull_type sorted_source24) wf25' validate_values b25'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv25 : Parse.ancillary_validate_env Det.cbor_det_match env25.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv24 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv25 : ancillary_bundle_env Det.cbor_det_match env25.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv24 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv25 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env25.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv24 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source25 = List.Tot.tl sorted_source24
(*
let _ : unit = _ by (FStar.Tactics.print ("18 defs remaining. Producing definitions for header_map"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf26 = compute_wf_typ env25.be_ast (T.pull_name sorted_source25) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source25) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf26' : ast0_wf_typ _ = wf26
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf26_eq : squash (wf26' == wf26) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_header_map = Impl.validate_typ Det.cbor_det_impl env25.be_v true _ wf26'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b26 = impl_bundle_wf_type' Det.cbor_det_impl env25 avenv25 aenv25 aaenv25 wf26' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_header_map = b26.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b26' = { b26 with b_parser = parse_header_map }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env26 =
  bundle_env_extend_typ_with_weak env25 (T.pull_name sorted_source25) (T.pull_type sorted_source25) wf26' validate_header_map b26'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv26 : Parse.ancillary_validate_env Det.cbor_det_match env26.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv25 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv26 : ancillary_bundle_env Det.cbor_det_match env26.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv25 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv26 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env26.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv25 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source26 = List.Tot.tl sorted_source25

let _ : unit = _ by (FStar.Tactics.print ("17 defs remaining. Producing definitions for empty_or_serialized_map"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf27 = compute_wf_typ env26.be_ast (T.pull_name sorted_source26) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source26) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf27' : ast0_wf_typ _ = wf27
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf27_eq : squash (wf27' == wf27) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_empty_or_serialized_map = Impl.validate_typ Det.cbor_det_impl env26.be_v true _ wf27'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b27 = impl_bundle_wf_type' Det.cbor_det_impl env26 avenv26 aenv26 aaenv26 wf27' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_empty_or_serialized_map = b27.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b27' = { b27 with b_parser = parse_empty_or_serialized_map }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env27 =
  bundle_env_extend_typ_with_weak env26 (T.pull_name sorted_source26) (T.pull_type sorted_source26) wf27' validate_empty_or_serialized_map b27'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv27 : Parse.ancillary_validate_env Det.cbor_det_match env27.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv26 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv27 : ancillary_bundle_env Det.cbor_det_match env27.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv26 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv27 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env27.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv26 _
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
let avenv28 : Parse.ancillary_validate_env Det.cbor_det_match env28.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv27 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv28 : ancillary_bundle_env Det.cbor_det_match env28.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv27 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv28 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env28.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv27 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source28 = List.Tot.tl sorted_source27

let _ : unit = _ by (FStar.Tactics.print ("15 defs remaining. Producing definitions for COSE_Signature"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf29 = compute_wf_typ env28.be_ast (T.pull_name sorted_source28) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source28) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf29' : ast0_wf_typ _ = wf29
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf29_eq : squash (wf29' == wf29) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Signature = Impl.validate_typ Det.cbor_det_impl env28.be_v true _ wf29'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b29 = impl_bundle_wf_type' Det.cbor_det_impl env28 avenv28 aenv28 aaenv28 wf29' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Signature = b29.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b29' = { b29 with b_parser = parse_COSE_Signature }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env29 =
  bundle_env_extend_typ_with_weak env28 (T.pull_name sorted_source28) (T.pull_type sorted_source28) wf29' validate_COSE_Signature b29'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv29 : Parse.ancillary_validate_env Det.cbor_det_match env29.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv28 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv29 : ancillary_bundle_env Det.cbor_det_match env29.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv28 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv29 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env29.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv28 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source29 = List.Tot.tl sorted_source28

let _ : unit = _ by (FStar.Tactics.print ("14 defs remaining. Producing definitions for COSE_Sign"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf30 = compute_wf_typ env29.be_ast (T.pull_name sorted_source29) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source29) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf30' : ast0_wf_typ _ = wf30
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf30_eq : squash (wf30' == wf30) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign = Impl.validate_typ Det.cbor_det_impl env29.be_v true _ wf30'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b30 = impl_bundle_wf_type' Det.cbor_det_impl env29 avenv29 aenv29 aaenv29 wf30' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Sign = b30.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b30' = { b30 with b_parser = parse_COSE_Sign }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env30 =
  bundle_env_extend_typ_with_weak env29 (T.pull_name sorted_source29) (T.pull_type sorted_source29) wf30' validate_COSE_Sign b30'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv30 : Parse.ancillary_validate_env Det.cbor_det_match env30.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv29 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv30 : ancillary_bundle_env Det.cbor_det_match env30.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv29 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv30 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env30.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv29 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source30 = List.Tot.tl sorted_source29

let _ : unit = _ by (FStar.Tactics.print ("13 defs remaining. Producing definitions for COSE_Sign_Tagged"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf31 = compute_wf_typ env30.be_ast (T.pull_name sorted_source30) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source30) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf31' : ast0_wf_typ _ = wf31
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf31_eq : squash (wf31' == wf31) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign_Tagged = Impl.validate_typ Det.cbor_det_impl env30.be_v true _ wf31'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b31 = impl_bundle_wf_type' Det.cbor_det_impl env30 avenv30 aenv30 aaenv30 wf31' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Sign_Tagged = b31.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b31' = { b31 with b_parser = parse_COSE_Sign_Tagged }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env31 =
  bundle_env_extend_typ_with_weak env30 (T.pull_name sorted_source30) (T.pull_type sorted_source30) wf31' validate_COSE_Sign_Tagged b31'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv31 : Parse.ancillary_validate_env Det.cbor_det_match env31.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv30 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv31 : ancillary_bundle_env Det.cbor_det_match env31.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv30 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv31 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env31.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv30 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source31 = List.Tot.tl sorted_source30

let _ : unit = _ by (FStar.Tactics.print ("12 defs remaining. Producing definitions for COSE_Sign1"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf32 = compute_wf_typ env31.be_ast (T.pull_name sorted_source31) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source31) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf32' : ast0_wf_typ _ = wf32
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf32_eq : squash (wf32' == wf32) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign1 = Impl.validate_typ Det.cbor_det_impl env31.be_v true _ wf32'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b32 = impl_bundle_wf_type' Det.cbor_det_impl env31 avenv31 aenv31 aaenv31 wf32' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Sign1 = b32.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b32' = { b32 with b_parser = parse_COSE_Sign1 }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env32 =
  bundle_env_extend_typ_with_weak env31 (T.pull_name sorted_source31) (T.pull_type sorted_source31) wf32' validate_COSE_Sign1 b32'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv32 : Parse.ancillary_validate_env Det.cbor_det_match env32.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv31 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv32 : ancillary_bundle_env Det.cbor_det_match env32.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv31 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv32 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env32.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv31 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source32 = List.Tot.tl sorted_source31

let _ : unit = _ by (FStar.Tactics.print ("11 defs remaining. Producing definitions for COSE_Untagged_Message"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf33 = compute_wf_typ env32.be_ast (T.pull_name sorted_source32) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source32) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf33' : ast0_wf_typ _ = wf33
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf33_eq : squash (wf33' == wf33) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Untagged_Message = Impl.validate_typ Det.cbor_det_impl env32.be_v true _ wf33'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b33 = impl_bundle_wf_type' Det.cbor_det_impl env32 avenv32 aenv32 aaenv32 wf33' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Untagged_Message = b33.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b33' = { b33 with b_parser = parse_COSE_Untagged_Message }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env33 =
  bundle_env_extend_typ_with_weak env32 (T.pull_name sorted_source32) (T.pull_type sorted_source32) wf33' validate_COSE_Untagged_Message b33'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv33 : Parse.ancillary_validate_env Det.cbor_det_match env33.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv32 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv33 : ancillary_bundle_env Det.cbor_det_match env33.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv32 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv33 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env33.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv32 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source33 = List.Tot.tl sorted_source32

let _ : unit = _ by (FStar.Tactics.print ("10 defs remaining. Producing definitions for COSE_Sign1_Tagged"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf34 = compute_wf_typ env33.be_ast (T.pull_name sorted_source33) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source33) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf34' : ast0_wf_typ _ = wf34
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf34_eq : squash (wf34' == wf34) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Sign1_Tagged = Impl.validate_typ Det.cbor_det_impl env33.be_v true _ wf34'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b34 = impl_bundle_wf_type' Det.cbor_det_impl env33 avenv33 aenv33 aaenv33 wf34' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Sign1_Tagged = b34.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b34' = { b34 with b_parser = parse_COSE_Sign1_Tagged }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env34 =
  bundle_env_extend_typ_with_weak env33 (T.pull_name sorted_source33) (T.pull_type sorted_source33) wf34' validate_COSE_Sign1_Tagged b34'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv34 : Parse.ancillary_validate_env Det.cbor_det_match env34.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv33 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv34 : ancillary_bundle_env Det.cbor_det_match env34.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv33 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv34 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env34.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv33 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source34 = List.Tot.tl sorted_source33

let _ : unit = _ by (FStar.Tactics.print ("9 defs remaining. Producing definitions for COSE_Tagged_Message"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf35 = compute_wf_typ env34.be_ast (T.pull_name sorted_source34) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source34) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf35' : ast0_wf_typ _ = wf35
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf35_eq : squash (wf35' == wf35) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Tagged_Message = Impl.validate_typ Det.cbor_det_impl env34.be_v true _ wf35'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b35 = impl_bundle_wf_type' Det.cbor_det_impl env34 avenv34 aenv34 aaenv34 wf35' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Tagged_Message = b35.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b35' = { b35 with b_parser = parse_COSE_Tagged_Message }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env35 =
  bundle_env_extend_typ_with_weak env34 (T.pull_name sorted_source34) (T.pull_type sorted_source34) wf35' validate_COSE_Tagged_Message b35'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv35 : Parse.ancillary_validate_env Det.cbor_det_match env35.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv34 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv35 : ancillary_bundle_env Det.cbor_det_match env35.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv34 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv35 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env35.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv34 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source35 = List.Tot.tl sorted_source34

let _ : unit = _ by (FStar.Tactics.print ("8 defs remaining. Producing definitions for COSE_Messages"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf36 = compute_wf_typ env35.be_ast (T.pull_name sorted_source35) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source35) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf36' : ast0_wf_typ _ = wf36
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf36_eq : squash (wf36' == wf36) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_COSE_Messages = Impl.validate_typ Det.cbor_det_impl env35.be_v true _ wf36'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b36 = impl_bundle_wf_type' Det.cbor_det_impl env35 avenv35 aenv35 aaenv35 wf36' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_COSE_Messages = b36.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b36' = { b36 with b_parser = parse_COSE_Messages }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env36 =
  bundle_env_extend_typ_with_weak env35 (T.pull_name sorted_source35) (T.pull_type sorted_source35) wf36' validate_COSE_Messages b36'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv36 : Parse.ancillary_validate_env Det.cbor_det_match env36.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv35 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv36 : ancillary_bundle_env Det.cbor_det_match env36.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv35 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv36 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env36.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv35 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source36 = List.Tot.tl sorted_source35

let _ : unit = _ by (FStar.Tactics.print ("7 defs remaining. Producing definitions for Sig_structure"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf37 = compute_wf_typ env36.be_ast (T.pull_name sorted_source36) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source36) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf37' : ast0_wf_typ _ = wf37
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf37_eq : squash (wf37' == wf37) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_Sig_structure = Impl.validate_typ Det.cbor_det_impl env36.be_v true _ wf37'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b37 = impl_bundle_wf_type' Det.cbor_det_impl env36 avenv36 aenv36 aaenv36 wf37' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_Sig_structure = b37.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b37' = { b37 with b_parser = parse_Sig_structure }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env37 =
  bundle_env_extend_typ_with_weak env36 (T.pull_name sorted_source36) (T.pull_type sorted_source36) wf37' validate_Sig_structure b37'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv37 : Parse.ancillary_validate_env Det.cbor_det_match env37.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv36 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv37 : ancillary_bundle_env Det.cbor_det_match env37.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv36 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv37 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env37.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv36 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source37 = List.Tot.tl sorted_source36

let _ : unit = _ by (FStar.Tactics.print ("6 defs remaining. Producing definitions for Internal_Types"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf38 = compute_wf_typ env37.be_ast (T.pull_name sorted_source37) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source37) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf38' : ast0_wf_typ _ = wf38
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf38_eq : squash (wf38' == wf38) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_Internal_Types = Impl.validate_typ Det.cbor_det_impl env37.be_v true _ wf38'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b38 = impl_bundle_wf_type' Det.cbor_det_impl env37 avenv37 aenv37 aaenv37 wf38' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_Internal_Types = b38.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b38' = { b38 with b_parser = parse_Internal_Types }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env38 =
  bundle_env_extend_typ_with_weak env37 (T.pull_name sorted_source37) (T.pull_type sorted_source37) wf38' validate_Internal_Types b38'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv38 : Parse.ancillary_validate_env Det.cbor_det_match env38.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv37 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv38 : ancillary_bundle_env Det.cbor_det_match env38.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv37 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv38 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env38.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv37 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source38 = List.Tot.tl sorted_source37

let _ : unit = _ by (FStar.Tactics.print ("5 defs remaining. Producing definitions for start"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf39 = compute_wf_typ env38.be_ast (T.pull_name sorted_source38) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source38) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf39' : ast0_wf_typ _ = wf39
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf39_eq : squash (wf39' == wf39) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_start = Impl.validate_typ Det.cbor_det_impl env38.be_v true _ wf39'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b39 = impl_bundle_wf_type' Det.cbor_det_impl env38 avenv38 aenv38 aaenv38 wf39' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_start = b39.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b39' = { b39 with b_parser = parse_start }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env39 =
  bundle_env_extend_typ_with_weak env38 (T.pull_name sorted_source38) (T.pull_type sorted_source38) wf39' validate_start b39'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv39 : Parse.ancillary_validate_env Det.cbor_det_match env39.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv38 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv39 : ancillary_bundle_env Det.cbor_det_match env39.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv38 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv39 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env39.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv38 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source39 = List.Tot.tl sorted_source38

let _ : unit = _ by (FStar.Tactics.print ("4 defs remaining. Producing definitions for eb64url"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf40 = compute_wf_typ env39.be_ast (T.pull_name sorted_source39) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source39) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf40' : ast0_wf_typ _ = wf40
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf40_eq : squash (wf40' == wf40) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_eb64url = Impl.validate_typ Det.cbor_det_impl env39.be_v true _ wf40'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b40 = impl_bundle_wf_type' Det.cbor_det_impl env39 avenv39 aenv39 aaenv39 wf40' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_eb64url = b40.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b40' = { b40 with b_parser = parse_eb64url }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env40 =
  bundle_env_extend_typ_with_weak env39 (T.pull_name sorted_source39) (T.pull_type sorted_source39) wf40' validate_eb64url b40'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv40 : Parse.ancillary_validate_env Det.cbor_det_match env40.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv39 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv40 : ancillary_bundle_env Det.cbor_det_match env40.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv39 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv40 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env40.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv39 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source40 = List.Tot.tl sorted_source39

let _ : unit = _ by (FStar.Tactics.print ("3 defs remaining. Producing definitions for eb64legacy"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf41 = compute_wf_typ env40.be_ast (T.pull_name sorted_source40) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source40) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf41' : ast0_wf_typ _ = wf41
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf41_eq : squash (wf41' == wf41) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_eb64legacy = Impl.validate_typ Det.cbor_det_impl env40.be_v true _ wf41'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b41 = impl_bundle_wf_type' Det.cbor_det_impl env40 avenv40 aenv40 aaenv40 wf41' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_eb64legacy = b41.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b41' = { b41 with b_parser = parse_eb64legacy }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env41 =
  bundle_env_extend_typ_with_weak env40 (T.pull_name sorted_source40) (T.pull_type sorted_source40) wf41' validate_eb64legacy b41'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv41 : Parse.ancillary_validate_env Det.cbor_det_match env41.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv40 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv41 : ancillary_bundle_env Det.cbor_det_match env41.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv40 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv41 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env41.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv40 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source41 = List.Tot.tl sorted_source40

let _ : unit = _ by (FStar.Tactics.print ("2 defs remaining. Producing definitions for eb16"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf42 = compute_wf_typ env41.be_ast (T.pull_name sorted_source41) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source41) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf42' : ast0_wf_typ _ = wf42
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf42_eq : squash (wf42' == wf42) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_eb16 = Impl.validate_typ Det.cbor_det_impl env41.be_v true _ wf42'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b42 = impl_bundle_wf_type' Det.cbor_det_impl env41 avenv41 aenv41 aaenv41 wf42' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_eb16 = b42.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b42' = { b42 with b_parser = parse_eb16 }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env42 =
  bundle_env_extend_typ_with_weak env41 (T.pull_name sorted_source41) (T.pull_type sorted_source41) wf42' validate_eb16 b42'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv42 : Parse.ancillary_validate_env Det.cbor_det_match env42.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv41 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv42 : ancillary_bundle_env Det.cbor_det_match env42.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv41 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv42 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env42.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv41 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source42 = List.Tot.tl sorted_source41

let _ : unit = _ by (FStar.Tactics.print ("1 defs remaining. Producing definitions for cbor-any"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf43 = compute_wf_typ env42.be_ast (T.pull_name sorted_source42) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source42) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let wf43' : ast0_wf_typ _ = wf43
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf43_eq : squash (wf43' == wf43) = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_cborany = Impl.validate_typ Det.cbor_det_impl env42.be_v true _ wf43'
let _ : unit = _ by (FStar.Tactics.print ("bundle"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b43 = impl_bundle_wf_type' Det.cbor_det_impl env42 avenv42 aenv42 aaenv42 wf43' (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let parse_cborany = b43.b_parser
let _ : unit = _ by (FStar.Tactics.print ("bundle'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; bundle_attr; bundle_get_impl_type_attr]
let b43' = { b43 with b_parser = parse_cborany }
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let env43 =
  bundle_env_extend_typ_with_weak env42 (T.pull_name sorted_source42) (T.pull_type sorted_source42) wf43' validate_cborany b43'
let _ : unit = _ by (FStar.Tactics.print ("ancillary envs"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let avenv43 : Parse.ancillary_validate_env Det.cbor_det_match env43.be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend avenv42 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aenv43 : ancillary_bundle_env Det.cbor_det_match env43.be_ast.e_sem_env =
  ancillary_bundle_env_extend aenv42 _
[@@noextract_to "krml"; sem_attr; bundle_attr] noextract
let aaenv43 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match env43.be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aaenv42 _
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; base_attr] noextract
let sorted_source43 = List.Tot.tl sorted_source42

(*

Verified module: CDDLTest.Validate
All verification conditions discharged successfully
touch -c CDDLTest.Validate.fst.checked
