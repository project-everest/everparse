module CDDLTest.Parse
open CDDL.Pulse.AST.Env
open CDDL.Pulse.AST.GenValidators
module Det = CDDL.Pulse.AST.Det.C
module Impl = CDDL.Pulse.AST.Validate
module Parse = CDDL.Pulse.AST.Parse
module T = CDDL.Spec.AST.Tactics
module SZ = FStar.SizeT

(*
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let option_source = // CDDL.Spec.AST.Plugin.parse ["cose.cddl"; "../spec/postlude.cddl"]
    Some
    [
      "int", DType (TChoice (TElem EUInt) (TElem ENInt));
    ]

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let source = Some?.v option_source

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let option_sorted_source = topological_sort source

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source0 = Some?.v option_sorted_source
*)

  [@@ noextract_to "krml"; sem_attr]
  noextract
  let sorted_source0 =
    [
      "int", DType (TChoice (TElem EUInt) (TElem ENInt))
    ]

[@@noextract_to "krml"] noextract
let env0 : spec_and_impl_env = empty_spec_and_impl_env

[@@noextract_to "krml"] noextract
let venv0 : Impl.validator_env Det.cbor_det_match env0.si_ast.e_sem_env =
  Impl.empty_validator_env _

[@@noextract_to "krml"; sem_attr] noextract
let avenv0 : Parse.ancillary_validate_env Det.cbor_det_match env0.si_ast.e_sem_env =
  fun _ -> None

[@@noextract_to "krml"; sem_attr] noextract
let aenv0 : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r env0.si_sp =
  fun _ _ -> None

[@@noextract_to "krml"; sem_attr] noextract
let aaenv0 : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r env0.si_sp =
  fun _ _ -> None

[@@noextract_to "krml"; sem_attr] noextract
let penv0 : Parse.parse_env Det.cbor_det_match env0.si_r env0.si_sp =
  Parse.empty_parse_env _

let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64)

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let defs = produce_defs sorted_source0

[@@noextract_to "krml"; sem_attr] noextract inline_for_extraction
let inline_coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x

let _ : unit = _ by (FStar.Tactics.print defs; FStar.Tactics.exact (`()))

(*
fstar.exe  --load_cmxs evercddl_lib --load_cmxs evercddl_plugin --warn_error -342 --odir _output   --include /home/tahina/everest/everparse/src/cbor/spec --include /home/tahina/everest/everparse/src/cddl/spec --include /home/tahina/everest/everparse/lib/evercddl/lib --include /home/tahina/everest/everparse/lib/evercddl/plugin --include /home/tahina/everest/everparse/src/cbor/pulse --include /home/tahina/everest/everparse/src/cddl/pulse --include /home/tahina/everest/karamel/krmllib --include /home/tahina/everest/karamel/krmllib/obj --include /home/tahina/everest/pulse/out/lib/pulse --include . --cache_checked_modules --warn_error @241 --already_cached PulseCore,Pulse,C,LowStar,*,-CDDLTest,Prims,FStar,LowStar --cmi --ext context_pruning   CDDLTest.fst
TAC>> 
*)

#set-options "--print_implicits"

let _ : unit = _ by (FStar.Tactics.print ("43 defs remaining. Producing definitions for either_uint_negint"); FStar.Tactics.exact (`()))

let _ : unit = _ by (FStar.Tactics.print ("wf"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"] noextract
let wf1 = compute_wf_typ env0.si_ast (T.pull_name sorted_source0) (_ by (FStar.Tactics.trefl ())) (T.pull_type sorted_source0) (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print ("wf'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let wf1' : ast0_wf_typ _ = wf1
let _ : unit = _ by (FStar.Tactics.print ("wf_eq"); FStar.Tactics.exact (`()))
let wf1_eq : squash (wf1' == wf1) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
let _ : unit = _ by (FStar.Tactics.print ("validator"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let validate_either_uint_negint = Impl.validate_typ Det.cbor_det_impl venv0 true _ wf1'
let _ : unit = _ by (FStar.Tactics.print ("ancillaries"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"] noextract
let ask1_0 : option _ = Parse.ask_zero_copy_wf_type (Parse.ancillary_validate_env_is_some avenv0) (Parse.ancillary_parse_env_is_some aenv0) (Parse.ancillary_parse_array_group_env_is_some aaenv0) wf1'
let _ = assert_norm (None? ask1_0)
let _ : unit = _ by (FStar.Tactics.print ("parser type'"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "krml"; sem_attr]
let parse_either_uint_negint_t' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ env0.si_sp wf1').parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match env0.si_r (target_type_of_wf_typ wf1')).sem_rel
let _ : unit = _ by (FStar.Tactics.print ("parser type"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm T.steps; FStar.Tactics.trefl ()); sem_attr]
let parse_either_uint_negint_t = parse_either_uint_negint_t'
let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let parse_either_uint_negint : parse_either_uint_negint_t = inline_coerce_eq (_ by (FStar.Tactics.norm [nbe; delta; iota; zeta; primops]; FStar.Tactics.trefl ())) (Parse.impl_zero_copy_wf_type Det.cbor_det_impl venv0 env0.si_r env0.si_sp penv0 avenv0 aenv0 aaenv0 wf1')
let _ : unit = _ by (FStar.Tactics.print ("parser'"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "krml"]
let parse_either_uint_negint' : parse_either_uint_negint_t' = inline_coerce_eq (_ by (FStar.Tactics.norm [nbe; delta; iota; zeta; primops]; FStar.Tactics.trefl ())) parse_either_uint_negint
let _ : unit = _ by (FStar.Tactics.print ("env'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let env1 : spec_and_impl_env =
  spec_and_impl_env_extend_typ_with_weak Det.cbor_det_impl env0 (T.pull_name sorted_source0) (T.pull_type sorted_source0) wf1'
let _ : unit = _ by (FStar.Tactics.print ("venv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let venv1 : Impl.validator_env Det.cbor_det_match env1.si_ast.e_sem_env =
  Impl.extend_validator_env_with_typ_weak venv0 (T.pull_name sorted_source0) (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())) (T.pull_type sorted_source0) (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())) validate_either_uint_negint
let _ : unit = _ by (FStar.Tactics.print ("penv'"); FStar.Tactics.exact (`()))
[@@noextract_to "krml"; sem_attr] noextract
let penv1 : Parse.parse_env Det.cbor_det_match env1.si_r env1.si_sp =
  parse_env_extend Det.cbor_det_impl env0 penv0 (T.pull_name sorted_source0) (T.pull_type sorted_source0) wf1' parse_either_uint_negint'
let _ : unit = _ by (FStar.Tactics.print ("source'"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "krml"; sem_attr] noextract
let sorted_source1 = List.Tot.tl sorted_source0
