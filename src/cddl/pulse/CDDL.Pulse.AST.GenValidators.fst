module CDDL.Pulse.AST.GenValidators
include CDDL.Spec.AST.Driver
module U32 = FStar.UInt32

let filter_char (c: FStar.Char.char) : Tot bool =
  let code = FStar.Char.u32_of_char c in
  (code `U32.gte` FStar.Char.u32_of_char 'A' &&
    code `U32.lte` FStar.Char.u32_of_char 'Z') ||
  (code `U32.gte` FStar.Char.u32_of_char 'a' &&
    code `U32.lte` FStar.Char.u32_of_char 'z') ||
  (code `U32.gte` FStar.Char.u32_of_char '0' &&
    code `U32.lte` FStar.Char.u32_of_char '9') ||
  code = FStar.Char.u32_of_char '_'

let filter_name (name: string) = 
  FStar.String.string_of_list (List.Tot.filter filter_char (FStar.String.list_of_string name))

let mk_validator_name (name: string) : string =
  "validate_" ^ filter_name name

let mk_impltype_name (name: string) : string =
  "impltype_" ^ filter_name name

let mk_parsertype_name (name: string) : string =
  "parsertype_" ^ filter_name name

let mk_parser_name (name: string) : string =
  "parse_" ^ filter_name name

let krml = "\"krml\""

let extend_ancillaries env env' source source' =
"let _ : unit = _ by (FStar.Tactics.print (\"ancillary envs\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"; sem_attr] noextract
let av"^env'^" : Parse.ancillary_validate_env Det.cbor_det_match "^env'^".si_ast.e_sem_env =
  Parse.ancillary_validate_env_extend av"^env^" _
[@@noextract_to "^krml^"; sem_attr] noextract
let a"^env'^" : Parse.ancillary_parse_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match "^env'^".si_r "^env'^".si_sp =
  Parse.ancillary_parse_env_extend a"^env^" _ _
[@@noextract_to "^krml^"; sem_attr] noextract
let aa"^env'^" : Parse.ancillary_parse_array_group_env Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match "^env'^".si_r "^env'^".si_sp =
  Parse.ancillary_parse_array_group_env_extend aa"^env^" _ _
let _ : unit = _ by (FStar.Tactics.print (\"source'\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "^krml^"; sem_attr] noextract
let "^source'^" = List.Tot.tl "^source^"
"

let produce_typ_defs
  (index: nat)
  (name: string)
: Tot string
= 
  let i = string_of_int index in
  let j = string_of_int (index + 1) in
  let validator = mk_validator_name name in
  let impltype = mk_impltype_name name in
  let parsertype = mk_parsertype_name name in
  let parser = mk_parser_name name in
  let wf = "wf" ^ j in
  let wf' = wf ^ "'" in
  let env = "env" ^ i in
  let env' = "env" ^ j in
  let ask = "ask" ^ j in
  let source = "sorted_source" ^ i in
  let source' = "sorted_source" ^ j in
  (
"
let _ : unit = _ by (FStar.Tactics.print (\"wf\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"] noextract
let "^wf^" = compute_wf_typ "^env^".si_ast (T.pull_name "^source^") (_ by (FStar.Tactics.trefl ())) (T.pull_type "^source^") (_ by (T.solve_mk_wf_typ_fuel_for ()))
let _ : unit = _ by (FStar.Tactics.print (\"wf'\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "^krml^"; sem_attr] noextract
let "^wf'^" : ast0_wf_typ _ = "^wf^"
let _ : unit = _ by (FStar.Tactics.print (\"wf_eq\"); FStar.Tactics.exact (`()))
let "^wf^"_eq : squash ("^wf'^" == "^wf^") = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print (\"validator\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let "^validator^" = Impl.validate_typ Det.cbor_det_impl "^env^".si_v true _ "^wf'^"
let _ : unit = _ by (FStar.Tactics.print (\"impltype'\"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "^krml^"; sem_attr]
let "^impltype^"' = (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match "^env^".si_r (target_type_of_wf_typ "^wf'^")).sem_impl_type
let _ : unit = _ by (FStar.Tactics.print (\"impltype\"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "^krml^"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (T.steps); FStar.Tactics.trefl ())]
let "^impltype^" = "^impltype^"'
let _ : unit = _ by (FStar.Tactics.print (\"eqimpltype\"); FStar.Tactics.exact (`()))
let eq"^impltype^" : squash ("^impltype^"' == "^impltype^") = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print (\"parser type'\"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "^krml^"; sem_attr]
let "^parsertype^"' = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ "^env^".si_sp "^wf'^").parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match "^env^".si_r (target_type_of_wf_typ "^wf'^")).sem_rel
let _ : unit = _ by (FStar.Tactics.print (\"parser type\"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "^krml^"]
let "^parsertype^" = impl_zero_copy_parse Det.cbor_det_match (spec_of_wf_typ "^env^".si_sp "^wf'^").parser #"^impltype^" (coerce_rel (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match "^env^".si_r (target_type_of_wf_typ "^wf'^")).sem_rel "^impltype^" eq"^impltype^")
let eq"^parsertype^" : squash ("^parsertype^"' == "^parsertype^") = impl_zero_copy_parse_t_eq Det.cbor_det_match (spec_of_wf_typ "^env^".si_sp "^wf'^").parser (impl_type_sem Det.cbor_det_match Det.cbor_det_array_iterator_match Det.cbor_det_map_iterator_match "^env^".si_r (target_type_of_wf_typ "^wf'^")).sem_rel "^impltype^" eq"^impltype^"
let _ : unit = _ by (FStar.Tactics.print (\"parser\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let "^parser^" : "^parsertype^" = T.inline_coerce_eq eq"^parsertype^" (Parse.impl_zero_copy_wf_type' "^env^" av"^env^" a"^env^" aa"^env^" "^wf'^" (_ by (T.trefl_or_norm ())))
let _ : unit = _ by (FStar.Tactics.print (\"parser'\"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "^krml^"]
let "^parser^"' : "^parsertype^"' = T.inline_coerce_eq_reverse eq"^parsertype^" "^parser^"
let _ : unit = _ by (FStar.Tactics.print (\"env'\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"; sem_attr] noextract
let "^env'^" (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_typ_with_weak "^env^" (T.pull_name "^source^") (T.pull_type "^source^") "^wf'^" "^validator^" "^parser^"'
" ^ extend_ancillaries env env' source source'
)

let produce_group_defs
  (index: nat)
: Tot string
=
  let i = string_of_int index in
  let j = string_of_int (index + 1) in
  let env = "env" ^ i in
  let env' = "env" ^ j in
  let source = "sorted_source" ^ i in
  let source' = "sorted_source" ^ j in
(
"
let _ : unit = _ by (FStar.Tactics.print (\"env'\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"; sem_attr] noextract
let "^env'^" (* : spec_and_impl_env Det.cbor_det_impl *) =
  spec_and_impl_env_extend_group "^env^" (T.pull_name "^source^") (T.pull_group "^source^") (_ by (T.trefl_or_norm ())) (_ by (T.trefl_or_norm ()))
" ^ extend_ancillaries env env' source source'
)

let rec produce_defs'
  (index: nat)
  (accu: string)
  (l: list (string & decl))
: Tot string
  (decreases l)
= match l with
  | [] -> accu
  | (name, def) :: q ->
    let accu = accu ^
"
let _ : unit = _ by (FStar.Tactics.print (\"" ^ string_of_int (List.Tot.length l) ^ " defs remaining. Producing definitions for "^name^"\"); FStar.Tactics.exact (`()))
"
    in
    begin match def with
    | DType _ ->
      produce_defs' (index + 1) (accu ^ produce_typ_defs index name) q
    | DGroup _ ->
      produce_defs' (index + 1) (accu ^ produce_group_defs index) q
    end

let produce_defs l = produce_defs' 0 "
*)
" l ^ "
(*
"
