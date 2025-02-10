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
[@@noextract_to "^krml^"; sem_attr; bundle_attr] noextract
let av"^env'^" : Parse.ancillary_validate_env Det.cbor_det_match "^env'^".be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend av"^env^" _
[@@noextract_to "^krml^"; sem_attr; bundle_attr] noextract
let a"^env'^" : ancillary_bundle_env Det.cbor_det_match "^env'^".be_ast.e_sem_env =
  ancillary_bundle_env_extend a"^env^" _
[@@noextract_to "^krml^"; sem_attr; bundle_attr] noextract
let aa"^env'^" : ancillary_array_bundle_env Det.cbor_det_array_iterator_match "^env'^".be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aa"^env^" _
let _ : unit = _ by (FStar.Tactics.print (\"source'\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "^krml^"; base_attr] noextract
let "^source'^" = List.Tot.tl "^source^"
"

let rec compute_wf_typ
  (env: wf_ast_env)
  (name: string)
  (t: typ)
  (fuel: nat)
: FStar.Tactics.Tac (res: result (nat & wf_ast_env) { ~ (ROutOfFuel? res) })
= if None? (env.e_sem_env.se_bound name)
  then match mk_wf_typ' fuel env t with
  | RFailure s -> RFailure s
  | ROutOfFuel -> compute_wf_typ env name t (fuel + 1)
  | RSuccess wt -> RSuccess (fuel, wf_ast_env_extend_typ_with_weak env name t wt)
  else RFailure (name ^ " is already defined")

let produce_typ_defs
  (index: nat)
  (wenv: wf_ast_env)
  (name: string)
  (t: typ)
: FStar.Tactics.Tac (res: result (string & wf_ast_env) { ~ (ROutOfFuel? res) })
= match compute_wf_typ wenv name t 0 with
  | RFailure s -> RFailure s
  | RSuccess (fuel, wenv') ->
  let i = string_of_int index in
  let j = string_of_int (index + 1) in
  let validator = mk_validator_name name in
  let impltype = mk_impltype_name name in
  let parsertype = mk_parsertype_name name in
  let parser = mk_parser_name name in
  let wf = "wf" ^ j in
  let env = "env" ^ i in
  let env' = "env" ^ j in
  let ask = "ask" ^ j in
  let source = "sorted_source" ^ i in
  let source' = "sorted_source" ^ j in
  let bundle = "b" ^ j in
  let fuel = string_of_int fuel in
  let msg =
"
let _ : unit = _ by (FStar.Tactics.print (\"owf'\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"] noextract
let o"^wf^"' = compute_wf_typ' "^env^".be_ast (T.pull_name "^source^") (_ by (T.trefl_or_norm ())) (T.pull_type "^source^") "^fuel^"
let _ : unit = _ by (FStar.Tactics.print (\"owf\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "^krml^"] noextract
let o"^wf^" = o"^wf^"'
let o"^wf^"_eq : squash (o"^wf^" == o"^wf^"') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print (\"wf'\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"] noextract
let "^wf^"' = extract_computed_wf_typ' "^env^".be_ast (T.pull_name "^source^") (T.pull_type "^source^") "^fuel^" o"^wf^" (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print (\"wf\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "^krml^"; base_attr] noextract
let "^wf^" = "^wf^"'
let _ : squash ("^wf^" == "^wf^"') = _ by (T.trefl_or_norm ())
let _ : unit = _ by (FStar.Tactics.print (\"validator\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let "^validator^" = Impl.validate_typ Det.cbor_det_impl "^env^".be_v true _ "^wf^"
let _ : unit = _ by (FStar.Tactics.print (\"bundle\"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "^krml^"; bundle_attr; bundle_get_impl_type_attr]
let "^bundle^" = impl_bundle_wf_type' Det.cbor_det_impl "^env^" av"^env^" a"^env^" aa"^env^" "^wf^" (_ by (T.trefl_or_norm ()))
let _ : unit = _ by (FStar.Tactics.print (\"parser\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let "^parser^" = "^bundle^".b_parser
let _ : unit = _ by (FStar.Tactics.print (\"bundle'\"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "^krml^"; bundle_attr; bundle_get_impl_type_attr]
let "^bundle^"' = { "^bundle^" with b_parser = "^parser^" }
let _ : unit = _ by (FStar.Tactics.print (\"env'\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"; sem_attr; bundle_attr] noextract
let "^env'^" =
  bundle_env_extend_typ_with_weak "^env^" (T.pull_name "^source^") (T.pull_type "^source^") "^wf^" "^validator^" "^bundle^"'
" ^ extend_ancillaries env env' source source'
in
  RSuccess (msg, wenv')

let produce_group_defs
  (wenv: wf_ast_env)
  (name: string)
  (g: group)
  (index: nat)
: Tot (res: result (string & wf_ast_env) { ~ (ROutOfFuel? res) })
= if Some? (wenv.e_sem_env.se_bound name)
  then RFailure (name ^ " already defined")
  else if not (group_bounded wenv.e_sem_env.se_bound g)
  then RFailure (name ^ " : group not bounded. We do not support recursive CDDL groups yet")
  else
  let wenv' = wf_ast_env_extend_group wenv name g () () in
  let i = string_of_int index in
  let j = string_of_int (index + 1) in
  let env = "env" ^ i in
  let env' = "env" ^ j in
  let source = "sorted_source" ^ i in
  let source' = "sorted_source" ^ j in
  let msg =
(
"
let _ : unit = _ by (FStar.Tactics.print (\"env'\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"; sem_attr; bundle_attr] noextract
let "^env'^" =
  bundle_env_extend_group "^env^" (T.pull_name "^source^") (T.pull_group "^source^") (_ by (T.trefl_or_norm ())) (_ by (T.trefl_or_norm ()))
" ^ extend_ancillaries env env' source source'
)
  in
  RSuccess (msg, wenv')

let rec produce_defs'
  (index: nat)
  (accu: string)
  (env: wf_ast_env)
  (l: list (string & decl))
: FStar.Tactics.Tac (res: result (string & wf_ast_env) { ~ (ROutOfFuel? res) })
= match l with
  | [] -> RSuccess (accu, env)
  | (name, def) :: q ->
    let accu = accu ^
"
let _ : unit = _ by (FStar.Tactics.print (\"" ^ string_of_int (List.Tot.length l) ^ " defs remaining. Producing definitions for "^name^"\"); FStar.Tactics.exact (`()))
"
    in
    begin match def with
    | DType t ->
      begin match produce_typ_defs index env name t with
      | RSuccess (msg, env') ->
        produce_defs' (index + 1) (accu ^ msg) env' q
      | RFailure s -> RFailure s
      end
    | DGroup g ->
      begin match produce_group_defs env name g index with
      | RFailure s -> RFailure s
      | RSuccess (msg, env') ->
        produce_defs' (index + 1) (accu ^ msg) env' q
      end
    end

let produce_defs
  (l: list (string & decl))
: FStar.Tactics.Tac unit
= let accu = "
*)
" in
  match produce_defs' 0 accu empty_wf_ast_env l with
  | RFailure s -> FStar.Tactics.fail s
  | RSuccess (msg, _) -> let msg = msg ^ "
(*
"
    in
    FStar.Tactics.print msg;
    FStar.Tactics.exact (`())
