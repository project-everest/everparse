module CDDL.Pulse.AST.Gen
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

let extend_ancillaries' env' ancillary_env source source' = "
let _ : unit = _ by (FStar.Tactics.print (\"ancillary envs\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"; sem_attr; bundle_attr] noextract
let av"^env'^"_0 : Parse.ancillary_validate_env Det.cbor_det_match "^env'^".be_ast.e_sem_env =
  Parse.ancillary_validate_env_extend av"^ancillary_env^" _
[@@noextract_to "^krml^"; sem_attr; bundle_attr] noextract
let a"^env'^"_0 : ancillary_bundle_env Det.cbor_det_match "^env'^".be_ast.e_sem_env =
  ancillary_bundle_env_extend a"^ancillary_env^" _
[@@noextract_to "^krml^"; sem_attr; bundle_attr] noextract
let aa"^env'^"_0 : ancillary_array_bundle_env Det.cbor_det_array_iterator_match "^env'^".be_ast.e_sem_env =
  ancillary_array_bundle_env_extend aa"^ancillary_env^" _
let _ : unit = _ by (FStar.Tactics.print (\"source'\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ()); noextract_to "^krml^"; base_attr] noextract
let "^source'^" = List.Tot.tl "^source

let extend_ancillaries_for_typ env env' ancillary_index source source' =
  extend_ancillaries' env' (env ^ "_" ^ string_of_int ancillary_index) source source'

let extend_ancillaries_for_array_group env env' source source' =
  extend_ancillaries' env' (env ^ "_0") source source'

let call_ask_for_base wf ancillaries =
  "Parse.ask_zero_copy_wf_type "^ancillaries^" "^wf

let call_ask_for_aux candidate ancillaries =
  "Parse.ask_zero_copy_ask_for_option "^ancillaries^" "^candidate

let compute_ancillary_env env ancillary_index =
  let env_ancillary_index = env ^ "_" ^ string_of_int ancillary_index in
  "av"^env_ancillary_index^" a"^env_ancillary_index^" aa"^env_ancillary_index

module P = CDDL.Pulse.AST.Parse

noeq
type ancillaries_t (se: sem_env) = {
  validators: P.ancillary_validate_env_bool se.se_bound;
  parsers: P.ancillary_parse_env_bool se;
  array_parsers: P.ancillary_parse_array_group_env_bool se;
}

noeq
type ancillaries_aux_t (se: sem_env) = {
  anc: ancillaries_t se;
  next_candidate_index: pos;
  env_index: nat;
  output: string;
}

let compute_wf_typ_ret
  (env: sem_env)
= result (nat & ((ancillaries_t env -> option (P.ask_for env)) & wf_ast_env))

let compute_wf_typ_post
  (env: wf_ast_env)
  (res: compute_wf_typ_ret env.e_sem_env)
: Tot prop
= match res with
  | ROutOfFuel -> False
  | RFailure _ -> True
  | RSuccess (_, (_, env')) -> ast_env_included env env'

let rec compute_wf_typ
  (env: wf_ast_env)
  (name: string)
  (t: typ)
  (fuel: nat)
: FStar.Tactics.Tac (res: compute_wf_typ_ret env.e_sem_env { compute_wf_typ_post env res })
= if None? (env.e_sem_env.se_bound name)
  then match mk_wf_typ' fuel env t with
  | RFailure s -> RFailure s
  | ROutOfFuel -> compute_wf_typ env name t (fuel + 1)
  | RSuccess wt ->
    let f (anc: ancillaries_t env.e_sem_env) : Tot (option (P.ask_for env.e_sem_env)) =
      P.ask_zero_copy_wf_type anc.validators anc.parsers anc.array_parsers wt
    in
    RSuccess (fuel, (f, wf_ast_env_extend_typ_with_weak env name t wt))
  else RFailure (name ^ " is already defined")

let produce_validator env wf validator = "
let _ : unit = _ by (FStar.Tactics.print (\"validator\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let "^validator^" = Impl.validate_typ Det.cbor_det_impl "^env^".be_v true _ "^wf

let produce_parser env env_anc' wf validator parser bundle =
produce_validator env wf validator^"
let _ : unit = _ by (FStar.Tactics.print (\"bundle\"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "^krml^"; bundle_attr; bundle_get_impl_type_attr]
let "^bundle^"' = impl_bundle_wf_type' Det.cbor_det_impl "^env^" av"^env_anc'^" a"^env_anc'^" aa"^env_anc'^" "^wf^" (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print (\"parser\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let "^parser^" = "^bundle^"'.b_parser
let _ : unit = _ by (FStar.Tactics.print (\"bundle'\"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "^krml^"; bundle_attr; bundle_get_impl_type_attr]
let "^bundle^" = { "^bundle^"' with b_parser = "^parser^" }"

let produce_ask_for_validator env wf validator =
"let _ : unit = _ by (FStar.Tactics.print (\"validator\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let "^validator^" = Parse.validate_ask_for_type Det.cbor_det_impl "^env^".be_v "^wf^" (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))"

let produce_ask_for_parser env env_anc' wf validator parser bundle =
produce_ask_for_validator env wf validator^"
let _ : unit = _ by (FStar.Tactics.print (\"bundle\"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "^krml^"; bundle_attr; bundle_get_impl_type_attr]
let "^bundle^"' = impl_bundle_wf_ask_for_guarded_type Det.cbor_det_impl "^env^" av"^env_anc'^" a"^env_anc'^" aa"^env_anc'^" "^wf^" (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print (\"parser\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let "^parser^" = "^bundle^"'.b_parser
let _ : unit = _ by (FStar.Tactics.print (\"bundle'\"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "^krml^"; bundle_attr; bundle_get_impl_type_attr]
let "^bundle^" = { "^bundle^"' with b_parser = "^parser^" }"

let produce_ask_for_array_validator env wf validator = "
let _ : unit = _ by (FStar.Tactics.print (\"validator\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.steps); FStar.Tactics.trefl ())]
let "^validator^" = Parse.validate_ask_for_array_group Det.cbor_det_impl "^env^".be_v "^wf^" (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))"

let produce_ask_for_array_parser env env_anc' wf validator parser bundle =
produce_ask_for_array_validator env wf validator^"
let _ : unit = _ by (FStar.Tactics.print (\"bundle\"); FStar.Tactics.exact (`()))
noextract [@@noextract_to "^krml^"; bundle_attr; bundle_get_impl_type_attr]
let "^bundle^"' = impl_bundle_wf_ask_for_array_group Det.cbor_det_impl "^env^" av"^env_anc'^" a"^env_anc'^" aa"^env_anc'^" "^wf^" (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))
let _ : unit = _ by (FStar.Tactics.print (\"parser\"); FStar.Tactics.exact (`()))
[@@FStar.Tactics.postprocess_for_extraction_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ()); FStar.Tactics.postprocess_type]
let "^parser^" = "^bundle^"'.ab_parser
let _ : unit = _ by (FStar.Tactics.print (\"bundle'\"); FStar.Tactics.exact (`()))
inline_for_extraction noextract [@@noextract_to "^krml^"; bundle_attr; bundle_get_impl_type_attr]
let "^bundle^" = { "^bundle^"' with ab_parser = "^parser^" }"

let rec compute_ancillaries_aux
  (#se: sem_env)
  (anc: ancillaries_aux_t se)
  (ask: option (P.ask_for se))
  (env: string)
  (wf: string)
  (validator: string)
  (bundle: string)
  (parser: string)
: FStar.Tactics.Tac (ancillaries_aux_t se)
=
  let anc_env = env ^ "_" ^ string_of_int anc.env_index in
  match P.ask_zero_copy_ask_for_option anc.anc.validators anc.anc.parsers anc.anc.array_parsers ask with
  | None ->
    let env_index' = anc.env_index + 1 in
    let anc_env' = env ^ "_" ^ string_of_int env_index' in
    begin match ask with
    | None -> anc
    | Some (P.AskForType t _ false) ->
      let msg = produce_ask_for_validator env wf validator ^ "
let _ : unit = _ by (FStar.Tactics.print (\"ancillary env'\"); FStar.Tactics.exact (`()))
[@@bundle_attr; sem_attr; noextract_to "^krml^"] noextract
let av"^anc_env'^" = Parse.ancillary_validate_env_set_ask_for av"^anc_env^" "^wf^" (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) "^validator^"
[@@bundle_attr; noextract_to "^krml^"] noextract
let a"^anc_env'^" = a" ^ anc_env ^ "
[@@bundle_attr; noextract_to "^krml^"] noextract
let aa"^anc_env'^" = aa" ^ anc_env
      in
      { anc with
        anc = {
          anc.anc with
          validators = (fun v -> if v = t then true else anc.anc.validators v);
        };
        env_index = env_index';
        output = anc.output ^ msg;
      }
    | Some (P.AskForType t t_wf true) ->
      let msg = produce_ask_for_parser env anc_env wf validator parser bundle ^ "
let _ : unit = _ by (FStar.Tactics.print (\"ancillary env'\"); FStar.Tactics.exact (`()))
[@@bundle_attr; sem_attr; noextract_to "^krml^"] noextract
let av"^anc_env'^" = av"^anc_env^"
[@@bundle_attr; noextract_to "^krml^"] noextract
let a"^anc_env'^" = ancillary_bundle_env_set_ask_for a"^anc_env^" "^wf^" (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) "^validator^" "^bundle^"
[@@bundle_attr; noextract_to "^krml^"] noextract
let aa"^anc_env'^" = aa" ^ anc_env
      in
      { anc with
        anc = {
          anc.anc with
          parsers = (fun t' t_wf' -> if t = t' && t_wf = t_wf' then true else anc.anc.parsers t' t_wf');
        };
        env_index = env_index';
        output = anc.output ^ msg;
      }
    | Some (P.AskForArrayGroup t t_wf) ->
      let msg = produce_ask_for_array_parser env anc_env wf validator parser bundle ^ "
let _ : unit = _ by (FStar.Tactics.print (\"ancillary env'\"); FStar.Tactics.exact (`()))
[@@bundle_attr; sem_attr; noextract_to "^krml^"] noextract
let av"^anc_env'^" = av"^anc_env^"
[@@bundle_attr; noextract_to "^krml^"] noextract
let a"^anc_env'^" = a"^anc_env^"
[@@bundle_attr; noextract_to "^krml^"] noextract
let aa"^anc_env'^" = ancillary_array_bundle_env_set_ask_for aa"^anc_env^" "^wf^" (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ())) "^validator^" "^bundle
      in
      { anc with
        anc = {
          anc.anc with
          array_parsers = (fun t' t_wf' -> if t = t' && t_wf = t_wf' then true else anc.anc.array_parsers t' t_wf');
        };
        env_index = env_index';
        output = anc.output ^ msg;
      }
    end
  | ask' ->
    let msg wf' = "
[@@noextract_to "^krml^"; bundle_attr] noextract
let "^wf'^"' = Parse.ask_zero_copy_ask_for_option (Parse.ancillary_validate_env_is_some av"^anc_env^") (ancillary_bundle_env_is_some a"^anc_env^") (ancillary_array_bundle_env_is_some aa"^anc_env^") "^wf
    in
    let anc2 = init_compute_ancillaries_aux anc ask' env msg in
    compute_ancillaries_aux anc2 ask env wf validator bundle parser

and init_compute_ancillaries_aux
  (#se: sem_env)
  (anc: ancillaries_aux_t se)
  (ask': option (P.ask_for se))
  (env: string)
  (msg: (string -> string))
: FStar.Tactics.Tac (ancillaries_aux_t se)
=
    let candidate = string_of_int anc.next_candidate_index in
    let wf' = "aux_" ^ env ^ "_wf_" ^ candidate in
    let msg' = "
let _ : unit = _ by (FStar.Tactics.print (\"ancillary "^wf'^"'\"); FStar.Tactics.exact (`()))"^msg wf'^"
let _ : unit = _ by (FStar.Tactics.print (\"ancillary "^wf'^"\"); FStar.Tactics.exact (`()))
[@@base_attr; noextract_to "^krml^"; FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm (nbe :: T.bundle_steps); FStar.Tactics.trefl ())] noextract
let "^wf'^" = "^wf'^"'
let _ : unit = _ by (FStar.Tactics.print (\"ancillary "^wf'^"_eq\"); FStar.Tactics.exact (`()))
let _ : squash ("^wf'^" == "^wf'^"') = (_ by (FStar.Tactics.norm (nbe :: T.bundle_steps); T.trefl_or_trivial ()))"
    in
    let validator' = "aux_" ^ env ^ "_validate_" ^ candidate in
    let parser' = "aux_" ^ env ^ "_parse_" ^ candidate in
    let bundle' = "aux_" ^ env ^ "_bundle_" ^ candidate in
    let anc1 = {
      anc with
      next_candidate_index = anc.next_candidate_index + 1;
      output = anc.output ^ msg';
    }
    in
    compute_ancillaries_aux anc1 ask' env wf' validator' bundle' parser'

let rec compute_ancillaries
  (#se: sem_env)
  (init: ancillaries_t se -> option (P.ask_for se))
  (anc: ancillaries_aux_t se)
  (env: string)
  (wf: string)
: FStar.Tactics.Tac (anc': ancillaries_aux_t se {
    None? (init anc'.anc)
  })
= match init anc.anc with
  | None -> anc
  | ask ->
    let anc_env = env ^ "_" ^ string_of_int anc.env_index in
    let msg wf' = "
[@@noextract_to "^krml^"; bundle_attr] noextract
let "^wf'^"' = Parse.ask_zero_copy_wf_type (Parse.ancillary_validate_env_is_some av"^anc_env^") (ancillary_bundle_env_is_some a"^anc_env^") (ancillary_array_bundle_env_is_some aa"^anc_env^") "^wf
    in
    let anc2 = init_compute_ancillaries_aux anc ask env msg in
    compute_ancillaries init anc2 env wf

let extend_ancillaries_t
  (#se: sem_env)
  (anc: ancillaries_t se)
  (se': sem_env { sem_env_included se se' })
: Tot (ancillaries_t se')
= let ne = se.se_bound in
  {
    validators = (fun t -> if typ_bounded ne t then anc.validators t else false);
    parsers = (fun t t_wf -> if typ_bounded ne t && bounded_wf_typ ne _ t_wf then anc.parsers t t_wf else false);
    array_parsers = (fun t t_wf -> if group_bounded ne t && bounded_wf_array_group ne _ t_wf then anc.array_parsers t t_wf else false);
  }

let produce_typ_defs_t : Type0
= result (string & (wenv': wf_ast_env & ancillaries_t wenv'.e_sem_env))

let produce_typ_defs_post
  (wenv: wf_ast_env)
  (res: produce_typ_defs_t)
: Tot prop
= match res with
  | RFailure _ -> True
  | ROutOfFuel -> False
  | RSuccess (_, (| wenv', _ |)) -> ast_env_included wenv wenv'

let produce_typ_defs
  (index: nat)
  (wenv: wf_ast_env)
  (anc: ancillaries_t wenv.e_sem_env)
  (name: string)
  (t: typ)
: FStar.Tactics.Tac (res: produce_typ_defs_t { produce_typ_defs_post wenv res })
= match compute_wf_typ wenv name t 0 with
  | RFailure s -> RFailure s
  | RSuccess (fuel, (f, wenv')) ->
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
  let anc1 = compute_ancillaries f {
    anc = anc;
    env_index = 0;
    next_candidate_index = 1;
    output = "";
  }
    env wf
  in
  let env_anc' = env ^ "_" ^ string_of_int anc1.env_index in
  let anc' : ancillaries_t wenv'.e_sem_env = extend_ancillaries_t anc1.anc wenv'.e_sem_env in
  let msg = "
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
let _ : squash ("^wf^" == "^wf^"') = _ by (T.trefl_or_norm ())"^
anc1.output^produce_parser env env_anc' wf validator parser bundle ^"
let _ : unit = _ by (FStar.Tactics.print (\"env'\"); FStar.Tactics.exact (`()))
[@@noextract_to "^krml^"; sem_attr; bundle_attr] noextract
let "^env'^" =
  bundle_env_extend_typ_with_weak "^env^" (T.pull_name "^source^") (T.pull_type "^source^") "^wf^" "^validator^" "^bundle^
extend_ancillaries_for_typ env env' anc1.env_index source source'
in
  RSuccess (msg, (| wenv', anc' |))

let produce_group_defs
  (wenv: wf_ast_env)
  (anc: ancillaries_t wenv.e_sem_env)
  (name: string)
  (g: group)
  (index: nat)
: Tot (res: produce_typ_defs_t { produce_typ_defs_post wenv res })
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
  bundle_env_extend_group "^env^" (T.pull_name "^source^") (T.pull_group "^source^") (_ by (T.trefl_or_norm ())) (_ by (T.trefl_or_norm ()))" ^ extend_ancillaries_for_array_group env env' source source'
)
  in
  RSuccess (msg, (| wenv', extend_ancillaries_t anc _ |))

let rec produce_defs'
  (index: nat)
  (accu: string)
  (env: wf_ast_env)
  (anc: ancillaries_t env.e_sem_env)
  (l: list (string & decl))
: FStar.Tactics.Tac (res: result string { ~ (ROutOfFuel? res) })
= match l with
  | [] -> RSuccess accu
  | (name, def) :: q ->
    let accu = accu ^
"
let _ : unit = _ by (FStar.Tactics.print (\"" ^ string_of_int (List.Tot.length l) ^ " defs remaining. Producing definitions for "^name^"\"); FStar.Tactics.exact (`()))"
    in
    begin match def with
    | DType t ->
      begin match produce_typ_defs index env anc name t with
      | RSuccess (msg, (| env', anc' |)) ->
        produce_defs' (index + 1) (accu ^ msg) env' anc' q
      | RFailure s -> RFailure s
      end
    | DGroup g ->
      begin match produce_group_defs env anc name g index with
      | RFailure s -> RFailure s
      | RSuccess (msg, (| env', anc' |)) ->
        produce_defs' (index + 1) (accu ^ msg) env' anc' q
      end
    end

let empty_ancillaries : ancillaries_t empty_sem_env = {
  validators = (fun _ -> false);
  parsers = (fun _ _ -> false);
  array_parsers = (fun _ _ -> false);
}

let produce_defs
  (l: list (string & decl))
: FStar.Tactics.Tac unit
= let accu = "
*)
" in
  match produce_defs' 0 accu empty_wf_ast_env empty_ancillaries l with
  | RFailure s -> FStar.Tactics.fail s
  | RSuccess msg -> let msg = msg ^ "
(*
"
    in
    FStar.Tactics.print msg;
    FStar.Tactics.exact (`())
