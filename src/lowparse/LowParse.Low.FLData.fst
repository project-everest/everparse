module LowParse.Low.FLData
include LowParse.Low.Combinators
include LowParse.Spec.FLData

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module Cast = FStar.Int.Cast
module U64 = FStar.UInt64

let valid_fldata_gen
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    U32.v pos + sz < 4294967296 /\
    valid_exact p h input pos (pos `U32.add` U32.uint_to_t sz)
  ))
  (ensures (
    U32.v pos + sz < 4294967296 /\ (
    let pos' = pos `U32.add` U32.uint_to_t sz in
    valid_content_pos (parse_fldata p sz) h input pos (contents_exact p h input pos pos') pos'
  )))
= valid_facts (parse_fldata p sz) h input pos;
  let pos' = pos `U32.add` U32.uint_to_t sz in
  let input' = { base = input.base; len = pos'; } in
  valid_facts p h input' pos;
  valid_exact_equiv p h input pos pos';
  contents_exact_eq p h input pos pos'

let valid_fldata_gen_elim
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    valid (parse_fldata p sz) h input pos
  ))
  (ensures (
    U32.v pos + sz < 4294967296 /\ (
    let pos' = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos (pos `U32.add` U32.uint_to_t sz) /\
    valid_content_pos (parse_fldata p sz) h input pos (contents_exact p h input pos pos') pos'
  )))
= valid_facts (parse_fldata p sz) h input pos;
  let pos' = pos `U32.add` U32.uint_to_t sz in
  let input' = { base = input.base; len = pos'; } in
  valid_facts p h input' pos;
  valid_exact_equiv p h input pos pos';
  contents_exact_eq p h input pos pos'

inline_for_extraction
let validate_fldata_gen
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator (parse_fldata p sz))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_fldata p sz) h input (uint64_to_uint32 pos) in
  if (Cast.uint32_to_uint64 input.len `U64.sub` pos) `U64.lt` Cast.uint32_to_uint64 sz32
  then validator_error_not_enough_data
  else
    [@inline_let] let input' = { base = input.base; len = uint64_to_uint32 pos `U32.add` sz32; } in
    [@inline_let] let _ = valid_facts p h input' (uint64_to_uint32 pos) in
    let pos' = v input' pos in
    if is_error pos'
    then
      if pos' = validator_error_not_enough_data
      then validator_error_generic (* the size was fixed ahead of time, so if the parser runs out of data, then that size was wrong in the first place. *) 
      else pos' // error propagation
    else
    if pos' `U64.sub` pos <> Cast.uint32_to_uint64 sz32
    then validator_error_generic
    else pos'

inline_for_extraction
let validate_fldata_consumes_all
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
  (sq: squash (k.parser_kind_subkind == Some ParserConsumesAll))
: Tot (validator (parse_fldata p sz))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ =
    valid_facts (parse_fldata p sz) h input (uint64_to_uint32 pos);
    parse_fldata_consumes_all_correct p sz (bytes_of_slice_from h input (uint64_to_uint32 pos))
  in
  if (Cast.uint32_to_uint64 input.len `U64.sub` pos) `U64.lt` Cast.uint32_to_uint64 sz32
  then validator_error_not_enough_data
  else
    [@inline_let] let input' = { base = input.base; len = uint64_to_uint32 pos `U32.add` sz32; } in
    [@inline_let] let _ = valid_facts p h input' (uint64_to_uint32 pos) in
    let pos' = v input' pos in
    if is_error pos'
    then
      if pos' = validator_error_not_enough_data
      then validator_error_generic (* the size was fixed ahead of time, so if the parser runs out of data, then that size was wrong in the first place. *) 
      else pos' // error propagation
    else pos'

inline_for_extraction
let validate_fldata
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator (parse_fldata p sz))
= if k.parser_kind_subkind = Some ParserConsumesAll
  then validate_fldata_consumes_all v sz sz32 ()
  else validate_fldata_gen v sz sz32

let valid_fldata_strong_gen
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    U32.v pos + sz < 4294967296 /\
    valid_exact p h input pos (pos `U32.add` U32.uint_to_t sz)
  ))
  (ensures (
    U32.v pos + sz < 4294967296 /\
    valid_exact p h input pos (pos `U32.add` U32.uint_to_t sz) /\ (
    let pos' = pos `U32.add` U32.uint_to_t sz in
    let x = contents_exact p h input pos pos' in
    Seq.length (serialize s x) == sz /\
    valid_content_pos (parse_fldata_strong s sz) h input pos x pos'
  )))
= valid_facts (parse_fldata_strong s sz) h input pos;
  let pos' = pos `U32.add` U32.uint_to_t sz in
  let input' = { base = input.base; len = pos'; } in
  valid_facts p h input' pos;
  valid_exact_equiv p h input pos pos';
  contents_exact_eq p h input pos pos'

let valid_fldata_strong_gen_elim
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  #rrel #rel
  (input: slice rrel rel)
  (pos: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    valid (parse_fldata_strong s sz) h input pos
  ))
  (ensures (
    U32.v pos + sz < 4294967296 /\ (
    let pos' = pos `U32.add` U32.uint_to_t sz in
    valid_exact p h input pos (pos `U32.add` U32.uint_to_t sz) /\ (
    let x = contents_exact p h input pos pos' in
    Seq.length (serialize s x) == sz /\
    valid_content_pos (parse_fldata_strong s sz) h input pos x pos'
  ))))
= valid_facts (parse_fldata_strong s sz) h input pos;
  let pos' = pos `U32.add` U32.uint_to_t sz in
  let input' = { base = input.base; len = pos'; } in
  valid_facts p h input' pos;
  valid_exact_equiv p h input pos pos';
  contents_exact_eq p h input pos pos'

inline_for_extraction
let validate_fldata_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator (parse_fldata_strong s sz))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_fldata p sz) h input (uint64_to_uint32 pos) in
  [@inline_let] let _ = valid_facts (parse_fldata_strong s sz) h input (uint64_to_uint32 pos) in
  validate_fldata v sz sz32 input pos

inline_for_extraction
let jump_fldata
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (jumper (parse_fldata p sz))
= jump_constant_size (parse_fldata p sz) sz32 ()

inline_for_extraction
let jump_fldata_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (jumper (parse_fldata_strong s sz))
= jump_constant_size (parse_fldata_strong s sz) sz32 ()

let gaccessor_fldata'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong } )
  (sz: nat)
: Tot (gaccessor' (parse_fldata p sz) p (clens_id _))
= fun (input: bytes) -> (
    let _ = match parse (parse_fldata p sz) input with
    | None -> ()
    | Some (_, consumed) ->
      if consumed = sz
      then parse_strong_prefix p (Seq.slice input 0 sz) input
      else ()
    in
    0
  )

let gaccessor_fldata
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong } )
  (sz: nat)
: Tot (gaccessor (parse_fldata p sz) p (clens_id _))
= gaccessor_prop_equiv (parse_fldata p sz) p (clens_id _) (gaccessor_fldata' p sz);
  gaccessor_fldata' p sz

inline_for_extraction
let accessor_fldata
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong } )
  (sz: nat)
: Tot (accessor (gaccessor_fldata p sz))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_fldata p sz) input pos in
  pos

let clens_fldata_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
: Tot (clens (parse_fldata_strong_t s sz) t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (x: parse_fldata_strong_t s sz) -> (x <: t));
}

inline_for_extraction
let gaccessor_fldata_strong'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (sz: nat)
: Tot (gaccessor' (parse_fldata_strong s sz) p (clens_fldata_strong s sz))
= fun (input: bytes) -> 
    let _ = match parse (parse_fldata_strong s sz) input with
    | None -> ()
    | Some (_, consumed) ->
      if consumed = sz
      then parse_strong_prefix p (Seq.slice input 0 sz) input
      else ()
    in
    0

inline_for_extraction
let gaccessor_fldata_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (sz: nat)
: Tot (gaccessor (parse_fldata_strong s sz) p (clens_fldata_strong s sz))
= gaccessor_prop_equiv (parse_fldata_strong s sz) p (clens_fldata_strong s sz) (gaccessor_fldata_strong' s sz);
  gaccessor_fldata_strong' s sz

inline_for_extraction
let accessor_fldata_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (sz: nat)
: Tot (accessor (gaccessor_fldata_strong s sz))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_fldata_strong s sz) input pos in
  pos
