module LowParse.Low.Option
include LowParse.Spec.Option
include LowParse.Low.Base

module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

inline_for_extraction
let validate_option (#k: parser_kind) (#t: Type) (#p: parser k t) (v: validator p) : Tot (validator (parse_option p)) =
  fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_option p) h input pos in
  [@inline_let] let _ = valid_facts p h input pos in
  let r = v input pos in
  if validator_max_length `U64.lt` r
  then Cast.uint32_to_uint64 pos
  else r
