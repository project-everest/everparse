module LowParseExample5.Aux

module LPC = LowParse.Spec.Combinators
module LPI = LowParse.Low.Int
module LP = LowParse.Low.Base

module U32 = FStar.UInt32
module U16 = FStar.UInt16
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

noeq
type inner = {
  left: U16.t;
  right: U16.t;
}

noeq
type t = {
  inner: inner;
  last: U32.t;
}

inline_for_extraction
noextract
let parse_inner_kind : LP.parser_kind = LP.strong_parser_kind 4 4 (Some LP.ParserKindMetadataTotal)

val parse_inner: LP.parser parse_inner_kind inner

val serialize_inner: LP.serializer parse_inner

inline_for_extraction
let slice = LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _))

val serialize_inner_intro
  (h: HS.mem)
  (b: slice)
  (lo: U32.t)
: Lemma
  (requires (
    LP.valid LPI.parse_u16 h b lo /\
    LP.valid LPI.parse_u16 h b (LP.get_valid_pos LPI.parse_u16 h b lo)
  ))
  (ensures (
    LP.valid_content_pos parse_inner h b lo
      ({
        left = LP.contents LPI.parse_u16 h b lo;
        right = LP.contents LPI.parse_u16 h b (LP.get_valid_pos LPI.parse_u16 h b lo);
      })
      (lo `U32.add` 4ul)
  ))

val parse_t_kind : (k: LP.parser_kind { k.LP.parser_kind_subkind == Some LP.ParserStrong /\ k.LP.parser_kind_high == Some 8 })

val parse_t : LP.parser parse_t_kind t

val serialize_t : LP.serializer parse_t

val serialize_t_intro
  (h: HS.mem)
  (b: slice)
  (lo: U32.t)
: Lemma
  (requires (
    LP.valid parse_inner h b lo /\
    LP.valid LPI.parse_u32 h b (LP.get_valid_pos parse_inner h b lo)
  ))
  (ensures (
    LP.valid_content_pos parse_t h b lo
      ({
        inner = LP.contents parse_inner h b lo;
        last = LP.contents LPI.parse_u32 h b (LP.get_valid_pos parse_inner h b lo);
      })
      (lo `U32.add` 8ul)
  ))
