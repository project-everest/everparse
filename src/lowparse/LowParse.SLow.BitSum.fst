module LowParse.SLow.BitSum
include LowParse.SLow.Enum
include LowParse.BitFields
include LowParse.Spec.BitSum

module U32 = FStar.UInt32
module B32 = FStar.Bytes


(* WARNING: these functions currently does not extract to C *)

inline_for_extraction
let parse32_bitsum
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (p32: parser32 p)
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (f32: (x: bitsum'_key_type b) -> Tot (parser32 (dsnd (f x))))
: Tot (parser32 (parse_bitsum b tag_of_data type_of_tag synth_case p f))
= fun x ->
  parse_bitsum_eq' b tag_of_data type_of_tag synth_case p f (B32.reveal x);
  match p32 x with
  | None -> None
  | Some (tg', consumed1) ->
    if filter_bitsum' b tg'
    then
      let tg = synth_bitsum' b tg' in
      let x' = B32.slice x consumed1 (B32.len x) in
      begin match f32 (bitsum'_key_of_t b tg) x' with
      | None -> None
      | Some (y, consumed2) ->
        Some ((synth_case.f tg y <: data), consumed1 `U32.add` consumed2)
      end
    else
      None

let serialize32_bitsum_cond
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (k: parser_kind)
  (type_of_tag: (bitsum'_key_type b -> Tot Type))
  (f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
: Tot bool
= match k.parser_kind_high, (weaken_parse_bitsum_cases_kind b type_of_tag f).parser_kind_high with
  | Some max1, Some max2 -> max1 + max2 < 4294967296
  | _ -> false

inline_for_extraction
let serialize32_bitsum
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (#s: serializer p)
  (s32: serializer32 s { kt.parser_kind_subkind == Some ParserStrong } )
  (#f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (g: (x: bitsum'_key_type b) -> Tot (serializer (dsnd (f x))))
  (g32: (x: bitsum'_key_type b) -> Tot (serializer32 (g x)))
  (sq: squash (
    serialize32_bitsum_cond b kt type_of_tag f
  ))
: Tot (serializer32 (serialize_bitsum b tag_of_data type_of_tag synth_case s #f g))
=
  fun x ->
    serialize_bitsum_eq b tag_of_data type_of_tag synth_case s g x;
    let tg = tag_of_data x in
    let k = bitsum'_key_of_t b tg in
    let payload = synth_case.g tg x in
    let s_tg = s32 (synth_bitsum'_recip b tg) in
    let s_pl = g32 k payload in
    s_tg `B32.append` s_pl
