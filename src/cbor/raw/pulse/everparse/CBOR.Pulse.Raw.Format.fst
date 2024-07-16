module CBOR.Pulse.Raw.Format
open CBOR.Spec.Raw.Format
open LowParse.Pulse.Util
open LowParse.Pulse.Combinators
open LowParse.Pulse.Int
open LowParse.Pulse.BitSum

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_initial_byte_t' : reader serialize_initial_byte_t =
  read_synth'
    (read_bitsum'
      destr_initial_byte
      (reader_of_leaf_reader (read_u8' ()))
    )
    synth_initial_byte
    synth_initial_byte_recip

(* FIXME: WHY WHY WHY does this not extract?
let read_initial_byte_t : leaf_reader serialize_initial_byte_t =
  leaf_reader_of_reader read_initial_byte_t'
*)

```pulse
fn read_initial_byte_t (_: unit) : leaf_reader #initial_byte_t #(parse_filter_kind parse_u8_kind) #parse_initial_byte_t serialize_initial_byte_t =
  (input: Pulse.Lib.Slice.slice byte)
  (#pm: perm)
  (#v: _)
{
  leaf_reader_of_reader read_initial_byte_t' input #pm #v
}
```

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_initial_byte : validator parse_initial_byte =
    validate_filter'
      (validate_synth
        (validate_ext
          (validate_total_constant_size
            (LowParse.Spec.BitSum.tot_parse_bitsum'_no_bitsum
              initial_byte_desc
              tot_parse_u8
            )
            1sz
          )
          parse_initial_byte'
        )
        synth_initial_byte
      )
      (read_initial_byte_t ())
      initial_byte_wf

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_initial_byte : jumper parse_initial_byte =
  jump_constant_size parse_initial_byte 1sz

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_initial_byte : reader serialize_initial_byte =
  read_filter
    (reader_of_leaf_reader (read_initial_byte_t ()))
    initial_byte_wf

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_8_simple_value
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
  (sq2: squash ((b.major_type = cbor_major_type_simple_value) == true))
: Tot (reader (serialize_long_argument b))
=
          reader_ext
            (read_synth'
              (read_filter
                (reader_of_leaf_reader (read_u8' ()))
                simple_value_long_argument_wf
              )
              (LongArgumentSimpleValue #b ())
              (LongArgumentSimpleValue?.v)
            )
            (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_8_not_simple_value
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
  (sq2: squash ((b.major_type = cbor_major_type_simple_value) == false))
: Tot (reader (serialize_long_argument b))
=
              reader_ext
                (read_synth'
                  (reader_of_leaf_reader (read_u8' ()))
                  (LongArgumentU8 #b ())
                  (LongArgumentU8?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_8
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
: Tot (reader (serialize_long_argument b))
= ifthenelse_reader
    (serialize_long_argument b)
    (b.major_type = cbor_major_type_simple_value)
    (read_long_argument_8_simple_value b sq1)
    (read_long_argument_8_not_simple_value b sq1)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_16
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_16_bits) == true))
: Tot (reader (serialize_long_argument b))
=
              reader_ext
                (read_synth'
                  (reader_of_leaf_reader (read_u16' ()))
                  (LongArgumentU16 #b ())
                  (LongArgumentU16?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_32
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_32_bits) == true))
: Tot (reader (serialize_long_argument b))
=
              reader_ext
                (read_synth'
                  (reader_of_leaf_reader (read_u32' ()))
                  (LongArgumentU32 #b ())
                  (LongArgumentU32?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_64
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_64_bits) == true))
: Tot (reader (serialize_long_argument b))
=
              reader_ext
                (read_synth'
                  (reader_of_leaf_reader (read_u64' ()))
                  (LongArgumentU64 #b ())
                  (LongArgumentU64?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_other
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
  (sq64: squash ((b.additional_info = additional_info_long_argument_64_bits) == false))
: Tot (reader (serialize_long_argument b))
=
              reader_ext
                (read_synth'
                  (reader_of_leaf_reader leaf_read_empty)
                  (LongArgumentOther #b b.additional_info ())
                  LongArgumentOther?.v
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_not_8_16_32
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
: Tot (reader (serialize_long_argument b))
= ifthenelse_reader
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_64_bits)
    (read_long_argument_64 b)
    (read_long_argument_other b sq8 sq16 sq32)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_not_8_16
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
: Tot (reader (serialize_long_argument b))
= ifthenelse_reader
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_32_bits)
    (read_long_argument_32 b)
    (read_long_argument_not_8_16_32 b sq8 sq16)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument_not_8
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
: Tot (reader (serialize_long_argument b))
= ifthenelse_reader
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_16_bits)
    (read_long_argument_16 b)
    (read_long_argument_not_8_16 b sq8)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_long_argument
  (b: initial_byte)
: Tot (reader (serialize_long_argument b))
= ifthenelse_reader
      (serialize_long_argument b)
      (b.additional_info = additional_info_long_argument_8_bits)
      (read_long_argument_8 b)
      (read_long_argument_not_8 b)

(* // FIXME: ideally I want lambdas, as in the following:
inline_for_extraction
noextract
let read_long_argument
  (b: initial_byte)
: Tot (reader (serialize_long_argument b))
=   ifthenelse_reader
      (serialize_long_argument b)
      (b.additional_info = additional_info_long_argument_8_bits)
      (fun _ -> ifthenelse_reader
        (serialize_long_argument b)
        (b.major_type = cbor_major_type_simple_value)
        (fun _ ->
          reader_ext
            (read_synth'
              (read_filter
                (reader_of_leaf_reader (read_u8' ()))
                simple_value_long_argument_wf
              )
              (LongArgumentSimpleValue #b ())
              (LongArgumentSimpleValue?.v)
            )
            (serialize_long_argument b)
        )
        (fun _ ->
          reader_ext
            (read_synth'
              (reader_of_leaf_reader (read_u8' ()))
              (LongArgumentU8 #b ())
              (LongArgumentU8?.v)
            )
            (serialize_long_argument b)
        )
      )
      (fun _ -> ifthenelse_reader
        (serialize_long_argument b)
        (b.additional_info = additional_info_long_argument_16_bits)
        (fun _ ->
          reader_ext
            (read_synth'
              (reader_of_leaf_reader (read_u16' ()))
              (LongArgumentU16 #b ())
              (LongArgumentU16?.v)
            )
            (serialize_long_argument b)
        )
        (fun _ -> ifthenelse_reader
          (serialize_long_argument b)
          (b.additional_info = additional_info_long_argument_32_bits)
          (fun _ ->
            reader_ext
              (read_synth'
                (reader_of_leaf_reader (read_u32' ()))
                (LongArgumentU32 #b ())
                (LongArgumentU32?.v)
              )
              (serialize_long_argument b)
          )
          (fun _ -> ifthenelse_reader
            (serialize_long_argument b)
            (b.additional_info = additional_info_long_argument_64_bits)
            (fun _ ->
              reader_ext
                (read_synth'
                  (reader_of_leaf_reader (read_u64' ()))
                  (LongArgumentU64 #b ())
                  (LongArgumentU64?.v)
                )
                (serialize_long_argument b)
            )
            (fun _ ->
              reader_ext
                (read_synth'
                  (reader_of_leaf_reader leaf_read_empty)
                  (LongArgumentOther #b b.additional_info ())
                  LongArgumentOther?.v
                )
                (serialize_long_argument b)
            )
          )
        )
      )
*)

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_header' : reader serialize_header =
  read_dtuple2
    jump_initial_byte
    read_initial_byte
    read_long_argument

```pulse
fn read_header (_: unit) : leaf_reader #header #parse_header_kind #parse_header serialize_header =
  (input: Pulse.Lib.Slice.slice byte)
  (#pm: perm)
  (#v: _)
{
  leaf_reader_of_reader read_header' input #pm #v
}
```

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_8_simple_value
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
  (sq2: squash ((b.major_type = cbor_major_type_simple_value) == true))
: Tot (validator (parse_long_argument b))
=
          validate_ext
            (validate_synth
              (validate_filter'
                validate_u8
                (read_u8' ())
                simple_value_long_argument_wf
              )
              (LongArgumentSimpleValue #b ())
            )
            (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_8_not_simple_value
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
  (sq2: squash ((b.major_type = cbor_major_type_simple_value) == false))
: Tot (validator (parse_long_argument b))
=
              validate_ext
                (validate_synth
                  validate_u8
                  (LongArgumentU8 #b ())
                )
                (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_8
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
: Tot (validator (parse_long_argument b))
= ifthenelse_validator
    (parse_long_argument b)
    (b.major_type = cbor_major_type_simple_value)
    (validate_long_argument_8_simple_value b sq1)
    (validate_long_argument_8_not_simple_value b sq1)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_16
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_16_bits) == true))
: Tot (validator (parse_long_argument b))
=
              validate_ext
                (validate_synth
                  validate_u16
                  (LongArgumentU16 #b ())
                )
                (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_32
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_32_bits) == true))
: Tot (validator (parse_long_argument b))
=
              validate_ext
                (validate_synth
                  validate_u32
                  (LongArgumentU32 #b ())
                )
                (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_64
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_64_bits) == true))
: Tot (validator (parse_long_argument b))
=
              validate_ext
                (validate_synth
                  validate_u64
                  (LongArgumentU64 #b ())
                )
                (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_other
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
  (sq64: squash ((b.additional_info = additional_info_long_argument_64_bits) == false))
: Tot (validator (parse_long_argument b))
=
              validate_ext
                (validate_synth
                  validate_empty
                  (LongArgumentOther #b b.additional_info ())
                )
                (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_not_8_16_32
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
: Tot (validator (parse_long_argument b))
= ifthenelse_validator
    (parse_long_argument b)
    (b.additional_info = additional_info_long_argument_64_bits)
    (validate_long_argument_64 b)
    (validate_long_argument_other b sq8 sq16 sq32)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_not_8_16
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
: Tot (validator (parse_long_argument b))
= ifthenelse_validator
    (parse_long_argument b)
    (b.additional_info = additional_info_long_argument_32_bits)
    (validate_long_argument_32 b)
    (validate_long_argument_not_8_16_32 b sq8 sq16)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument_not_8
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
: Tot (validator (parse_long_argument b))
= ifthenelse_validator
    (parse_long_argument b)
    (b.additional_info = additional_info_long_argument_16_bits)
    (validate_long_argument_16 b)
    (validate_long_argument_not_8_16 b sq8)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_long_argument
  (b: initial_byte)
: Tot (validator (parse_long_argument b))
= ifthenelse_validator
      (parse_long_argument b)
      (b.additional_info = additional_info_long_argument_8_bits)
      (validate_long_argument_8 b)
      (validate_long_argument_not_8 b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_long_argument_8
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
: Tot (jumper (parse_long_argument b))
=
        jump_ext
          (jump_constant_size (if b.major_type = cbor_major_type_simple_value then tot_parse_synth (tot_parse_filter tot_parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b ()) else tot_weaken (parse_filter_kind parse_u8_kind) (tot_parse_synth tot_parse_u8 (LongArgumentU8 #b ()))) 1sz)
          (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_long_argument_16
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_16_bits) == true))
: Tot (jumper (parse_long_argument b))
=
              jump_ext
                (jump_synth
                  jump_u16
                  (LongArgumentU16 #b ())
                )
                (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_long_argument_32
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_32_bits) == true))
: Tot (jumper (parse_long_argument b))
=
              jump_ext
                (jump_synth
                  jump_u32
                  (LongArgumentU32 #b ())
                )
                (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_long_argument_64
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_64_bits) == true))
: Tot (jumper (parse_long_argument b))
=
              jump_ext
                (jump_synth
                  jump_u64
                  (LongArgumentU64 #b ())
                )
                (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_long_argument_other
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
  (sq64: squash ((b.additional_info = additional_info_long_argument_64_bits) == false))
: Tot (jumper (parse_long_argument b))
=
              jump_ext
                (jump_synth
                  jump_empty
                  (LongArgumentOther #b b.additional_info ())
                )
                (parse_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_long_argument_not_8_16_32
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
: Tot (jumper (parse_long_argument b))
= ifthenelse_jumper
    (parse_long_argument b)
    (b.additional_info = additional_info_long_argument_64_bits)
    (jump_long_argument_64 b)
    (jump_long_argument_other b sq8 sq16 sq32)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_long_argument_not_8_16
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
: Tot (jumper (parse_long_argument b))
= ifthenelse_jumper
    (parse_long_argument b)
    (b.additional_info = additional_info_long_argument_32_bits)
    (jump_long_argument_32 b)
    (jump_long_argument_not_8_16_32 b sq8 sq16)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_long_argument_not_8
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
: Tot (jumper (parse_long_argument b))
= ifthenelse_jumper
    (parse_long_argument b)
    (b.additional_info = additional_info_long_argument_16_bits)
    (jump_long_argument_16 b)
    (jump_long_argument_not_8_16 b sq8)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_long_argument
  (b: initial_byte)
: Tot (jumper (parse_long_argument b))
= ifthenelse_jumper
      (parse_long_argument b)
      (b.additional_info = additional_info_long_argument_8_bits)
      (jump_long_argument_8 b)
      (jump_long_argument_not_8 b)

```pulse
fn validate_header (_: unit) : validator #header #parse_header_kind parse_header =
  (input: _)
  (poffset: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  validate_dtuple2 validate_initial_byte (leaf_reader_of_reader read_initial_byte) validate_long_argument
    input poffset #offset #pm #v
}
```

```pulse
fn jump_header (_: unit) : jumper #header #parse_header_kind parse_header =
  (input: _)
  (offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  jump_dtuple2 jump_initial_byte (leaf_reader_of_reader read_initial_byte) jump_long_argument
    input offset #pm #v
}
```

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_header_initial_byte
  (h: header)
: Tot initial_byte
= match h with (| b, _ |) -> b

inline_for_extraction
noextract [@@noextract_to "krml"]
let get_header_long_argument
  (h: header)
: Tot (long_argument (get_header_initial_byte h))
= match h with (| _, l |) -> l

module U64 = FStar.UInt64

let get_header_argument_as_uint64
  (h: header { ~ (long_argument_simple_value_prop (get_header_initial_byte h)) })
: Tot U64.t
= match h with (| b, l |) -> argument_as_uint64 b l

inline_for_extraction
noextract [@@noextract_to "krml"]
let impl_leaf_content_seq_cond
  (h: header)
: Pure bool
    (requires True)
    (ensures (fun res -> res == true <==> leaf_content_seq_cond h))
= let b = get_header_initial_byte h in
  b.major_type = cbor_major_type_byte_string ||
  b.major_type = cbor_major_type_text_string

module SZ = FStar.SizeT

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_leaf_content_seq
  (sq: squash (SZ.fits_u64))
  (h: header)
  (prf: squash (impl_leaf_content_seq_cond h == true))
: Tot (validator (parse_leaf_content h))
= validate_ext
    (validate_total_constant_size
      (LowParse.Spec.SeqBytes.tot_parse_lseq_bytes (U64.v (get_header_argument_as_uint64 h)) `tot_parse_synth` LeafContentSeq ())
      (SZ.uint64_to_sizet (get_header_argument_as_uint64 h))
    )
    (parse_leaf_content h)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_leaf_content_empty
  (sq: squash (SZ.fits_u64))
  (h: header)
  (prf: squash (impl_leaf_content_seq_cond h == false))
: Tot (validator (parse_leaf_content h))
= validate_ext
    (validate_synth
      validate_empty
      (LeafContentEmpty ())
    )
    (parse_leaf_content h)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_leaf_content
  (sq: squash (SZ.fits_u64))
  (h: header)
: Tot (validator (parse_leaf_content h))
= ifthenelse_validator
    (parse_leaf_content h)
    (impl_leaf_content_seq_cond h)
    (validate_leaf_content_seq sq h)
    (validate_leaf_content_empty sq h)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_leaf
  (sq: squash (SZ.fits_u64))
: Tot (validator parse_leaf)
= validate_dtuple2
    (validate_header ())
    (read_header ())
    (validate_leaf_content sq)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_leaf_content_seq
  (sq: squash (SZ.fits_u64))
  (h: header)
  (prf: squash (impl_leaf_content_seq_cond h == true))
: Tot (jumper (parse_leaf_content h))
= jump_ext
    (jump_constant_size
      (LowParse.Spec.SeqBytes.tot_parse_lseq_bytes (U64.v (get_header_argument_as_uint64 h)) `tot_parse_synth` LeafContentSeq ())
      (SZ.uint64_to_sizet (get_header_argument_as_uint64 h))
    )
    (parse_leaf_content h)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_leaf_content_empty
  (sq: squash (SZ.fits_u64))
  (h: header)
  (prf: squash (impl_leaf_content_seq_cond h == false))
: Tot (jumper (parse_leaf_content h))
= jump_ext
    (jump_synth
      jump_empty
      (LeafContentEmpty ())
    )
    (parse_leaf_content h)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_leaf_content
  (sq: squash (SZ.fits_u64))
  (h: header)
: Tot (jumper (parse_leaf_content h))
= ifthenelse_jumper
    (parse_leaf_content h)
    (impl_leaf_content_seq_cond h)
    (jump_leaf_content_seq sq h)
    (jump_leaf_content_empty sq h)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_leaf
  (sq: squash (SZ.fits_u64))
: Tot (jumper parse_leaf)
= jump_dtuple2
    (jump_header ())
    (read_header ())
    (jump_leaf_content sq)

noextract [@@noextract_to "krml"]
let test_parse = parse_header

inline_for_extraction
noextract [@@noextract_to "krml"]
let test_jump : jumper test_parse = jump_header ()
