module CBOR.Pulse.Raw.EverParse.Format
#lang-pulse
open LowParse.Pulse.Int
open LowParse.Pulse.BitSum
open LowParse.Pulse.SeqBytes

inline_for_extraction
noextract [@@noextract_to "krml"]
let read_initial_byte_t' : reader serialize_initial_byte_t =
  reader_ext
    (read_synth'
      (read_bitsum'
        destr_initial_byte
        (reader_of_leaf_reader (read_u8' ()))
      )
      synth_initial_byte
      synth_initial_byte_recip
    )
    _

(* FIXME: WHY WHY WHY does this not extract?
let read_initial_byte_t : leaf_reader serialize_initial_byte_t =
  leaf_reader_of_reader read_initial_byte_t'
*)

fn read_initial_byte_t (_: unit) : leaf_reader #initial_byte_t #(parse_filter_kind parse_u8_kind) #parse_initial_byte_t serialize_initial_byte_t =
  (input: Pulse.Lib.Slice.slice byte)
  (#pm: perm)
  (#v: _)
{
  leaf_reader_of_reader read_initial_byte_t' input #pm #v
}

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_initial_byte : validator parse_initial_byte =
    validate_filter'
      (validate_synth
        (validate_ext
          (validate_total_constant_size
            (LowParse.Spec.BitSum.parse_bitsum'_no_bitsum
              initial_byte_desc
              parse_u8
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
                  (LongArgumentOther #b ())
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
                  (LongArgumentOther #b ())
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
  reader_ext
    (read_dtuple2
      jump_initial_byte
      read_initial_byte
      read_long_argument
    )
    _

fn read_header (_: unit) : leaf_reader #header #parse_header_kind #parse_header serialize_header =
  (input: Pulse.Lib.Slice.slice byte)
  (#pm: perm)
  (#v: _)
{
  leaf_reader_of_reader read_header' input #pm #v
}

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
                  (LongArgumentOther #b ())
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
          (jump_constant_size (if b.major_type = cbor_major_type_simple_value then parse_synth (parse_filter parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b ()) else weaken (parse_filter_kind parse_u8_kind) (parse_synth parse_u8 (LongArgumentU8 #b ()))) 1sz)
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
                  (LongArgumentOther #b ())
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

fn jump_header (_: unit) : jumper #header #parse_header_kind parse_header =
  (input: _)
  (offset: _)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  jump_dtuple2 jump_initial_byte (leaf_reader_of_reader read_initial_byte) jump_long_argument
    input offset #pm #v
}

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

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_leaf_content_seq'
  (h: header)
  (prf: squash (impl_leaf_content_seq_cond h == true))
  (n: SZ.t { SZ.v n == U64.v (get_header_argument_as_uint64 h) })
: Tot (validator (parse_leaf_content h))
= validate_ext
    (validate_synth
      (validate_filter_gen
        (validate_total_constant_size
          (LowParse.Spec.SeqBytes.parse_lseq_bytes (SZ.v n))
          n
        )
        (LowParse.Spec.SeqBytes.serialize_lseq_bytes (SZ.v n))
        _
        (CBOR.Pulse.Raw.EverParse.UTF8.impl_lseq_utf8_correct (get_header_major_type h) n)
      )
      (LeafContentSeq ())
    )
    (parse_leaf_content h)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn validate_leaf_content_seq
  (sq: squash (SZ.fits_u64))
  (h: header)
  (prf: squash (impl_leaf_content_seq_cond h == true))
: validator #_ #_ (parse_leaf_content h)
= (input: _)
  (poffset: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  let n = SZ.uint64_to_sizet (get_header_argument_as_uint64 h);
  validate_leaf_content_seq' h prf n input poffset;
}

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
      (parse_filter (LowParse.Spec.SeqBytes.parse_lseq_bytes (U64.v (get_header_argument_as_uint64 h))) (lseq_utf8_correct (get_header_major_type h) _) `parse_synth` LeafContentSeq ())
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

fn validate_recursive_step_count_leaf (_: squash SZ.fits_u64) :
  validate_recursive_step_count #parse_raw_data_item_param serialize_raw_data_item_param
=
    (#va: Ghost.erased leaf)
    (#pm: perm)
    (a: _)
    (bound: SZ.t)
    (#rem: Ghost.erased SZ.t)
    (prem: R.ref SZ.t)
{
  pts_to_serialized_ext_trade
    (serializer_of_tot_serializer serialize_raw_data_item_param.serialize_header)
    (serialize_dtuple2 serialize_header serialize_leaf_content)
    a;
  let input1, input2 = split_dtuple2 serialize_header (jump_header ()) serialize_leaf_content a;
  unfold (split_dtuple2_post serialize_header serialize_leaf_content a pm va (input1, input2));
  unfold (split_dtuple2_post' serialize_header serialize_leaf_content a pm va input1 input2);
  let h = read_header () input1;
  elim_trade
    (pts_to_serialized serialize_header input1 #pm (dfst va) ** pts_to_serialized (serialize_leaf_content (dfst va)) input2 #pm (dsnd va))
    (pts_to_serialized (serialize_dtuple2 serialize_header serialize_leaf_content) a #pm va);
  elim_trade _ _;
  let typ = get_header_major_type h;
  if (typ = cbor_major_type_array) {
    let arg64 = get_header_argument_as_uint64 h;
    prem := SZ.uint64_to_sizet arg64;
    false
  }
  else if (typ = cbor_major_type_map) {
    let arg64 = get_header_argument_as_uint64 h;
    let arg = SZ.uint64_to_sizet arg64;
    if SZ.gt arg bound {
      true
    } else if SZ.lt (SZ.sub bound arg) arg {
      true
    } else {
      prem := (SZ.add arg arg);
      false
    }
  }
  else if (typ = cbor_major_type_tagged) {
    prem := 1sz;
    false
  }
  else {
    prem := 0sz;
    false
  }
}

fn jump_recursive_step_count_leaf (_: squash SZ.fits_u64) :
  jump_recursive_step_count #parse_raw_data_item_param serialize_raw_data_item_param
=
    (#va: Ghost.erased leaf)
    (#pm: perm)
    (a: _)
    (bound: SZ.t)
{
  pts_to_serialized_ext_trade
    (serializer_of_tot_serializer serialize_raw_data_item_param.serialize_header)
    (serialize_dtuple2 serialize_header serialize_leaf_content)
    a;
  let input1, input2 = split_dtuple2 serialize_header (jump_header ()) serialize_leaf_content a;
  unfold (split_dtuple2_post serialize_header serialize_leaf_content a pm va (input1, input2));
  unfold (split_dtuple2_post' serialize_header serialize_leaf_content a pm va input1 input2);
  let h = read_header () input1;
  elim_trade
    (pts_to_serialized serialize_header input1 #pm (dfst va) ** pts_to_serialized (serialize_leaf_content (dfst va)) input2 #pm (dsnd va))
    (pts_to_serialized (serialize_dtuple2 serialize_header serialize_leaf_content) a #pm va);
  elim_trade _ _;
  let typ = get_header_major_type h;
  if (typ = cbor_major_type_array) {
    let arg64 = get_header_argument_as_uint64 h;
    SZ.uint64_to_sizet arg64
  }
  else if (typ = cbor_major_type_map) {
    let arg64 = get_header_argument_as_uint64 h;
    let arg = SZ.uint64_to_sizet arg64;
    SZ.add arg arg
  }
  else if (typ = cbor_major_type_tagged) {
    1sz
  }
  else {
    0sz
  }
}

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_raw_data_item' (_: squash SZ.fits_u64) : validator #raw_data_item #parse_raw_data_item_kind parse_raw_data_item =
  validate_recursive
    serialize_raw_data_item_param
    (validate_leaf ())
    (validate_recursive_step_count_leaf ())

fn validate_raw_data_item (_: squash SZ.fits_u64) : validator #raw_data_item #parse_raw_data_item_kind parse_raw_data_item =
  (input: _)
  (poffset: _)
  (#offset: _)
  (#pm: _)
  (#v: _)
{
  validate_raw_data_item' ()
    input poffset #offset #pm #v
}

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_raw_data_item' (_: squash SZ.fits_u64) : jumper #raw_data_item #parse_raw_data_item_kind parse_raw_data_item =
  jump_recursive
    serialize_raw_data_item_param
    (jump_leaf ())
    (jump_recursive_step_count_leaf ())

fn jump_raw_data_item (_: squash SZ.fits_u64) : jumper #raw_data_item #parse_raw_data_item_kind parse_raw_data_item =
  (input: _)
  (offset: _)
  (#pm: _)
  (#v: _)
{
  jump_raw_data_item' ()
    input offset #pm #v
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn get_header_and_contents
  (input: S.slice byte)
  (outh: R.ref header)
  (#pm: perm)
  (#v: Ghost.erased raw_data_item)
  norewrite
  requires exists* h . pts_to_serialized serialize_raw_data_item input #pm v ** pts_to outh h
  returns outc: S.slice byte
  ensures exists* h c .
    pts_to outh h **
    pts_to_serialized (serialize_content h) outc #pm c **
    trade (pts_to_serialized (serialize_content h) outc #pm c) (pts_to_serialized serialize_raw_data_item input #pm v) **
    pure (synth_raw_data_item_recip v == (| h, c |))
{
  Classical.forall_intro parse_raw_data_item_eq;
  pts_to_serialized_ext_trade
    serialize_raw_data_item
    serialize_raw_data_item_aux
    input;
  pts_to_serialized_synth_l2r_trade
    (serialize_dtuple2 serialize_header serialize_content)
    synth_raw_data_item
    synth_raw_data_item_recip
    input;
  LowParse.Pulse.VCList.trade_trans_nounify _ _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
  with v' . assert (pts_to_serialized (serialize_dtuple2 serialize_header serialize_content) input #pm v');
  let ph, outc = split_dtuple2 serialize_header (jump_header ()) serialize_content input;
  unfold (split_dtuple2_post serialize_header serialize_content input pm v' (ph, outc));
  unfold (split_dtuple2_post' serialize_header serialize_content input pm v' ph outc);
  Trade.trans _ _ (pts_to_serialized serialize_raw_data_item input #pm v);
  let h = read_header () ph;
  Trade.elim_hyp_l _ _ _;
  outh := h;
  rewrite each dfst (synth_raw_data_item_recip
                      v) as h;
  outc
}

ghost
fn get_string_payload
  (input: S.slice byte)
  (v: Ghost.erased raw_data_item)
  (#pm: perm)
  (#h: Ghost.erased header)
  (#c: Ghost.erased (content h)) 
  requires pts_to_serialized (serialize_content h) input #pm c ** pure (synth_raw_data_item_recip v == (| Ghost.reveal h, Ghost.reveal c |) /\ String? v)
  ensures exists* (v': Seq.seq byte) .
    pts_to input #pm v' **
    trade (pts_to input #pm v') (pts_to_serialized (serialize_content h) input #pm c) **
    pure (String? v /\ v' == String?.v v)
{
  pts_to_serialized_ext_trade_gen
    (serialize_content h)
    (serialize_filter (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v (String?.len v).value)) (lseq_utf8_correct (get_header_major_type h) _))
    input;
  pts_to_serialized_filter_elim_trade (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v (String?.len v).value)) (lseq_utf8_correct (get_header_major_type h) _) input;
  Trade.trans _ _ (pts_to_serialized (serialize_content h) input #pm c);
  with v1 . assert (pts_to_serialized (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v (String?.len v).value)) input #pm v1);
  let v2 : Ghost.erased bytes = Ghost.hide #bytes (Ghost.reveal #(Seq.lseq byte (U64.v (String?.len v).value)) v1);
  Trade.rewrite_with_trade
    (pts_to_serialized (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v (String?.len v).value)) input #pm v1)
    (pts_to input #pm v2);
  Trade.trans _ _ (pts_to_serialized (serialize_content h) input #pm c)
}

ghost
fn get_tagged_payload
  (input: S.slice byte)
  (v: Ghost.erased raw_data_item)
  (#pm: perm)
  (#h: Ghost.erased header)
  (#c: Ghost.erased (content h)) 
  requires pts_to_serialized (serialize_content h) input #pm c ** pure (synth_raw_data_item_recip v == (| Ghost.reveal h, Ghost.reveal c |) /\ Tagged? v)
  ensures exists* v' .
    pts_to_serialized serialize_raw_data_item input #pm v' **
    trade (pts_to_serialized serialize_raw_data_item input #pm v') (pts_to_serialized (serialize_content h) input #pm c) **
    pure (Tagged? v /\ v' == Tagged?.v v)
{
  pts_to_serialized_ext_trade
    (serialize_content h)
    serialize_raw_data_item
    input;
  rewrite
  trade #emp_inames
      (pts_to_serialized #parse_raw_data_item_kind
          #(content (reveal #header h))
          #parse_raw_data_item
          serialize_raw_data_item
          input
          #pm
          (reveal #(content (reveal #header h)) c))
      (pts_to_serialized #parse_content_kind
          #(content (reveal #header h))
          #(parse_content parse_raw_data_item (reveal #header h))
          (serialize_content (reveal #header h))
          input
          #pm
          (reveal #(content (reveal #header h)) c))
    as
    trade #emp_inames
      (pts_to_serialized #parse_raw_data_item_kind
          #raw_data_item
          #parse_raw_data_item
          serialize_raw_data_item
          input
          #pm
          (reveal #(content (reveal #header h)) c))
      (pts_to_serialized #parse_content_kind
          #(content (reveal #header h))
          #(parse_content parse_raw_data_item (reveal #header h))
          (serialize_content (reveal #header h))
          input
          #pm
          (reveal #(content (reveal #header h)) c))
      ;
  ()
}

ghost
fn get_array_payload'
  (input: S.slice byte)
  (v: Ghost.erased raw_data_item {Array? v })
  (#pm: perm)
  (#h: Ghost.erased header)
  (#c: Ghost.erased (content h))
  requires pts_to_serialized (serialize_content h) input #pm c ** pure (synth_raw_data_item_recip v == (| Ghost.reveal h, Ghost.reveal c |))
  ensures exists* v' .
    pts_to_serialized (L.serialize_nlist (U64.v (Array?.len v).value) serialize_raw_data_item) input #pm v' **
    trade (pts_to_serialized (L.serialize_nlist (U64.v (Array?.len v).value) serialize_raw_data_item) input #pm v') (pts_to_serialized (serialize_content h) input #pm c) **
    pure (v' == Array?.v v)
{
  pts_to_serialized_ext_trade
    (serialize_content h)
    (L.serialize_nlist (U64.v (Array?.len v).value) serialize_raw_data_item)
    input;
  rewrite
    trade #emp_inames
      (pts_to_serialized #(L.parse_nlist_kind (U64.v (Array?.len (reveal #raw_data_item v))
                    .value)
              parse_raw_data_item_kind)
          #(content (reveal #header h))
          #(L.parse_nlist (U64.v (Array?.len (reveal #raw_data_item v)).value)
              #parse_raw_data_item_kind
              #raw_data_item
              parse_raw_data_item)
          (L.serialize_nlist (U64.v (Array?.len (reveal #raw_data_item v)).value)
              #parse_raw_data_item_kind
              #raw_data_item
              #parse_raw_data_item
              serialize_raw_data_item)
          input
          #pm
          (reveal #(content (reveal #header h)) c))
      (pts_to_serialized #parse_content_kind
          #(content (reveal #header h))
          #(parse_content parse_raw_data_item (reveal #header h))
          (serialize_content (reveal #header h))
          input
          #pm
          (reveal #(content (reveal #header h)) c))  
   as
    trade #emp_inames
      (pts_to_serialized #(L.parse_nlist_kind (U64.v (Array?.len (reveal #raw_data_item v))
                    .value)
              parse_raw_data_item_kind)
          #(L.nlist (U64.v (Array?.len (reveal #raw_data_item v)).value) raw_data_item)
          #(L.parse_nlist (U64.v (Array?.len (reveal #raw_data_item v)).value)
              #parse_raw_data_item_kind
              #raw_data_item
              parse_raw_data_item)
          (L.serialize_nlist (U64.v (Array?.len (reveal #raw_data_item v)).value)
              #parse_raw_data_item_kind
              #raw_data_item
              #parse_raw_data_item
              serialize_raw_data_item)
          input
          #pm
          (reveal #(content (reveal #header h)) c))
      (pts_to_serialized #parse_content_kind
          #(content (reveal #header h))
          #(parse_content parse_raw_data_item (reveal #header h))
          (serialize_content (reveal #header h))
          input
          #pm
          (reveal #(content (reveal #header h)) c));
  ()
}

ghost
fn get_array_payload
  (input: S.slice byte)
: get_array_payload_t input
=
  (v: _)
  (#pm: perm)
  (#h: Ghost.erased header)
  (#c: Ghost.erased (content h)) 
{
  get_array_payload' input v
}

#push-options "--z3rlimit 20"
ghost
fn get_map_payload'
  (input: S.slice byte)
  (v: Ghost.erased raw_data_item {Map? v })
  (#pm: perm)
  (#h: Ghost.erased header)
  (#c: Ghost.erased (content h))
  requires pts_to_serialized (serialize_content h) input #pm c ** pure (synth_raw_data_item_recip v == (| Ghost.reveal h, Ghost.reveal c |))
  ensures exists* v' .
    pts_to_serialized (L.serialize_nlist (U64.v (Map?.len v).value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) input #pm v' **
    trade (pts_to_serialized (L.serialize_nlist (U64.v (Map?.len v).value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) input #pm v') (pts_to_serialized (serialize_content h) input #pm c) **
    pure (v' == Map?.v v)
{
  pts_to_serialized_ext_trade
    (serialize_content h)
    (L.serialize_nlist (U64.v (Map?.len v).value) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
    input;
  rewrite
  trade #emp_inames
      (pts_to_serialized #(L.parse_nlist_kind (U64.v (Map?.len (reveal #raw_data_item v))
                    .value)
              (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind))
          #(content (reveal #header h))
          #(L.parse_nlist (U64.v (Map?.len (reveal #raw_data_item v)).value)
              #(and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)
              #(raw_data_item & raw_data_item)
              (nondep_then #parse_raw_data_item_kind
                  #raw_data_item
                  parse_raw_data_item
                  #parse_raw_data_item_kind
                  #raw_data_item
                  parse_raw_data_item))
          (L.serialize_nlist (U64.v (Map?.len (reveal #raw_data_item v)).value)
              #(and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)
              #(raw_data_item & raw_data_item)
              #(nondep_then #parse_raw_data_item_kind
                  #raw_data_item
                  parse_raw_data_item
                  #parse_raw_data_item_kind
                  #raw_data_item
                  parse_raw_data_item)
              (serialize_nondep_then #parse_raw_data_item_kind
                  #raw_data_item
                  #parse_raw_data_item
                  serialize_raw_data_item
                  #parse_raw_data_item_kind
                  #raw_data_item
                  #parse_raw_data_item
                  serialize_raw_data_item))
          input
          #pm
          (reveal #(content (reveal #header h)) c))
      (pts_to_serialized #parse_content_kind
          #(content (reveal #header h))
          #(parse_content parse_raw_data_item (reveal #header h))
          (serialize_content (reveal #header h))
          input
          #pm
          (reveal #(content (reveal #header h)) c))
   as trade #emp_inames
      (pts_to_serialized #(L.parse_nlist_kind (U64.v (Map?.len (reveal #raw_data_item v))
                    .value)
              (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind))
          #(L.nlist (U64.v (Map?.len (reveal #raw_data_item v)).value)
              (raw_data_item & raw_data_item))
          #(L.parse_nlist (U64.v (Map?.len (reveal #raw_data_item v)).value)
              #(and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)
              #(raw_data_item & raw_data_item)
              (nondep_then #parse_raw_data_item_kind
                  #raw_data_item
                  parse_raw_data_item
                  #parse_raw_data_item_kind
                  #raw_data_item
                  parse_raw_data_item))
          (L.serialize_nlist (U64.v (Map?.len (reveal #raw_data_item v)).value)
              #(and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)
              #(raw_data_item & raw_data_item)
              #(nondep_then #parse_raw_data_item_kind
                  #raw_data_item
                  parse_raw_data_item
                  #parse_raw_data_item_kind
                  #raw_data_item
                  parse_raw_data_item)
              (serialize_nondep_then #parse_raw_data_item_kind
                  #raw_data_item
                  #parse_raw_data_item
                  serialize_raw_data_item
                  #parse_raw_data_item_kind
                  #raw_data_item
                  #parse_raw_data_item
                  serialize_raw_data_item))
          input
          #pm
          (reveal #(content (reveal #header h)) c))
      (pts_to_serialized #parse_content_kind
          #(content (reveal #header h))
          #(parse_content parse_raw_data_item (reveal #header h))
          (serialize_content (reveal #header h))
          input
          #pm
          (reveal #(content (reveal #header h)) c))
    ;
  ()
}
#pop-options

ghost
fn get_map_payload
  (input: S.slice byte)
: get_map_payload_t input
=
  (v: _)
  (#pm: perm)
  (#h: Ghost.erased header)
  (#c: Ghost.erased (content h)) 
{
  get_map_payload' input v
}
