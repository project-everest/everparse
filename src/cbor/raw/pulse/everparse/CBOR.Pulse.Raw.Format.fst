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

(*
inline_for_extraction
noextract
let jump_long_argument
  (b: initial_byte)
: Tot (jumper (parse_long_argument b))
= match b with
  | (major_type, (additional_info, _)) ->
    ifthenelse_jumper
      (parse_long_argument b)
      (additional_info = additional_info_long_argument_8_bits)
      (fun _ ->
        jump_ext
          (jump_constant_size (if major_type = cbor_major_type_simple_value then tot_parse_synth (tot_parse_filter tot_parse_u8 simple_value_long_argument_wf) (LongArgumentSimpleValue #b ()) else tot_weaken (parse_filter_kind parse_u8_kind) (tot_parse_synth tot_parse_u8 (LongArgumentU8 #b ()))) 1sz)
          (parse_long_argument b)
      )
      (fun _ -> ifthenelse_jumper
        (parse_long_argument b)
        (additional_info = additional_info_long_argument_16_bits)
        (fun _ ->
          jump_ext
            (jump_synth
              jump_u16
              (LongArgumentU16 #b ())
            )
            (parse_long_argument b)
        )
        (fun _ -> ifthenelse_jumper
          (parse_long_argument b)
          (additional_info = additional_info_long_argument_32_bits)
          (fun _ ->
            jump_ext
              (jump_synth
                jump_u32
                (LongArgumentU32 #b ())
              )
              (parse_long_argument b)
          )
          (fun _ -> ifthenelse_jumper
            (parse_long_argument b)
            (additional_info = additional_info_long_argument_64_bits)
            (fun _ ->
              jump_ext
                (jump_synth
                  jump_u64
                  (LongArgumentU64 #b ())
                )
                (parse_long_argument b)
            )
            (fun _ ->
              jump_ext
                (jump_synth
                  jump_empty
                  (LongArgumentOther #b additional_info ())
                )
                (parse_long_argument b)
            )
          )
        )
      )
*)

inline_for_extraction
noextract [@@noextract_to "krml"]
let validate_header : validator parse_header =
  validate_dtuple2 validate_initial_byte (leaf_reader_of_reader read_initial_byte) validate_long_argument

(*
inline_for_extraction
noextract
let jump_header : jumper parse_header =
  jump_dtuple2 jump_initial_byte read_initial_byte jump_long_argument
*)

noextract [@@noextract_to "krml"]
let test_parse = tot_parse_dtuple2 tot_parse_u8 (fun _ -> tot_parse_u8)

inline_for_extraction
noextract [@@noextract_to "krml"]
let jump_u8'_on (x: FStar.UInt8.t) : jumper tot_parse_u8 =
  jump_constant_size tot_parse_u8 1sz

inline_for_extraction
noextract [@@noextract_to "krml"]
let test_jump : jumper test_parse = jump_dtuple2 jump_u8 (read_u8' ()) jump_u8'_on
