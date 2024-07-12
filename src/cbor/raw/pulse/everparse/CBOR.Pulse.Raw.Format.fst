module CBOR.Pulse.Raw.Format
open CBOR.Spec.Raw.Format
open LowParse.Pulse.Util
open LowParse.Pulse.Combinators
open LowParse.Pulse.Int
open LowParse.Pulse.BitSum

inline_for_extraction
noextract
let validate_initial_byte : validate_and_read parse_initial_byte =
  validate_and_read_filter
    (validate_bitsum'
      filter_initial_byte
      destr_initial_byte
      (validate_and_read_intro
        validate_u8
        read_u8
      )
    )
    initial_byte_wf
    (fun x -> initial_byte_wf x)

inline_for_extraction
noextract
let jump_initial_byte : jumper parse_initial_byte =
  jump_filter
    (jump_bitsum'
      initial_byte_desc
      jump_u8
    )
    initial_byte_wf

inline_for_extraction
noextract
let read_initial_byte : reader serialize_initial_byte =
  read_filter
    (read_bitsum'
      destr_initial_byte
      read_u8
    )
    initial_byte_wf

inline_for_extraction
noextract
let validate_long_argument
  (b: initial_byte)
: Tot (validate_and_read (parse_long_argument b))
= match b with
  | (major_type, (additional_info, _)) ->
    ifthenelse_validate_and_read
      (parse_long_argument b)
      (additional_info = additional_info_long_argument_8_bits)
      (fun _ -> ifthenelse_validate_and_read
        (parse_long_argument b)
        (major_type = cbor_major_type_simple_value)
        (fun _ ->
          validate_and_read_ext
            (validate_and_read_synth'
              (validate_and_read_filter
                (validate_and_read_u8)
                simple_value_long_argument_wf
                (fun x -> simple_value_long_argument_wf x)
              )
              (LongArgumentSimpleValue #b ())
            )
            (parse_long_argument b)
        )
        (fun _ ->
          validate_and_read_ext
            (validate_and_read_synth'
              validate_and_read_u8
              (LongArgumentU8 #b ())
            )
            (parse_long_argument b)
        )
      )
      (fun _ -> ifthenelse_validate_and_read
        (parse_long_argument b)
        (additional_info = additional_info_long_argument_16_bits)
        (fun _ ->
          validate_and_read_ext
            (validate_and_read_synth'
              validate_and_read_u16
              (LongArgumentU16 #b ())
            )
            (parse_long_argument b)
        )
        (fun _ -> ifthenelse_validate_and_read
          (parse_long_argument b)
          (additional_info = additional_info_long_argument_32_bits)
          (fun _ ->
            validate_and_read_ext
              (validate_and_read_synth'
                validate_and_read_u32
                (LongArgumentU32 #b ())
              )
              (parse_long_argument b)
          )
          (fun _ -> ifthenelse_validate_and_read
            (parse_long_argument b)
            (additional_info = additional_info_long_argument_64_bits)
            (fun _ ->
              validate_and_read_ext
                (validate_and_read_synth'
                  validate_and_read_u64
                  (LongArgumentU64 #b ())
                )
                (parse_long_argument b)
            )
            (fun _ ->
              validate_and_read_ext
                (validate_and_read_synth'
                  validate_and_read_empty
                  (LongArgumentOther #b additional_info ())
                )
                (parse_long_argument b)
            )
          )
        )
      )

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

inline_for_extraction
noextract
let validate_header : validate_and_read parse_header =
  validate_and_read_dtuple2 validate_initial_byte validate_long_argument

inline_for_extraction
noextract
let jump_header : jumper parse_header =
  jump_dtuple2 jump_initial_byte read_initial_byte jump_long_argument

let test_parse = tot_parse_dtuple2 tot_parse_u8 (fun _ -> tot_parse_u8)

inline_for_extraction
let jump_u8'_on (x: FStar.UInt8.t) : jumper tot_parse_u8 =
  jump_constant_size tot_parse_u8 1sz

inline_for_extraction
let test_jump : jumper test_parse = jump_dtuple2 jump_u8 read_u8 jump_u8'_on
