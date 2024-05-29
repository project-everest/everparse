module CBOR.SteelST.Raw.Validate

inline_for_extraction
noextract
let validate_initial_byte : validate_and_read parse_initial_byte =
  validate_filter_and_read
    (validate_bitsum'
      filter_initial_byte
      destr_initial_byte
      (mk_validate_and_read
        I.validate_u8
        (cps_reader_of_leaf_reader read_u8)
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
      I.jump_u8
    )
    initial_byte_wf

inline_for_extraction
noextract
let read_and_jump_initial_byte : read_and_jump parse_initial_byte =
  read_and_jump_filter
    (read_and_jump_bitsum'
      destr_initial_byte
      (mk_read_and_jump
        (cps_reader_of_leaf_reader read_u8)
        I.jump_u8
      )
    )
    initial_byte_wf

inline_for_extraction
noextract
let read_initial_byte : cps_reader parse_initial_byte =
  cps_read_filter
    (read_bitsum'
      destr_initial_byte
      (cps_reader_of_leaf_reader read_u8)
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
      (additional_info = additional_info_long_argument_8_bits)
      (fun _ -> ifthenelse_validate_and_read
        (major_type = cbor_major_type_simple_value)
        (fun _ ->
          rewrite_validate_and_read
            (validate_and_read_weaken
              (strong_parser_kind 0 8 None)
              (validate_and_read_synth'
                (validate_filter_and_read
                  (mk_validate_and_read I.validate_u8 (cps_reader_of_leaf_reader read_u8))
                  simple_value_long_argument_wf
                  (fun x -> simple_value_long_argument_wf x)
                )
                (LongArgumentSimpleValue #b ())
                ()
              )
              ()
            )
            (parse_long_argument b)
        )
        (fun _ ->
          rewrite_validate_and_read
            (validate_and_read_weaken
              (strong_parser_kind 0 8 None)
              (validate_and_read_synth'
                (validate_filter_and_read
                  (mk_validate_and_read I.validate_u8 (cps_reader_of_leaf_reader read_u8))
                  uint8_wf
                  (fun x -> uint8_wf x)
                )
                (LongArgumentU8 #b ())
                ()
              )
              ()
            )
            (parse_long_argument b)
        )
      )
      (fun _ -> ifthenelse_validate_and_read
        (additional_info = additional_info_long_argument_16_bits)
        (fun _ ->
          rewrite_validate_and_read
            (validate_and_read_weaken
              (strong_parser_kind 0 8 None)
              (validate_and_read_synth'
                (validate_filter_and_read
                  (mk_validate_and_read I.validate_u16 (cps_reader_of_leaf_reader read_u16))
                  uint16_wf
                  (fun x -> uint16_wf x)
                )
                (LongArgumentU16 #b ())
                ()
              )
              ()
            )
            (parse_long_argument b)
        )
        (fun _ -> ifthenelse_validate_and_read
          (additional_info = additional_info_long_argument_32_bits)
          (fun _ ->
            rewrite_validate_and_read
              (validate_and_read_weaken
                (strong_parser_kind 0 8 None)
                (validate_and_read_synth'
                  (validate_filter_and_read
                    (mk_validate_and_read I.validate_u32 (cps_reader_of_leaf_reader read_u32))
                    uint32_wf
                    (fun x -> uint32_wf x)
                  )
                  (LongArgumentU32 #b ())
                  ()
                )
                ()
              )
              (parse_long_argument b)
          )
          (fun _ -> ifthenelse_validate_and_read
            (additional_info = additional_info_long_argument_64_bits)
            (fun _ ->
              rewrite_validate_and_read
                (validate_and_read_weaken
                  (strong_parser_kind 0 8 None)
                  (validate_and_read_synth'
                    (validate_filter_and_read
                      (mk_validate_and_read I.validate_u64 (cps_reader_of_leaf_reader read_u64))
                      uint64_wf
                      (fun x -> uint64_wf x)
                    )
                    (LongArgumentU64 #b ())
                    ()
                  )
                  ()
                )
                (parse_long_argument b)
            )
            (fun _ ->
              rewrite_validate_and_read
                (validate_and_read_weaken
                  (strong_parser_kind 0 8 None)
                  (validate_and_read_synth'
                    (mk_validate_and_read validate_empty (cps_reader_of_leaf_reader read_empty))
                    (LongArgumentOther #b additional_info ())
                    ()
                  )
                  ()
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
: Tot (read_and_jump (parse_long_argument b))
= match b with
  | (major_type, (additional_info, _)) ->
    ifthenelse_read_and_jump
      (additional_info = additional_info_long_argument_8_bits)
      (fun _ -> ifthenelse_read_and_jump
        (major_type = cbor_major_type_simple_value)
        (fun _ ->
          rewrite_read_and_jump
            (read_and_jump_weaken
              (strong_parser_kind 0 8 None)
              (read_and_jump_synth'
                (read_and_jump_filter
                  (mk_read_and_jump (cps_reader_of_leaf_reader read_u8) I.jump_u8)
                  simple_value_long_argument_wf
                )
                (LongArgumentSimpleValue #b ())
                ()
              )
              ()
            )
            (parse_long_argument b)
        )
        (fun _ ->
          rewrite_read_and_jump
            (read_and_jump_weaken
              (strong_parser_kind 0 8 None)
              (read_and_jump_synth'
                (read_and_jump_filter
                  (mk_read_and_jump (cps_reader_of_leaf_reader read_u8) I.jump_u8)
                  uint8_wf
                )
                (LongArgumentU8 #b ())
                ()
              )
              ()
            )
            (parse_long_argument b)
        )
      )
      (fun _ -> ifthenelse_read_and_jump
        (additional_info = additional_info_long_argument_16_bits)
        (fun _ ->
          rewrite_read_and_jump
            (read_and_jump_weaken
              (strong_parser_kind 0 8 None)
              (read_and_jump_synth'
                (read_and_jump_filter
                  (mk_read_and_jump (cps_reader_of_leaf_reader read_u16) I.jump_u16)
                  uint16_wf
                )
                (LongArgumentU16 #b ())
                ()
              )
              ()
            )
            (parse_long_argument b)
        )
        (fun _ -> ifthenelse_read_and_jump
          (additional_info = additional_info_long_argument_32_bits)
          (fun _ ->
            rewrite_read_and_jump
              (read_and_jump_weaken
                (strong_parser_kind 0 8 None)
                (read_and_jump_synth'
                  (read_and_jump_filter
                    (mk_read_and_jump (cps_reader_of_leaf_reader read_u32) I.jump_u32)
                    uint32_wf
                  )
                  (LongArgumentU32 #b ())
                  ()
                )
                ()
              )
              (parse_long_argument b)
          )
          (fun _ -> ifthenelse_read_and_jump
            (additional_info = additional_info_long_argument_64_bits)
            (fun _ ->
              rewrite_read_and_jump
                (read_and_jump_weaken
                  (strong_parser_kind 0 8 None)
                  (read_and_jump_synth'
                    (read_and_jump_filter
                      (mk_read_and_jump (cps_reader_of_leaf_reader read_u64) I.jump_u64)
                      uint64_wf
                    )
                    (LongArgumentU64 #b ())
                    ()
                  )
                  ()
                )
                (parse_long_argument b)
            )
            (fun _ ->
              rewrite_read_and_jump
                (read_and_jump_weaken
                  (strong_parser_kind 0 8 None)
                  (read_and_jump_synth'
                    (mk_read_and_jump (cps_reader_of_leaf_reader read_empty) jump_empty)
                    (LongArgumentOther #b additional_info ())
                    ()
                  )
                  ()
                )
                (parse_long_argument b)
            )
          )
        )
      )

inline_for_extraction
noextract
let validate_header : validate_and_read parse_header =
  validate_and_read_dtuple2 validate_initial_byte _ validate_long_argument

inline_for_extraction
noextract
let read_and_jump_header : read_and_jump parse_header =
  read_and_jump_dtuple2 read_and_jump_initial_byte _ jump_long_argument

let jump_header' : jumper parse_header =
  jumper_of_read_and_jump read_and_jump_header

let jump_header : jumper parse_header =
  fun a -> jump_header' a

inline_for_extraction
noextract
let validate_leaf_content
  (sq: squash SZ.fits_u64)
  (h: header)
: Tot (validator (parse_leaf_content h))
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      ifthenelse_validate
        (major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string)
        (fun _ -> rewrite_validator
          (validate_weaken
            parse_content_kind
            (validate_synth
              (validate_lseq_bytes (SZ.uint64_to_sizet (argument_as_uint64 b long_arg)))
              (LeafContentSeq #h ())
              ()
            )
            ()
          )
          (parse_leaf_content h)
        )
        (fun _ -> rewrite_validator
          (validate_weaken
            parse_content_kind
            (validate_synth
              validate_empty
              (LeafContentEmpty #h ())
              ()
            )
            ()
          )
          (parse_leaf_content h)
        )

inline_for_extraction
noextract
let jump_leaf_content
  (sq: squash SZ.fits_u64)
  (h: header)
: Tot (jumper (parse_leaf_content h))
= match h with
  | (| b, long_arg |) ->
    match b with
    | (major_type, _) ->
      ifthenelse_jump
        (major_type = cbor_major_type_byte_string || major_type = cbor_major_type_text_string)
        (fun _ -> rewrite_jumper
          (jump_weaken
            parse_content_kind
            (jump_synth
              (jump_lseq_bytes (SZ.uint64_to_sizet (argument_as_uint64 b long_arg)))
              (LeafContentSeq #h ())
              ()
            )
            ()
          )
          (parse_leaf_content h)
        )
        (fun _ -> rewrite_jumper
          (jump_weaken
            parse_content_kind
            (jump_synth
              jump_empty
              (LeafContentEmpty #h ())
              ()
            )
            ()
          )
          (parse_leaf_content h)
        )

inline_for_extraction
noextract
let validate_leaf
  (sq: squash SZ.fits_u64)
: Tot (validator parse_leaf) =
  validate_dtuple2_and_read_tag
    validate_header
    _
    (validate_leaf_content ())

inline_for_extraction
noextract
let jump_leaf'
  (sq: squash SZ.fits_u64)
: Tot (jumper parse_leaf) =
  jump_dtuple2_and_read_tag
    read_and_jump_header
    _
    (jump_leaf_content ())

let jump_leaf
: jumper parse_leaf
= fun a ->
    let sq = Steel.ST.HigherArray.intro_fits_u64 () in
    jump_leaf' sq a

(* FIXME: the current design of validate_recursive independently
   validates a leaf content before asking the number of expected
   children. In the general case, it is not possible to reuse the data
   read during validation for the computation of that number, unless
   the whole leaf is read, which we don't want here (we have byte
   strings.) *)


#push-options "--z3rlimit 16 --split_queries always"

let read_header_major_type
  (#va: v (get_parser_kind parse_header) header)
  (a: byte_array)
: ST byte
    (aparse parse_header a va)
    (fun _ -> aparse parse_header a va)
    True
    (fun res ->
      res == get_header_major_type va.contents
    )
= let _ = rewrite_aparse a (parse_dtuple2 parse_initial_byte parse_long_argument) in
  let a_long = ghost_split_dtuple2_full _ _ a in
  let _ = gen_elim () in
  let res = read_initial_byte a (aparse _ a_long _) byte (fun res -> aparse parse_header a va `star` pure (
    res == get_header_major_type va.contents
  )) (fun (major_type, _) ->
    let _ = intro_dtuple2 parse_initial_byte parse_long_argument a a_long in
    let _ = rewrite_aparse a parse_header in
    vpattern_rewrite (aparse _ a) va;
    return major_type
  )
  in
  let _ = elim_pure _ in
  return res

#restart-solver
let read_major_type
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST byte
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    True
    (fun res -> res == get_major_type va.contents)
= Classical.forall_intro parse_raw_data_item_eq;
  let _ = rewrite_aparse a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let va1 = elim_synth _ _ a () in // (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
  let a_content = ghost_split_dtuple2_full _ _ a in // parse_header (parse_content parse_raw_data_item) a in
  let _ = gen_elim () in
  let res = read_header_major_type a in
  let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a_content in
  let _ = intro_synth (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
  let _ = rewrite_aparse a parse_raw_data_item in
  vpattern_rewrite (aparse parse_raw_data_item a) va;
  return res

let read_header_argument_as_uint64
  (#va: v (get_parser_kind parse_header) header)
  (a: byte_array)
: ST UInt64.t
    (aparse parse_header a va)
    (fun _ -> aparse parse_header a va)
    True
    (fun res ->
      res == get_header_argument_as_uint64 va.contents
    )
= let res = read_and_jump_header a emp UInt64.t (fun res -> aparse parse_header a va `star` pure (
      res == get_header_argument_as_uint64 va.contents
  )) (fun _ (| b, x |) ->
    noop ();
    return (argument_as_uint64 b x)
  )
  in
  let _ = elim_pure _ in
  return res

let read_argument_as_uint64' : read_argument_as_uint64_t = fun #va a ->
  Classical.forall_intro parse_raw_data_item_eq;
  let _ = rewrite_aparse a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let va1 = elim_synth _ _ a () in // (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
  let a_content = ghost_split_dtuple2_full _ _ a in // parse_header (parse_content parse_raw_data_item) a in
  let _ = gen_elim () in
  let res = read_header_argument_as_uint64 a in
  let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a_content in
  let _ = intro_synth (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
  let _ = rewrite_aparse a parse_raw_data_item in
  vpattern_rewrite (aparse parse_raw_data_item a) va;
  return res

let read_argument_as_uint64 =
  fun a -> read_argument_as_uint64' a

let count_remaining_data_items
: (validate_recursive_step_count parse_raw_data_item_param)
= fun #va a bound perr ->
    let sq = Steel.ST.HigherArray.intro_fits_u64 () in
    let _ = rewrite_aparse a parse_leaf in
    let ar = ghost_split_dtuple2_full parse_header parse_leaf_content a in
    let _ = gen_elim () in
    let major_type = read_header_major_type a in
    if major_type = cbor_major_type_array
    then begin
      let arg = read_header_argument_as_uint64 a in
      let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
      let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
      vpattern_rewrite (aparse _ a) va;
      let res = SZ.uint64_to_sizet arg in
      noop ();
      return res
    end
    else if major_type = cbor_major_type_map
    then begin
      let arg = read_header_argument_as_uint64 a in
      let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
      let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
      vpattern_rewrite (aparse _ a) va;
      let half = SZ.uint64_to_sizet arg in
      let overflow =
        if half `SZ.gt` bound
        then true
        else (bound `SZ.sub` half) `SZ.lt` half
      in
      if overflow
      then begin
        R.write perr validator_error_not_enough_data;
        noop ();
        return 0sz
      end else begin
        [@@inline_let]
        let res = size_add_fits half half bound () in
        noop ();
        return res
      end
    end
    else begin
      let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
      let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
      vpattern_rewrite (aparse _ a) va;
      noop ();
      if major_type = cbor_major_type_tagged
      then begin
        noop ();
        noop ();
        return 1sz
      end
      else begin
        noop ();
        noop ();
        return 0sz
      end
    end

let validate_raw_data_item'
  (sq: squash SZ.fits_u64)
: Tot (validator parse_raw_data_item)
=
    validate_recursive
      parse_raw_data_item_param
      (validate_leaf ())
      (count_remaining_data_items)

let validate_raw_data_item
: validator parse_raw_data_item
= fun a len err ->
    let sq = Steel.ST.HigherArray.intro_fits_u64 () in
    validate_raw_data_item' sq a len err

let jump_count_remaining_data_items
: (jump_recursive_step_count parse_raw_data_item_param)
= fun #va a bound ->
    let sq = Steel.ST.HigherArray.intro_fits_u64 () in
    let _ = rewrite_aparse a parse_leaf in
    let ar = ghost_split_dtuple2_full parse_header parse_leaf_content a in
    let _ = gen_elim () in
    let major_type = read_header_major_type a in
    if major_type = cbor_major_type_array
    then begin
      let arg = read_header_argument_as_uint64 a in
      let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
      let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
      vpattern_rewrite (aparse _ a) va;
      let res = SZ.uint64_to_sizet arg in
      noop ();
      return res
    end
    else if major_type = cbor_major_type_map
    then begin
      let arg = read_header_argument_as_uint64 a in
      let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
      let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
      vpattern_rewrite (aparse _ a) va;
      let half = SZ.uint64_to_sizet arg in
      [@@inline_let]
      let res = size_add_fits half half bound () in
      noop ();
      return res
    end
    else begin
      let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
      let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
      vpattern_rewrite (aparse _ a) va;
      noop ();
      if major_type = cbor_major_type_tagged
      then begin
        noop ();
        noop ();
        return 1sz
      end
      else begin
        noop ();
        noop ();
        return 0sz
      end
    end

let jump_raw_data_item'
: jumper parse_raw_data_item
=
    jump_recursive
      parse_raw_data_item_param
      (jump_leaf)
      (jump_count_remaining_data_items)

let jump_raw_data_item
= fun a ->
    jump_raw_data_item' a

#pop-options
