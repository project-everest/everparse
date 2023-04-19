module CBOR.SteelST
include CBOR.Spec
open LowParse.SteelST.Combinators
open LowParse.SteelST.Recursive
open LowParse.SteelST.BitSum
open LowParse.SteelST.Int
open LowParse.SteelST.ValidateAndRead

#set-options "--print_universes"

inline_for_extraction
noextract
let validate_initial_byte : validate_and_read parse_initial_byte =
  validate_filter_and_read
    (validate_bitsum'
      filter_initial_byte
      destr_initial_byte
      (mk_validate_and_read
        validate_u8
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
      jump_u8
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
        jump_u8
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
      (additional_info = 24uy)
      (fun _ -> ifthenelse_validate_and_read
        (major_type = 7uy)
        (fun _ ->
          rewrite_validate_and_read
            (validate_and_read_weaken
              (strong_parser_kind 0 8 None)
              (validate_and_read_synth'
                (validate_filter_and_read
                  (mk_validate_and_read validate_u8 (cps_reader_of_leaf_reader read_u8))
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
                  (mk_validate_and_read validate_u8 (cps_reader_of_leaf_reader read_u8))
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
        (additional_info = 25uy)
        (fun _ ->
          rewrite_validate_and_read
            (validate_and_read_weaken
              (strong_parser_kind 0 8 None)
              (validate_and_read_synth'
                (validate_filter_and_read
                  (mk_validate_and_read validate_u16 (cps_reader_of_leaf_reader read_u16))
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
          (additional_info = 26uy)
          (fun _ ->
            rewrite_validate_and_read
              (validate_and_read_weaken
                (strong_parser_kind 0 8 None)
                (validate_and_read_synth'
                  (validate_filter_and_read
                    (mk_validate_and_read validate_u32 (cps_reader_of_leaf_reader read_u32))
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
            (additional_info = 27uy)
            (fun _ ->
              rewrite_validate_and_read
                (validate_and_read_weaken
                  (strong_parser_kind 0 8 None)
                  (validate_and_read_synth'
                    (validate_filter_and_read
                      (mk_validate_and_read validate_u64 (cps_reader_of_leaf_reader read_u64))
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
      (additional_info = 24uy)
      (fun _ -> ifthenelse_read_and_jump
        (major_type = 7uy)
        (fun _ ->
          rewrite_read_and_jump
            (read_and_jump_weaken
              (strong_parser_kind 0 8 None)
              (read_and_jump_synth'
                (read_and_jump_filter
                  (mk_read_and_jump (cps_reader_of_leaf_reader read_u8) jump_u8)
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
                  (mk_read_and_jump (cps_reader_of_leaf_reader read_u8) jump_u8)
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
        (additional_info = 25uy)
        (fun _ ->
          rewrite_read_and_jump
            (read_and_jump_weaken
              (strong_parser_kind 0 8 None)
              (read_and_jump_synth'
                (read_and_jump_filter
                  (mk_read_and_jump (cps_reader_of_leaf_reader read_u16) jump_u16)
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
          (additional_info = 26uy)
          (fun _ ->
            rewrite_read_and_jump
              (read_and_jump_weaken
                (strong_parser_kind 0 8 None)
                (read_and_jump_synth'
                  (read_and_jump_filter
                    (mk_read_and_jump (cps_reader_of_leaf_reader read_u32) jump_u32)
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
            (additional_info = 27uy)
            (fun _ ->
              rewrite_read_and_jump
                (read_and_jump_weaken
                  (strong_parser_kind 0 8 None)
                  (read_and_jump_synth'
                    (read_and_jump_filter
                      (mk_read_and_jump (cps_reader_of_leaf_reader read_u64) jump_u64)
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
let jump_header : read_and_jump parse_header =
  read_and_jump_dtuple2 read_and_jump_initial_byte _ jump_long_argument

module SZ = FStar.SizeT

inline_for_extraction
noextract
let validate_lseq_bytes
  (sz: SZ.t)
: Tot (validator (LowParse.Spec.SeqBytes.parse_lseq_bytes (SZ.v sz)))
= validate_total_constant_size _ sz

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
        (major_type = 2uy || major_type = 3uy)
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
let jump_lseq_bytes
  (sz: SZ.t)
: Tot (jumper (LowParse.Spec.SeqBytes.parse_lseq_bytes (SZ.v sz)))
= jump_constant_size _ sz

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
        (major_type = 2uy || major_type = 3uy)
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
let jump_leaf
  (sq: squash SZ.fits_u64)
: Tot (jumper parse_leaf) =
  jump_dtuple2_and_read_tag
    jump_header
    _
    (jump_leaf_content ())

(* FIXME: the current design of validate_recursive independently
   validates a leaf content before asking the number of expected
   children. In the general case, it is not possible to reuse the data
   read during validation for the computation of that number, unless
   the whole leaf is read, which we don't want here (we have byte
   strings.) *)

open Steel.ST.GenElim

module R = Steel.ST.Reference

inline_for_extraction
noextract
let count_remaining_data_items
  (sq: squash SZ.fits_u64)
: Tot (validate_recursive_step_count parse_raw_data_item_param)
= fun #va a bound perr ->
    let _ = rewrite_aparse a (parse_dtuple2 parse_header parse_leaf_content) in
    let ar = ghost_split_dtuple2 parse_header parse_leaf_content a in
    let _ = gen_elim () in
    let _ = ghost_dtuple2_tag parse_header parse_leaf_content a ar in
    let _ = gen_elim () in
    jump_header
      a
      (aparse _ ar _ `star` R.pts_to perr _ _)
      SZ.t
      (fun res ->
        aparse parse_raw_data_item_param.parse_header a va `star`
        exists_ (fun err ->
          R.pts_to perr full_perm err `star`
          pure (validate_recursive_step_count_post parse_raw_data_item_param va bound res err)
      ))
      (fun _ l ->
        let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
        let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
        match l with
        | (| b, long_arg |) ->
          match b with
          | (major_type, _) ->
            if major_type = 4uy
            then begin
              noop ();
              return (SZ.uint64_to_sizet (argument_as_uint64 b long_arg))
            end
            else if major_type = 5uy
            then begin
              let count = SZ.uint64_to_sizet (argument_as_uint64 b long_arg) in
              let overflow =
                if count `SZ.gt` bound
                then true
                else count `SZ.gt` (bound `SZ.sub` count)
              in
              if overflow
              then begin
                R.write perr validator_error_not_enough_data;
                return 0sz
              end
              else begin
//                SZ.fits_lte (SZ.v count + SZ.v count) (SZ.v bound);
                let count' = count `SZ.add` count in
                noop ();
                return count'
              end
            end
            else if major_type = 6uy
            then begin
              noop ();
              return 1sz
            end
            else begin
              noop ();
              return 0sz
            end
      )

inline_for_extraction
noextract
let validate_raw_data_item'
  (sq: squash SZ.fits_u64)
: Tot (validator parse_raw_data_item)
=
    validate_recursive
      parse_raw_data_item_param
      (validate_leaf ())
      (count_remaining_data_items ())

let validate_raw_data_item
: validator parse_raw_data_item
= fun a len err ->
    let sq = Steel.ST.HigherArray.intro_fits_u64 () in
    validate_raw_data_item' sq a len err

inline_for_extraction
noextract
let jump_count_remaining_data_items
  (sq: squash SZ.fits_u64)
: Tot (jump_recursive_step_count parse_raw_data_item_param)
= fun #va a bound ->
    let _ = rewrite_aparse a (parse_dtuple2 parse_header parse_leaf_content) in
    let ar = ghost_split_dtuple2 parse_header parse_leaf_content a in
    let _ = gen_elim () in
    let _ = ghost_dtuple2_tag parse_header parse_leaf_content a ar in
    let _ = gen_elim () in
    let res = jump_header
      a
      (aparse _ ar _)
      SZ.t
      (fun res ->
        aparse parse_raw_data_item_param.parse_header a va `star`
        pure (SZ.v res == parse_raw_data_item_param.count va.contents)
      )
      (fun _ l ->
        let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
        let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
        match l with
        | (| b, long_arg |) ->
          match b with
          | (major_type, _) ->
            if major_type = 4uy
            then begin
              noop ();
              return (SZ.uint64_to_sizet (argument_as_uint64 b long_arg))
            end
            else if major_type = 5uy
            then begin
              let count = SZ.uint64_to_sizet (argument_as_uint64 b long_arg) in
              let count' = count `SZ.add` count in
              noop ();
              return count'
            end
            else if major_type = 6uy
            then begin
              noop ();
              return 1sz
            end
            else begin
              noop ();
              return 0sz
            end
      )
    in
    elim_pure _;
    return res

inline_for_extraction
noextract
let jump_raw_data_item'
  (sq: squash SZ.fits_u64)
: Tot (jumper parse_raw_data_item)
=
    jump_recursive
      parse_raw_data_item_param
      (jump_leaf ())
      (jump_count_remaining_data_items ())

let jump_raw_data_item
: jumper parse_raw_data_item
= fun a ->
    let sq = Steel.ST.HigherArray.intro_fits_u64 () in
    jump_raw_data_item' sq a
