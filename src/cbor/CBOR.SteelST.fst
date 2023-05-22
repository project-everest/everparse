module CBOR.SteelST
include CBOR.Spec
open LowParse.SteelST.Combinators
open LowParse.SteelST.Recursive
open LowParse.SteelST.BitSum
open LowParse.SteelST.ValidateAndRead
open LowParse.SteelST.SeqBytes
open Steel.ST.GenElim

module I = LowParse.SteelST.Int
module AP = LowParse.SteelST.ArrayPtr

let read_u8 = I.read_u8

#set-options "--print_universes"

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

let read_u16 = I.read_u16
let read_u32 = I.read_u32
let read_u64 = I.read_u64

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
        (additional_info = 25uy)
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
          (additional_info = 26uy)
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
            (additional_info = 27uy)
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
      (additional_info = 24uy)
      (fun _ -> ifthenelse_read_and_jump
        (major_type = 7uy)
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
        (additional_info = 25uy)
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
          (additional_info = 26uy)
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
            (additional_info = 27uy)
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

let jump_header : jumper parse_header =
  jumper_of_read_and_jump read_and_jump_header

module SZ = FStar.SizeT

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

module R = Steel.ST.Reference

#set-options "--ide_id_info_off"

#push-options "--z3rlimit 16 --split_queries always"

let get_major_type_synth_raw_data_item
  (x: raw_data_item')
: Lemma
  (get_major_type (synth_raw_data_item x) == (match x with (| (| (major_type, _), _ |), _ |) -> major_type))
  [SMTPat (synth_raw_data_item x)]
= assert_norm (pow2 3 == 8)

noextract
let get_header_major_type
  (h: header)
: Tot major_type_t
= let (| (major_type, _), _ |) = h in
  major_type

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

let get_raw_data_item_header
  (x: raw_data_item)
: GTot header
= dfst (synth_raw_data_item_recip x)

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

noextract
let get_header_argument_as_uint64
  (h: header)
: Tot UInt64.t
= let (| b, l |) = h in
  argument_as_uint64 b l

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

let read_argument_as_uint64
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST UInt64.t
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    True
    (fun res ->
      let (| (| b, x |), _ |) = synth_raw_data_item_recip va.contents in
      res == argument_as_uint64 b x
    )
= Classical.forall_intro parse_raw_data_item_eq;
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

let count_remaining_data_items
: (validate_recursive_step_count parse_raw_data_item_param)
= fun #va a bound perr ->
    let sq = Steel.ST.HigherArray.intro_fits_u64 () in
    let _ = rewrite_aparse a parse_leaf in
    let ar = ghost_split_dtuple2_full parse_header parse_leaf_content a in
    let _ = gen_elim () in
    let major_type = read_header_major_type a in
    if major_type = 4uy
    then begin
      let arg = read_header_argument_as_uint64 a in
      let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
      let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
      vpattern_rewrite (aparse _ a) va;
      let res = SZ.uint64_to_sizet arg in
      noop ();
      return res
    end
    else if major_type = 5uy
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
      if major_type = 6uy
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

inline_for_extraction
noextract
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
    if major_type = 4uy
    then begin
      let arg = read_header_argument_as_uint64 a in
      let _ = intro_dtuple2 parse_header parse_leaf_content a ar in
      let _ = rewrite_aparse a parse_raw_data_item_param.parse_header in
      vpattern_rewrite (aparse _ a) va;
      let res = SZ.uint64_to_sizet arg in
      noop ();
      return res
    end
    else if major_type = 5uy
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
      if major_type = 6uy
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

let jump_raw_data_item
: jumper parse_raw_data_item
=
    jump_recursive
      parse_raw_data_item_param
      (jump_leaf)
      (jump_count_remaining_data_items)

(* 4.2 Ordering of map keys *)

module NL = LowParse.SteelST.VCList.Sorted
module SB = LowParse.SteelST.SeqBytes

inline_for_extraction
noextract
let map_entry_order_impl
  (#kkey: Ghost.erased parser_kind)
  (#key: Type0)
  (pkey: parser kkey key)
  (#key_order: Ghost.erased (key -> key -> bool))
  (key_order_impl: NL.order_impl pkey key_order)
  (#kvalue: Ghost.erased parser_kind)
  (#value: Type0)
  (pvalue: parser kvalue value)
: Pure (NL.order_impl (pkey `nondep_then` pvalue) (map_entry_order key_order value))
    (requires (kkey.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #va1 #va2 a1 a2 ->
    let av1 = g_split_pair pkey pvalue a1 in
    let _ = gen_elim () in
    let av2 = g_split_pair pkey pvalue a2 in
    let _ = gen_elim () in
    let res = key_order_impl a1 a2 in
    let _ = merge_pair pkey pvalue a1 av1 in
    vpattern_rewrite (aparse _ a1) va1;
    let _ = merge_pair pkey pvalue a2 av2 in
    vpattern_rewrite (aparse _ a2) va2;
    return res

#restart-solver
unfold
let get_raw_data_item_payload_map_post
  (va: v parse_raw_data_item_kind raw_data_item)
  (vh: v (get_parser_kind parse_header) header)
  (n: nat)
  (vc: v (NL.parse_nlist_kind n (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)) (NL.nlist n (raw_data_item & raw_data_item)))
: GTot prop
=
        let (| h, c |) = synth_raw_data_item_recip va.contents in
        let (| b, x |) = h in
        // order of the following conjuncts matters for typechecking
        vh.contents == h /\
        n == UInt64.v (argument_as_uint64 b x) /\
        va.contents == Map vc.contents /\
        vc.contents == c /\
        AP.merge_into (array_of' vh) (array_of' vc) (array_of va)

#set-options "--ide_id_info_off"

let elim_synth'
  #opened
  #k1 #t1 (p1: parser k1 t1)
  #t2 (f2: t1 -> GTot t2) (g1: t2 -> GTot t1)
  #va2 (a: byte_array)
  (sq: squash (synth_injective f2 /\
    synth_inverse f2 g1
  ))
: STGhost (v k1 t1) opened
    (aparse (p1 `parse_synth` f2) a va2)
    (fun va -> aparse p1 a va)
    True
    (fun va ->
      array_of va2 == array_of va /\
      va2.contents == f2 (va.contents) /\
      va.contents == g1 va2.contents
    )
= let va = elim_synth p1 f2 a () in
  assert (f2 (g1 va2.contents) == va2.contents);
  noop ();
  va

let get_raw_data_item_payload_map
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vh -> exists_ (fun (n: nat) -> exists_ (fun vc ->
      aparse parse_header a vh `star`
      aparse (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) a' vc `star`
      pure (get_raw_data_item_payload_map_post va vh n vc)
    ))))
    (Map? va.contents)
    (fun _ -> True)
= Classical.forall_intro parse_raw_data_item_eq;
  let _ = rewrite_aparse a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let va1 = elim_synth' _ _ synth_raw_data_item_recip a () in // (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
  let a' = ghost_split_dtuple2_full _ _ a in // parse_header (parse_content parse_raw_data_item) a in
  let _ = gen_elim () in
  let vh = vpattern_replace (aparse _ a) in
  let (| b, x |) = vh.contents in
  let n = UInt64.v (argument_as_uint64 b x) in
  let vc = rewrite_aparse a' (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) in
  assert (get_raw_data_item_payload_map_post va vh n vc);
  noop ();
  a'

let intro_raw_data_item_map
  (#opened: _)
  (#vh: v (get_parser_kind parse_header) header)
  (h: byte_array)
  (#n: nat)
  (#vc: v (NL.parse_nlist_kind n (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)) (NL.nlist n (raw_data_item & raw_data_item)))
  (c: byte_array)
: STGhost (v parse_raw_data_item_kind raw_data_item) opened
    (aparse parse_header h vh `star`
      aparse (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) c vc
    )
    (fun va -> aparse parse_raw_data_item h va)
    (
      let (| b, x |) = vh.contents in
      let (major_type, _) = b in
      n == UInt64.v (argument_as_uint64 b x) /\
      major_type == get_major_type (Map vc.contents) /\
      AP.adjacent (array_of' vh) (array_of' vc)
    )
    (fun va ->
      get_raw_data_item_payload_map_post va vh n vc
    )
= Classical.forall_intro parse_raw_data_item_eq;
  let h' = uint64_as_argument (get_major_type (Map vc.contents)) (UInt64.uint_to_t n) in
  assert (vh.contents == h');
  noop ();
  let _ = rewrite_aparse c (parse_content parse_raw_data_item vh.contents) in
  let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) h c in
  let _ = intro_synth (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item h () in 
  rewrite_aparse h parse_raw_data_item

#restart-solver
inline_for_extraction
noextract
let check_data_item_wf_head
  (#order: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (order_impl: NL.order_impl parse_raw_data_item order)
  (sq: squash (SZ.fits_u64))
: Tot (pred_recursive_base_t serialize_raw_data_item_param (data_item_wf_head order))
= fun a va ->
  rewrite (aparse _ a _) (aparse parse_raw_data_item a va);
  let major_type = read_major_type a in
  if major_type = 5uy
  then begin
    let n64 = read_argument_as_uint64 a in
    let n = SZ.uint64_to_sizet n64 in
    let gac = get_raw_data_item_payload_map a in
    let _ = gen_elim () in
    let ac = hop_aparse_aparse jump_header _ a gac in
    let _ = rewrite_aparse ac (NL.parse_nlist (SZ.v n) (parse_raw_data_item `nondep_then` parse_raw_data_item)) in
    let res = NL.nlist_sorted
      (jump_pair jump_raw_data_item jump_raw_data_item)
      (map_entry_order_impl _ order_impl _)
      n
      _
      ac
    in
    let _ = intro_raw_data_item_map a ac in
    rewrite (aparse _ a _) (aparse (parse_recursive parse_raw_data_item_param) a va);
    return res
  end else begin
    rewrite (aparse _ a _) (aparse (parse_recursive parse_raw_data_item_param) a va);
    return true
  end

inline_for_extraction
noextract
let validate_data_item'
  (#order: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (order_impl: NL.order_impl parse_raw_data_item order)
  (sq: squash (SZ.fits_u64))
: Tot (validator (parse_data_item order))
= rewrite_validator
    (validate_filter_gen
      validate_raw_data_item
      (data_item_wf order)
      (fun #va a ->
        rewrite (aparse _ a _) (aparse (parse_recursive parse_raw_data_item_param) a va);
        let res = pred_recursive
          serialize_raw_data_item_param
          (jump_leaf)
          (jump_count_remaining_data_items)
          a
          (data_item_wf_pred order)
          (check_data_item_wf_head order_impl sq)
        in
        rewrite (aparse _ a _) (aparse parse_raw_data_item a va);
        return res
      )
    )
    (parse_data_item order)

#pop-options

inline_for_extraction
noextract
let validate_data_item
  (#order: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (order_impl: NL.order_impl parse_raw_data_item order)
: Tot (validator (parse_data_item order))
= fun a len err ->
    let sq = Steel.ST.HigherArray.intro_fits_u64 () in
    validate_data_item' order_impl sq a len err

let deterministically_encoded_cbor_map_key_order_impl
: NL.order_impl parse_raw_data_item deterministically_encoded_cbor_map_key_order
= fun #va1 #va2 a1 a2 ->
    let n1 = get_parsed_size jump_raw_data_item a1 in
    let n2 = get_parsed_size jump_raw_data_item a2 in
    let vb1 = elim_aparse_with_serializer serialize_raw_data_item a1 in
    let vb2 = elim_aparse_with_serializer serialize_raw_data_item a2 in
    let res = LowParse.SteelST.SeqBytes.byte_array_lex_order n1 a1 n2 a2 in
    let _ = intro_aparse parse_raw_data_item a1 in
    let _ = intro_aparse parse_raw_data_item a2 in
    vpattern_rewrite (aparse _ a1) va1;
    vpattern_rewrite (aparse _ a2) va2;
    return res

let validate_deterministically_encoded_cbor_data_item
: validator (parse_data_item deterministically_encoded_cbor_map_key_order)
= validate_data_item deterministically_encoded_cbor_map_key_order_impl

let canonical_cbor_map_key_order_impl
: NL.order_impl parse_raw_data_item canonical_cbor_map_key_order
= fun #va1 #va2 a1 a2 ->
    let n1 = get_parsed_size jump_raw_data_item a1 in
    let n2 = get_parsed_size jump_raw_data_item a2 in
    let vb1 = elim_aparse_with_serializer serialize_raw_data_item a1 in
    let vb2 = elim_aparse_with_serializer serialize_raw_data_item a2 in
    let res = LowParse.SteelST.SeqBytes.byte_array_length_first_lex_order n1 a1 n2 a2 in
    let _ = intro_aparse parse_raw_data_item a1 in
    let _ = intro_aparse parse_raw_data_item a2 in
    vpattern_rewrite (aparse _ a1) va1;
    vpattern_rewrite (aparse _ a2) va2;
    return res

let validate_canonical_cbor_data_item
: validator (parse_data_item canonical_cbor_map_key_order)
= validate_data_item canonical_cbor_map_key_order_impl

let jump_data_item
  (order: Ghost.erased (raw_data_item -> raw_data_item -> bool))
: Tot (jumper (parse_data_item order))
= jump_filter
    jump_raw_data_item
    (data_item_wf order)

(* Readers and accessors *)

module U8 = FStar.UInt8

let get_header_argument_as_simple_value_initial_byte_precond
  (b: initial_byte)
: GTot bool
= 
  let (major_type, (additional_info, _)) = b in
  major_type = 7uy && additional_info `U8.lte` 24uy

(* Here we only retain the two cases for simple values. Otherwise, if
   we use the general-purpose jump_long_argument, F* extracts to
   `match B with A -> ...` with mismatching constructors, which neither F*
   nor Karamel eliminate as dead code.
 *)

inline_for_extraction
noextract
let jump_long_argument_as_simple_value
  (b: parse_filter_refine get_header_argument_as_simple_value_initial_byte_precond)
: Tot (read_and_jump (parse_long_argument b))
= match b with
  | (major_type, (additional_info, _)) ->
    ifthenelse_read_and_jump
      (additional_info = 24uy)
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
               (mk_read_and_jump (cps_reader_of_leaf_reader read_empty) jump_empty)
               (LongArgumentOther #b additional_info ())
               ()
             )
             ()
           )
           (parse_long_argument b)
      )

let get_header_argument_as_simple_value_precond
  (h: header)
: GTot bool
=
      let (| b, x |) = h in
      get_header_argument_as_simple_value_initial_byte_precond b

let get_header_argument_as_simple_value
  (h: header)
: Ghost simple_value
  (requires (get_header_argument_as_simple_value_precond h))
  (ensures (fun _ -> True))
= let (| b, x |) = h in
  argument_as_simple_value b x

inline_for_extraction
noextract
let read_header_argument_as_simple_value
  (#va: v (get_parser_kind parse_header) header)
  (a: byte_array)
: ST simple_value
    (aparse parse_header a va)
    (fun _ -> aparse parse_header a va)
    (get_header_argument_as_simple_value_precond va.contents)
    (fun res -> 
      let (| b, x |) = va.contents in
      let (major_type, (additional_info, _)) = b in
      major_type = 7uy /\ additional_info `U8.lte` 24uy /\
      res == argument_as_simple_value b x
    )
= rewrite (aparse parse_header a va) (aparse (parse_dtuple2 parse_initial_byte parse_long_argument) a va);
  let _ = intro_dtuple2_filter_tag parse_initial_byte get_header_argument_as_simple_value_initial_byte_precond parse_long_argument a in
  let res = read_and_jump_dtuple2
    (read_and_jump_filter read_and_jump_initial_byte get_header_argument_as_simple_value_initial_byte_precond)
    parse_long_argument
    jump_long_argument_as_simple_value
    a
    emp
    simple_value
    (fun res -> aparse parse_header a va `star` pure (
      get_header_argument_as_simple_value_precond va.contents == true /\
      res == get_header_argument_as_simple_value va.contents
    ))
    (fun _ (| b, x |) ->
      let _ = elim_dtuple2_filter_tag parse_initial_byte get_header_argument_as_simple_value_initial_byte_precond parse_long_argument a in
      rewrite (aparse (parse_dtuple2 parse_initial_byte parse_long_argument) a _) (aparse parse_header a va);
      return (argument_as_simple_value b x)
    )
  in
  let _ = elim_pure _ in
  return res

#push-options "--z3rlimit 16"
#restart-solver

let read_simple_value
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST simple_value
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    (Simple? va.contents)
    (fun res -> va.contents == Simple res)
= Classical.forall_intro parse_raw_data_item_eq;
  let _ = rewrite_aparse a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let va1 = elim_synth _ _ a () in
  let a_content = ghost_split_dtuple2_full _ _ a in // parse_header (parse_content parse_raw_data_item) a in
  let _ = gen_elim () in
  let res = read_header_argument_as_simple_value a in
  let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a_content in
  let _ = intro_synth (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
  let _ = rewrite_aparse a parse_raw_data_item in
  vpattern_rewrite (aparse parse_raw_data_item a) va;
  return res

#pop-options

module U64 = FStar.UInt64

let read_uint64
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST U64.t
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    (UInt64? va.contents)
    (fun res -> va.contents == UInt64 res)
= read_argument_as_uint64 a

let read_neg_int64
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST U64.t
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    (NegInt64? va.contents)
    (fun res -> va.contents == NegInt64 res)
= read_argument_as_uint64 a

(* Writers *)

let write_u8 = I.write_u8

let write_initial_byte
  (t: major_type_t)
  (x: additional_info_t)
  (sq: squash (
    initial_byte_wf (t, (x, ()))
  ))
  (#va: AP.v byte)
  (a: byte_array)
: ST (v (get_parser_kind parse_initial_byte) initial_byte)
    (AP.arrayptr a va)
    (fun va' ->
      aparse parse_initial_byte a va'
    )
    (AP.length (AP.array_of va) == 1 /\
      AP.array_perm (AP.array_of va) == full_perm
    )
    (fun va' -> 
       array_of' va' == AP.array_of va /\
       va'.contents == mk_initial_byte t x
    )
= let _ = exact_write (write_bitsum' mk_synth_initial_byte (write_constant_size write_u8 1sz)) (mk_initial_byte t x) a in
  let _ = intro_filter _ initial_byte_wf a in
  rewrite_aparse a parse_initial_byte

inline_for_extraction
noextract
let write_initial_byte'
: exact_writer serialize_initial_byte
= fun x a ->
  match x with
  | (major_type, (additional_info, _)) ->
    write_initial_byte major_type additional_info () a

module Cast = FStar.Int.Cast

noextract
let parse_long_argument_kind = strong_parser_kind 0 8 None

let write_u16 = I.write_u16
let write_u32 = I.write_u32
let write_u64 = I.write_u64

#push-options "--z3rlimit 16"

(* In fact, I can follow the structure of the type instead. Indeed, the
   data constructors for long_argument do follow the structure of the ifthenelse
   in the parser or the serializer: each branch of the match corresponds to exactly 
   one branch of the ifthenelse.
*)
#restart-solver
inline_for_extraction
noextract
let write_long_argument
  (b: initial_byte)
  (a: long_argument b)
: Tot (r2l_writer_for (serialize_long_argument b) a)
= match a with
  | LongArgumentSimpleValue _ _ ->
    rewrite_r2l_writer
      #_ #(long_argument b)
      (r2l_write_weaken parse_long_argument_kind
        (r2l_write_synth'
          (r2l_write_filter
            (r2l_write_constant_size write_u8 1sz)
            simple_value_long_argument_wf
          )
          (LongArgumentSimpleValue ())
          LongArgumentSimpleValue?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU8 _ _ ->
    rewrite_r2l_writer
      #_ #(long_argument b)
      (r2l_write_weaken parse_long_argument_kind
        (r2l_write_synth'
          (r2l_write_filter
            (r2l_write_constant_size write_u8 1sz)
            uint8_wf
          )
          (LongArgumentU8 ())
          LongArgumentU8?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU16 _ _ ->
    rewrite_r2l_writer
      #_ #(long_argument b)
      (r2l_write_weaken parse_long_argument_kind
        (r2l_write_synth'
          (r2l_write_filter
            (r2l_write_constant_size write_u16 2sz)
            uint16_wf
          )
          (LongArgumentU16 ())
          LongArgumentU16?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU32 _ _ ->
    rewrite_r2l_writer
      #_ #(long_argument b)
      (r2l_write_weaken parse_long_argument_kind
        (r2l_write_synth'
          (r2l_write_filter
            (r2l_write_constant_size write_u32 4sz)
            uint32_wf
          )
          (LongArgumentU32 ())
          LongArgumentU32?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU64 _ _ ->
    rewrite_r2l_writer
      #_ #(long_argument b)
      (r2l_write_weaken parse_long_argument_kind
        (r2l_write_synth'
          (r2l_write_filter
            (r2l_write_constant_size write_u64 8sz)
            uint64_wf
          )
          (LongArgumentU64 ())
          LongArgumentU64?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentOther additional_info _ _ ->
    rewrite_r2l_writer
      #_ #(long_argument b)
      (r2l_write_weaken parse_long_argument_kind
        (r2l_write_synth'
          (r2l_write_constant_size exact_write_empty 0sz)
          (LongArgumentOther additional_info ())
          LongArgumentOther?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a

#pop-options

inline_for_extraction
noextract
let write_header : r2l_writer serialize_header
=
  r2l_write_dtuple2
    (r2l_write_constant_size write_initial_byte' 1sz)
    write_long_argument

inline_for_extraction
noextract
let cps_uint64_as_argument
  (t': Type)
  (t'_ifthenelse: if_combinator_weak t')
  (ty: major_type_t { ty `U8.lt` 7uy })
  (x: U64.t)
  (k: (h: header) -> Pure t'
    (requires (h == uint64_as_argument ty x))
    (ensures (fun _ -> True))
  )
: Tot t'
= t'_ifthenelse (x `U64.lt` 24uL)
    (fun _ -> k (| mk_initial_byte ty (Cast.uint64_to_uint8 x), LongArgumentOther (Cast.uint64_to_uint8 x) () () |))
    (fun _ -> t'_ifthenelse (x `U64.lt` 256uL)
      (fun _ -> k (| mk_initial_byte ty 24uy, LongArgumentU8 () (Cast.uint64_to_uint8 x) |))
      (fun _ -> t'_ifthenelse (x `U64.lt` 65536uL)
        (fun _ -> k (| mk_initial_byte ty 25uy, LongArgumentU16 () (Cast.uint64_to_uint16 x) |))
        (fun _ -> t'_ifthenelse (x `U64.lt` 4294967296uL)
          (fun _ -> k (| mk_initial_byte ty 26uy, LongArgumentU32 () (Cast.uint64_to_uint32 x) |))
          (fun _ -> k (| mk_initial_byte ty 27uy, LongArgumentU64 () x |))
        )
      )
    )

let write_uint64_as_argument
  (ty: major_type_t { ty `U8.lt` 7uy })
  (x: U64.t)
: Tot (r2l_writer_for serialize_header (uint64_as_argument ty x))
= cps_uint64_as_argument
    (r2l_writer_for serialize_header (uint64_as_argument ty x))
    (ifthenelse_r2l_writer_for serialize_header (uint64_as_argument ty x))
    ty
    x
    (fun h out ->
      let res = write_header h out in
      vpattern_rewrite
        (fun v -> maybe_r2l_write serialize_header out _ v _)
        (uint64_as_argument ty x);
      return res
    )

module W = LowParse.SteelST.R2LOutput

#push-options "--z3rlimit 32 --split_queries always"
#restart-solver

let maybe_r2l_write_uint64
  (#opened: _)
  (x: U64.t)
  (#vout: _)
  (out: W.t)
  (success: bool)
: STGhostT unit opened
   (maybe_r2l_write serialize_header out vout (uint64_as_argument 0uy x) success)
   (fun _ -> maybe_r2l_write serialize_raw_data_item out vout (UInt64 x) success)
= if success
  then begin
    let a = ghost_elim_r2l_write_success serialize_header out in
    let _ = gen_elim () in
    let a' = aparse_split_zero_r parse_header a in
    let _ = gen_elim () in
    let _ = intro_aparse parse_empty a' in
    let _ = rewrite_aparse a' (parse_content parse_raw_data_item (uint64_as_argument 0uy x)) in
    let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a' in
    Classical.forall_intro parse_raw_data_item_eq;
    let _ = intro_synth _ synth_raw_data_item a () in
    let _ = rewrite_aparse a parse_raw_data_item in
    intro_r2l_write_success serialize_raw_data_item out vout (UInt64 x) _ _ _;
    vpattern_rewrite (maybe_r2l_write serialize_raw_data_item out vout (UInt64 x)) success
  end else begin
    elim_r2l_write_failure serialize_header out;
    serialize_raw_data_item_aux_correct (UInt64 x);
    serialize_synth_eq (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item (serialize_dtuple2 serialize_header serialize_content) synth_raw_data_item_recip () (UInt64 x);
    serialize_dtuple2_eq serialize_header serialize_content (| uint64_as_argument 0uy x, () |);
    noop ();
    intro_r2l_write_failure serialize_raw_data_item out vout (UInt64 x);
    vpattern_rewrite (maybe_r2l_write serialize_raw_data_item out vout (UInt64 x)) success
  end

#pop-options

let write_uint64
  (x: U64.t)
: Tot (r2l_writer_for serialize_raw_data_item (UInt64 x))
= fun out ->
    let res = write_uint64_as_argument 0uy x out in
    maybe_r2l_write_uint64 x out res;
    return res

#push-options "--z3rlimit 32 --split_queries always"
#restart-solver

let maybe_r2l_write_neg_int64
  (#opened: _)
  (x: U64.t)
  (#vout: _)
  (out: W.t)
  (success: bool)
: STGhostT unit opened
   (maybe_r2l_write serialize_header out vout (uint64_as_argument 1uy x) success)
   (fun _ -> maybe_r2l_write serialize_raw_data_item out vout (NegInt64 x) success)
= if success
  then begin
    let a = ghost_elim_r2l_write_success serialize_header out in
    let _ = gen_elim () in
    let a' = aparse_split_zero_r parse_header a in
    let _ = gen_elim () in
    let _ = intro_aparse parse_empty a' in
    let _ = rewrite_aparse a' (parse_content parse_raw_data_item (uint64_as_argument 1uy x)) in
    let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a' in
    Classical.forall_intro parse_raw_data_item_eq;
    let _ = intro_synth _ synth_raw_data_item a () in
    let _ = rewrite_aparse a parse_raw_data_item in
    intro_r2l_write_success serialize_raw_data_item out vout (NegInt64 x) _ _ _;
    vpattern_rewrite (maybe_r2l_write serialize_raw_data_item out vout (NegInt64 x)) success
  end else begin
    elim_r2l_write_failure serialize_header out;
    serialize_raw_data_item_aux_correct (NegInt64 x);
    serialize_synth_eq (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item (serialize_dtuple2 serialize_header serialize_content) synth_raw_data_item_recip () (NegInt64 x);
    serialize_dtuple2_eq serialize_header serialize_content (| uint64_as_argument 1uy x, () |);
    noop ();
    intro_r2l_write_failure serialize_raw_data_item out vout (NegInt64 x);
    vpattern_rewrite (maybe_r2l_write serialize_raw_data_item out vout (NegInt64 x)) success
  end

#pop-options

let write_neg_int64
  (x: U64.t)
: Tot (r2l_writer_for serialize_raw_data_item (NegInt64 x))
= fun out ->
    let res = write_uint64_as_argument 1uy x out in
    maybe_r2l_write_neg_int64 x out res;
    return res

let ifthenelse_vprop
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
: Tot vprop
= if cond
  then vtrue ()
  else vfalse ()

let intro_ifthenelse_vprop_true
  (#opened: _)
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
  (cond_true: squash (cond == true))
: STGhostT unit opened
    (vtrue ())
    (fun _ -> ifthenelse_vprop cond vtrue vfalse)
= rewrite
    (vtrue ())
    (ifthenelse_vprop cond vtrue vfalse)

let intro_ifthenelse_vprop_false
  (#opened: _)
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
  (cond_false: squash (cond == false))
: STGhostT unit opened
    (vfalse ())
    (fun _ -> ifthenelse_vprop cond vtrue vfalse)
= rewrite
    (vfalse ())
    (ifthenelse_vprop cond vtrue vfalse)

let elim_ifthenelse_vprop_true
  (#opened: _)
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
  (sq: squash (cond == true))
: STGhostT unit opened
    (ifthenelse_vprop cond vtrue vfalse)
    (fun _ -> vtrue ())
= rewrite
    (ifthenelse_vprop cond vtrue vfalse)
    (vtrue ())

let elim_ifthenelse_vprop_false
  (#opened: _)
  (cond: bool)
  (vtrue: squash (cond == true) -> vprop)
  (vfalse: squash (cond == false) -> vprop)
  (sq: squash (cond == false))
: STGhostT unit opened
    (ifthenelse_vprop cond vtrue vfalse)
    (fun _ -> vfalse ())
= rewrite
    (ifthenelse_vprop cond vtrue vfalse)
    (vfalse ())

#push-options "--z3rlimit 16"
#restart-solver

let intro_raw_data_item_byte_string
  (#opened: _)
  (#vh: v (get_parser_kind parse_header) header)
  (ah: byte_array)
  (#vp: _)
  (ap: byte_array)
: STGhost (v parse_raw_data_item_kind raw_data_item) opened
    (aparse parse_header ah vh `star` AP.arrayptr ap vp)
    (fun v' -> aparse parse_raw_data_item ah v')
    (
      let (| b, arg |) = vh.contents in
      let (major_type, _) = b in
      major_type == 2uy /\
      AP.adjacent (array_of vh) (AP.array_of vp) /\
      U64.v (argument_as_uint64 b arg) == Seq.length (AP.contents_of vp)
    )
    (fun v' ->
      let (| b, arg |) = vh.contents in
      AP.merge_into (array_of vh) (AP.array_of vp) (array_of v') /\
      U64.v (argument_as_uint64 b arg) == Seq.length (AP.contents_of vp) /\
      v'.contents == ByteString (AP.contents_of vp)
    )
=
  let (| b, arg |) = vh.contents in
  let _ = intro_lseq_bytes (U64.v (argument_as_uint64 b arg)) ap in
  let _ = rewrite_aparse ap (parse_content parse_raw_data_item vh.contents) in
  let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) ah ap in
  let _ = intro_synth _ synth_raw_data_item ah () in
  Classical.forall_intro parse_raw_data_item_eq;
  noop ();
  rewrite_aparse ah parse_raw_data_item

let ghost_focus_byte_string_post
  (va: v parse_raw_data_item_kind raw_data_item)
  (vp: AP.v byte)
: GTot prop
=
        FStar.UInt.fits (Seq.length (AP.contents_of vp)) U64.n /\
        va.contents == ByteString (AP.contents_of vp)

let finalize_raw_data_item_byte_string_failure
  (vout: AP.array byte)
  (vp: AP.v byte)
: GTot prop
= 
  FStar.UInt.fits (Seq.length (AP.contents_of vp)) U64.n /\
  Seq.length (serialize serialize_raw_data_item (ByteString (AP.contents_of vp))) > AP.length vout + AP.length (AP.array_of vp)

[@@__reduce__]
let finalize_raw_data_item_byte_string_post
  (vout: AP.array byte)
  (out: W.t)
  (vp: AP.v byte)
  (ap: byte_array)
  (res: bool)
: Tot vprop
=
      ifthenelse_vprop
        res
        (fun _ -> exists_ (fun vout' -> exists_ (fun a -> exists_ (fun va ->
          aparse parse_raw_data_item a va `star`
          W.vp out vout' `star`
          pure (
            AP.adjacent vout (AP.array_of vp) /\
            AP.merge_into vout' (array_of va) (AP.merge vout (AP.array_of vp)) /\
            ghost_focus_byte_string_post va vp
        )))))
        (fun _ ->
          pure (finalize_raw_data_item_byte_string_failure vout vp) `star`
          W.vp out vout `star` AP.arrayptr ap vp
        )

#push-options "--z3rlimit 32"
#restart-solver

let maybe_finalize_raw_data_item_byte_string
  (#opened: _)
  (#vout: _)
  (out: W.t)
  (#vp: _)
  (ap: byte_array)
  (len: U64.t)
  (res: bool)
: STGhost unit opened
    (maybe_r2l_write serialize_header out vout (uint64_as_argument 2uy len) res `star`
      AP.arrayptr ap vp
    )
    (fun _ ->
      finalize_raw_data_item_byte_string_post vout out vp ap res
    )
    (U64.v len == AP.length (AP.array_of vp) /\
      AP.adjacent vout (AP.array_of vp)
    )
    (fun _ -> True)
=
  if res
  then begin
      let ah = ghost_elim_r2l_write_success serialize_header out in
      let _ = gen_elim () in
      let _ = intro_raw_data_item_byte_string ah ap in
      noop ();
      intro_ifthenelse_vprop_true res _ _ ()
    end else begin
      elim_r2l_write_failure serialize_header out;
      serialize_raw_data_item_aux_correct (ByteString (AP.contents_of vp));
      serialize_synth_eq _ synth_raw_data_item (serialize_dtuple2 serialize_header serialize_content) synth_raw_data_item_recip () (ByteString (AP.contents_of vp));
      serialize_dtuple2_eq serialize_header serialize_content (| uint64_as_argument 2uy len, AP.contents_of vp |);
      noop ();
      intro_ifthenelse_vprop_false res _ _ ()
    end

#pop-options

let finalize_raw_data_item_byte_string
  (#vout: _)
  (out: W.t)
  (#vp: _)
  (ap: Ghost.erased byte_array)
  (len: U64.t)
: ST bool
    (W.vp out vout `star` AP.arrayptr ap vp)
    (fun res -> finalize_raw_data_item_byte_string_post vout out vp ap res)
    (U64.v len == AP.length (AP.array_of vp) /\
      AP.adjacent vout (AP.array_of vp)
    )
    (fun _ -> True)
= let res = write_uint64_as_argument 2uy len out in
  maybe_finalize_raw_data_item_byte_string out ap len res;
  return res

let elim_raw_data_item_byte_string_post
  (va: v parse_raw_data_item_kind raw_data_item)
  (vh: v (get_parser_kind parse_header) header)
  (vp: AP.v byte)
: GTot prop
= 
      let (| b, arg |) = vh.contents in
      let (major_type, _) = b in
      major_type == 2uy /\
      AP.merge_into (array_of vh) (AP.array_of vp) (array_of va) /\
      U64.v (argument_as_uint64 b arg) == Seq.length (AP.contents_of vp) /\
      va.contents == ByteString (AP.contents_of vp)

let elim_raw_data_item_byte_string
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun (vh: v (get_parser_kind parse_header) header) -> exists_ (fun vp ->
      aparse parse_header a vh `star`
      AP.arrayptr a' vp `star`
      pure (elim_raw_data_item_byte_string_post va vh vp)
    )))
    (ByteString? va.contents)
    (fun _ -> True)
= 
  Classical.forall_intro parse_raw_data_item_eq;
  noop ();
  let _ = rewrite_aparse a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let _ = elim_synth _ _ a () in
  let a' = ghost_split_dtuple2_full _ _ a in
  let _ = gen_elim () in
  let vh = vpattern_replace (aparse _ a) in
  let (| b, arg |) = vh.contents in
  let _ = rewrite_aparse a' (parse_lseq_bytes (U64.v (argument_as_uint64 b arg))) in
  let _ = elim_lseq_bytes _ a' in
  noop ();
  a'

(*
let ghost_focus_byte_string_strong
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vp ->
      AP.arrayptr a' vp `star`
      pure (ghost_focus_byte_string_post va vp) `star`
      (forall_ (fun vp' ->
        (AP.arrayptr a' vp' `star` pure (AP.array_of vp' == AP.array_of vp))
        `implies_`
        (exists_ (fun va' -> aparse parse_raw_data_item a va' `star` pure (
          AP.length (AP.array_of vp') < 4294967296 /\
          array_of va' == array_of va /\
          va'.contents == ByteString (AP.contents_of vp')
      )))))
    ))
    (ByteString? va.contents)
    (fun _ -> True)
= ...
*)

let ghost_focus_byte_string
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vp ->
      AP.arrayptr a' vp `star`
      pure (
        ghost_focus_byte_string_post va vp
      ) `star`
      (AP.arrayptr a' vp `implies_` aparse parse_raw_data_item a va)
    ))
    (ByteString? va.contents)
    (fun _ -> True)
= let a' = elim_raw_data_item_byte_string a in
  let _ = gen_elim () in
  intro_implies (AP.arrayptr a' _) (aparse parse_raw_data_item a va) (aparse _ a _) (fun _ ->
    let _ = intro_raw_data_item_byte_string a a' in
    vpattern_rewrite (aparse _ a) va
  );
  noop ();
  a'

let focus_byte_string
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST byte_array
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vp ->
      AP.arrayptr a' vp `star`
      pure (
        ghost_focus_byte_string_post va vp
      ) `star`
      (AP.arrayptr a' vp `implies_` aparse parse_raw_data_item a va)
    ))
    (ByteString? va.contents)
    (fun _ -> True)
= let _ = elim_raw_data_item_byte_string a in
  let _ = gen_elim () in
  let a' = hop_aparse_arrayptr jump_header _ _ in
  intro_implies (AP.arrayptr a' _) (aparse parse_raw_data_item a va) (aparse _ a _) (fun _ ->
    let _ = intro_raw_data_item_byte_string a a' in
    vpattern_rewrite (aparse _ a) va
  );
  noop ();
  return a'


#pop-options
