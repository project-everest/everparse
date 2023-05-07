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

let get_major_type_synth_raw_data_item
  (x: raw_data_item')
: Lemma
  (get_major_type (synth_raw_data_item x) == (match x with (| (| (major_type, _), _ |), _ |) -> major_type))
= assert_norm (pow2 3 == 8)

#push-options "--z3rlimit 16 --split_queries always"

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
  get_major_type_synth_raw_data_item va1.contents;
  let a_content = ghost_split_dtuple2_full _ _ a in // parse_header (parse_content parse_raw_data_item) a in
  let _ = gen_elim () in
  let _ = rewrite_aparse a (parse_dtuple2 parse_initial_byte parse_long_argument) in
  let a_long = ghost_split_dtuple2_full _ _ a in
  let _ = gen_elim () in
  let res = read_initial_byte a (aparse _ a_content _ `star` aparse _ a_long _) byte (fun res -> aparse parse_raw_data_item a va `star` pure (res == get_major_type va.contents)) (fun (major_type, _) ->
    let res = major_type in
    let _ = intro_dtuple2 parse_initial_byte parse_long_argument a a_long in
    let _ = rewrite_aparse a parse_header in
    let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a_content in
    noop ();
    let _ = intro_synth (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
    let _ = rewrite_aparse a parse_raw_data_item in
    noop ();
    vpattern_rewrite (aparse parse_raw_data_item a) va;
    return res
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
  let res = jump_header a (aparse _ a_content _) UInt64.t (fun res -> aparse parse_raw_data_item a va `star` pure (
      let (| (| b, x |), _ |) = synth_raw_data_item_recip va.contents in
      res == argument_as_uint64 b x
  )) (fun _ (| b, x |) ->
    let res = argument_as_uint64 b x in
    let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a_content in
    noop ();
    let _ = intro_synth (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
    let _ = rewrite_aparse a parse_raw_data_item in
    noop ();
    vpattern_rewrite (aparse parse_raw_data_item a) va;
    return res
  )
  in
  let _ = elim_pure _ in
  return res

module AP = LowParse.SteelST.ArrayPtr

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
    let ac = hop_aparse_aparse (jumper_of_read_and_jump jump_header) _ a gac in
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
          (jump_leaf sq)
          (jump_count_remaining_data_items sq)
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
