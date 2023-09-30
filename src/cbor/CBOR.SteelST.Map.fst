module CBOR.SteelST.Map
include CBOR.SteelST.Base
open CBOR.SteelST.Validate
open LowParse.SteelST.Combinators
open LowParse.SteelST.Assoc
open LowParse.SteelST.Recursive
open LowParse.SteelST.BitSum
open LowParse.SteelST.ValidateAndRead
open LowParse.SteelST.SeqBytes
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module NL = LowParse.SteelST.VCList.Sorted
module SB = LowParse.SteelST.SeqBytes
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module I16 = FStar.Int16
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

#set-options "--print_universes"

#set-options "--ide_id_info_off"

(* 4.2 Ordering of map keys *)

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


#push-options "--z3rlimit 32"

#restart-solver
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
  if major_type = major_type_map
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

#pop-options

unfold
inline_for_extraction
let coerce_squash
  (t2: Type)
  (#t1: Type)
  (x: t1)
  (sq: squash (t1 == t2))
: Tot t2
= (x <: t2)

inline_for_extraction
noextract
let validate_raw_data_item_filter
  (#p: Ghost.erased (raw_data_item -> bool))
  (p_impl: pred_recursive_base_t serialize_raw_data_item_param p)
: Tot (validator (parse_filter parse_raw_data_item (holds_on_raw_data_item p)))
=   (validate_filter_gen
      validate_raw_data_item
      (holds_on_raw_data_item p)
      (fun #va a ->
        rewrite (aparse _ a _) (aparse (parse_recursive parse_raw_data_item_param) a va);
        let res = pred_recursive
          serialize_raw_data_item_param
          (jump_leaf)
          (jump_count_remaining_data_items)
          a
          (holds_on_raw_data_item_pred p)
          (coerce_squash _ p_impl (_ by (FStar.Tactics.trefl ())))
        in
        rewrite (aparse _ a _) (aparse parse_raw_data_item a va);
        return res
      )
    )

#push-options "--z3rlimit 16"

#restart-solver
inline_for_extraction
noextract
let validate_data_item
  (#order: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (order_impl: NL.order_impl parse_raw_data_item order)
: Tot (validator (parse_data_item order))
= fun a len err ->
    let sq = Steel.ST.HigherArray.intro_fits_u64 () in
    rewrite_validator
      (validate_raw_data_item_filter
        (check_data_item_wf_head order_impl sq))
      (parse_data_item order)
      a len err

#pop-options

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

let validate_canonical_cbor_data_item0
: validator (parse_data_item canonical_cbor_map_key_order)
= validate_data_item canonical_cbor_map_key_order_impl

inline_for_extraction // necessary for the reexport into CBOR.SteelST
let validate_canonical_cbor_data_item
: validator (parse_data_item canonical_cbor_map_key_order)
= fun a len perr -> validate_canonical_cbor_data_item0 a len perr

let jump_data_item
  (order: Ghost.erased (raw_data_item -> raw_data_item -> bool))
: Tot (jumper (parse_data_item order))
= jump_filter
    jump_raw_data_item
    (data_item_wf order)

(* Comparisons with unserialized values *)
  
let byte_compare_pure_impl (x y: byte) : Pure I16.t
  (requires True)
  (ensures (fun res -> I16.v res `NL.same_sign` byte_compare x y))
= FStar.Int.Cast.uint8_to_int16 x `I16.sub` FStar.Int.Cast.uint8_to_int16 y

#restart-solver
let lex_compare_with_header_long_argument
  (ty1: major_type_t { ty1 `U8.lt` major_type_simple_value })
  (x1: U64.t)
  (ty2: major_type_t { ty2 `U8.lt` major_type_simple_value })
  (x2: U64.t)
: Lemma
  (requires (
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2
  ))
  (ensures (
    let h1 = uint64_as_argument ty1 x1 in
    let (| b1, l1 |) = h1 in
    let h2 = uint64_as_argument ty2 x2 in
    let (| b2, l2 |) = h2 in
    ty1 == ty2 /\
    b1 == b2 /\
    (bytes_lex_compare (serialize serialize_header h1) (serialize serialize_header h2) ==
      bytes_lex_compare (serialize (serialize_long_argument b1) l1) (serialize (serialize_long_argument b2) l2))
  ))
=
  let h1 = uint64_as_argument ty1 x1 in
  let h2 = uint64_as_argument ty2 x2 in
  get_uint64_as_initial_byte_header_correct ty1 x1;
  get_uint64_as_initial_byte_header_correct ty2 x2;
  get_initial_byte_header_inj h1 h2;
  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h1;
  serialize_dtuple2_eq serialize_initial_byte serialize_long_argument h2;
  let (| b1, l1 |) = h1 in
  let (| _, l2 |) = h2 in
  LowParse.Spec.Endianness.seq_to_list_append (serialize serialize_initial_byte b1) (serialize (serialize_long_argument b1) l1);
  LowParse.Spec.Endianness.seq_to_list_append (serialize serialize_initial_byte b1) (serialize (serialize_long_argument b1) l2);
  lex_compare_prefix byte_compare (fun _ _ -> ()) (Seq.seq_to_list (serialize serialize_initial_byte b1)) (Seq.seq_to_list (serialize (serialize_long_argument b1) l1)) (Seq.seq_to_list (serialize (serialize_long_argument b1) l2))

#push-options "--z3rlimit 16"

#restart-solver
let lex_compare_with_header_uint
  (ty1: major_type_t { ty1 `U8.lt` major_type_simple_value })
  (x1: U64.t)
  (ty2: major_type_t { ty2 `U8.lt` major_type_simple_value })
  (x2: U64.t)
  (b1: initial_byte)
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (phi: (t -> GTot bool))
  (f: (parse_filter_refine phi -> GTot (long_argument b1)) { synth_injective f })
  (g: (long_argument b1 -> GTot (parse_filter_refine phi)) { synth_inverse f g })
  (s: serializer p)
  (n: nat)
  (uv: (t -> FStar.UInt.uint_t (8 `op_Multiply` n)))
  (s_spec: (
    (x: t) ->
    Lemma
    (serialize s x == FStar.Endianness.n_to_be n (uv x))
  ))
  (uv_spec: (
    (x: U64.t) ->
    Lemma
    (requires (
      dfst (uint64_as_argument ty1 x) == b1
    ))
    (ensures (
      uv (g (dsnd (uint64_as_argument ty1 x))) == U64.v x
    ))
  ))
: Lemma
  (requires (
    let h1 = uint64_as_argument ty1 x1 in
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2 /\
    dfst h1 == b1 /\
    parse_filter_kind parse_long_argument_kind `is_weaker_than` k /\
    parse_long_argument b1 == LowParse.Spec.Base.weaken parse_long_argument_kind (parse_synth (parse_filter p phi) f)
  ))
  (ensures (
    ty1 == ty2 /\
    (bytes_lex_compare (serialize serialize_header (uint64_as_argument ty1 x1)) (serialize serialize_header (uint64_as_argument ty2 x2)) < 0 <==> x1 `U64.lt` x2)
  ))
= lex_compare_with_header_long_argument ty1 x1 ty2 x2;
  uv_spec x1;
  uv_spec x2;
  let (| _, l1 |) = uint64_as_argument ty1 x1 in
  let (| _, l2 |) = uint64_as_argument ty2 x2 in
  let p1' : parser parse_long_argument_kind (long_argument b1) = LowParse.Spec.Base.weaken parse_long_argument_kind (parse_synth (parse_filter p phi) f) in
  assert (parse_long_argument b1 == p1');
  let s1_pre = serialize_synth #_ #_ #(long_argument b1) _ f (serialize_filter s phi) g () in
  let s1' : serializer p1' = serialize_weaken parse_long_argument_kind s1_pre in
  serializer_unique (parse_long_argument b1) (serialize_long_argument b1) s1' l1;
  assert (serialize s1' l1 == serialize s1_pre l1);
  serialize_synth_eq #_ #_ #(long_argument b1) _ f (serialize_filter s phi) g () l1;
  s_spec (g l1);
  serializer_unique (parse_long_argument b1) (serialize_long_argument b1) s1' l2;
  assert (serialize s1' l2 == serialize s1_pre l2);
  serialize_synth_eq #_ #_ #(long_argument b1) _ f (serialize_filter s phi) g () l2;
  s_spec (g l2);
  LowParse.Spec.Endianness.big_endian_lex_compare n byte_compare (fun _ _ -> ()) (fun _ _ -> ()) (uv (g l1)) (uv (g l2))

#restart-solver
let lex_compare_with_header_correct'
  (ty1: major_type_t { ty1 `U8.lt` major_type_simple_value })
  (x1: U64.t)
  (ty2: major_type_t { ty2 `U8.lt` major_type_simple_value })
  (x2: U64.t)
: Lemma
  (requires (
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2
  ))
  (ensures (
    ty1 == ty2 /\
    (bytes_lex_compare (serialize serialize_header (uint64_as_argument ty1 x1)) (serialize serialize_header (uint64_as_argument ty2 x2)) < 0 <==> x1 `U64.lt` x2)
  ))
= let h1 = uint64_as_argument ty1 x1 in
  let (| b1, l1 |) = h1 in
  let (_, (a1, _)) = b1 in
  if a1 = additional_info_long_argument_8_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 parse_u8 uint8_wf (LongArgumentU8 #b1 ()) LongArgumentU8?.v serialize_u8 1 U8.v (fun x -> serialize_u8_spec_be x) (fun x -> ())
  end else
  if a1 = additional_info_long_argument_16_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 parse_u16 uint16_wf (LongArgumentU16 #b1 ()) LongArgumentU16?.v serialize_u16 2 U16.v (fun x -> serialize_u16_spec_be x) (fun x -> ())
  end else
  if a1 = additional_info_long_argument_32_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 parse_u32 uint32_wf (LongArgumentU32 #b1 ()) LongArgumentU32?.v serialize_u32 4 U32.v (fun x -> serialize_u32_spec_be x) (fun x -> ())
  end else
  if a1 = additional_info_long_argument_64_bits
  then begin
    lex_compare_with_header_uint ty1 x1 ty2 x2 b1 parse_u64 uint64_wf (LongArgumentU64 #b1 ()) LongArgumentU64?.v serialize_u64 8 U64.v (fun x -> serialize_u64_spec_be x) (fun x -> ())
  end else
  begin
    lex_compare_with_header_long_argument ty1 x1 ty2 x2;
    let (| _, l2 |) = uint64_as_argument ty2 x2 in
    let p1' : parser parse_long_argument_kind (long_argument b1) = LowParse.Spec.Base.weaken parse_long_argument_kind (parse_synth parse_empty (LongArgumentOther #b1 a1 ())) in
    assert (parse_long_argument b1 == p1');
    let s1_pre = serialize_synth #_ #_ #(long_argument b1) _ (LongArgumentOther #b1 a1 ()) serialize_empty LongArgumentOther?.v () in
    let s1' : serializer p1' = serialize_weaken parse_long_argument_kind s1_pre in
    serializer_unique (parse_long_argument b1) (serialize_long_argument b1) s1' l1;
    assert (serialize s1' l1 == serialize s1_pre l1);
    assert (serialize s1' l1 `Seq.equal` Seq.empty);
    assert (serialize (serialize_long_argument b1) l1 == Seq.empty);
    serializer_unique (parse_long_argument b1) (serialize_long_argument b1) s1' l2;
    assert (serialize s1' l2 == serialize s1_pre l2);
    assert (serialize s1' l2 `Seq.equal` Seq.empty);
    assert (serialize (serialize_long_argument b1) l2 == Seq.empty)
  end

#pop-options

let compare_u64
  (x1 x2: U64.t)
: Tot I16.t
= if x1 `U64.lt` x2 then -1s else if x2 `U64.lt` x1 then 1s else 0s

let lex_compare_with_header_correct
  (ty1: major_type_t { ty1 `U8.lt` major_type_simple_value })
  (x1: U64.t)
  (ty2: major_type_t { ty2 `U8.lt` major_type_simple_value })
  (x2: U64.t)
: Lemma
  (requires (
    get_uint64_as_initial_byte ty1 x1 == get_uint64_as_initial_byte ty2 x2
  ))
  (ensures (
    ty1 == ty2 /\
    bytes_lex_compare (serialize serialize_header (uint64_as_argument ty1 x1)) (serialize serialize_header (uint64_as_argument ty2 x2)) `same_sign` I16.v (compare_u64 x1 x2)
  ))
= lex_compare_with_header_correct' ty1 x1 ty2 x2;
  lex_compare_with_header_correct' ty2 x2 ty1 x1;
  let l1 = Seq.seq_to_list (serialize serialize_header (uint64_as_argument ty1 x1)) in
  let l2 = Seq.seq_to_list (serialize serialize_header (uint64_as_argument ty2 x2)) in
  lex_compare_antisym byte_compare (fun _ _ -> ()) l1 l2;
  lex_compare_antisym byte_compare (fun _ _ -> ()) l2 l1

#push-options "--z3rlimit 32 --ifuel 8"

#restart-solver
let lex_compare_with_header
  (ty: Ghost.erased major_type_t { ty `U8.lt` major_type_simple_value })
  (x: U64.t)
  (b: U8.t)
  (#vh: v (get_parser_kind parse_header) header)
  (a: byte_array)
: ST I16.t
    (aparse parse_header a vh)
    (fun _ -> aparse parse_header a vh)
    (b == get_uint64_as_initial_byte ty x)
    (fun i ->
      let s0 = serialize serialize_header (uint64_as_argument ty x) in
      let s = serialize serialize_header vh.contents in
      bytes_lex_compare s0 s `same_sign` I16.v i
    )
= get_uint64_as_initial_byte_header_correct ty x;
  let _ = elim_aparse_with_serializer serialize_header a in
  let first_byte = AP.index a 0sz in
  let _ = intro_aparse parse_header a in
  vpattern_rewrite (aparse _ a) vh;
  let compare_first_byte = byte_compare_pure_impl b first_byte in
  if compare_first_byte <> 0s
  then begin
    noop ();
    return compare_first_byte
  end else begin
    get_initial_byte_header_inj (uint64_as_argument ty x) vh.contents;
    let b' : Ghost.erased initial_byte = dfst vh.contents in
    let ty' : Ghost.erased major_type_t = let (ty', _) = Ghost.reveal b' in ty' in
    let gx' : Ghost.erased U64.t = get_header_argument_as_uint64 vh.contents in
    assert (vh.contents == uint64_as_argument ty' gx');
    let x' = read_header_argument_as_uint64 a in
    get_uint64_as_initial_byte_header_correct ty' x';
    lex_compare_with_header_correct ty x ty' x';
    return (compare_u64 x x')
  end

#pop-options
