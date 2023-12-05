module CBOR.SteelST.Raw.Map

#set-options "--print_universes"

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

let focus_map_with_ghost_length
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
  (n: Ghost.erased nat)
: ST byte_array
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun va' ->
      aparse (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) a' va' `star`

      (aparse (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) a' va' `implies_`
        aparse parse_raw_data_item a va) `star`
      pure (focus_map_postcond va n va')
    ))
    (Map? va.contents /\
      Ghost.reveal n == List.Tot.length (Map?.v va.contents)
    )
    (fun _ -> True)
= 
  Classical.forall_intro parse_raw_data_item_eq;
  noop ();
  let va1 = rewrite_aparse_with_implies a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let va2 = elim_synth_with_implies _ _ a () in
  implies_trans
    (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) a va2)
    (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) a va1)
    (aparse parse_raw_data_item a va);
  let ga' = ghost_split_dtuple2_full _ _ a in
  let _ = gen_elim () in
  let vh = vpattern_replace (aparse _ a) in
  let vc = rewrite_aparse ga' (parse_content parse_raw_data_item vh.contents) in
  let a' = hop_aparse_aparse jump_header (parse_content parse_raw_data_item vh.contents) a ga' in
  intro_implies
    (aparse (parse_content parse_raw_data_item vh.contents) a' vc)
    (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) a va2)
    (aparse parse_header a vh)
    (fun _ ->
      let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a' in
      vpattern_rewrite (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) a) va2
    );
  implies_trans
    (aparse (parse_content parse_raw_data_item vh.contents) a' vc)
    (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) a va2)
    (aparse parse_raw_data_item a va);
  let _ = rewrite_aparse_with_implies a' (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) in
  implies_trans
    (aparse (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) a' _)
    (aparse (parse_content parse_raw_data_item vh.contents) a' vc)
    (aparse parse_raw_data_item a va);
  return a'

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
  if major_type = cbor_major_type_map
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
let check_raw_data_item
  (#p: Ghost.erased (raw_data_item -> bool))
  (p_impl: pred_recursive_base_t serialize_raw_data_item_param p)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST bool
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    True
    (fun res -> res == holds_on_raw_data_item p va.contents)
= 
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
        check_raw_data_item p_impl a
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

let compare_u64
  (x1 x2: U64.t)
  : Tot I16.t
  = if x1 `U64.lt` x2 then -1s else if x2 `U64.lt` x1 then 1s else 0s

#push-options "--z3rlimit 32 --ifuel 8"

#restart-solver
let lex_compare_with_header
  (ty: Ghost.erased major_type_t { ty `U8.lt` cbor_major_type_simple_value })
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
