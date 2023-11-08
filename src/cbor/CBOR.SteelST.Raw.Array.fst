module CBOR.SteelST.Raw.Array

let get_raw_data_item_payload_array
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vh -> exists_ (fun (n: nat) -> exists_ (fun vc ->
      aparse parse_header a vh `star`
      aparse (NL.parse_nlist n parse_raw_data_item) a' vc `star`
      pure (get_raw_data_item_payload_array_post va vh n vc)
    ))))
    (Array? va.contents)
    (fun _ -> True)
= Classical.forall_intro parse_raw_data_item_eq;
  let _ = rewrite_aparse a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let va1 = elim_synth' _ _ synth_raw_data_item_recip a () in // (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
  let a' = ghost_split_dtuple2_full _ _ a in // parse_header (parse_content parse_raw_data_item) a in
  let _ = gen_elim () in
  let vh = vpattern_replace (aparse _ a) in
  let (| b, x |) = vh.contents in
  let n = UInt64.v (argument_as_uint64 b x) in
  let vc = rewrite_aparse a' (NL.parse_nlist n parse_raw_data_item) in
  assert (get_raw_data_item_payload_array_post va vh n vc);
  noop ();
  a'

#push-options "--z3rlimit 32"

#restart-solver
let intro_raw_data_item_array
  (#opened: _)
  (#vh: v (get_parser_kind parse_header) header)
  (h: byte_array)
  (#n: nat)
  (#vc: v (NL.parse_nlist_kind n parse_raw_data_item_kind) (NL.nlist n raw_data_item))
  (c: byte_array)
: STGhost (v parse_raw_data_item_kind raw_data_item) opened
    (aparse parse_header h vh `star`
      aparse (NL.parse_nlist n parse_raw_data_item) c vc
    )
    (fun va -> aparse parse_raw_data_item h va)
    (
      let (| b, x |) = vh.contents in
      let (major_type, _) = b in
      n == UInt64.v (argument_as_uint64 b x) /\
      major_type == get_major_type (Array vc.contents) /\
      AP.adjacent (array_of' vh) (array_of' vc)
    )
    (fun va ->
      get_raw_data_item_payload_array_post va vh n vc
    )
= Classical.forall_intro parse_raw_data_item_eq;
  let h' = uint64_as_argument (get_major_type (Array vc.contents)) (UInt64.uint_to_t n) in
  assert (vh.contents == h');
  noop ();
  let _ = rewrite_aparse c (parse_content parse_raw_data_item vh.contents) in
  let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) h c in
  let _ = intro_synth (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item h () in 
  rewrite_aparse h parse_raw_data_item

#pop-options

#push-options "--z3rlimit 16"

#restart-solver

let focus_array_with_ghost_length
  (n: Ghost.erased nat)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST byte_array
    (aparse parse_raw_data_item a va)
    (fun res -> exists_ (fun vres ->
      aparse (NL.parse_nlist n parse_raw_data_item) res vres `star`
      (aparse (NL.parse_nlist n parse_raw_data_item) res vres `implies_`
        aparse parse_raw_data_item a va
      ) `star` pure (
      focus_array_with_ghost_length_post n va vres
    )))
    (Array? va.contents /\
      Ghost.reveal n == List.Tot.length (Array?.v va.contents)
    )
    (fun _ -> True)
= let ga' = get_raw_data_item_payload_array a in
  let _ = gen_elim () in
  let gl = rewrite_aparse ga' (NL.parse_nlist n parse_raw_data_item) in
  let a' = hop_aparse_aparse jump_header _ a ga' in
  intro_implies
    (aparse (NL.parse_nlist n parse_raw_data_item) a' _)
    (aparse parse_raw_data_item a va)
    (aparse parse_header a _)
    (fun _ ->
      let _ = intro_raw_data_item_array a a' in
      vpattern_rewrite (aparse parse_raw_data_item a) va
    );
  return a'

let focus_array
  (#n': Ghost.erased U64.t)
  (#a': Ghost.erased byte_array)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (pn: R.ref U64.t)
  (pa: R.ref byte_array)
  (a: byte_array)
: ST focus_array_res
    (aparse parse_raw_data_item a va `star`
      R.pts_to pn full_perm n' `star`
      R.pts_to pa full_perm a'
    )
    (fun res ->
      R.pts_to pn full_perm res.n `star`
      R.pts_to pa full_perm res.a `star`
      aparse (NL.parse_nlist (U64.v res.n) parse_raw_data_item) res.a res.l `star`
      (aparse (NL.parse_nlist (U64.v res.n) parse_raw_data_item) res.a res.l `implies_`
        aparse parse_raw_data_item a va
      )
    )
    (Array? va.contents)
    (fun res ->
      va.contents == Array res.l.contents
    )
= let gn : Ghost.erased U64.t = Ghost.hide (U64.uint_to_t (List.Tot.length (Array?.v va.contents))) in
  let ga' = get_raw_data_item_payload_array a in
  let _ = gen_elim () in
  let gl = rewrite_aparse ga' (NL.parse_nlist (U64.v gn) parse_raw_data_item) in
  let a' = hop_aparse_aparse jump_header _ a ga' in
  let n = read_header_argument_as_uint64 a in
  let res = {
    n = n;
    l = gl;
    a = a';
  }
  in
  R.write pn n;
  R.write pa a';
  rewrite (aparse _ a' _) (aparse (NL.parse_nlist (U64.v res.n) parse_raw_data_item) res.a res.l);
  intro_implies
    (aparse (NL.parse_nlist (U64.v res.n) parse_raw_data_item) res.a res.l)
    (aparse parse_raw_data_item a va)
    (aparse parse_header a _)
    (fun _ ->
      let _ = intro_raw_data_item_array a res.a in
      vpattern_rewrite (aparse parse_raw_data_item a) va
    );
  return res

#pop-options
