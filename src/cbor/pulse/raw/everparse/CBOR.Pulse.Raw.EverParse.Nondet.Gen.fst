module CBOR.Pulse.Raw.EverParse.Nondet.Gen
#lang-pulse

inline_for_extraction
let impl_equiv_with_bound_t
  (#t: Type)
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> t)
=
  (l1: S.slice byte) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (raw_data_item)) ->
  stt t
    (pts_to_serialized (serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_raw_data_item) l2 #p2 gl2 **
      pure (raw_data_item_size gl1 + raw_data_item_size gl2 <= bound)
    )
    (fun res ->
      pts_to_serialized (serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        raw_data_item_size gl1 + raw_data_item_size gl2 <= bound /\
        res == equiv gl1 gl2
      )
    )

inline_for_extraction
let impl_equiv_hd_with_bound_t
  (#t: Type)
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> t)
=
  (n1: Ghost.erased nat) ->
  (l1: S.slice byte) ->
  (n2: Ghost.erased nat) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (nlist n1 raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (nlist n2 raw_data_item)) ->
  stt t
    (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0 /\
        raw_data_item_size (List.Tot.hd gl1) + raw_data_item_size (List.Tot.hd gl2) <= bound
      )
    )
    (fun res ->
pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0 /\
        raw_data_item_size (List.Tot.hd gl1) + raw_data_item_size (List.Tot.hd gl2) <= bound /\
        res == equiv (List.Tot.hd gl1) (List.Tot.hd gl2)
      )
    )

#push-options "--z3rlimit 32"

let pts_to_serialized_nlist_raw_data_item_head_header'_post_children
  (n: pos)
  (va: LowParse.Spec.VCList.nlist n raw_data_item)
  (h: header) (v': (header & (leaf_content h & (nlist (remaining_data_items_header h) raw_data_item & nlist (n - 1)  raw_data_item  ))))
: Lemma
  (requires
    pts_to_serialized_nlist_raw_data_item_head_header'_post n va h v'
  )
  (ensures
    (fst (snd (snd v')) <: list raw_data_item) == begin match List.Tot.hd va with
    | Array _ v -> v
    | Map _ v -> CBOR.Spec.Util.list_of_pair_list v
    | Tagged _ v -> [v]
    | _ -> []
    end
  )
= // assert (synth_raw_data_item_from_alt (synth_raw_data_item_from_alt_recip (List.Tot.hd va)) == List.Tot.hd va);
  ()

#pop-options

let check_equiv_head
  (a1 a2: raw_data_item)
: Tot bool
= 
      match a1, a2 with
      | Int64 ty1 v1, Int64 ty2 v2 ->
        ty1 = ty2 &&
        v1.value = v2.value
      | Simple v1, Simple v2 ->
        v1 = v2
      | String ty1 _ s1, String ty2 _ s2 ->
        ty1 = ty2 &&
        s1 = s2
      | Tagged tag1 b1, Tagged tag2 b2 ->
        tag1.value = tag2.value
      | Array len1 ar1, Array len2 ar2 ->
        len1.value = len2.value
      | _ -> false

let check_equiv_head_correct_pre
  (gl1: list raw_data_item)
  (gl2: list raw_data_item)
  (equiv: ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 }) -> option bool))
: Tot prop
=
    List.Tot.length gl1 == List.Tot.length gl2 /\
    Cons? gl1 /\ Cons? gl2 /\ (
    let a1 = List.Tot.hd gl1 in
    let a2 = List.Tot.hd gl2 in
    let gc1 = dsnd (dfst (synth_raw_data_item_from_alt_recip a1)) in
    let gc2 = dsnd (dfst (synth_raw_data_item_from_alt_recip a2)) in
    let h1 = get_raw_data_item_header a1 in
    let h2 = get_raw_data_item_header a2 in
    get_header_major_type h1 == get_header_major_type h2 /\
    equiv a1 a2 = Some false
  )

let check_equiv_head_correct_post
  (gl1: list raw_data_item)
  (gl2: list raw_data_item)
  (equiv: ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 }) -> option bool))
: Tot prop
=
  check_equiv_head_correct_pre gl1 gl2 equiv /\ (
    let a1 :: q1 = gl1 in
    let a2 :: q2 = gl2 in
    let l1' = dsnd (synth_raw_data_item_from_alt_recip a1) `List.Tot.append` q1 in
    let l2' = dsnd (synth_raw_data_item_from_alt_recip a2) `List.Tot.append` q2 in
    (check_equiv_head a1 a2 ==> list_sum raw_data_item_size l1' + list_sum raw_data_item_size l2' <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2) /\
    check_equiv_list gl1 gl2 equiv == (if check_equiv_head a1 a2 then check_equiv_list l1' l2' equiv else Some false)
  )

#push-options "--z3rlimit 64"

let check_equiv_head_correct
  (gl1: list raw_data_item)
  (gl2: list raw_data_item)
  (equiv: ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 }) -> option bool))
  (sq: squash (check_equiv_head_correct_pre gl1 gl2 equiv))
: Lemma
  (ensures (
    check_equiv_head_correct_post gl1 gl2 equiv
  ))
=
  let a1 :: q1 = gl1 in
  let a2 :: q2 = gl2 in
  let l1' = dsnd (synth_raw_data_item_from_alt_recip a1) `List.Tot.append` q1 in
  let l2' = dsnd (synth_raw_data_item_from_alt_recip a2) `List.Tot.append` q2 in
  raw_data_item_size_eq a1;
  raw_data_item_size_eq a2;
  match a1, a2 with
  | Array len1 ar1, Array len2 ar2 ->
        list_sum_append raw_data_item_size ar1 q1;
        list_sum_append raw_data_item_size ar2 q2;
        ()
  | _ ->  ()

module U64 = FStar.UInt64

#pop-options

#push-options "--z3rlimit 64"

let pi
  (h1: header)
  (mt1: major_type_t)
  (len: U64.t)
  (sq: squash (
      mt1 == get_header_major_type h1 /\
      (mt1 == cbor_major_type_byte_string \/ mt1 == cbor_major_type_text_string) /\
      len == argument_as_uint64 (dfst h1) (dsnd h1) 
  ))
= 
  parse_synth  (parse_filter (LowParse.Spec.SeqBytes.parse_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq #h1 ())

let pi_correct
  (h1: header)
  (mt1: major_type_t)
  (len: U64.t)
  (sq: squash (
      mt1 == get_header_major_type h1 /\
      (mt1 == cbor_major_type_byte_string \/ mt1 == cbor_major_type_text_string) /\
      len == argument_as_uint64 (dfst h1) (dsnd h1) 
  ))
: Lemma
  (forall b . parse (parse_leaf_content h1) b == parse (pi h1 mt1 len sq) b)
= ()

let sigma
  (h1: header)
  (mt1: major_type_t)
  (len: U64.t)
  (sq: squash (
      mt1 == get_header_major_type h1 /\
      (mt1 == cbor_major_type_byte_string \/ mt1 == cbor_major_type_text_string) /\
      len == argument_as_uint64 (dfst h1) (dsnd h1) 
  ))
: serializer (pi h1 mt1 len sq)
= 
  serialize_synth  #_ #_ #(c: leaf_content h1 {b2t (LeafContentSeq? #h1 c)}) _ (LeafContentSeq #h1 ()) (serialize_filter (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq?.v #h1) ()

// FIXME: WHY WHY WHY do I need to break abstraction here? I can't unfold sigma in pulse.
let sigma_correct
  (a1: raw_data_item)
  (h1: header)
  (mt1: major_type_t)
  (len: U64.t)
  (c1: leaf_content h1)
  (sq: squash (
      mt1 == get_header_major_type h1 /\
      (mt1 == cbor_major_type_byte_string \/ mt1 == cbor_major_type_text_string) /\
      len == argument_as_uint64 (dfst h1) (dsnd h1) /\
      h1 == get_raw_data_item_header a1 /\
      c1 == dsnd (dfst (synth_raw_data_item_from_alt_recip a1))
  ))
: Lemma
  (serialize (sigma h1 mt1 len ()) c1 == String?.v a1)
= assert (serialize (sigma h1 mt1 len ()) c1 == serialize (serialize_synth #_ #_ #(c: leaf_content h1 {b2t (LeafContentSeq? #h1 c)}) _ (LeafContentSeq #h1 ()) (serialize_filter (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq?.v #h1) ()) c1)
  ;
  serialize_synth_eq
    _ (LeafContentSeq #h1 ()) (serialize_filter (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq?.v #h1) ()
    c1;
  assert ((LeafContentSeq?.v c1 <: bytes ) == (String?.v a1 <: bytes));
  assert (serialize (sigma h1 mt1 len ()) c1 == serialize (serialize_filter (LowParse.Spec.SeqBytes.serialize_lseq_bytes (U64.v len)) (lseq_utf8_correct mt1 _)) (LeafContentSeq?.v #h1 c1));
  assert (serialize (sigma h1 mt1 len ()) c1 == String?.v a1);
  ()

inline_for_extraction
fn impl_check_equiv_head
  (h1: header)
  (c1: S.slice byte)
  (h2: header)
  (c2: S.slice byte)
  (#p1: perm)
  (#gc1: Ghost.erased (leaf_content h1))
  (#p2: perm)
  (#gc2: Ghost.erased (leaf_content h2))
  (a1: Ghost.erased raw_data_item)
  (a2: Ghost.erased raw_data_item)
requires
  pts_to_serialized (serialize_leaf_content h1) c1 #p1 gc1 **
  pts_to_serialized (serialize_leaf_content h2) c2 #p2 gc2 **
  pure (
    h1 == get_raw_data_item_header a1 /\
    Ghost.reveal gc1 == dsnd (dfst (synth_raw_data_item_from_alt_recip a1)) /\
    h2 == get_raw_data_item_header a2 /\
    Ghost.reveal gc2 == dsnd (dfst (synth_raw_data_item_from_alt_recip a2)) /\
    get_header_major_type h1 == get_header_major_type h2
  )
returns res: bool
ensures
  pts_to_serialized (serialize_leaf_content h1) c1 #p1 gc1 **
  pts_to_serialized (serialize_leaf_content h2) c2 #p2 gc2 **
  pure (
    res == check_equiv_head a1 a2
  )
{
  let mt1 = get_header_major_type h1;
  if (mt1 = cbor_major_type_simple_value) {
    let sv1 = argument_as_simple_value (dfst h1) (dsnd h1);
    let sv2 = argument_as_simple_value (dfst h2) (dsnd h2);
    (sv1 = sv2)
  } else {
    let len = argument_as_uint64 (dfst h1) (dsnd h1);
    let len2 = argument_as_uint64 (dfst h2) (dsnd h2);
    if (len <> len2) {
      false
    } else if (mt1 = cbor_major_type_byte_string || mt1 = cbor_major_type_text_string) {
      pi_correct h1 mt1 len ();
      pts_to_serialized_ext_trade
        (serialize_leaf_content h1)
        (sigma h1 mt1 len ())
        c1;
      sigma_correct a1 h1 mt1 len gc1 ();
      pts_to_serialized_elim_trade
        (sigma h1 mt1 len ())
        c1;
      Trade.trans _ _ (pts_to_serialized (serialize_leaf_content h1) c1 #p1 gc1);
      pi_correct h2 mt1 len ();
      pts_to_serialized_ext_trade
        (serialize_leaf_content h2)
        (sigma h2 mt1 len ())
        c2;
      sigma_correct a2 h2 mt1 len gc2 ();
      pts_to_serialized_elim_trade
        (sigma h2 mt1 len ())
        c2;
      Trade.trans _ _ (pts_to_serialized (serialize_leaf_content h2) c2 #p2 gc2);
      CBOR.Spec.Raw.Format.bytes_lex_compare_equal (String?.v a1) (String?.v a2);
      let cmp = CBOR.Pulse.Raw.Compare.Bytes.lex_compare_bytes c1 c2;
      Trade.elim _ (pts_to_serialized (serialize_leaf_content h1) c1 #p1 gc1);
      Trade.elim _ (pts_to_serialized (serialize_leaf_content h2) c2 #p2 gc2);
      (cmp = 0s)
    } else {
       (mt1 <> cbor_major_type_map)
    }
  }
}

inline_for_extraction
let impl_check_equiv_list_with_bound_t
  (bound: Ghost.erased nat)
  (equiv: ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool))
=
  (n1: SZ.t) ->
  (l1: S.slice byte) ->
  (n2: SZ.t) ->
  (l2: S.slice byte) ->
  (#p1: perm) ->
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item)) ->
  (#p2: perm) ->
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item)) ->
  (sq: squash (
    list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 <= bound
  )) ->
  stt (option bool)
(requires
  pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v n2) serialize_raw_data_item) l2 #p2 gl2
)
(ensures fun res ->
  pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v n2) serialize_raw_data_item) l2 #p2 gl2 **
  pure (
    res == check_equiv_list gl1 gl2 equiv
  )
)

inline_for_extraction
fn impl_check_equiv_list
  (#bound: Ghost.erased nat)
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool))
  (impl_equiv: impl_equiv_hd_with_bound_t bound equiv)
: impl_check_equiv_list_with_bound_t bound equiv
=
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item))
  (sq: squash (
    list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 <= bound
  ))
{
  if (n1 <> n2) {
    Some false
  } else {
    let mut pn = n1;
    let mut pl1 = l1;
    let mut pl2 = l2;
    Trade.refl
      (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1);
    pts_to_serialized_ext_trade
      (serialize_nlist (SZ.v n2) serialize_raw_data_item)
      (serialize_nlist (SZ.v n1) serialize_raw_data_item)
      l2;
    let mut pres = Some true;
    while (
      let res = !pres;
      let n = !pn;
      (CBOR.Pulse.Raw.Util.eq_Some_true res && SZ.gt n 0sz)
    )
    invariant b . exists* res n' l1' l2' gl1' gl2' .
      pts_to pres res **
      pts_to pn n' **
      pts_to pl1 l1' **
      pts_to pl2 l2' **
      pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l1' #p1 gl1' **
      Trade.trade
        (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l1' #p1 gl1')
        (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1) **
      pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l2' #p2 gl2' **
      Trade.trade
        (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) l2' #p2 gl2')
        (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l2 #p2 gl2) **
      pure (
        b == ((res = Some true) && SZ.v n' > 0) /\
        list_sum raw_data_item_size gl1' + list_sum raw_data_item_size gl2' <= list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 /\
        check_equiv_list gl1 gl2 equiv == (if res = Some true then check_equiv_list gl1' gl2' equiv else res)
      )
    {
      let l1' = !pl1;
      let l2' = !pl2;
      let r = impl_equiv _ l1' _ l2';
      if (None? r) {
        pres := r
      } else {
        let n = !pn;
        with gl1' . assert (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
        with gl2' . assert (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
        assume (pure (SZ.fits_u64));
        raw_data_item_size_eq (List.Tot.hd gl1');
        raw_data_item_size_eq (List.Tot.hd gl2');
        if (CBOR.Pulse.Raw.Util.eq_Some_true r) {
          let n' = SZ.sub n 1sz;
          let tl1 = LowParse.Pulse.VCList.nlist_tl
            serialize_raw_data_item
            (jump_raw_data_item ())
            (SZ.v n)
            l1';
          Trade.trans _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1') _;
          pts_to_serialized_nlist_ext
            serialize_raw_data_item
            _
            tl1
            serialize_raw_data_item
            (SZ.v n');
          Trade.trans (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) tl1 #p1 _) _ _;
          let tl2 = LowParse.Pulse.VCList.nlist_tl
            serialize_raw_data_item
            (jump_raw_data_item ())
            (SZ.v n)
            l2';
          Trade.trans _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2') _;
          pts_to_serialized_nlist_ext
            serialize_raw_data_item
            _
            tl2
            serialize_raw_data_item
            (SZ.v n');
          Trade.trans (pts_to_serialized (serialize_nlist (SZ.v n') serialize_raw_data_item) tl2 #p2 _) _ _;
          pn := n';
          pl1 := tl1;
          pl2 := tl2;
        } else {
          let gh1 = pts_to_serialized_nlist_raw_data_item_head_header' l1' (SZ.v n);
          let (hd1, tl1) = split_nondep_then'
            _ (jump_header ())
            _ l1';
          Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
          let h1 = read_header () hd1;
          Trade.elim_hyp_l _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
          rewrite each gh1 as h1;
          let mt1 = get_header_major_type h1;
          let gh2 = pts_to_serialized_nlist_raw_data_item_head_header' l2' (SZ.v n);
          let (hd2, tl2) = split_nondep_then'
            _ (jump_header ())
            _ l2';
          Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
          let h2 = read_header () hd2;
          Trade.elim_hyp_l _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
          rewrite each gh2 as h2;
          let mt2 = get_header_major_type h2;
          if (mt1 <> mt2) {
            Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
            Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
            pres := Some false
          } else {
            let (lc1, tl1') = split_nondep_then'
              _ (jump_leaf_content () h1)
              _ tl1;
            Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
            with w1 . assert (
              pts_to_serialized (serialize_nondep_then (serialize_nlist (remaining_data_items_header h1) serialize_raw_data_item) (serialize_nlist (SZ.v n - 1) serialize_raw_data_item)) tl1' #p1 w1
            );
            list_sum_append raw_data_item_size (fst w1) (snd w1);
            pts_to_serialized_nlist_append serialize_raw_data_item tl1' _ _;
            Trade.trans_hyp_r _ _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
            pts_to_serialized_length _ tl1';
            assert (pure (remaining_data_items_header h1 + (SZ.v n - 1) <= SZ.v (S.len tl1')));
            let n' : SZ.t = SZ.add (impl_remaining_data_items_header (S.len tl1') h1) (SZ.sub n 1sz);
            pts_to_serialized_nlist_ext
              serialize_raw_data_item
              _
              tl1'
              serialize_raw_data_item
              (SZ.v n')
              ;
            Trade.trans_hyp_r _ _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');

            let (lc2, tl2') = split_nondep_then'
              _ (jump_leaf_content () h2)
              _ tl2;
            Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
            pts_to_serialized_nlist_append serialize_raw_data_item tl2' _ _;
            Trade.trans_hyp_r _ _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');

            assert (pure (check_equiv_head_correct_pre gl1' gl2' equiv));
            let sq : squash (check_equiv_head_correct_pre gl1' gl2' equiv) = ();
            check_equiv_head_correct gl1' gl2' equiv sq;
            if (impl_check_equiv_head h1 lc1 h2 lc2 (List.Tot.hd gl1') (List.Tot.hd gl2')) {
                Trade.elim_hyp_l _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
                Trade.trans _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1') _;
                Trade.elim_hyp_l _ _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
                Trade.trans _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2') _;
                pn := n';
                pl1 := tl1';
                pl2 := tl2';
            } else {
              Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l1' #p1 gl1');
              Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n) serialize_raw_data_item) l2' #p2 gl2');
              pres := Some false
            }
          }
        }
      }
    };
    Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l1 #p1 gl1);
    Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v n1) serialize_raw_data_item) l2 #p2 gl2);
    !pres
  }
}

inline_for_extraction
fn impl_equiv_hd_with_bound_weaken
  (#t: Type0)
  (#bound1: Ghost.erased nat)
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound1 }) -> t))
  (impl_equiv: impl_equiv_hd_with_bound_t bound1 equiv)
  (bound2: Ghost.erased nat)
  (sq: squash (Ghost.reveal bound2 <= Ghost.reveal bound1))
: impl_equiv_hd_with_bound_t #t bound2 equiv
=
  (n1: Ghost.erased nat)
  (l1: S.slice byte)
  (n2: Ghost.erased nat)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist n1 raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist n2 raw_data_item))
{
  impl_equiv n1 l1 n2 l2
}

inline_for_extraction
fn impl_check_equiv_aux
  (#bound: Ghost.erased nat)
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool))
  (impl_equiv: impl_check_equiv_list_with_bound_t bound equiv)
: impl_equiv_with_bound_t #_ bound (check_equiv_aux bound equiv)
=
  (l1: S.slice byte)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (raw_data_item))
{
  LowParse.Pulse.VCList.pts_to_serialized_nlist_1
    serialize_raw_data_item
    l1;
  LowParse.Pulse.VCList.pts_to_serialized_nlist_1
    serialize_raw_data_item
    l2;
  let sq : squash (list_sum raw_data_item_size [Ghost.reveal gl1] + list_sum raw_data_item_size [Ghost.reveal gl2] <= bound) = ();
  let res = impl_equiv 1sz l1 1sz l2 sq;
  Trade.elim _ (pts_to_serialized serialize_raw_data_item l1 #p1 gl1);
  Trade.elim _ (pts_to_serialized serialize_raw_data_item l2 #p2 gl2);
  res
}

let serialize_list_of_pair_list
  (n: nat)
  (l: nlist n (raw_data_item & raw_data_item))
: Lemma
  (serialize (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l ==
    serialize (serialize_nlist (n + n) serialize_raw_data_item) (list_of_pair_list _ n l)
  )
= let b = serialize (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l in
  parse_pair_list_as_list
    parse_raw_data_item
    n
    b;
  assert (parse (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item)) b == Some (l, Seq.length b));
  let Some (l', _) = parse (parse_nlist (n + n) parse_raw_data_item) b in
  assert (l == pair_list_of_list _ n l');
  list_of_pair_list_of_list n l';
  parse_injective
    (parse_nlist (n + n) parse_raw_data_item)
    b
    (serialize (serialize_nlist (n + n) serialize_raw_data_item) l');
  ()

inline_for_extraction
fn impl_setoid_assoc_eq_with_overflow
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> option bool))
  (#bound: Ghost.erased nat)
  (impl_equiv: impl_equiv_with_bound_t bound equiv)
  (nl: SZ.t)
  (ll: S.slice byte)
  (xr_key: S.slice byte)
  (xr_value: S.slice byte)
  (#pl: perm)
  (#gll: Ghost.erased (nlist (SZ.v nl) (raw_data_item & raw_data_item)))
  (#pxr_key: perm)
  (#gxr_key: Ghost.erased raw_data_item)
  (#pxr_value: perm)
  (#gxr_value: Ghost.erased raw_data_item)
requires
  pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll **
  pts_to_serialized serialize_raw_data_item xr_key #pxr_key gxr_key **
  pts_to_serialized serialize_raw_data_item xr_value #pxr_value gxr_value **
  pure (list_sum (pair_sum raw_data_item_size raw_data_item_size) gll + (raw_data_item_size gxr_key + raw_data_item_size gxr_value) <= bound)
returns res: option bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll **
  pts_to_serialized serialize_raw_data_item xr_key #pxr_key gxr_key **
  pts_to_serialized serialize_raw_data_item xr_value #pxr_value gxr_value **
  pure (list_sum (pair_sum raw_data_item_size raw_data_item_size) gll + (raw_data_item_size gxr_key + raw_data_item_size gxr_value) <= bound /\
    res == setoid_assoc_eq_with_overflow equiv equiv gll (Ghost.reveal gxr_key, Ghost.reveal gxr_value)
  )
{
  Trade.refl
    (pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll);
  let mut pll = ll;
  let mut pn = nl;
  let mut pres = Some false;
  let mut pcont = true;
  while (
    let n = !pn;
    let res = !pres;
    let cont = !pcont;
    (SZ.gt n 0sz && CBOR.Pulse.Raw.Util.eq_Some_false res && cont)
  ) invariant b . exists* l n (gl: nlist (SZ.v n) (raw_data_item & raw_data_item)) res cont .
    pts_to pll l **
    pts_to pn n **
    pts_to_serialized
      (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l #pl
      gl **
    Trade.trade
      (pts_to_serialized
        (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl
        gl
      )
      (pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll) **
    pts_to pres res **
    pts_to_serialized serialize_raw_data_item xr_key #pxr_key gxr_key **
    pts_to_serialized serialize_raw_data_item xr_value #pxr_value gxr_value **
    pts_to pcont cont **
    pure (
      b == (SZ.v n > 0 && res = Some false && cont) /\
      list_sum (pair_sum raw_data_item_size raw_data_item_size) gl + (raw_data_item_size gxr_key + raw_data_item_size gxr_value) <= bound /\
      setoid_assoc_eq_with_overflow equiv equiv gll (Ghost.reveal gxr_key, Ghost.reveal gxr_value) == (if res = Some false && cont then setoid_assoc_eq_with_overflow equiv equiv gl (Ghost.reveal gxr_key, Ghost.reveal gxr_value) else res)
    )
  {
    let l = !pll;
    with gn (gl: nlist (SZ.v gn) (raw_data_item & raw_data_item)) . assert (
      pts_to pn gn **
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl
        gl
    );
    let n = !pn;
    let n' = SZ.sub n 1sz;
    nlist_cons_as_nondep_then
      (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      (SZ.v n)
      l;
    pts_to_serialized_nondep_then_assoc_l2r
      serialize_raw_data_item
      serialize_raw_data_item
      (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl
        gl
    );
    let ki : Ghost.erased parser_kind = and_then_kind
      parse_raw_data_item_kind
      (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
    let pi : parser ki (raw_data_item & nlist (SZ.v n') (raw_data_item & raw_data_item)) = nondep_then
        parse_raw_data_item
        (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
    let si : serializer pi = serialize_nondep_then
        serialize_raw_data_item
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
    assume (pure (SZ.fits_u64));
    let (lh, lt) = split_nondep_then'
      serialize_raw_data_item
      (jump_raw_data_item ())
      si
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl
        gl
    );
    let res = impl_equiv xr_key lh;
    if (None? res) {
      Trade.elim _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl
          gl
      );
      pres := res;
    } else {
      Trade.elim_hyp_l _ _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl
          gl
      );
      let kj : Ghost.erased parser_kind = (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
      let pj : parser kj (nlist (SZ.v n') (raw_data_item & raw_data_item)) =
          (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
      let sj : serializer pj =
          (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
      assert (pure (si == serialize_nondep_then serialize_raw_data_item sj));
      let sq : squash (split_nondep_then''_precond pi parse_raw_data_item pj) = ();
      let (lv, lt') = split_nondep_then''
        serialize_raw_data_item
        (jump_raw_data_item ())
        sj
        lt
        sq;
      Trade.trans _ _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl
          gl
      );
      if (Some?.v res) {
        pres := impl_equiv xr_value lv;
        Trade.elim _ (
          pts_to_serialized
            (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
            l #pl
            gl
        );
        pcont := false;
        ()
      } else {
        Trade.elim_hyp_l _ _ (
          pts_to_serialized
            (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
            l #pl
            gl
        );
        Trade.trans _ (
          pts_to_serialized
            (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
            l #pl
            gl
        ) _;
        pts_to_serialized_ext_trade
          sj
          (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          lt';
        Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll);
        pll := lt';
        pn := n';
        ()
      }
    }
  };
  Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v nl) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) ll #pl gll);
  !pres
}

inline_for_extraction
fn impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_with_bound
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> option bool))
  (#bound: Ghost.erased nat)
  (impl_equiv: impl_equiv_with_bound_t bound equiv)
  (nl1: SZ.t)
  (l1: S.slice byte)
  (nl2: SZ.t)
  (l2: S.slice byte)
  (#pl1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v nl1) (raw_data_item & raw_data_item)))
  (#pl2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v nl2) (raw_data_item & raw_data_item)))
requires
  pts_to_serialized (serialize_nlist (SZ.v nl1) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l1 #pl1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2 **
  pure (list_sum (pair_sum raw_data_item_size raw_data_item_size) gl1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) gl2 <= bound)
returns res: option bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v nl1) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l1 #pl1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2 **
  pure (list_sum (pair_sum raw_data_item_size raw_data_item_size) gl1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) gl2 <= bound /\
    res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv gl1) gl2
  )
{
  Trade.refl
    (pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2);
  let mut pl = l2;
  let mut pn = nl2;
  let mut pres = Some true;
  while (
    let n = !pn;
    let res = !pres;
    (SZ.gt n 0sz && (CBOR.Pulse.Raw.Util.eq_Some_true res))
  ) invariant b . exists* l n (gl: nlist (SZ.v n) (raw_data_item & raw_data_item)) res .
    pts_to pl l **
    pts_to pn n **
    pts_to_serialized
      (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l #pl2
      gl **
    Trade.trade
      (pts_to_serialized
        (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
      )
      (pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2) **
    pts_to pres res **
    pts_to_serialized (serialize_nlist (SZ.v nl1) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l1 #pl1 gl1 **
    pure (
      b == (SZ.v n > 0 && res = Some true) /\
      list_sum (pair_sum raw_data_item_size raw_data_item_size) gl1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) gl <= bound /\
      list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv gl1) gl2 == (if res = Some true then list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv gl1) gl else res)
    )
  {
    let l = !pl;
    with gn (gl: nlist (SZ.v gn) (raw_data_item & raw_data_item)) . assert (
      pts_to pn gn **
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
    );
    let n = !pn;
    let n' = SZ.sub n 1sz;
    nlist_cons_as_nondep_then
      (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      (SZ.v n)
      l;
    pts_to_serialized_nondep_then_assoc_l2r
      serialize_raw_data_item
      serialize_raw_data_item
      (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
    );
    let ki : Ghost.erased parser_kind = and_then_kind
      parse_raw_data_item_kind
      (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
    let pi : parser ki (raw_data_item & nlist (SZ.v n') (raw_data_item & raw_data_item)) = nondep_then
        parse_raw_data_item
        (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
    let si : serializer pi = serialize_nondep_then
        serialize_raw_data_item
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
    assume (pure (SZ.fits_u64));
    let (lh, lt) = split_nondep_then'
      serialize_raw_data_item
      (jump_raw_data_item ())
      si
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
    );
    let kj : Ghost.erased parser_kind = (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
    let pj : parser kj (nlist (SZ.v n') (raw_data_item & raw_data_item)) =
        (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
    let sj : serializer pj =
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
    assert (pure (si == serialize_nondep_then serialize_raw_data_item sj));
    let sq : squash (split_nondep_then''_precond pi parse_raw_data_item pj) = ();
    let (lv, lt') = split_nondep_then''
      serialize_raw_data_item
      (jump_raw_data_item ())
      sj
      lt
      sq;
    let res = impl_setoid_assoc_eq_with_overflow impl_equiv nl1 l1 lh lv;
    Trade.elim_hyp_l (pts_to_serialized serialize_raw_data_item lv #pl2 _) _ _;
    Trade.trans_hyp_r _ _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pl2
        gl
    );
    Trade.elim_hyp_l (pts_to_serialized serialize_raw_data_item lh #pl2 _) _ _;
    if (CBOR.Pulse.Raw.Util.eq_Some_true res) {
      Trade.trans _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl2
          gl
      ) _;
      pts_to_serialized_ext_trade
        sj
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        lt';
      Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2);
      pl := lt';
      pn := n';
    } else {
      Trade.elim _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pl2
          gl
      );
      pres := res
    }
  };
  Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2);
  !pres
}

inline_for_extraction
fn impl_equiv_with_bound_of_equiv
  (#t: Type0)
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> t))
  (impl: impl_equiv_t equiv)
  (bound: Ghost.erased nat)
: impl_equiv_with_bound_t #t (Ghost.reveal bound) (Ghost.reveal equiv)
=
  (l1: S.slice byte)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (raw_data_item))
{
  impl l1 l2
}

inline_for_extraction
fn impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow
  (#equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> option bool))
  (impl_equiv: impl_equiv_t equiv)
  (nl1: SZ.t)
  (l1: S.slice byte)
  (nl2: SZ.t)
  (l2: S.slice byte)
  (#pl1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v nl1) (raw_data_item & raw_data_item)))
  (#pl2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v nl2) (raw_data_item & raw_data_item)))
requires
  pts_to_serialized (serialize_nlist (SZ.v nl1) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l1 #pl1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2
returns res: option bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v nl1) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l1 #pl1 gl1 **
  pts_to_serialized (serialize_nlist (SZ.v nl2) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l2 #pl2 gl2 **
  pure (
    res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv gl1) gl2
  )
{
  impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_with_bound
    (impl_equiv_with_bound_of_equiv
      impl_equiv
      (list_sum (pair_sum raw_data_item_size raw_data_item_size) gl1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) gl2)
    )
    nl1 l1 nl2 l2
}

inline_for_extraction
fn impl_equiv_hd_with_bound_of_equiv_hd
  (#t: Type0)
  (equiv: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> t))
  (impl: impl_equiv_hd_t equiv)
  (bound: Ghost.erased nat)
: impl_equiv_hd_with_bound_t #t (Ghost.reveal bound) (Ghost.reveal equiv)
=
  (n1: Ghost.erased nat)
  (l1: S.slice byte)
  (n2: Ghost.erased nat)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist n1 raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist n2 raw_data_item))
{
  impl n1 l1 n2 l2
}

inline_for_extraction
fn impl_check_equiv_map_hd_body
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_data_model: impl_equiv_hd_t data_model)
  (impl_check_equiv_map_hd: impl_check_equiv_map_hd_t data_model)
: impl_check_equiv_map_hd_t (Ghost.reveal data_model)
=
  (map_bound: _)
  (n1: Ghost.erased nat)
  (l1: S.slice byte)
  (n2: Ghost.erased nat)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist n1 raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist n2 raw_data_item))
{
  check_equiv_map_eq data_model (option_sz_v map_bound) (List.Tot.hd gl1) (List.Tot.hd gl2);
  if impl_data_model n1 l1 n2 l2 {
    Some true
  } else {
    let _ = pts_to_serialized_nlist_raw_data_item_head_header' l1 n1;
    let ph1 = nondep_then_fst
      serialize_header
      (jump_header ())
      _
      l1;
    Trade.trans _ _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
    let h1 = read_header () ph1;
    Trade.elim _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
    let _ = pts_to_serialized_nlist_raw_data_item_head_header' l2 n2;
    let ph2 = nondep_then_fst
      serialize_header
      (jump_header ())
      _
      l2;
    Trade.trans _ _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
    let h2 = read_header () ph2;
    Trade.elim _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
    let mt1 = get_header_major_type h1;
    let mt2 = get_header_major_type h2;
    if (mt1 = cbor_major_type_map && mt2 = cbor_major_type_map) {
      if (CBOR.Pulse.Raw.Util.eq_Some_0sz map_bound) {
        None
      } else {
        let map_bound' : option SZ.t = (match map_bound with None -> None | Some b -> Some (SZ.sub b 1sz));
        let bound : Ghost.erased nat = Ghost.hide (
          let Map _ v1 = List.Tot.hd gl1 in
          let Map _ v2 = List.Tot.hd gl2 in
          list_sum (pair_sum raw_data_item_size raw_data_item_size) v1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) v2
        );
        assume (pure (SZ.fits_u64));
        let nv1 = SZ.uint64_to_sizet (argument_as_uint64 (dfst h1) (dsnd h1));
        let nv2 = SZ.uint64_to_sizet (argument_as_uint64 (dfst h2) (dsnd h2));
        let map1 = nlist_hd' serialize_raw_data_item (jump_raw_data_item ()) n1 l1 ();
        let mut ph = h1;
        let c1 = get_header_and_contents map1 ph;
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
        get_map_payload c1 (List.Tot.hd gl1);
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
        pts_to_serialized_nlist_ext
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
          (U64.v (Map?.len (List.Tot.hd gl1)).value)
          c1
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
          (SZ.v nv1);
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
        let map2 = nlist_hd' serialize_raw_data_item (jump_raw_data_item ()) n2 l2 ();
        let c2 = get_header_and_contents map2 ph;
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
        get_map_payload c2 (List.Tot.hd gl2);
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
        pts_to_serialized_nlist_ext
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
          (U64.v (Map?.len (List.Tot.hd gl2)).value)
          c2
          (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
          (SZ.v nv2);
        Trade.trans _ _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
        let res = impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_with_bound
          (impl_check_equiv_aux
            (impl_check_equiv_list
              (impl_equiv_hd_with_bound_of_equiv_hd
                _
                (impl_check_equiv_map_hd map_bound')
                bound
              )
            )
          )
          nv2 c2 nv1 c1;
        if (CBOR.Pulse.Raw.Util.eq_Some_true res) {
          let res = impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_with_bound
          (impl_check_equiv_aux
            (impl_check_equiv_list
              (impl_equiv_hd_with_bound_of_equiv_hd
                _
                (impl_check_equiv_map_hd map_bound')
                bound
              )
            )
          )
          nv1 c1 nv2 c2;
          Trade.elim _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
          Trade.elim _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
          res
        } else {
          Trade.elim _ (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1);
          Trade.elim _ (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2);
          res
        }
      }
    } else {
      Some false
    }
  }
}

#pop-options

inline_for_extraction
fn impl_check_equiv_list_map
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_check_equiv_map_hd: impl_check_equiv_map_hd_t data_model)
  (map_bound: option SZ.t)
: impl_check_equiv_list_t (check_equiv_map data_model (option_sz_v map_bound))
=
  (n1: Ghost.erased nat)
  (l1: S.slice byte)
  (n2: Ghost.erased nat)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist n1 raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist n2 raw_data_item))
{
  let bound : Ghost.erased nat = list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2;
  let sq : squash (
    list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 <= bound
  ) = ();
  impl_check_equiv_list
    (impl_equiv_hd_with_bound_of_equiv_hd
      _
      (impl_check_equiv_map_hd map_bound)
      bound
    )
    n1 l1 n2 l2
    sq
}

inline_for_extraction
fn impl_check_equiv_list_with_bound_of_check_equiv_list
  (#equiv: Ghost.erased (raw_data_item -> raw_data_item -> option bool))
  (i: impl_check_equiv_list_t equiv)
  (bound: Ghost.erased nat)
: impl_check_equiv_list_with_bound_t bound equiv
=
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item))
  (sq: squash (
    list_sum raw_data_item_size gl1 + list_sum raw_data_item_size gl2 <= bound
  ))
{
  if (n1 <> n2) {
    Some false
  } else if (n1 = 0sz) {
    Some true
  } else  {
    i n1 l1 n2 l2
  }
}

inline_for_extraction
fn impl_check_equiv
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (map_bound: option SZ.t)
  (impl_check_equiv_list: impl_check_equiv_list_t (check_equiv_map data_model (option_sz_v map_bound)))
: impl_equiv_t #_ (check_equiv data_model (option_sz_v map_bound))
=
  (l1: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (raw_data_item))
  (l2: S.slice byte)
  (#p2: perm)
  (#gl2: Ghost.erased (raw_data_item))
{
  impl_check_equiv_aux
    (impl_check_equiv_list_with_bound_of_check_equiv_list
      impl_check_equiv_list
      (raw_data_item_size gl1 + raw_data_item_size gl2)
    )
    l1 l2
}

inline_for_extraction
fn impl_list_existsb_with_overflow_map_fst
  (#p: Ghost.erased (raw_data_item -> option bool))
  (#inv: slprop)
  (impl_p: impl_fun_with_invariant_t p inv)
  (n0: SZ.t)
  (l0: S.slice byte)
  (#pm: perm)
  (#gl0: Ghost.erased (nlist (SZ.v n0) (raw_data_item & raw_data_item)))
requires
  inv **
  pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0
returns res: option bool
ensures
  inv **
  pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0 **
  pure (
    res == list_existsb_with_overflow p (List.Tot.map fst gl0)
  )
{
  Trade.refl
    (pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0);
  let mut pl = l0;
  let mut pn = n0;
  let mut pres = Some false;
  while (
    let n = !pn;
    let res = !pres;
    (SZ.gt n 0sz && CBOR.Pulse.Raw.Util.eq_Some_false res)
  ) invariant b . exists* n l (gl: nlist (SZ.v n) (raw_data_item & raw_data_item)) res . (
    inv **
    pts_to pn n **
    pts_to pl l **
    pts_to_serialized (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l #pm gl **
    Trade.trade
      (pts_to_serialized (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l #pm gl)
      (pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0) **
    pts_to pres res **
    pure (
      b == (res = Some false && SZ.gt n 0sz) /\
      list_existsb_with_overflow p (List.Tot.map fst gl0) == (if res = Some false then list_existsb_with_overflow p (List.Tot.map fst gl) else res)
    )
  )
  {
    let n = !pn;
    let n' = SZ.sub n 1sz;
    let l = !pl;
    with gn (gl: nlist (SZ.v gn) (raw_data_item & raw_data_item)) . assert (
      pts_to pn gn **
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pm
        gl
    );
    nlist_cons_as_nondep_then
      (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      (SZ.v n)
      l;
    pts_to_serialized_nondep_then_assoc_l2r
      serialize_raw_data_item
      serialize_raw_data_item
      (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pm
        gl
    );
    let ki : Ghost.erased parser_kind = and_then_kind
      parse_raw_data_item_kind
      (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
    let pi : parser ki (raw_data_item & nlist (SZ.v n') (raw_data_item & raw_data_item)) = nondep_then
        parse_raw_data_item
        (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
    let si : serializer pi = serialize_nondep_then
        serialize_raw_data_item
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
    assume (pure (SZ.fits_u64));
    let (lh, lt) = split_nondep_then'
      serialize_raw_data_item
      (jump_raw_data_item ())
      si
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pm
        gl
    );
    let res = impl_p lh;
    if (CBOR.Pulse.Raw.Util.eq_Some_false res) {
      Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0);
      Trade.elim_hyp_l _ _ _;
      let kj : Ghost.erased parser_kind = (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
      let pj : parser kj (nlist (SZ.v n') (raw_data_item & raw_data_item)) =
          (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
      let sj : serializer pj =
          (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
      assert (pure (si == serialize_nondep_then serialize_raw_data_item sj));
      let sq : squash (split_nondep_then''_precond pi parse_raw_data_item pj) = ();
      let (lv, lt') = split_nondep_then''
        serialize_raw_data_item
        (jump_raw_data_item ())
        sj
        lt
        sq;
      Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0);
      Trade.elim_hyp_l _ _ _;
      pts_to_serialized_ext_trade
        sj
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        lt';
      Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0);
      pl := lt';
      pn := n';
      ()
    } else {
      Trade.elim _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pm
          gl
      );
      pres := res;
    }
  };
  Trade.elim _ _;
  !pres
}

module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 64"

fn rec impl_check_map_depth_aux
  (bound: SZ.t)
  (pl: ref (S.slice byte))
  (n1: SZ.t)
  (l1: Ghost.erased (list raw_data_item))
  (l2: Ghost.erased (list raw_data_item))
  (#l0: Ghost.erased (S.slice byte))
  (#pm: perm)
  (#gn0: Ghost.erased nat)
  (#gl0: Ghost.erased (nlist gn0 raw_data_item))
requires
  pts_to pl l0 **
  pts_to_serialized (serialize_nlist gn0 serialize_raw_data_item) l0 #pm gl0 **
  pure (
    (Ghost.reveal gl0 <: list raw_data_item) == List.Tot.append l1 l2 /\
    List.Tot.length l1 == SZ.v n1
  )
returns res: bool
ensures exists* l' gn' (gl': nlist gn' raw_data_item) .
  pts_to pl l' **
  pts_to_serialized (serialize_nlist gn' serialize_raw_data_item) l' #pm gl' **
  Trade.trade
    (pts_to_serialized (serialize_nlist gn' serialize_raw_data_item) l' #pm gl')
    (pts_to_serialized (serialize_nlist gn0 serialize_raw_data_item) l0 #pm gl0) **
  pure (
    res == check_map_depth (SZ.v bound) l1 /\
    (res ==> (gl' <: list raw_data_item) == Ghost.reveal l2)
  )
{
  Trade.refl (pts_to_serialized (serialize_nlist gn0 serialize_raw_data_item) l0 #pm gl0);
  List.Tot.append_length l1 l2;
  let mut pn = n1;
  let mut pres = true;
  let pl1 = GR.alloc (Ghost.reveal l1);
  while (
    let res = !pres;
    let n = !pn;
    (res && (SZ.gt n 0sz))
  ) invariant b . exists* n l gn (gl: nlist gn raw_data_item) res ll . (
    pts_to pn n **
    pts_to pl l **
    pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl **
    Trade.trade
      (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl)
      (pts_to_serialized (serialize_nlist gn0 serialize_raw_data_item) l0 #pm gl0) **
    pts_to pres res **
    GR.pts_to pl1 ll **
    pure (
      check_map_depth (SZ.v bound) l1 == (res && check_map_depth (SZ.v bound) ll) /\
      (res ==> (List.Tot.length ll == SZ.v n /\ gn == SZ.v n + List.Tot.length l2 /\ (gl <: list raw_data_item) == List.Tot.append ll l2)) /\
      b == (res && SZ.v n > 0)
    )
  ) {
    let l = !pl;
    let n = !pn;
    let n' = SZ.sub n 1sz;
    with gn (gl: nlist gn raw_data_item) . assert (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl);
    let gn' : Ghost.erased nat = gn - 1;
    let gh = pts_to_serialized_nlist_raw_data_item_head_header'
      l
      gn;
    let (hd, tl') = split_nondep_then'
        _ (jump_header ())
        _ l;
    Trade.trans _ _ (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl);
    let h = read_header () hd;
    Trade.elim_hyp_l _ _ _;
    rewrite each gh as h;
    assume (pure (SZ.fits_u64));
    let (_, tl) = split_nondep_then'
      _ (jump_leaf_content () h)
      _ tl';
    Trade.trans _ _ (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl);
    Trade.elim_hyp_l _ _ _;
    pts_to_serialized_nlist_append
      serialize_raw_data_item
      tl _ _;
    Trade.trans _ _ (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl);
    let m = get_header_major_type h;
    with ll . assert (GR.pts_to pl1 ll);
    if (m = cbor_major_type_tagged) {
      GR.op_Colon_Equals pl1 (Tagged?.v (List.Tot.hd ll) :: List.Tot.tl ll);
      Trade.trans _ (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl) _;
      pl := tl;
      ()
    } else if (m = cbor_major_type_array) {
      List.Tot.append_assoc (Array?.v (List.Tot.hd ll)) (List.Tot.tl ll) l2;
      List.Tot.append_length (Array?.v (List.Tot.hd ll)) (List.Tot.tl ll);
      let ll' = Ghost.hide (List.Tot.append (Array?.v (List.Tot.hd ll)) (List.Tot.tl ll));
      List.Tot.append_length ll' l2;
      pts_to_serialized_length _ tl;
      GR.op_Colon_Equals pl1 ll';
      Trade.trans _ (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl) _;
      pl := tl;
      pn := SZ.add (SZ.uint64_to_sizet (argument_as_uint64 (dfst h) (dsnd h))) n';
      ()
    } else if (m = cbor_major_type_map) {
      if (bound = 0sz) {
        Trade.elim _ (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl);
        pres := false
      } else {
        list_of_pair_list_length (Map?.v (List.Tot.hd ll));
        let ll' = Ghost.hide (CBOR.Spec.Util.list_of_pair_list (Map?.v (List.Tot.hd ll)));
        List.Tot.append_assoc ll' (List.Tot.tl ll) l2;
        let l2' = Ghost.hide (List.Tot.append (List.Tot.tl ll) l2);
        List.Tot.append_length ll' l2;
        pts_to_serialized_length _ tl;
        Trade.trans _ (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl) _;
        pl := tl;
        let npairs = SZ.uint64_to_sizet (argument_as_uint64 (dfst h) (dsnd h));
        let res = impl_check_map_depth_aux (SZ.sub bound 1sz) pl (SZ.add npairs npairs) ll' l2';
        Trade.trans _ _ (pts_to_serialized (serialize_nlist gn0 serialize_raw_data_item) l0 #pm gl0);
        if res {
          GR.op_Colon_Equals pl1 (List.Tot.tl ll);
          pn := n';
          ()
        } else {
          pres := false
        }
      }
    } else {
      Trade.trans _ (pts_to_serialized (serialize_nlist gn serialize_raw_data_item) l #pm gl) _;
      pl := tl;
      pn := n';
      GR.op_Colon_Equals pl1 (List.Tot.tl ll);
    }
  };
  GR.free pl1;
  !pres
}

#pop-options

fn impl_check_map_depth
  (bound: SZ.t)
  (n0: SZ.t)
  (l0: S.slice byte)
  (#pm: perm)
  (#gl0: Ghost.erased (nlist (SZ.v n0) raw_data_item))
requires
  pts_to_serialized (serialize_nlist (SZ.v n0) serialize_raw_data_item) l0 #pm gl0
returns res: bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v n0) serialize_raw_data_item) l0 #pm gl0 **
  pure (
    res == check_map_depth (SZ.v bound) gl0
  )
{
  let mut pl = l0;
  List.Tot.append_l_nil gl0;
  let res = impl_check_map_depth_aux bound pl n0 (Ghost.hide (Ghost.reveal gl0)) [];
  Trade.elim _ _;
  res
}

fn impl_check_map_depth_opt
  (bound: option SZ.t)
  (n0: SZ.t)
  (l0: S.slice byte)
  (#pm: perm)
  (#gl0: Ghost.erased (nlist (SZ.v n0) raw_data_item))
requires
  pts_to_serialized (serialize_nlist (SZ.v n0) serialize_raw_data_item) l0 #pm gl0
returns res: bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v n0) serialize_raw_data_item) l0 #pm gl0 **
  pure (
    res == (if None? bound then true else check_map_depth (SZ.v (Some?.v bound)) gl0)
  )
{
  if None? bound {
    true
  } else {
    impl_check_map_depth (Some?.v bound) n0 l0
  }
}

inline_for_extraction
fn impl_list_no_setoid_repeats_with_overflow_map_fst
  (#equiv: Ghost.erased (raw_data_item -> raw_data_item -> option bool))
  (impl_equiv: impl_equiv_t equiv)
  (bound: option SZ.t)
  (n0: SZ.t)
  (l0: S.slice byte)
  (#pm: perm)
  (#gl0: Ghost.erased (nlist (SZ.v n0) (raw_data_item & raw_data_item)))
requires
  pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0
returns res: option bool
ensures
  pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0 **
  pure (
    res == list_no_setoid_repeats_with_overflow equiv (option_sz_v bound) (List.Tot.map fst gl0)
  )
{
  Trade.refl
    (pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0);
  let mut pl = l0;
  let mut pn = n0;
  let mut pres = Some true;
  while (
    let n = !pn;
    let res = !pres;
    (SZ.gt n 0sz && CBOR.Pulse.Raw.Util.eq_Some_true res)
  ) invariant b . exists* n l (gl: nlist (SZ.v n) (raw_data_item & raw_data_item)) res . (
    pts_to pn n **
    pts_to pl l **
    pts_to_serialized (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l #pm gl **
    Trade.trade
      (pts_to_serialized (serialize_nlist (SZ.v n) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l #pm gl)
      (pts_to_serialized (serialize_nlist (SZ.v n0) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) l0 #pm gl0) **
    pts_to pres res **
    pure (
      b == (res = Some true && SZ.gt n 0sz) /\
      list_no_setoid_repeats_with_overflow equiv (option_sz_v bound) (List.Tot.map fst gl0) == (if res = Some true then list_no_setoid_repeats_with_overflow equiv (option_sz_v bound) (List.Tot.map fst gl) else res)
    )
  )
  {
    let n = !pn;
    let n' = SZ.sub n 1sz;
    let l = !pl;
    with gn (gl: nlist (SZ.v gn) (raw_data_item & raw_data_item)) . assert (
      pts_to pn gn **
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pm
        gl
    );
    nlist_cons_as_nondep_then
      (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      (SZ.v n)
      l;
    pts_to_serialized_nondep_then_assoc_l2r
      serialize_raw_data_item
      serialize_raw_data_item
      (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pm
        gl
    );
    let ki : Ghost.erased parser_kind = and_then_kind
      parse_raw_data_item_kind
      (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
    let pi : parser ki (raw_data_item & nlist (SZ.v n') (raw_data_item & raw_data_item)) = nondep_then
        parse_raw_data_item
        (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
    let si : serializer pi = serialize_nondep_then
        serialize_raw_data_item
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
    assume (pure (SZ.fits_u64));
    let (lh, lt) = split_nondep_then'
      serialize_raw_data_item
      (jump_raw_data_item ())
      si
      l;
    Trade.trans _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pm
        gl
    );
    let kj : Ghost.erased parser_kind = (parse_nlist_kind (SZ.v n') (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind));
    let pj : parser kj (nlist (SZ.v n') (raw_data_item & raw_data_item)) =
        (parse_nlist (SZ.v n') (nondep_then parse_raw_data_item parse_raw_data_item));
    let sj : serializer pj =
        (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item));
    assert (pure (si == serialize_nondep_then serialize_raw_data_item sj));
    let sq : squash (split_nondep_then''_precond pi parse_raw_data_item pj) = ();
    let (lv, lt') = split_nondep_then''
      serialize_raw_data_item
      (jump_raw_data_item ())
      sj
      lt
      sq;
    Trade.elim_hyp_l (pts_to_serialized serialize_raw_data_item lv #pm _) _ _;
    Trade.trans_hyp_r _ _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pm
        gl
    );
    pts_to_serialized_ext_trade
      sj
      (serialize_nlist (SZ.v n') (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
      lt';
    Trade.trans_hyp_r _ _ _ (
      pts_to_serialized
        (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
        l #pm
        gl
    );
    let res = impl_list_existsb_with_overflow_map_fst #(Ghost.hide (Ghost.reveal equiv (fst (List.Tot.hd gl)))) (impl_equiv lh) n' lt';
    if None? res {
      Trade.elim _  (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pm
          gl
      );
      pres := None;
    } else if Some?.v res {
      Trade.elim _  (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pm
          gl
      );
      pres := Some false;
    } else {
      pts_to_serialized_nlist_1
        serialize_raw_data_item
        lh;
      Trade.trans_hyp_l _ _ _ (
        pts_to_serialized
          (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
          l #pm
          gl
      );
      if impl_check_map_depth_opt bound 1sz lh {
        Trade.trans _ (
          pts_to_serialized
            (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
            l #pm
            gl
        ) _;
        Trade.elim_hyp_l _ _ _;
        pn := n';
        pl := lt' ;
        ()
      } else {
        Trade.elim _  (
          pts_to_serialized
            (serialize_nlist (SZ.v gn) (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item))
            l #pm
            gl
        );
        pres := None;
      }
    }
  };
  Trade.elim _ _;
  !pres
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn impl_check_valid_item
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (map_bound: option SZ.t)
  (impl_check_equiv: impl_equiv_t #_ (check_equiv data_model (option_sz_v map_bound)))
  (strict_bound_check: bool)
: LowParse.Pulse.Recursive.impl_pred_t #_ serialize_raw_data_item_param (check_valid_item data_model (option_sz_v map_bound) strict_bound_check)
=
  (a: S.slice byte)
  (n: SZ.t)
  (#pm: perm)
  (#va: _)
{
  pts_to_serialized_nlist_raw_data_item_head_header
    a
    (SZ.v n);
  with l gh v' . assert (
    pts_to_serialized
      (LowParse.Spec.Combinators.serialize_nondep_then
        serialize_header
        (LowParse.Spec.Combinators.serialize_nondep_then
          (serialize_leaf_content gh)
          (LowParse.Pulse.Recursive.serialize_nlist_recursive_cons_payload serialize_raw_data_item_param (SZ.v n) l)
        )
      )
      a #pm v'
  );
  let (ah, a1) = split_nondep_then'
    _ (jump_header ())
    _ a;
  Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
  assume (pure (SZ.fits_u64));
  let h = read_header () ah;
  Trade.elim _ _;
  if (get_header_major_type h = cbor_major_type_map) {
    pts_to_serialized_nlist_ext
      _
      (SZ.v n)
      a
      serialize_raw_data_item
      (SZ.v n);
    let hd = nlist_hd
      serialize_raw_data_item
      (jump_raw_data_item ())
      (SZ.v n)
      a;
    Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
    let mut ph = h;
    let c = get_header_and_contents hd ph;
    Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
    get_map_payload c (List.Tot.hd va);
    Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) (serializer_of_tot_serializer (LowParse.Spec.Recursive.serialize_recursive serialize_raw_data_item_param))) a #pm va);
    let res = impl_list_no_setoid_repeats_with_overflow_map_fst
      (impl_check_equiv)
      (if strict_bound_check then map_bound else None)
      (SZ.uint64_to_sizet (argument_as_uint64 (dfst h) (dsnd h)))
      c;
    Trade.elim _ _;
    (CBOR.Pulse.Raw.Util.eq_Some_true res)
  } else {
    true
  }
}

#pop-options

inline_for_extraction
fn impl_check_valid
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (map_bound: option SZ.t)
  (impl_check_equiv: impl_equiv_t #_ (check_equiv data_model (option_sz_v map_bound)))
  (strict_bound_check: bool)
: impl_fun_with_invariant_t #_
    (check_valid data_model (option_sz_v map_bound) strict_bound_check)
    emp
=
  (l1: S.slice byte)
  (#p1: perm)
  (#gl1: _)
{
  assume (pure (SZ.fits_u64));
  impl_holds_on_raw_data_item
    ()
    _
    (impl_check_valid_item map_bound impl_check_equiv strict_bound_check)
    l1
}
