module LowParse.Low.Writers.Instances
include LowParse.Low.Writers
include LowParse.Low.Combinators
include LowParse.Low.Bytes
include LowParse.Low.BitSum

module HS = FStar.HyperStack
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

inline_for_extraction
noextract
let swrite_nondep_then
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (#s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#space_beyond: nat)
  (w1: swriter s1 h0 space_beyond sout pout_from0)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (#s2: serializer p2 { k2.parser_kind_subkind == Some ParserStrong })
  (w2: swriter s2 h0 space_beyond sout pout_from0)
: Tot (w: swriter (s1 `serialize_nondep_then` s2) h0 space_beyond sout pout_from0 {
    swvalue w == (swvalue w1, swvalue w2)
  })
= SWriter (Ghost.hide (swvalue w1, swvalue w2)) (fun pout_from ->
    serialized_length_eq (s1 `serialize_nondep_then` s2) (swvalue w1, swvalue w2);
    serialize_nondep_then_eq s1 s2 (swvalue w1, swvalue w2);
    serialized_length_eq s1 (swvalue w1);
    serialized_length_eq s2 (swvalue w2);
    let pos1 = swrite w1 pout_from in
    let pos2 = swrite w2 pos1 in
    let h' = HST.get () in
    valid_nondep_then h' p1 p2 sout pout_from;
    pos2
  )

inline_for_extraction
noextract
let swrite_filter
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (#s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#space_beyond: nat)
  (cond: (t1 -> GTot bool)) 
  (w1: swriter s1 h0 space_beyond sout pout_from0 { cond (swvalue w1) } )
: Tot (w2: swriter (serialize_filter s1 cond) h0 space_beyond sout pout_from0 {
    swvalue w2 == swvalue w1
  })
= SWriter (Ghost.hide (swvalue w1)) (fun pout_from ->
    serialized_length_eq (serialize_filter s1 cond) (swvalue w1);
    serialized_length_eq s1 (swvalue w1);
    let res = swrite w1 pout_from in
    let h = HST.get () in
    valid_filter h p1 cond sout pout_from;
    res
  )

inline_for_extraction
noextract
let swrite_synth
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (#s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#space_beyond: nat)
  (w1: swriter s1 h0 space_beyond sout pout_from0)
  (#t2: Type0)
  (f12: (t1 -> GTot t2))
  (f21: (t2 -> GTot t1))
  (prf: squash (
    synth_injective f12 /\
    synth_inverse f12 f21
  ))
: Tot (w2: swriter (serialize_synth p1 f12 s1 f21 ()) h0 space_beyond sout pout_from0 {
    swvalue w2 == f12 (swvalue w1) /\
    swvalue w1 == f21 (swvalue w2)
  })
= [@inline_let] let _ =
    serialize_synth_eq p1 f12 s1 f21 () (f12 (swvalue w1));
    synth_injective_synth_inverse_synth_inverse_recip f12 f21 ()
  in
  SWriter (Ghost.hide (f12 (swvalue w1))) (fun pout_from ->
    serialized_length_eq (serialize_synth p1 f12 s1 f21 ()) (f12 (swvalue w1));
    serialized_length_eq s1 (swvalue w1);
    let res = swrite w1 pout_from in
    let h = HST.get () in
    valid_synth h p1 f12 sout pout_from;
    res
  )

module U8 = FStar.UInt8
module FB = FStar.Bytes

#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let swrite_bounded_vlbytes
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (len: U32.t { min <= U32.v len /\ U32.v len <= max })
  (b: B.lbuffer U8.t (U32.v len) {
    B.live h0 b /\
    B.loc_disjoint (B.loc_buffer b) (loc_slice_from sout pout_from0)
  })
: Tot (w: swriter (serialize_bounded_vlbytes min max) h0 0 sout pout_from0 {
    swvalue w == FB.hide (B.as_seq h0 b)
  })
= SWriter (Ghost.hide (FB.hide (B.as_seq h0 b))) (fun pout_from ->
    serialized_length_eq (serialize_bounded_vlbytes min max) (FB.hide (B.as_seq h0 b));
    length_serialize_bounded_vlbytes min max (FB.hide (B.as_seq h0 b));
    let pout_payload = pout_from `U32.add` U32.uint_to_t (log256' max) in
    let payload = B.sub sout.base pout_payload len in
    B.blit b 0ul payload 0ul len;
    finalize_bounded_vlbytes min max sout pout_from len
  )

inline_for_extraction
noextract
let swrite_bounded_vlgenbytes
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#kk: parser_kind)
  (#pk: parser kk (bounded_int32 min max))
  (#sk: serializer pk { kk.parser_kind_subkind == Some ParserStrong })
  (wk: leaf_writer_strong sk)
  (len: U32.t { min <= U32.v len /\ U32.v len <= max })
  (b: B.lbuffer U8.t (U32.v len) {
    B.live h0 b /\
    B.loc_disjoint (B.loc_buffer b) (loc_slice_from sout pout_from0)
  })
: Tot (w: swriter (serialize_bounded_vlgenbytes min max sk) h0 0 sout pout_from0 {
    swvalue w == FB.hide (B.as_seq h0 b)
  })
= SWriter (Ghost.hide (FB.hide (B.as_seq h0 b))) (fun pout_from ->
    serialized_length_eq (serialize_bounded_vlgenbytes min max sk) (FB.hide (B.as_seq h0 b));
    length_serialize_bounded_vlgenbytes min max sk (FB.hide (B.as_seq h0 b));
    serialized_length_eq sk len;
    let pout_payload = swrite (swrite_leaf wk h0 sout pout_from0 len) pout_from in
    let payload = B.sub sout.base pout_payload len in
    B.blit b 0ul payload 0ul len;
    let h = HST.get () in
    valid_bounded_vlgenbytes min max pk sout pout_from h;
    pout_payload `U32.add` len
  )

#pop-options

#push-options "--z3rlimit 32"

inline_for_extraction
noextract
let swrite_bitsum
  (h0: HS.mem)
  (space_beyond: nat)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (#kt: parser_kind)
  (#tot: pos)
  (#t: eqtype)
  (#cl: uint_t tot t)
  (b: bitsum' cl tot)
  (#data: Type0)
  (tag_of_data: (data -> Tot (bitsum'_type b)))
  (type_of_tag: (bitsum'_key_type b -> Tot Type0))
  (synth_case: synth_case_t b data tag_of_data type_of_tag)
  (#p: parser kt t)
  (#s: serializer p { kt.parser_kind_subkind == Some ParserStrong } )
  (w_tg: leaf_writer_strong s)
  (mk: synth_bitsum'_recip_t b)
  (#f: (x: bitsum'_key_type b) -> Tot (k: parser_kind & parser k (type_of_tag x)))
  (g: (x: bitsum'_key_type b) -> Tot (serializer (dsnd (f x))))
  (k: bitsum'_type b {
    (parse_bitsum_kind kt b type_of_tag f).parser_kind_subkind == Some ParserStrong /\
    (dfst (f (bitsum'_key_of_t b k))).parser_kind_subkind == Some ParserStrong
  })
  (w_pl: swriter (g (bitsum'_key_of_t b k)) h0 space_beyond sout pout_from0)
: Tot (w' : swriter (serialize_bitsum b tag_of_data type_of_tag synth_case s #f g) h0 space_beyond sout pout_from0 {
    swvalue w' == synth_case.f k (swvalue w_pl)
  })
= SWriter (Ghost.hide (synth_case.f k (swvalue w_pl))) (fun pout_from ->
    serialized_length_eq (serialize_bitsum b tag_of_data type_of_tag synth_case s #f g) (synth_case.f k (swvalue w_pl));
    serialized_length_eq s (synth_bitsum'_recip b k);
    serialized_length_eq (g (bitsum'_key_of_t b k)) (swvalue w_pl);
    serialize_bitsum_eq_2 b tag_of_data type_of_tag synth_case s g k (swvalue w_pl);
    let pos1 = w_tg (mk k) sout pout_from in
    let pos2 = swrite w_pl pos1 in
    let h = HST.get () in
    valid_filter h p (filter_bitsum' b) sout pout_from;
    synth_bitsum'_injective b;
    synth_bitsum'_recip_inverse b;
    assert (filter_bitsum' b (mk k) == true);
    assert (synth_bitsum' b (mk k) == k);
    valid_synth h (p `parse_filter` filter_bitsum' b) (synth_bitsum' b) sout pout_from;
    valid_bitsum_intro b tag_of_data type_of_tag synth_case p f h sout pout_from;
    pos2
  )

#pop-options
