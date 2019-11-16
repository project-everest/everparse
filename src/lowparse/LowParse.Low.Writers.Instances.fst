module LowParse.Low.Writers.Instances
include LowParse.Low.Writers
include LowParse.Low.Combinators
include LowParse.Low.Bytes

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
    swvalue w2 == f12 (swvalue w1)
  })
= SWriter (Ghost.hide (f12 (swvalue w1))) (fun pout_from ->
    serialized_length_eq (serialize_synth p1 f12 s1 f21 ()) (f12 (swvalue w1));
    serialized_length_eq s1 (swvalue w1);
    serialize_synth_eq p1 f12 s1 f21 () (f12 (swvalue w1));
    synth_injective_synth_inverse_synth_inverse_recip f12 f21 ();
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
