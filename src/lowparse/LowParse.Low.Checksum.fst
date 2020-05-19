module LowParse.Low.Checksum
include LowParse.Low.Combinators

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module U32 = FStar.UInt32
module Ghost = FStar.Ghost

inline_for_extraction
let cut
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (sl: slice (B.trivial_preorder _) (B.trivial_preorder _))
  (pos: U32.t)
: HST.Stack (slice (B.trivial_preorder _) (B.trivial_preorder _))
  (requires (fun h ->
    valid p h sl pos
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    valid p h sl pos /\
    loc_slice_from_to sl pos (get_valid_pos p h sl pos) == B.loc_buffer res.base /\
    B.live h res.base /\
    B.as_seq h res.base == serialize s (contents p h sl pos) /\
    res.len == B.len res.base
  ))
= let h = HST.get () in
  let pos' = j sl pos in
  let x = Ghost.hide (contents p h sl pos) in
  valid_facts p h sl pos;
  parsed_data_is_serialize s (bytes_of_slice_from h sl pos);
  parse_serialize s x;
  parse_strong_prefix p (serialize s x) (bytes_of_slice_from h sl pos);
  let len = (pos' `U32.sub` pos) in
  let base =  B.sub sl.base pos len in
  { base = base; len = len; }

inline_for_extraction
let checksum
  (#k: parser_kind)
  (#t: eqtype)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (checksum_spec: (bytes -> GTot t))
  (zero: Ghost.erased t)
  (checksum_impl: (
    (b1: B.buffer byte) ->
    (len1: U32.t { B.len b1 == len1 }) ->
    (b2: B.buffer byte) ->
    (len2: U32.t { B.len b2 == len2 }) ->
    HST.Stack t
    (requires (fun h ->
      B.live h b1 /\
      B.live h b2
    ))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      res == checksum_spec (B.as_seq h b1 `Seq.append` serialize s zero `Seq.append` B.as_seq h b2) 
    ))
  ))
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1)
  (j1: jumper p1 { k1.parser_kind_subkind == Some ParserStrong })
  (r: leaf_reader p)
  (j: jumper p)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (j2: jumper p2 { k2.parser_kind_subkind == Some ParserStrong })
  (sl: slice (B.trivial_preorder _) (B.trivial_preorder _))
  (pos: U32.t)
: HST.Stack bool
  (requires (fun h ->
    valid ((p1 `nondep_then` p) `nondep_then` p2) h sl pos
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    valid ((p1 `nondep_then` p) `nondep_then` p2) h sl pos /\
    begin let ((x1, x), x2) = contents ((p1 `nondep_then` p) `nondep_then` p2) h sl pos in
      res == (x = checksum_spec (serialize ((s1 `serialize_nondep_then` s) `serialize_nondep_then` s2) ((x1, Ghost.reveal zero), x2)))
    end
  ))
= let h = HST.get () in
  valid_nondep_then h (p1 `nondep_then` p) p2 sl pos;
  valid_nondep_then h p1 p sl pos;
  let sl1 = cut j1 s1 sl pos in
  let posx = j1 sl pos in
  let x = r sl posx in
  let pos2 = j sl posx in
  let sl2 = cut j2 s2 sl pos2 in
  let pos' = j2 sl pos2 in
  let x' = checksum_impl sl1.base sl1.len sl2.base sl2.len in
  let x1 = Ghost.hide (contents p1 h sl pos) in
  let x2 = Ghost.hide (contents p2 h sl pos2) in
  serialize_nondep_then_eq (s1 `serialize_nondep_then` s) s2 ((Ghost.reveal x1, Ghost.reveal zero), Ghost.reveal x2);
  serialize_nondep_then_eq s1 s (Ghost.reveal x1, Ghost.reveal zero);
  x = x'
