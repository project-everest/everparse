module LowParseWriters.LowParse

module LP = LowParse.Low.Combinators
module LPI = LowParse.Low.Int
module U8 = FStar.UInt8
module Seq = FStar.Seq

noeq
inline_for_extraction
type parser'' t = {
  kind: (kind: LP.parser_kind { kind.LP.parser_kind_subkind == Some LP.ParserStrong }); // needed because of star; will be a problem with parse_list...
  parser: LP.parser kind t;
  serializer: LP.serializer parser;
  jumper: LP.jumper parser;
}

let parser' t = (parser'' t)

let slice_of_buffer
  (b: B.buffer U8.t)
: GTot (LP.slice _ _)
= LP.make_slice b (B.len b)

let valid_pos
  p h b pos pos'
= LP.valid_pos (dsnd p).parser h (slice_of_buffer b) pos pos'

let valid_pos_post
  p h b pos pos'
= ()

let contents
  p h b pos pos'
=
  LP.contents (dsnd p).parser h (slice_of_buffer b) pos

let size
  p x
= Seq.length (LP.serialize (dsnd p).serializer x)

let contents_size
  p h b pos pos'
= LP.valid_pos_valid_exact (dsnd p).parser h (slice_of_buffer b) pos pos';
  LP.valid_exact_serialize (dsnd p).serializer h (slice_of_buffer b) pos pos'

let emp' = {
  kind = _;
  parser = LP.parse_empty;
  serializer = LP.serialize_empty;
  jumper = LP.jump_empty;
}

let valid_emp
  h b pos pos'
=
  LP.valid_exact_equiv LP.parse_empty h (slice_of_buffer b) pos pos'

let size_emp = ()

let star'
  #t1 #t2 p1 p2
= {
  kind = _;
  parser = LP.nondep_then p1.parser p2.parser;
  serializer = LP.serialize_nondep_then p1.serializer p2.serializer;
  jumper = LP.jump_nondep_then p1.jumper p2.jumper;
}

let valid_star
  p1 p2 h b pos1 pos2 pos3
=
  LP.valid_nondep_then h (dsnd p1).parser (dsnd p2).parser (slice_of_buffer b) pos1

let size_star
  p1 p2 x1 x2
=
  LP.length_serialize_nondep_then (dsnd p1).serializer (dsnd p2).serializer x1 x2

let valid_frame
  p h b pos pos' l h'
= ()

unfold
let valid'
  (#rrel #rel: _)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (h: HS.mem)
  (s: LP.slice rrel rel)
  (pos: U32.t)
: GTot Type0
= U32.v pos <= U32.v s.LP.len /\
  LP.live_slice h s /\
  Some? (LP.parse p (LP.bytes_of_slice_from h s pos))

let valid_gsub_elim
  p h b pos0 pos1 pos2 len
= let s = slice_of_buffer b in
  let s' = slice_of_buffer (B.gsub b pos0 len) in
  LP.valid_facts (dsnd p).parser h s (pos0 `U32.add` pos1);
  LP.valid_facts (dsnd p).parser h s' pos1;
  LP.parse_strong_prefix (dsnd p).parser (LP.bytes_of_slice_from h s' pos1) (LP.bytes_of_slice_from h s (pos0 `U32.add` pos1))

let valid_gsub_intro
  p h b pos0 pos1 pos2 len
= let s = slice_of_buffer b in
  let s' = slice_of_buffer (B.gsub b pos0 len) in
  LP.valid_facts (dsnd p).parser h s (pos0 `U32.add` pos1);
  LP.valid_facts (dsnd p).parser h s' pos1;
  LP.parse_strong_prefix (dsnd p).parser (LP.bytes_of_slice_from h s (pos0 `U32.add` pos1)) (LP.bytes_of_slice_from h s' pos1)

let parse_u32' = {
  kind = _;
  parser = LPI.parse_u32;
  serializer = LPI.serialize_u32;
  jumper = LPI.jump_u32;
}

let write_u32
  b len x
= if len `U32.lt` 4ul
  then None
  else Some (LPI.write_u32 x (LP.make_slice b len) 0ul)

let valid_star_inv
  p1 p2 b len pos1 pos3
=
  let h = HST.get () in
  LP.valid_nondep_then h (dsnd p1).parser (dsnd p2).parser (LP.make_slice b len) pos1;
  (dsnd p1).jumper (LP.make_slice b len) pos1

let clens_to_lp_clens
  (#t1 #t2: Type)
  (c: clens t1 t2)
: GTot (LP.clens t1 t2)
= {
  LP.clens_cond = c.clens_cond;
  LP.clens_get = c.clens_get
}

let gaccessor
  p1 p2 lens
= LP.gaccessor (dsnd p1).parser (dsnd p2).parser (clens_to_lp_clens lens)

let gaccess
  #p1 #p2 #lens g h b
=
  let sl = LP.make_slice b (B.len b) in
  LP.valid_facts (dsnd p1).parser h sl 0ul;
  let posn = g (B.as_seq h b) in
  let pos = U32.uint_to_t posn in
  LP.valid_facts (dsnd p2).parser h sl pos;
  let pos' = LP.get_valid_pos (dsnd p2).parser h sl pos in
  let b1 = B.gsub b pos (B.len b `U32.sub` pos) in
  let len' = pos' `U32.sub` pos in
  let b' = B.gsub b1 0ul len' in
  LP.parse_strong_prefix (dsnd p2).parser (B.as_seq h b1) (B.as_seq h b');
  let sl' = LP.make_slice b' (B.len b') in
  LP.valid_facts (dsnd p2).parser h sl' 0ul;
  b'

let gaccessor_frame1
  (#p1 #p2: parser)
  (#lens: clens (dfst p1) (dfst p2))
  (g: gaccessor p1 p2 lens)
  (h: HS.mem)
  (b: B.buffer u8)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    B.modifies l h h' /\
    B.loc_disjoint l (B.loc_buffer b) /\ (
      (
        valid_buffer p1 h b /\
        lens.clens_cond (buffer_contents p1 h b)
      )
  )))
  (ensures (
    valid_buffer p1 h b /\
    valid_buffer p1 h' b /\
    buffer_contents p1 h b == buffer_contents p1 h' b /\
    lens.clens_cond (buffer_contents p1 h b) /\
    lens.clens_cond (buffer_contents p1 h' b) /\
    gaccess g h' b == gaccess g h b
  ))
= let sl = LP.make_slice b (B.len b) in
  LP.valid_facts (dsnd p1).parser h sl 0ul;
  let posn = g (B.as_seq h b) in
  let pos = U32.uint_to_t posn in
  LP.valid_facts (dsnd p2).parser h sl pos;
  let pos' = LP.get_valid_pos (dsnd p2).parser h sl pos in
  let b1 = B.gsub b pos (B.len b `U32.sub` pos) in
  let len' = pos' `U32.sub` pos in
  let b' = B.gsub b1 0ul len' in
  LP.parse_strong_prefix (dsnd p2).parser (B.as_seq h b1) (B.as_seq h b');
  let sl' = LP.make_slice b' (B.len b') in
  LP.valid_facts (dsnd p2).parser h sl' 0ul;
  ()

let gaccessor_frame
  #p1 #p2 #lens g h b l h'
=
  Classical.forall_intro (Classical.move_requires (gaccessor_frame1 g h b l))
