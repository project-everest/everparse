module LowParseWriters.LowParse

module LP = LowParse.Low.Combinators
module LPI = LowParse.Low.Int
module U8 = FStar.UInt8
module Seq = FStar.Seq

noeq
type parser'' t = {
  kind: (kind: LP.parser_kind { kind.LP.parser_kind_subkind == Some LP.ParserStrong }); // needed because of star; will be a problem with parse_list...
  parser: LP.parser kind t;
  serializer: LP.serializer parser;
}

let parser' t = Ghost.erased (parser'' t)

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

let valid_gsub
  p h b pos0 pos1 pos2 len
= let s = slice_of_buffer b in
  let s' = slice_of_buffer (B.gsub b pos0 len) in
  LP.valid_facts (dsnd p).parser h s (pos0 `U32.add` pos1);
  LP.valid_facts (dsnd p).parser h s' pos1;
  LP.parse_strong_prefix (dsnd p).parser (LP.bytes_of_slice_from h s' pos1) (LP.bytes_of_slice_from h s (pos0 `U32.add` pos1))

let parse_u32' = {
  kind = _;
  parser = LPI.parse_u32;
  serializer = LPI.serialize_u32;
}

let write_u32
  b len x
= if len `U32.lt` 4ul
  then None
  else Some (LPI.write_u32 x (LP.make_slice b len) 0ul)
