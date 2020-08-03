module LowParse.Slice
open LowParse.Bytes

module B = LowStar.Monotonic.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack

inline_for_extraction
noextract
type srel (a: Type) = (B.srel a)

inline_for_extraction
noextract
let buffer_srel_of_srel (#a: Type) (s: srel a) : Tot (B.srel a) =
  s

inline_for_extraction
noextract
let srel_of_buffer_srel (#a: Type) (s: B.srel a) : Tot (srel a) =
  s

let buffer_srel_of_srel_of_buffer_srel (#a: Type) (s: B.srel a) : Lemma
  (buffer_srel_of_srel (srel_of_buffer_srel s) == s)
  [SMTPat (buffer_srel_of_srel (srel_of_buffer_srel s))]
= ()

noeq
inline_for_extraction
type slice (rrel rel: srel byte) = {
  base: B.mbuffer byte (buffer_srel_of_srel rrel) (buffer_srel_of_srel rel);
  len: (len: U32.t { U32.v len <= B.length base } );
}

inline_for_extraction
noextract
let make_slice
  (#rrel #rel: _)
  (b: B.mbuffer byte rrel rel)
  (len: U32.t { U32.v len <= B.length b } )
: Tot (slice (srel_of_buffer_srel rrel) (srel_of_buffer_srel rel))
= {
  base = b;
  len = len;
}

let live_slice  (#rrel #rel: _) (h: HS.mem) (s: slice rrel rel) : GTot Type0 = B.live h s.base

let bytes_of_slice_from   (#rrel #rel: _)
  (h: HS.mem) (s: slice rrel rel) (pos: U32.t) : GTot bytes =
  if (U32.v pos <= U32.v s.len)
  then Seq.slice (B.as_seq h s.base) (U32.v pos) (U32.v s.len)  
  else Seq.empty

let loc_slice_from_to (#rrel #rel: _) (s: slice rrel rel) (pos pos' : U32.t) : GTot B.loc =
  B.loc_buffer_from_to s.base pos pos'

let loc_slice_from (#rrel #rel: _) (s: slice rrel rel) (pos: U32.t) : GTot B.loc =
  loc_slice_from_to s pos s.len
