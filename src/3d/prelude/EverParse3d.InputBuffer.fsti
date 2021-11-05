module EverParse3d.InputBuffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LPL = LowParse.Low.Base
module R = EverParse3d.Readable

inline_for_extraction
noextract
let triv = B.trivial_preorder LowParse.Bytes.byte

inline_for_extraction
noextract
val input_buffer_t (len: U32.t) : Type0

include LowParse.Low.Base

val slice_of (#len: U32.t) (x: input_buffer_t len) : GTot (sl: slice triv triv { sl.LPL.len == len })

inline_for_extraction
noextract
let slice_length (#len: U32.t) (x: input_buffer_t len) : Tot (v: U32.t { v == (slice_of x).LPL.len }) =
  len

val perm_of (#len: U32.t) (x: input_buffer_t len) : GTot (R.perm (slice_of x).base)

let live_input_buffer
  (h: HS.mem)
  (#len: U32.t)
  (sl: input_buffer_t len)
: GTot Type0
= LPL.live_slice h (slice_of sl) /\
  R.valid_perm h (perm_of sl)

let valid_input_buffer
  (#k: parser_kind)
  (#t: Type u#0)
  (p: parser k t)
  (h: HS.mem)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos: U32.t)
: GTot Type0
= LPL.valid p h (slice_of sl) pos /\
  R.valid_perm h (perm_of sl)

inline_for_extraction
noextract
val drop
  (#len: U32.t)
  (sl: input_buffer_t len)
  (from: Ghost.erased U32.t)
  (to: Ghost.erased U32.t { U32.v from <= U32.v to /\ U32.v to <= U32.v (slice_of sl).LPL.len })
: HST.Stack unit
  (requires (fun h ->
    R.readable h (perm_of sl) from to
  ))
  (ensures (fun h _ h' ->
    B.modifies (R.loc_perm (perm_of sl)) h h' /\
    live_input_buffer h' sl /\
    R.preserved (perm_of sl) 0ul from h h' /\
    R.preserved (perm_of sl) to (B.len (slice_of sl).LPL.base) h h' /\
    R.unreadable h' (perm_of sl) from to
  ))

inline_for_extraction noextract
val read_with_perm
  (#k: parser_kind)
  (#t: Type u#0)
  (#p: parser k t)
  (r: leaf_reader p)
  (#len: U32.t)
  (sl: input_buffer_t len)
  (pos: U32.t)
: HST.Stack t
  (requires (fun h ->
    valid_input_buffer p h sl pos /\
    R.readable h (perm_of sl) pos (get_valid_pos p h (slice_of sl) pos)
  ))
  (ensures (fun h res h' ->
    let pos' = get_valid_pos p h (slice_of sl) pos in
    B.modifies (R.loc_perm (perm_of sl)) h h' /\
    R.preserved (perm_of sl) 0ul pos h h' /\
    R.preserved (perm_of sl) pos' (B.len (slice_of sl).LPL.base) h h' /\
    R.unreadable h' (perm_of sl) pos pos' /\
    res == contents p h (slice_of sl) pos
  ))

(* for action_field_ptr *)

inline_for_extraction
noextract
val puint8: Type0

inline_for_extraction
noextract
val offset
  (#len: U32.t)
  (sl: input_buffer_t len)
  (off: U32.t)
: HST.Stack puint8
  (requires (fun h ->
    U32.v off <= B.length (slice_of sl).base /\
    live_input_buffer h sl
  ))
  (ensures (fun h _ h' ->
    h' == h
  ))
