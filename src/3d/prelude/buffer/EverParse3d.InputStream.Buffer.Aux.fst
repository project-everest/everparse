module EverParse3d.InputStream.Buffer.Aux

(* This module is here to break circularity in KReMLin bundles (because Prims must be in the EverParse bundle because of the string type, as opposed to C,FStar,LowStar.) *)

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--__temp_no_proj EverParse3d.InputStream.Buffer.Aux"

noeq
type input_buffer = {
  buf: B.buffer U8.t;
  len: U32.t;
  pos: B.pointer (Ghost.erased U32.t);
  g_all_buf: Ghost.erased (Seq.seq U8.t);
  g_all: Ghost.erased (Seq.seq U8.t);
  prf: squash (
    U32.v len <= B.length buf /\
    Seq.length g_all == U32.v len /\
    B.loc_disjoint (B.loc_buffer buf) (B.loc_buffer pos) /\
    Seq.length g_all_buf == B.length buf /\
    Ghost.reveal g_all == Seq.slice g_all_buf 0 (U32.v len)
  );
}

inline_for_extraction
noextract
let t = input_buffer

unfold
let _live
  (x: t)
  (h: HS.mem)
: Tot prop
=
  B.live h x.buf /\
  B.live h x.pos /\
  U32.v (B.deref h x.pos) <= U32.v x.len /\
  B.as_seq h x.buf == Ghost.reveal x.g_all_buf /\
  Seq.slice (B.as_seq h x.buf) 0 (U32.v x.len) == Ghost.reveal x.g_all

let _footprint
  (x: t)
: Ghost B.loc
  (requires True)
  (ensures (fun y -> B.address_liveness_insensitive_locs `B.loc_includes` y))
= B.loc_buffer x.buf `B.loc_union` B.loc_buffer x.pos

let _get_remaining
  (x: t)
  (h: HS.mem)
: Ghost (Seq.seq U8.t)
  (requires (_live x h))
  (ensures (fun y -> Seq.length y <= U32.v x.len))
= 
  let i = U32.v (B.deref h x.pos) in
  Seq.slice x.g_all i (Seq.length x.g_all)

val make_input_buffer
  (from: B.buffer U8.t)
  (n: U32.t)
  (pos: B.pointer (Ghost.erased U32.t))
: HST.Stack t
  (requires (fun h ->
    B.live h from /\
    B.live h pos /\
    B.loc_disjoint (B.loc_buffer from) (B.loc_buffer pos) /\
    U32.v n == B.length from
  ))
  (ensures (fun h res h' ->
    B.modifies (B.loc_buffer from `B.loc_union` B.loc_buffer pos) h h' /\
    _footprint res `B.loc_includes` (B.loc_buffer from `B.loc_union` B.loc_buffer pos) /\
    (B.loc_buffer from `B.loc_union` B.loc_buffer pos) `B.loc_includes` _footprint res /\
    _live res h' /\
    _get_remaining res h' == B.as_seq h from
  ))

open LowStar.BufferOps

let make_input_buffer from n pos =
  let h = HST.get () in
  let g = Ghost.hide (B.as_seq h from) in
  pos *= 0ul;
  {
    buf = from;
    len = n;
    pos = pos;
    g_all = g;
    g_all_buf = g;
    prf = ();
  }

(* default error handler *)

let default_error_handler
  (typename: string)
  (fieldname: string)
  (reason: string)
  (context: B.pointer ResultOps.error_frame)
  (input: input_buffer)
  (start_pos: U32.t)
: HST.Stack unit
  (requires (fun h -> B.live h context))
  (ensures (fun h _ h' -> B.modifies (B.loc_buffer context) h h'))
=
  if not ( !* context ).ResultOps.filled then begin
    context *= {
      ResultOps.filled = true;
      ResultOps.start_pos = start_pos;
      ResultOps.typename = typename;
      ResultOps.fieldname = fieldname;
      ResultOps.reason = reason;
    }
  end
