module EverParse3d.InputStream.Buffer.Aux

(* This module is here to break circularity in KReMLin bundles (because Prims must be in the EverParse bundle because of the string type, as opposed to C,FStar,LowStar.) *)

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--__temp_no_proj EverParse3d.InputStream.Buffer.Aux"

noeq
type input_buffer = {
  buf: B.buffer U8.t;
  len: Ghost.erased U32.t;
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

(* default error handler *)

open LowStar.BufferOps

let default_error_handler
  (typename: string)
  (fieldname: string)
  (reason: string)
  (context: B.pointer EverParse3d.ErrorCode.error_frame)
  (input: input_buffer)
  (start_pos: U64.t)
: HST.Stack unit
  (requires (fun h -> B.live h context))
  (ensures (fun h _ h' -> B.modifies (B.loc_buffer context) h h'))
=
  if not ( !* context ).EverParse3d.ErrorCode.filled then begin
    context *= {
      EverParse3d.ErrorCode.filled = true;
      EverParse3d.ErrorCode.start_pos = start_pos;
      EverParse3d.ErrorCode.typename = typename;
      EverParse3d.ErrorCode.fieldname = fieldname;
      EverParse3d.ErrorCode.reason = reason;
    }
  end
