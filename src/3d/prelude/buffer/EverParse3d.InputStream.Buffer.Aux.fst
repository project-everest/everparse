module EverParse3d.InputStream.Buffer.Aux

(* This module is here to break circularity in KReMLin bundles (because Prims must be in the EverParse bundle because of the string type, as opposed to C,FStar,LowStar.) *)

module IB = EverParse3d.InputBuffer
module IR = EverParse3d.Readable
module LP = LowParse.Low.Base
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--__temp_no_proj EverParse3d.InputStream.Buffer.Aux"

noeq
type input_buffer = {
  len0: Ghost.erased U32.t;
  buf: IB.input_buffer_t len0;
  perm_of: IR.perm (IB.slice_of buf).LP.base;
  len: Ghost.erased U32.t;
  pos: B.pointer (Ghost.erased U32.t);
  g_all_buf: Ghost.erased (Seq.seq U8.t);
  g_all: Ghost.erased (Seq.seq U8.t);
  prf: squash (
    U32.v len <= U32.v len0 /\
    Seq.length g_all == U32.v len /\
    B.loc_disjoint (B.loc_buffer (IB.slice_of buf).LP.base `B.loc_union` IR.loc_perm perm_of) (B.loc_buffer pos) /\
    Seq.length g_all_buf == U32.v len0 /\
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
  IB.live_input_buffer h x.buf x.perm_of /\
  B.live h x.pos /\
  U32.v (B.deref h x.pos) <= U32.v x.len /\
  B.as_seq h (IB.slice_of x.buf).LP.base == Ghost.reveal x.g_all_buf /\
  IR.unreadable h x.perm_of 0ul (B.deref h x.pos) /\
  IR.readable h x.perm_of (B.deref h x.pos) x.len0 /\
  Seq.slice (B.as_seq h (IB.slice_of x.buf).LP.base) 0 (U32.v x.len) == Ghost.reveal x.g_all

let _footprint
  (x: t)
: Ghost B.loc
  (requires True)
  (ensures (fun y -> B.address_liveness_insensitive_locs `B.loc_includes` y))
= B.loc_buffer (IB.slice_of x.buf).LP.base `B.loc_union` IR.loc_perm x.perm_of `B.loc_union` B.loc_buffer x.pos

let _perm_footprint
  (x: t)
: Ghost B.loc
  (requires True)
  (ensures (fun y -> _footprint x `B.loc_includes` y))
= IR.loc_perm x.perm_of `B.loc_union` B.loc_buffer x.pos

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
  (typename_s: string)
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
      EverParse3d.ErrorCode.typename_s = typename_s;
      EverParse3d.ErrorCode.fieldname = fieldname;
      EverParse3d.ErrorCode.reason = reason;
    }
  end
