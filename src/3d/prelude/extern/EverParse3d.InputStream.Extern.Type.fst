module EverParse3d.InputStream.Extern.Type
include EverParse3d.InputStream.Extern.Base

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U8 = FStar.UInt8

inline_for_extraction
noeq
type input_buffer = {
  base: t;
  has_length: bool;
  length: U32.t;
  position: B.pointer U32.t;
  prf: squash (
    B.loc_disjoint (footprint base) (B.loc_buffer position) /\
    (has_length == true ==> U32.v length <= U32.v (len_all base))
  );
}

open LowStar.BufferOps

let make_input_buffer
  (base: t)
  (position: B.pointer U32.t)
: HST.Stack input_buffer
  (requires (fun h ->
    B.loc_disjoint (footprint base) (B.loc_buffer position) /\
    B.live h position
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer position) h h' 
  ))
= position *= 0ul;
  {
    base = base;
    has_length = false;
    length = 0ul;
    position = position;
    prf = ();
  }

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
