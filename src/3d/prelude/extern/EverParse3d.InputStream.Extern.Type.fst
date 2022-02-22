module EverParse3d.InputStream.Extern.Type
include EverParse3d.InputStream.Extern.Base

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module LPE = EverParse3d.ErrorCode
module U64 = FStar.UInt64

noeq
type input_buffer = {
  base: t;
  has_length: bool;
  length: LPE.pos_t;
  position: B.pointer (Ghost.erased LPE.pos_t);
  prf: squash (
    B.loc_disjoint (footprint base) (B.loc_buffer position) /\
    (has_length == true ==> U64.v length <= U64.v (len_all base))
  );
}

open LowStar.BufferOps

let make_input_buffer
  (base: t)
  (position: B.pointer (Ghost.erased LPE.pos_t))
: HST.Stack input_buffer
  (requires (fun h ->
    B.loc_disjoint (footprint base) (B.loc_buffer position) /\
    B.live h position
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer position) h h' 
  ))
= position *= 0uL;
  {
    base = base;
    has_length = false;
    length = 0uL;
    position = position;
    prf = ();
  }

let default_error_handler
  (typename_s: string)
  (fieldname: string)
  (reason: string)
  (context: B.pointer LPE.error_frame)
  (input: input_buffer)
  (start_pos: U64.t)
: HST.Stack unit
  (requires (fun h -> B.live h context))
  (ensures (fun h _ h' -> B.modifies (B.loc_buffer context) h h'))
=
  if not ( !* context ).LPE.filled then begin
    context *= {
      LPE.filled = true;
      LPE.start_pos = start_pos;
      LPE.typename_s = typename_s;
      LPE.fieldname = fieldname;
      LPE.reason = reason;
    }
  end
