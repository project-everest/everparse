module EverParse3d.InputBuffer.Aux

module LPL = LowParse.Low.Base
module R = EverParse3d.Readable
module B = LowStar.Buffer
module U32 = FStar.UInt32

#set-options "--__temp_no_proj EverParse3d.InputBuffer.Aux"

inline_for_extraction
let input_buffer
  (len: U32.t)
: Tot Type0
= (base: (base: B.buffer LPL.byte { U32.v len <= B.length base }) & R.perm base)
