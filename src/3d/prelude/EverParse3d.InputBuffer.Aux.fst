module EverParse3d.InputBuffer.Aux

module LPL = LowParse.Low.Base
module R = EverParse3d.Readable
module B = LowStar.Buffer
module U32 = FStar.UInt32

#set-options "--__temp_no_proj EverParse3d.InputBuffer.Aux"

noeq
type input_buffer = {
  base: B.buffer LPL.byte;
  perm: R.perm base;
  len: (length: U32.t { U32.v length <= B.length base });
}
