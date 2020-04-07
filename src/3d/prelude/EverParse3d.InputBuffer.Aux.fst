module EverParse3d.InputBuffer.Aux

module LPL = LowParse.Low.Base
module R = EverParse3d.Readable
module B = LowStar.Buffer
module U32 = FStar.UInt32

inline_for_extraction
noeq
type input_buffer = {
  base: B.buffer LPL.byte;
  perm: R.perm base;
  len: (length: U32.t { U32.v length <= B.length base });
}
