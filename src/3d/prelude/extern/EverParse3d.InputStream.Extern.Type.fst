module EverParse3d.InputStream.Extern.Type
include EverParse3d.InputStream.Extern.Base

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U8 = FStar.UInt8

inline_for_extraction
noeq
type input_stream = {
  base: t;
  has_length: bool;
  length: U32.t;
  position: B.pointer U32.t;
  prf: squash (
    B.loc_disjoint (footprint base) (B.loc_buffer position) /\
    (has_length == true ==> U32.v length <= U32.v (len_all base))
  );
}
