module EverParse3d.CopyBuffer
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Pulse.Lib.Pervasives

noextract
inline_for_extraction
class copy_buffer (copy_buffer_t: Type0) (base_t: Type0) (len_t: Type0) (pos_t: Type0) {| I.input_stream_inst base_t len_t pos_t |} = {
  base_of : copy_buffer_t -> base_t;
  len_of : copy_buffer_t -> len_t;
  pos_of : copy_buffer_t -> pos_t;
}

let pts_to
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| I.input_stream_inst base_t len_t pos_t |}
  {| copy_buffer copy_buffer_t base_t len_t pos_t |}
  (c: copy_buffer_t) (contents: Seq.seq U8.t) (v: Seq.seq U8.t) : Tot slprop =
  I.pts_to #base_t #len_t #pos_t
    (base_of #_ #base_t #len_t #pos_t c)
    (len_of #_ #base_t #len_t #pos_t c)
    (pos_of #_ #base_t #len_t #pos_t c)
    contents v
