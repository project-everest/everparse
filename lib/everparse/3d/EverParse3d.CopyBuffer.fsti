module EverParse3d.CopyBuffer
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Pulse.Lib.Pervasives

class copy_buffer (copy_buffer_t: Type0) (input_buffer_t: Type0) {| I.input_stream_inst input_buffer_t |} = {
  stream_of : copy_buffer_t -> input_buffer_t;
}

let pts_to
  (#copy_buffer_t #input_buffer_t: Type0)
  {| I.input_stream_inst input_buffer_t |}
  {| copy_buffer copy_buffer_t input_buffer_t |}
  (c: copy_buffer_t) (contents: Seq.seq U8.t) (v: Seq.seq U8.t) : Tot slprop =
  I.pts_to #input_buffer_t (stream_of c) contents v
