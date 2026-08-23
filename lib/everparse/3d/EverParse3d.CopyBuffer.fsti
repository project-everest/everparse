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

  (* Rewind to the beginning. A copy buffer is reused across probe sites, so
     the position it is left at by one `probe_then_validate` has to be undone
     before the next one validates from it. The Low* interpreter has no
     equivalent because there the position is not part of the buffer: it is
     passed to the validator, which `probe_then_validate` calls at `0uL`. *)
  reset :
    (c: copy_buffer_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt unit
      (I.pts_to #base_t #len_t #pos_t (base_of c) (len_of c) (pos_of c) contents v)
      (fun _ -> I.pts_to #base_t #len_t #pos_t (base_of c) (len_of c) (pos_of c) contents contents);
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
