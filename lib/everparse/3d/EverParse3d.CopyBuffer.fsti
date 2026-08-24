module EverParse3d.CopyBuffer
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
open Pulse.Lib.Pervasives

(* A copy buffer is one level of indirection above the input stream: a
   reference to a *descriptor* holding the (base, len, pos) triple.

   In Low*, `copy_buffer_t` is an abstract type extracted as an opaque
   pointer, and `stream_of` is a spec-only projection. A probe callback is
   therefore free to *repoint* the copy buffer at the probed bytes instead of
   copying into them, which is what in-place probing does. The indirection
   here recovers that, and keeping it above the stream rather than inside it
   is what lets `probe_then_validate` run the very same validator on the copy
   buffer, with the very same `input_stream_inst`, without any change to the
   stream specs or instances.

   The descriptor type is a field of the class rather than a record defined
   here, so that each backend can pick a monomorphic one. A polymorphic
   record would be monomorphized by KaRaMeL under a mangled name, emitted
   into whichever generated module happens to use it first, instead of the
   stable `EVERPARSE_COPY_BUFFER_DESCR` in `EverParse.h` that hand-written
   probe callbacks need. *)
noextract
inline_for_extraction
class copy_buffer (copy_buffer_t: Type0) (base_t: Type0) (len_t: Type0) (pos_t: Type0) {| I.input_stream_inst base_t len_t pos_t |} = {
  (* The descriptor, and the three components it carries. *)
  descr_t : Type0;
  base_of : descr_t -> base_t;
  len_of : descr_t -> len_t;
  pos_of : descr_t -> pos_t;

  (* The handle. Extracted as a C pointer, so that a probe callback can
     overwrite the descriptor, exactly as the Low* backend allows. *)
  descr : copy_buffer_t -> R.ref descr_t;

  (* Rewind to the beginning. A copy buffer is reused across probe sites, so
     the position it is left at by one `probe_then_validate` has to be undone
     before the next one validates from it. The Low* interpreter has no
     equivalent because there the position is not part of the buffer: it is
     passed to the validator, which `probe_then_validate` calls at `0uL`.
     Removing it here would mean giving the stream class a way to allocate a
     fresh position, which is exactly the kind of change to the input stream
     specs this design avoids. *)
  reset :
    (c: copy_buffer_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt unit
      (exists* (d: descr_t).
        R.pts_to (descr c) d **
        I.pts_to #base_t #len_t #pos_t (base_of d) (len_of d) (pos_of d) contents v)
      (fun _ -> exists* (d: descr_t).
        R.pts_to (descr c) d **
        I.pts_to #base_t #len_t #pos_t (base_of d) (len_of d) (pos_of d) contents contents);
}

(* Note the existential over the descriptor: the caller of a probe function
   never learns which region the copy buffer points at. That is what makes a
   repointing probe expressible, and it is the exact analogue of Low*'s
   abstract `stream_of` over an opaque handle.

   As in Low*, the probe functions themselves are `assume val`s, so pointing
   the buffer at a fresh region is admitted by fiat. The corresponding C-side
   obligation -- that the new target be live, and disjoint from all other
   state tracked by the validator, for the whole validation -- is the
   counterpart of Low*'s assumed `region` disjointness in `properties`. *)
let pts_to
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| I.input_stream_inst base_t len_t pos_t |}
  {| cb: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (c: copy_buffer_t) (contents: Seq.seq U8.t) (v: Seq.seq U8.t) : Tot slprop =
  exists* (d: cb.descr_t).
    R.pts_to (descr #_ #base_t #len_t #pos_t c) d **
    I.pts_to #base_t #len_t #pos_t (base_of #_ #base_t #len_t #pos_t d) (len_of #_ #base_t #len_t #pos_t d) (pos_of #_ #base_t #len_t #pos_t d) contents v
