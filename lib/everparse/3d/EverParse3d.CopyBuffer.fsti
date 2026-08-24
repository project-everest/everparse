module EverParse3d.CopyBuffer
module AppCtxt = EverParse3d.AppCtxt
module I = EverParse3d.InputStream.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Pulse.Lib.Pervasives

(* A copy buffer is an opaque handle onto an input stream, exactly as in Low*.

   In Low*, `EverParse3d.CopyBuffer` declares

     val copy_buffer_t : Type0
     val stream_of : copy_buffer_t -> I.t
     val stream_len (c: copy_buffer_t) : I.tlen (stream_of c)

   with no implementing `.fst`, so all three are assumed; KaRaMeL emits
   `EverParseStreamOf`/`EverParseStreamLen` as `extern` declarations that the
   client implements in C, and the handle itself is a `void*`. This class is
   the same thing, one projection wider: Pulse input streams are a (base, len,
   pos) triple rather than a single `I.t`, so there is a third projection for
   the position cell.

   Keeping the projections *pure* is what lets a probe callback repoint the
   copy buffer at the probed bytes instead of copying into them. F* believes
   `base_of c` is a function of `c` alone; the client is free to make the
   underlying C function return a different pointer after a probe. That is a
   lie, and it is deliberately the *same* lie Low* tells about `stream_of`:
   the probe functions are `assume val`s, so the fresh region they hand back
   is admitted by fiat, and the C-side obligation -- that the new target be
   live, and disjoint from all other state the validator tracks, for the whole
   validation -- is the counterpart of Low*'s assumed `region` disjointness in
   `properties`.

   Note that the lie is *expressible* here, which is the whole point: the pre
   and post of a probe differ in `contents`/`v`, so a probe genuinely changes
   the slprop, and nothing in the interpreter ever learns which region the
   copy buffer points at. *)
noextract
inline_for_extraction
class copy_buffer (copy_buffer_t: Type0) (base_t: Type0) (len_t: Type0) (pos_t: Type0) {| I.input_stream_inst base_t len_t pos_t |} = {
  (* The three components of the stream the handle denotes. Extracted as
     client-implemented C functions, as `EverParseStreamOf` and
     `EverParseStreamLen` are in Low*. *)
  base_of : copy_buffer_t -> base_t;
  len_of : copy_buffer_t -> len_t;
  pos_of : copy_buffer_t -> pos_t;

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
      (I.pts_to #base_t #len_t #pos_t (base_of c) (len_of c) (pos_of c) contents v)
      (fun _ -> I.pts_to #base_t #len_t #pos_t (base_of c) (len_of c) (pos_of c) contents contents);
}

let pts_to
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| I.input_stream_inst base_t len_t pos_t |}
  {| cb: copy_buffer copy_buffer_t base_t len_t pos_t |}
  (c: copy_buffer_t) (contents: Seq.seq U8.t) (v: Seq.seq U8.t) : Tot slprop =
  I.pts_to #base_t #len_t #pos_t
    (base_of #_ #base_t #len_t #pos_t c)
    (len_of #_ #base_t #len_t #pos_t c)
    (pos_of #_ #base_t #len_t #pos_t c) contents v
