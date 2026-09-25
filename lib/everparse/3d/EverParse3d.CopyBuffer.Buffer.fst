module EverParse3d.CopyBuffer.Buffer

(* The `buffer` backend's copy-buffer handle, and its assumed projections onto
   the three components of an input stream.

   These are all that this module holds, deliberately. KaRaMeL's `-bundle`
   makes a whole *module* public or private at a time, so a module is the
   granularity at which we can say "these symbols are part of the client-facing
   ABI and belong in EverParse.h". Left in EverParse3d.InputStream.Buffer next
   to the stream implementation, they would drag that entire implementation
   public with them: every `inline_for_extraction` helper there would have to
   be materialised as a real function in EverParse.c, instead of being inlined
   into the generated validators.

   EverParse3d.InputStream.Buffer re-exports all four names, so the 3D frontend
   and the generated code still refer to them as `B.copy_buffer_t` and friends.

   The names are chosen for their extracted forms: the `[rename=EverParse,
   rename-prefix]` bundle turns `stream_of`/`stream_len`/`stream_pos` into
   `EverParseStreamOf`/`EverParseStreamLen`/`EverParseStreamPos`. The first two
   are exactly the Low* hooks, so a client written against the Low* backend
   only has to add the third, which returns the position cell that Pulse
   validators carry in the stream and Low* validators take as an argument.

   See EverParse3d.CopyBuffer for why keeping the projections *pure* -- and so
   letting a probe callback repoint the handle rather than copy into it -- is
   sound to the same degree as the Low* backend. *)

module AP = Pulse.Lib.ArrayPtr
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8

assume val copy_buffer_t : Type0

assume val stream_of : copy_buffer_t -> AP.ptr U8.t
assume val stream_len : copy_buffer_t -> SZ.t
assume val stream_pos : copy_buffer_t -> R.ref SZ.t
