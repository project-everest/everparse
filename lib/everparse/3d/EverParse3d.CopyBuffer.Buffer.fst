module EverParse3d.CopyBuffer.Buffer

(* The `buffer` backend's copy-buffer handle, and its assumed projections onto
   the three components of an input stream.

   This module separates client-facing ABI declarations from the stream
   implementation. Custard's foreign declaration attributes publish the
   projections in EverParse.h without exposing implementation helpers.

   EverParse3d.InputStream.Buffer re-exports all four names, so the 3D frontend
   and the generated code still refer to them as `B.copy_buffer_t` and friends.

   Explicit naming attributes map `stream_of`/`stream_len`/`stream_pos` to
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

[@@FStar.Attributes.custard_extern "EVERPARSE_COPY_BUFFER_T"; FStar.Attributes.custard_c_header "EverParseEndianness.h"]
assume val copy_buffer_t : Type0

[@@FStar.Attributes.rename_let "EverParseStreamOf"; FStar.Attributes.custard_declare_in_c_header]
assume val stream_of : copy_buffer_t -> AP.ptr U8.t
[@@FStar.Attributes.rename_let "EverParseStreamLen"; FStar.Attributes.custard_declare_in_c_header]
assume val stream_len : copy_buffer_t -> SZ.t
[@@FStar.Attributes.rename_let "EverParseStreamPos"; FStar.Attributes.custard_declare_in_c_header]
assume val stream_pos : copy_buffer_t -> R.ref SZ.t
