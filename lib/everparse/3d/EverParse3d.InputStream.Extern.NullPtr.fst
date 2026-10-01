module EverParse3d.InputStream.Extern.NullPtr

(* The client-supplied null pointer, `EverParseNullPtr`.

   It lives in a module of its own, apart from the stream primitives in
   EverParse3d.InputStream.Extern, because it is the one assumed *value* among
   them rather than an assumed *function*. The `static` backend asks KaRaMeL
   for a static-header declaration of that module, which turns every assumed
   function into a `static inline` prototype -- the point of `--input_stream
   static`. Applied to a value, the same flag would emit
   `static uint8_t *EverParseNullPtr;`: a per-translation-unit tentative
   definition, which shadows the client's own definition instead of linking
   against it, and which warns as unused in every translation unit that
   includes EverParse.h without needing it.

   Keeping it here means the `static` backend's static-header pattern, which
   names EverParse3d.InputStream.Extern exactly, does not reach it, so it stays
   a plain `extern` declaration under both backends. It is nonetheless an API
   module of the same `EverParse` bundle, so its C name is unchanged. *)

module U8 = FStar.UInt8
module AP = Pulse.Lib.ArrayPtr

assume val null_ptr : AP.ptr U8.t
