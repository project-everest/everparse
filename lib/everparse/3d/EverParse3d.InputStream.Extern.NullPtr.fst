module EverParse3d.InputStream.Extern.NullPtr

(* The client-supplied null pointer, `EverParseNullPtr`.

   This client-owned global must remain an `extern` declaration for both
   `extern` and `static` input streams. Keeping it separate from the stream
   functions lets the static profile use `static inline` client hooks without
   introducing a per-translation-unit definition of the null pointer. *)

module U8 = FStar.UInt8
module AP = Pulse.Lib.ArrayPtr

[@@FStar.Attributes.rename_let "EverParseNullPtr"]
assume val null_ptr : AP.ptr U8.t
