module EverParse3d.InputStream.All
include EverParse3d.InputStream.Base

(* These are defined in some EverParse3d.InputStream.fst defined in a subdirectory. The include path determines which one is used *)

inline_for_extraction
noextract
val t : Type0

[@@FStar.Tactics.Typeclasses.tcinstance]
inline_for_extraction
noextract
val inst : input_stream_inst t
