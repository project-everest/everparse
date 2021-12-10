module EverParse3d.InputStream.Buffer

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

open EverParse3d.InputStream.Base

inline_for_extraction
noextract
val t : Type0

[@@ FStar.Tactics.Typeclasses.tcinstance]
noextract
inline_for_extraction
val inst : input_stream_inst t
