module EverParse3d.InputStream.Prefix

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

open EverParse3d.InputStream

val t (base: Type0) : Tot Type0

[@@ FStar.Tactics.Typeclasses.tcinstance]
noextract
inline_for_extraction
val inst (#base: Type0) (# [FStar.Tactics.Typeclasses.tcresolve ()] base_inst : input_stream_inst base)
: Tot (input_stream_inst (t base))

val gmake
  (#base: Type0)
  (# [FStar.Tactics.Typeclasses.tcresolve ()] base_inst: input_stream_inst base)
  (from: base)
  (n: U32.t)
: Ghost (t base)
    (requires (
      U32.v n <= length_all #_ #base_inst from
    ))
    (ensures (fun y ->
      footprint (y <: t base) == footprint from
    ))

val get_suffix
  (#base: Type0)
  (# [FStar.Tactics.Typeclasses.tcresolve ()] base_inst: input_stream_inst base)
  (x: t base)
: GTot (Seq.seq U8.t)

val gmake_prop
  (#base: Type0)
  (# [FStar.Tactics.Typeclasses.tcresolve ()] base_inst: input_stream_inst base)
  (from: base)
  (n: U32.t)
  (h: HS.mem)
: Ghost (t base)
    (requires (
      U32.v n <= length_all #_ #base_inst from /\
      live (gmake from n) h
    ))
    (ensures (fun y ->
      live from h /\
      get_read from h == get_read (gmake from n) h /\
      get_remaining from h == get_remaining (gmake from n) h `Seq.append` get_suffix (gmake from n)
    ))

inline_for_extraction
val make
  (#base: Type0)
  (# [FStar.Tactics.Typeclasses.tcresolve ()] base_inst: input_stream_inst base)
  (from: base)
  (n: U32.t)
: HST.Stack (t base)
  (requires (fun h ->
    live from h /\
    U32.v n <= length_all #_ #base_inst from
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == gmake from n
  ))
