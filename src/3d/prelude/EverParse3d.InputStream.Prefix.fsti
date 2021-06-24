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

val made_from
  (#base: Type0)
  (# [FStar.Tactics.Typeclasses.tcresolve ()] base_inst: input_stream_inst base)
  (x: t base)
  (from: base)
: Tot prop

val get_suffix
  (#base: Type0)
  (# [FStar.Tactics.Typeclasses.tcresolve ()] base_inst: input_stream_inst base)
  (x: t base)
: GTot (Seq.seq U8.t)

val made_from_prop
  (#base: Type0)
  (# [FStar.Tactics.Typeclasses.tcresolve ()] base_inst: input_stream_inst base)
  (x: t base)
  (from: base)
  (h: HS.mem)
: Lemma
    (requires (
      live x h /\
      x `made_from` from
    ))
    (ensures (
      live from h /\
      get_read from h `Seq.equal` get_read x h /\
      get_remaining from h `Seq.equal` (get_remaining x h `Seq.append` get_suffix x)
    ))

inline_for_extraction
noextract
val make
  (#base: Type0)
  (# [FStar.Tactics.Typeclasses.tcresolve ()] base_inst: input_stream_inst base)
  (from: base)
  (n: U32.t)
: HST.Stack (t base)
  (requires (fun h ->
    live from h /\
    U32.v n <= Seq.length (get_remaining from h)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res `made_from` from /\
    footprint res == footprint from /\
    live res h' /\
    Seq.length (get_remaining res h') == U32.v n
  ))
