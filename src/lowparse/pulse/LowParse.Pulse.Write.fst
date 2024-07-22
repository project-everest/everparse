module LowParse.Pulse.Write
include LowParse.Pulse.Base
open LowParse.Spec.Base
open LowParse.Pulse.Util
open Pulse.Lib.Slice

module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT

inline_for_extraction
let l2r_writer
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
= (x': t') ->
  (#x: Ghost.erased t) ->
  (out: slice byte) ->
  (offset: SZ.t) ->
  (#v: Ghost.erased bytes) ->
  stt SZ.t
    (S.pts_to out v ** vmatch x' x ** pure (
      SZ.v offset + Seq.length (bare_serialize s x) <= Seq.length v
    ))
    (fun res -> exists* v' .
      S.pts_to out v' ** vmatch x' x ** pure (
      let bs = bare_serialize s x in
      SZ.v offset + Seq.length bs <= Seq.length v /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v offset) == Seq.slice v 0 (SZ.v offset) /\
      Seq.slice v' (SZ.v offset) (SZ.v offset + Seq.length bs) == bs
    ))
