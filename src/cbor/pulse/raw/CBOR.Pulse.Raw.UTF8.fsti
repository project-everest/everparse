module CBOR.Pulse.Raw.UTF8
include CBOR.Spec.API.UTF8
open Pulse.Lib.Pervasives

module U8 = FStar.UInt8
module S = Pulse.Lib.Slice

inline_for_extraction
val impl_utf8_correct
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt bool
    (pts_to s #p v)
    (fun res -> pts_to s #p v ** pure (res == correct v))
