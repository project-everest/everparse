module CBOR.Pulse.Raw.EverParse.UTF8
friend CBOR.Spec.Raw.Format.UTF8
friend CBOR.Spec.API.UTF8
include CBOR.Spec.API.UTF8
open Pulse.Lib.Pervasives
module U8 = FStar.UInt8
module S = Pulse.Lib.Slice
#lang-pulse

fn impl_correct
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to s #p v)
returns res: bool
ensures
    (pts_to s #p v ** pure (res == correct v))
{
  LowParse.Pulse.UTF8.impl_utf8_correct s
}
