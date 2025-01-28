module CBOR.Pulse.Raw.Iterator.Base
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module U64 = FStar.UInt64
open Pulse.Lib.Pervasives

noeq
type cbor_raw_serialized_iterator = {
  s: S.slice U8.t;
  p: perm;
  glen: Ghost.erased nat;
  len: U64.t;
}
