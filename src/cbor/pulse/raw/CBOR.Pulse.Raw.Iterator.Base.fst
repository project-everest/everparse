module CBOR.Pulse.Raw.Iterator.Base
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8

noeq
type cbor_raw_serialized_iterator = {
  s: S.slice U8.t;
  len: Ghost.erased nat;
}
