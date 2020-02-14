module Prelude.StaticHeader

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module BF = LowParse.BitFields

////////////////////////////////////////////////////////////////////////////////
// Bit fields
////////////////////////////////////////////////////////////////////////////////
[@CInline]
let get_bitfield32 (value:U32.t)
                   (bitsFrom:U32.t{U32.v bitsFrom < 32})
                   (bitsTo:U32.t{U32.v bitsFrom < U32.v bitsTo /\ U32.v bitsTo <= 32})
   : i:U32.t{FStar.UInt.size (U32.v i) (U32.v bitsTo - U32.v bitsFrom)}
   = BF.uint32.BF.get_bitfield_gen value bitsFrom bitsTo

[@CInline]
let get_bitfield64 (value:U64.t)
                   (bitsFrom:U32.t{U32.v bitsFrom < 64})
                   (bitsTo:U32.t{U32.v bitsFrom < U32.v bitsTo /\ U32.v bitsTo <= 64})
   : i:U64.t{FStar.UInt.size (U64.v i) (U32.v bitsTo - U32.v bitsFrom)}
   = BF.uint64.BF.get_bitfield_gen value bitsFrom bitsTo
