module EverParse3d.Prelude.StaticHeader

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module LBF = LowParse.BitFields

////////////////////////////////////////////////////////////////////////////////
// Bit fields
////////////////////////////////////////////////////////////////////////////////
[@CInline]
let get_bitfield8
  (value:U8.t)
  (bitsFrom:U32.t{U32.v bitsFrom < 8})
  (bitsTo:U32.t{U32.v bitsFrom < U32.v bitsTo /\ U32.v bitsTo <= 8})
: Tot (i:U8.t{FStar.UInt.size (U8.v i) (U32.v bitsTo - U32.v bitsFrom)})
= LBF.get_bitfield_eq_2 #8 (U8.v value) (U32.v bitsFrom) (U32.v bitsTo);
  (* NOTE: due to https://github.com/FStarLang/kremlin/issues/102 I need to introduce explicit let-bindings here *)
  let op1 = value `U8.shift_left` (8ul `U32.sub` bitsTo) in
  let op2 = op1 `U8.shift_right` ((8ul `U32.sub` bitsTo) `U32.add` bitsFrom) in
  op2

[@CInline]
let get_bitfield16 (value:U16.t)
                   (bitsFrom:U32.t{U32.v bitsFrom < 16})
                   (bitsTo:U32.t{U32.v bitsFrom < U32.v bitsTo /\ U32.v bitsTo <= 16})
   : i:U16.t{FStar.UInt.size (U16.v i) (U32.v bitsTo - U32.v bitsFrom)}
   = LBF.uint16.LBF.get_bitfield_gen value bitsFrom bitsTo

[@CInline]
let get_bitfield32 (value:U32.t)
                   (bitsFrom:U32.t{U32.v bitsFrom < 32})
                   (bitsTo:U32.t{U32.v bitsFrom < U32.v bitsTo /\ U32.v bitsTo <= 32})
   : i:U32.t{FStar.UInt.size (U32.v i) (U32.v bitsTo - U32.v bitsFrom)}
   = LBF.uint32.LBF.get_bitfield_gen value bitsFrom bitsTo

[@CInline]
let get_bitfield64 (value:U64.t)
                   (bitsFrom:U32.t{U32.v bitsFrom < 64})
                   (bitsTo:U32.t{U32.v bitsFrom < U32.v bitsTo /\ U32.v bitsTo <= 64})
   : i:U64.t{FStar.UInt.size (U64.v i) (U32.v bitsTo - U32.v bitsFrom)}
   = LBF.uint64.LBF.get_bitfield_gen value bitsFrom bitsTo
