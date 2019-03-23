module LowParse.BigEndianImpl.Base
include LowParse.BigEndian

module U = FStar.UInt
module U8 = FStar.UInt8

noeq
type uinttype (t: Type0) (n: nat) =
  | UIntType:
    (v: (t -> Tot (y: nat { U.fits y n } ))) ->
    (to_byte: ((x: t) -> Tot (y: U8.t { U8.v y == v x % 256 } ))) ->
    (from_byte: ((x: U8.t) -> Tot (y: t { v y == U8.v x } ))) ->
    (zero: t { v zero == 0 } ) ->
    (v_inj: ((x1: t) -> (x2: t) -> Lemma (requires (v x1 == v x2)) (ensures (x1 == x2)))) ->
    (add: ((x: t) -> (y: t) -> Pure t (requires (U.fits (v x + v y) n)) (ensures (fun z -> v z == v x + v y)))) ->
    (mul256: ((x: t) -> Pure t (requires (U.fits (Prims.op_Multiply (v x) 256) n)) (ensures (fun z -> v z == Prims.op_Multiply (v x) 256)))) ->
    (div256: ((x: t) -> Pure t (requires True) (ensures (fun z -> v z == v x / 256)))) ->
    uinttype t n

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

inline_for_extraction
let u8 () : uinttype U8.t 8 =
  UIntType
    (fun x -> U8.v x)
    (fun x -> x)
    (fun x -> x)
    0uy
    (fun x y -> ())
    (fun x y -> U8.add x y)
    (fun x -> 0uy)
    (fun x -> 0uy)

inline_for_extraction
let u16 () : uinttype U16.t 16 =
  UIntType
    (fun x -> U16.v x)
    (fun x -> Cast.uint16_to_uint8 x)
    (fun x -> Cast.uint8_to_uint16 x)
    0us
    (fun x y -> ())
    (fun x y -> U16.add x y)
    (fun x -> U16.mul x 256us)
    (fun x -> U16.div x 256us)

inline_for_extraction
let u32 () : uinttype U32.t 32 =
  UIntType
    (fun x -> U32.v x)
    (fun x -> Cast.uint32_to_uint8 x)
    (fun x -> Cast.uint8_to_uint32 x)
    0ul
    (fun x y -> ())
    (fun x y -> U32.add x y)
    (fun x -> U32.mul x 256ul)
    (fun x -> U32.div x 256ul)
