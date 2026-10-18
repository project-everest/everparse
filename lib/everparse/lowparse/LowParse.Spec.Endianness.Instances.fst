module LowParse.Spec.Endianness.Instances
include LowParse.Spec.Endianness

module U8 = FStar.UInt8

inline_for_extraction
noextract
let uint8 : uinttype U8.t 1 =
  UIntType
    (fun x -> U8.v x)
    (fun x -> x)
    (fun x -> x)
    0uy
    (fun _ _ -> ())
    (fun x y -> x `U8.add` y)
    (fun x -> 0uy)
    (fun x -> 0uy)

module U16 = FStar.UInt16

inline_for_extraction
noextract
let uint16 : uinttype U16.t 2 =
  UIntType
    (fun x -> U16.v x)
    (fun x -> FStar.Int.Cast.uint16_to_uint8 x)
    (fun x -> FStar.Int.Cast.uint8_to_uint16 x)
    0us
    (fun _ _ -> ())
    (fun x y -> x `U16.add` y)
    (fun x -> x `U16.mul` 256us)
    (fun x -> x `U16.div` 256us)

module U32 = FStar.UInt32

inline_for_extraction
noextract
let uint32 : uinttype U32.t 4 =
  UIntType
    (fun x -> U32.v x)
    (fun x -> FStar.Int.Cast.uint32_to_uint8 x)
    (fun x -> FStar.Int.Cast.uint8_to_uint32 x)
    0ul
    (fun _ _ -> ())
    (fun x y -> x `U32.add` y)
    (fun x -> x `U32.mul` 256ul)
    (fun x -> x `U32.div` 256ul)

module U64 = FStar.UInt64

inline_for_extraction
noextract
let uint64 : uinttype U64.t 8 =
  UIntType
    (fun x -> U64.v x)
    (fun x -> FStar.Int.Cast.uint64_to_uint8 x)
    (fun x -> FStar.Int.Cast.uint8_to_uint64 x)
    0uL
    (fun _ _ -> ())
    (fun x y -> x `U64.add` y)
    (fun x -> x `U64.mul` 256uL)
    (fun x -> x `U64.div` 256uL)

open LowParse.Spec.BoundedInt

inline_for_extraction
noextract
let bounded_integer
  (i: integer_size)
: Tot (uinttype (bounded_integer i) i)
= UIntType
    (fun (x: bounded_integer i) -> bounded_integer_prop_equiv i x; U32.v x)
    (fun x -> FStar.Int.Cast.uint32_to_uint8 x)
    (fun x -> FStar.Int.Cast.uint8_to_uint32 x)
    0ul
    (fun _ _ -> ())
    (fun x y -> x `U32.add` y)
    (fun x -> x `U32.mul` 256ul)
    (fun x -> x `U32.div` 256ul)
