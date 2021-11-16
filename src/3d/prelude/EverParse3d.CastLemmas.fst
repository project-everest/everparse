module EverParse3d.CastLemmas
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = FStar.Int.Cast

let cast_mul_fits_8_16 (x y :U8.t)
  : Lemma (
           FStar.UInt.fits
             ((U16.v (C.uint8_to_uint16 x))
               `op_Multiply`
              (U16.v (C.uint8_to_uint16 y)))
              16)
           [SMTPat ((U16.v (C.uint8_to_uint16 x))
                      `op_Multiply`
                   (U16.v (C.uint8_to_uint16 y)))]
  = let n = U16.v (C.uint8_to_uint16 x) in
    let m = U16.v (C.uint8_to_uint16 y) in
    FStar.Math.Lemmas.lemma_mult_lt_sqr n m (pow2 8)


let cast_mul_fits_16_32 (x y :U16.t)
  : Lemma (
           FStar.UInt.fits
             ((U32.v (C.uint16_to_uint32 x))
               `op_Multiply`
              (U32.v (C.uint16_to_uint32 y)))
              32)
           [SMTPat ((U32.v (C.uint16_to_uint32 x))
                      `op_Multiply`
                   (U32.v (C.uint16_to_uint32 y)))]
  = let n = U32.v (C.uint16_to_uint32 x) in
    let m = U32.v (C.uint16_to_uint32 y) in
    FStar.Math.Lemmas.lemma_mult_lt_sqr n m (pow2 16)

let cast_mul_fits_32_64 (x y :U32.t)
  : Lemma (
           FStar.UInt.fits
             ((U64.v (C.uint32_to_uint64 x))
               `op_Multiply`
              (U64.v (C.uint32_to_uint64 y)))
              64)
           [SMTPat ((U64.v (C.uint32_to_uint64 x))
                      `op_Multiply`
                      (U64.v (C.uint32_to_uint64 y)))]
  = let n = U64.v (C.uint32_to_uint64 x) in
    let m = U64.v (C.uint32_to_uint64 y) in
    FStar.Math.Lemmas.lemma_mult_lt_sqr n m (pow2 32)
