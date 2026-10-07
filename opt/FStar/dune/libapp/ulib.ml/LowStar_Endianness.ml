open Prims
type u8 = FStar_UInt8.t
type u16 = FStar_UInt16.t
type u32 = FStar_UInt32.t
type u64 = FStar_UInt64.t
type u128 = FStar_UInt128.t
let htole16 (uu___ : FStar_UInt16.t) : FStar_UInt16.t=
  failwith "Not yet implemented: LowStar.Endianness.htole16"
let le16toh (uu___ : FStar_UInt16.t) : FStar_UInt16.t=
  failwith "Not yet implemented: LowStar.Endianness.le16toh"
let htole32 (uu___ : FStar_UInt32.t) : FStar_UInt32.t=
  failwith "Not yet implemented: LowStar.Endianness.htole32"
let le32toh (uu___ : FStar_UInt32.t) : FStar_UInt32.t=
  failwith "Not yet implemented: LowStar.Endianness.le32toh"
let htole64 (uu___ : FStar_UInt64.t) : FStar_UInt64.t=
  failwith "Not yet implemented: LowStar.Endianness.htole64"
let le64toh (uu___ : FStar_UInt64.t) : FStar_UInt64.t=
  failwith "Not yet implemented: LowStar.Endianness.le64toh"
let htobe16 (uu___ : FStar_UInt16.t) : FStar_UInt16.t=
  failwith "Not yet implemented: LowStar.Endianness.htobe16"
let be16toh (uu___ : FStar_UInt16.t) : FStar_UInt16.t=
  failwith "Not yet implemented: LowStar.Endianness.be16toh"
let htobe32 (uu___ : FStar_UInt32.t) : FStar_UInt32.t=
  failwith "Not yet implemented: LowStar.Endianness.htobe32"
let be32toh (uu___ : FStar_UInt32.t) : FStar_UInt32.t=
  failwith "Not yet implemented: LowStar.Endianness.be32toh"
let htobe64 (uu___ : FStar_UInt64.t) : FStar_UInt64.t=
  failwith "Not yet implemented: LowStar.Endianness.htobe64"
let be64toh (uu___ : FStar_UInt64.t) : FStar_UInt64.t=
  failwith "Not yet implemented: LowStar.Endianness.be64toh"
type ('a, 'rrel, 'rel, 'b, 'i, 'j, 'predicate, 'h) store_pre = unit
type ('a, 'rrel, 'rel, 'b, 'i, 'j, 'predicate, 'h0, 'uuuuu, 'h1) store_post =
  unit
let store16_le_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (z : FStar_UInt16.t) : unit=
  failwith "Not yet implemented: LowStar.Endianness.store16_le_i"
let load16_le_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt16.t=
  failwith "Not yet implemented: LowStar.Endianness.load16_le_i"
let store16_be_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (z : FStar_UInt16.t) : unit=
  failwith "Not yet implemented: LowStar.Endianness.store16_be_i"
let load16_be_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt16.t=
  failwith "Not yet implemented: LowStar.Endianness.load16_be_i"
let store32_le_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (z : FStar_UInt32.t) : unit=
  failwith "Not yet implemented: LowStar.Endianness.store32_le_i"
let load32_le_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt32.t=
  failwith "Not yet implemented: LowStar.Endianness.load32_le_i"
let store32_be_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (z : FStar_UInt32.t) : unit=
  failwith "Not yet implemented: LowStar.Endianness.store32_be_i"
let load32_be_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt32.t=
  failwith "Not yet implemented: LowStar.Endianness.load32_be_i"
let store64_le_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (z : FStar_UInt64.t) : unit=
  failwith "Not yet implemented: LowStar.Endianness.store64_le_i"
let load64_le_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt64.t=
  failwith "Not yet implemented: LowStar.Endianness.load64_le_i"
let store64_be_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (z : FStar_UInt64.t) : unit=
  failwith "Not yet implemented: LowStar.Endianness.store64_be_i"
let load64_be_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt64.t=
  failwith "Not yet implemented: LowStar.Endianness.load64_be_i"
let store128_le_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (z : FStar_UInt128.t) : unit=
  failwith "Not yet implemented: LowStar.Endianness.store128_le_i"
let load128_le_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt128.t=
  failwith "Not yet implemented: LowStar.Endianness.load128_le_i"
let store128_be_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (z : FStar_UInt128.t) : unit=
  failwith "Not yet implemented: LowStar.Endianness.store128_be_i"
let load128_be_i
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt128.t=
  failwith "Not yet implemented: LowStar.Endianness.load128_be_i"
let store16_le (b : FStar_UInt8.t LowStar_Buffer.buffer) (z : FStar_UInt16.t)
  : unit= store16_le_i b Stdint.Uint32.zero z
let load16_le (b : FStar_UInt8.t LowStar_Buffer.buffer) : FStar_UInt16.t=
  load16_le_i b Stdint.Uint32.zero
let store16_be (b : FStar_UInt8.t LowStar_Buffer.buffer) (z : FStar_UInt16.t)
  : unit= store16_be_i b Stdint.Uint32.zero z
let load16_be (b : FStar_UInt8.t LowStar_Buffer.buffer) : FStar_UInt16.t=
  load16_be_i b Stdint.Uint32.zero
let store32_le (b : FStar_UInt8.t LowStar_Buffer.buffer) (z : FStar_UInt32.t)
  : unit= store32_le_i b Stdint.Uint32.zero z
let load32_le (b : FStar_UInt8.t LowStar_Buffer.buffer) : FStar_UInt32.t=
  load32_le_i b Stdint.Uint32.zero
let store32_be (b : FStar_UInt8.t LowStar_Buffer.buffer) (z : FStar_UInt32.t)
  : unit= store32_be_i b Stdint.Uint32.zero z
let load32_be (b : FStar_UInt8.t LowStar_Buffer.buffer) : FStar_UInt32.t=
  load32_be_i b Stdint.Uint32.zero
let store64_le (b : FStar_UInt8.t LowStar_Buffer.buffer) (z : FStar_UInt64.t)
  : unit= store64_le_i b Stdint.Uint32.zero z
let load64_le (b : FStar_UInt8.t LowStar_Buffer.buffer) : FStar_UInt64.t=
  load64_le_i b Stdint.Uint32.zero
let load64_be (b : FStar_UInt8.t LowStar_Buffer.buffer) : FStar_UInt64.t=
  load64_be_i b Stdint.Uint32.zero
let store64_be (b : FStar_UInt8.t LowStar_Buffer.buffer) (z : FStar_UInt64.t)
  : unit= store64_be_i b Stdint.Uint32.zero z
let load128_le (b : FStar_UInt8.t LowStar_Buffer.buffer) : FStar_UInt128.t=
  load128_le_i b Stdint.Uint32.zero
let store128_le (b : FStar_UInt8.t LowStar_Buffer.buffer)
  (z : FStar_UInt128.t) : unit= store128_le_i b Stdint.Uint32.zero z
let load128_be (b : FStar_UInt8.t LowStar_Buffer.buffer) : FStar_UInt128.t=
  load128_be_i b Stdint.Uint32.zero
let store128_be (b : FStar_UInt8.t LowStar_Buffer.buffer)
  (z : FStar_UInt128.t) : unit= store128_be_i b Stdint.Uint32.zero z
let index_32_be
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt32.t=
  load32_be_i b (FStar_UInt32.mul (Stdint.Uint32.of_int (4)) i)
let index_32_le
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt32.t=
  load32_le_i b (FStar_UInt32.mul (Stdint.Uint32.of_int (4)) i)
let index_64_be
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt64.t=
  load64_be_i b (FStar_UInt32.mul (Stdint.Uint32.of_int (8)) i)
let index_64_le
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) : FStar_UInt64.t=
  load64_le_i b (FStar_UInt32.mul (Stdint.Uint32.of_int (8)) i)
let upd_32_be
  (b : (FStar_UInt8.t, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer)
  (i : FStar_UInt32.t) (v : FStar_UInt32.t) : unit=
  let h0 = FStar_HyperStack_ST.get () in
  store32_be_i b (FStar_UInt32.mul (Stdint.Uint32.of_int (4)) i) v;
  (let h1 = FStar_HyperStack_ST.get () in ())
