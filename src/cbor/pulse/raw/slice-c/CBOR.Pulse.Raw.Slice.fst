module CBOR.Pulse.Raw.Slice
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8

// C backend implementation: a plain (extracted) abbreviation that survives
// KaRaMeL monomorphization and names the emitted C struct `byte_slice`.
let byte_slice : Type0 = S.slice U8.t

inline_for_extraction noextract [@@noextract_to "krml"]
let byte_slice0 : (t: Type0 { t == S.slice U8.t }) = byte_slice

// `byte_slice0` (hence `byte_slice1`) is transparently `slice uint8_t` here, so
// the coercions are the identity and erase at extraction.
inline_for_extraction noextract [@@noextract_to "krml"]
let to_slice (x: byte_slice1) : S.slice U8.t = x

inline_for_extraction noextract [@@noextract_to "krml"]
let of_slice (x: S.slice U8.t) : byte_slice1 = x

let to_of_slice x = ()
let of_to_slice x = ()
