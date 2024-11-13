module CBOR.Spec.API.UTF8
module U8 = FStar.UInt8

// Correctness of UTF-8 strings
noextract [@@noextract_to "krml"]
val correct: (Seq.seq U8.t) -> bool
