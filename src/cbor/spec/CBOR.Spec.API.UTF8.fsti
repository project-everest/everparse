module CBOR.Spec.API.UTF8
module U8 = FStar.UInt8

// Correctness of UTF-8 strings
noextract [@@noextract_to "krml"]
val correct: (Seq.seq U8.t) -> bool

val ascii_is_utf8
  (s: Seq.seq U8.t)
: Lemma
  (requires (forall i . i < Seq.length s ==> U8.v (Seq.index s i) < 128))
  (ensures (correct s))
