module LowParse.Spec.Endianness
include LowParse.Endianness

module U8 = FStar.UInt8
module E = LowParse.Endianness

open FStar.Mul

inline_for_extraction
noextract
noeq
type uinttype (t: Type) (n: nat) =
  | UIntType:
    (v: (t -> Tot (y: nat { y < pow2 (8 * n) } ))) ->
    (to_byte: ((x: t) -> Tot (y: U8.t { U8.v y == v x % 256 } ))) ->
    (from_byte: ((x: U8.t) -> Tot (y: t { v y == U8.v x } ))) ->
    (zero: t { v zero == 0 } ) ->
    (v_inj: ((x1: t) -> (x2: t) -> Lemma (requires (v x1 == v x2)) (ensures (x1 == x2)))) ->
    (add: ((x: t) -> (y: t) -> Pure t (requires (v x + v y < pow2 (8 * n))) (ensures (fun z -> v z == v x + v y)))) ->
    (mul256: ((x: t) -> Pure t (requires (v x * 256 < pow2 (8 * n))) (ensures (fun z -> v z == v x * 256)))) ->
    (div256: ((x: t) -> Pure t (requires True) (ensures (fun z -> v z == v x / 256)))) ->
    uinttype t n
