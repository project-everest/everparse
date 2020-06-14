module LowParse.SLow.Endianness
include LowParse.Spec.Endianness

module U8 = FStar.UInt8
module E = LowParse.Endianness
module B = LowParse.Bytes32
module U32 = FStar.UInt32

open FStar.Mul

inline_for_extraction
noextract
let be_to_n_t
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat { len <= tot })
: Tot Type
= (x: B.lbytes len) ->
  Tot (y: t { u.v y == E.be_to_n (B.reveal x) })

inline_for_extraction
noextract
let be_to_n_0
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
: Tot (be_to_n_t u 0)
= fun x ->
  E.reveal_be_to_n (B.reveal x);
  u.zero

open FStar.Math.Lemmas
module U32 = FStar.UInt32

inline_for_extraction
noextract
let be_to_n_S
  (#t: Type)
  (#tot: nat)
  (#u: uinttype t tot)
  (#len: nat { len + 1 <= tot })
  (ih: be_to_n_t u len)
: Tot (be_to_n_t u (len + 1))
= fun x ->
  assert_norm (pow2 8 == 256);
  E.reveal_be_to_n (B.reveal x);
  pow2_le_compat (8 * tot) (8 * (len + 1));
  pow2_le_compat (8 * (len + 1)) (8 * len);
  pow2_plus (8 * len) 8;
  [@inline_let]
  let ulen = U32.uint_to_t len in
  let last = B.get x ulen in
  let first = B.slice x 0ul ulen in
  let n = ih first in
  E.lemma_be_to_n_is_bounded (B.reveal first);
  assert (u.v n * 256 < 256 * pow2 (8 * len));
  assert (0 <= u.v n * 256);
  assert (u.v n * 256 < pow2 (8 * tot));
  let blast = u.from_byte last in
  blast `u.add` u.mul256 n

// attribute for use with delta_attr
noextract
noeq
type must_reduce = | MustReduce_dummy_do_not_use

[@must_reduce]
noextract
let rec mk_be_to_n
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat {len <= tot})
: Tot (be_to_n_t u len)
  (decreases len)
= if len = 0
  then be_to_n_0 u
  else be_to_n_S (mk_be_to_n u (len - 1))

inline_for_extraction
noextract
let n_to_be_t
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat { len <= tot })
: Tot Type
= (n: t { u.v n < pow2 (8 * len) }) ->
  Tot (b: B.bytes { B.reveal b `Seq.equal` E.n_to_be len (u.v n) })

inline_for_extraction
noextract
let n_to_be_0
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
: Tot (n_to_be_t u 0)
= fun _ -> B.empty_bytes

inline_for_extraction
noextract
let n_to_be_S
  (#t: Type)
  (#tot: nat)
  (#u: uinttype t tot)
  (#len: nat {len + 1 <= tot /\ tot < pow2 32})
  (ih: n_to_be_t u len)
: Tot (n_to_be_t u (len + 1))
= fun n ->
  reveal_n_to_be (len + 1) (u.v n);
  let lo = u.to_byte n in
  let hi = u.div256 n in
  let seq_hi = ih hi in
  let seq_lo = B.create 1ul lo in
  seq_hi `B.append` seq_lo

[@must_reduce]
noextract
let rec mk_n_to_be
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat {len <= tot /\ tot < pow2 32})
: Tot (n_to_be_t u len)
  (decreases len)
= if len = 0
  then n_to_be_0 u
  else n_to_be_S (mk_n_to_be u (len - 1))

inline_for_extraction
noextract
let le_to_n_t
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat { len <= tot })
: Tot Type
= (x: B.lbytes len) ->
  Tot (y: t { u.v y == E.le_to_n (B.reveal x) })

inline_for_extraction
noextract
let le_to_n_0
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
: Tot (le_to_n_t u 0)
= fun x ->
  E.reveal_le_to_n (B.reveal x);
  u.zero

open FStar.Math.Lemmas
module U32 = FStar.UInt32

inline_for_extraction
noextract
let le_to_n_S
  (#t: Type)
  (#tot: nat)
  (#u: uinttype t tot)
  (#len: nat { len + 1 <= tot })
  (ih: le_to_n_t u len)
: Tot (le_to_n_t u (len + 1))
= fun x ->
  assert_norm (pow2 8 == 256);
  E.reveal_le_to_n (B.reveal x);
  pow2_le_compat (8 * tot) (8 * (len + 1));
  pow2_le_compat (8 * (len + 1)) (8 * len);
  pow2_plus (8 * len) 8;
  [@inline_let]
  let ulen = U32.uint_to_t len in
  let last = B.get x 0ul in
  let first = B.slice x 1ul (ulen `U32.add` 1ul) in
  let n = ih first in
  E.lemma_le_to_n_is_bounded (B.reveal first);
  assert (u.v n * 256 < 256 * pow2 (8 * len));
  assert (0 <= u.v n * 256);
  assert (u.v n * 256 < pow2 (8 * tot));
  let blast = u.from_byte last in
  blast `u.add` u.mul256 n

[@must_reduce]
noextract
let rec mk_le_to_n
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat {len <= tot})
: Tot (le_to_n_t u len)
  (decreases len)
= if len = 0
  then le_to_n_0 u
  else le_to_n_S (mk_le_to_n u (len - 1))

inline_for_extraction
noextract
let n_to_le_t
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat { len <= tot })
: Tot Type
= (n: t { u.v n < pow2 (8 * len) }) ->
  Tot (b: B.bytes { B.reveal b `Seq.equal` E.n_to_le len (u.v n) })

inline_for_extraction
noextract
let n_to_le_0
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
: Tot (n_to_le_t u 0)
= fun _ -> B.empty_bytes

inline_for_extraction
noextract
let n_to_le_S
  (#t: Type)
  (#tot: nat)
  (#u: uinttype t tot)
  (#len: nat {len + 1 <= tot /\ tot < pow2 32})
  (ih: n_to_le_t u len)
: Tot (n_to_le_t u (len + 1))
= fun n ->
  reveal_n_to_le (len + 1) (u.v n);
  let lo = u.to_byte n in
  let hi = u.div256 n in
  let seq_hi = ih hi in
  let seq_lo = B.create 1ul lo in
  seq_lo `B.append` seq_hi

[@must_reduce]
noextract
let rec mk_n_to_le
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat {len <= tot /\ tot < pow2 32})
: Tot (n_to_le_t u len)
  (decreases len)
= if len = 0
  then n_to_le_0 u
  else n_to_le_S (mk_n_to_le u (len - 1))
