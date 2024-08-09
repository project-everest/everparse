module LowParse.Spec.Endianness
include LowParse.Endianness

module U8 = FStar.UInt8
module E = LowParse.Endianness
module Seq = FStar.Seq

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

open LowParse.Spec.Sorted

let big_endian_lex_compare_eq
  (n: nat)
  (compare: (U8.t -> U8.t -> int))
  (compare_eq: (
    (x: U8.t) ->
    (y: U8.t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (x y: nat)
: Lemma
  (requires (
    x < pow2 (8 * n) /\
    y < pow2 (8 * n)
  ))
  (ensures (
    lex_compare compare (Seq.seq_to_list (E.n_to_be n x)) (Seq.seq_to_list (E.n_to_be n y)) == 0 <==> x == y
  ))
=
  lex_compare_equal compare compare_eq (Seq.seq_to_list (E.n_to_be n x)) (Seq.seq_to_list (E.n_to_be n y));
  if lex_compare compare (Seq.seq_to_list (E.n_to_be n x)) (Seq.seq_to_list (E.n_to_be n y)) = 0
  then begin
    Seq.lemma_seq_list_bij (E.n_to_be n x);
    Seq.lemma_seq_list_bij (E.n_to_be n y);
    E.n_to_be_inj n x y
  end else ()

let seq_to_list_singleton (#t: Type) (x: t) : Lemma
  (Seq.seq_to_list (Seq.create 1 x) == [x])
  [SMTPat (Seq.seq_to_list (Seq.create 1 x))]
= assert (Seq.create 1 x `Seq.equal` Seq.cons x Seq.empty)

let rec big_endian_lex_compare_aux
  (n: nat)
  (compare: (U8.t -> U8.t -> int))
  (compare_eq: (
    (x: U8.t) ->
    (y: U8.t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (compare_neg: (
    (x: U8.t) ->
    (y: U8.t) ->
    Lemma
    (compare x y < 0 <==> x `U8.lt` y)
  ))
  (x y: nat)
: Lemma
  (requires (
    x < pow2 (8 * n) /\
    y < pow2 (8 * n) /\
    lex_compare compare (Seq.seq_to_list (E.n_to_be n x)) (Seq.seq_to_list (E.n_to_be n y)) < 0
  ))
  (ensures (
    x < y
  ))
  (decreases n)
= if n = 0
  then ()
  else begin
    assert_norm (pow2 8 == 256);
    FStar.Math.Lemmas.euclidean_division_definition x (pow2 8);
    FStar.Math.Lemmas.euclidean_division_definition y (pow2 8);
    E.reveal_n_to_be n x;
    E.reveal_n_to_be n y;
    seq_to_list_append (E.n_to_be (n - 1) (x / pow2 8)) (Seq.create 1 (U8.uint_to_t (x % pow2 8)));
    seq_to_list_append (E.n_to_be (n - 1) (y / pow2 8)) (Seq.create 1 (U8.uint_to_t (y % pow2 8)));
    lex_compare_append_recip compare (Seq.seq_to_list (E.n_to_be (n - 1) (x / pow2 8))) (Seq.seq_to_list (E.n_to_be (n - 1) (y / pow2 8))) [U8.uint_to_t (x % pow2 8)] [U8.uint_to_t (y % pow2 8)];
    if lex_compare compare (Seq.seq_to_list (E.n_to_be (n - 1) (x / pow2 8))) (Seq.seq_to_list (E.n_to_be (n - 1) (y / pow2 8))) = 0
    then begin
      big_endian_lex_compare_eq (n - 1) compare compare_eq (x / pow2 8) (y / pow2 8);
      lex_compare_prefix compare compare_eq (Seq.seq_to_list (E.n_to_be (n - 1) (x / pow2 8))) [U8.uint_to_t (x % pow2 8)] [U8.uint_to_t (y % pow2 8)];
      compare_neg (U8.uint_to_t (x % pow2 8)) (U8.uint_to_t (y % pow2 8))
    end else begin
      big_endian_lex_compare_aux (n - 1) compare compare_eq compare_neg (x / pow2 8) (y / pow2 8)
    end
  end

let big_endian_lex_compare
  (n: nat)
  (compare: (U8.t -> U8.t -> int))
  (compare_eq: (
    (x: U8.t) ->
    (y: U8.t) ->
    Lemma
    (compare x y == 0 <==> x == y)
  ))
  (compare_neg: (
    (x: U8.t) ->
    (y: U8.t) ->
    Lemma
    (compare x y < 0 <==> x `U8.lt` y)
  ))
  (x y: nat)
: Lemma
  (
    (x < pow2 (8 * n) /\ y < pow2 (8 * n)) ==>
    (lex_compare compare (Seq.seq_to_list (E.n_to_be n x)) (Seq.seq_to_list (E.n_to_be n y)) < 0 <==> x < y)
  )
= if x < pow2 (8 * n) && y < pow2 (8 * n)
  then begin
    let c = lex_compare compare (Seq.seq_to_list (E.n_to_be n x)) (Seq.seq_to_list (E.n_to_be n y)) in
    if c < 0
    then
      big_endian_lex_compare_aux n compare compare_eq compare_neg x y
    else if c = 0
    then begin
      big_endian_lex_compare_eq n compare compare_eq x y
    end else begin
      lex_compare_antisym compare (fun x y -> compare_eq x y; compare_eq y x; compare_neg x y; compare_neg y x) (Seq.seq_to_list (E.n_to_be n y)) (Seq.seq_to_list (E.n_to_be n x));
      big_endian_lex_compare_aux n compare compare_eq compare_neg y x
    end
  end else ()
