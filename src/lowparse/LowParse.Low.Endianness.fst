module LowParse.Low.Endianness
include LowParse.Low.Base
include LowStar.Endianness

module B = LowStar.Buffer
module HS = FStar.HyperStack
module Seq = FStar.Seq
module LE = LowStar.Endianness
module U32 = FStar.UInt32

let writable_store_pre
  (#rrel: _)
  (#rel: _)
  (b: B.mbuffer byte rrel rel)
  (i: nat)
  (j: nat)
  (predicate:Seq.seq byte -> Type)
  (h: HS.mem)
: Lemma
  (requires (
    writable b i (i + j) h /\
    i + j <= B.length b
  ))
  (ensures (
    LE.store_pre b i j predicate h
  ))
= let sb = B.as_seq h b in
  let len = B.length b in
  let phi
    (s: Seq.seq byte)
  : Lemma
    (requires (
      Seq.length s == len /\
      Seq.equal (Seq.slice s 0 i) (Seq.slice sb 0 i) /\
      Seq.equal (Seq.slice s (i + j) len) (Seq.slice sb (i + j) len) /\
      predicate (Seq.slice s i (i + j))
    ))
    (ensures (
      rel sb s
    ))
  = assert (sb `Seq.equal` Seq.replace_subseq sb i (i + j) (Seq.slice sb i (i + j)));
    assert (s `Seq.equal` Seq.replace_subseq sb i (i + j) (Seq.slice s i (i + j)))
  in
  Classical.forall_intro (Classical.move_requires phi)

let store_post_modifies
  (#a:Type) (#rrel #rel:B.srel a) (b:B.mbuffer a rrel rel)
  (i:nat) (j:nat{i + j <= B.length b}) (predicate:Seq.seq a -> Type)
  (h0: HS.mem)
  (h1: HS.mem)
: Lemma
  (requires (
    B.live h0 b /\
    LE.store_post b i j predicate h0 () h1
  ))
  (ensures (
    B.modifies (B.loc_buffer_from_to b (U32.uint_to_t i) (U32.uint_to_t (i + j))) h0 h1
  ))
= B.modifies_loc_buffer_from_to_intro b (U32.uint_to_t i) (U32.uint_to_t (i + j)) B.loc_none h0 h1
