module LowParse.MLow.Int.Aux
include LowParse.Spec.Int.Aux
include LowParse.MLow.Combinators

module Seq = FStar.Seq
module E = LowParse.BigEndianImpl.Low
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Monotonic.Buffer
module HST = FStar.HyperStack.ST
module Cast = FStar.Int.Cast

(*
inline_for_extraction
let read_u16 : leaf_reader parse_u16 =
  decode_u16_injective ();
    make_total_constant_size_reader 2 2ul
      #U16.t
      decode_u16
      ()
      (fun input ->
        E.be_to_n_2 _ _ (E.u16 ()) input)

inline_for_extraction
let read_u32 : leaf_reader parse_u32 =
    decode_u32_injective ();
    make_total_constant_size_reader 4 4ul
      #U32.t
      decode_u32
      ()
      (fun input ->
        E.be_to_n_4 _ _ (E.u32 ()) input)

inline_for_extraction
let read_u8 : leaf_reader parse_u8 =
  decode_u8_injective ();
  make_total_constant_size_reader 1 1ul
    decode_u8
    ()
    (fun b -> B.index b 0ul)
*)

inline_for_extraction
let serialize32_u8 : serializer32 #_ #_ #parse_u8 serialize_u8 =
  fun v (#rrel #rel: B.srel byte) out pos ->
  let h = HST.get () in
  writable_upd out (U32.v pos) (U32.v pos + 1) h (U32.v pos) v;
  B.upd' out pos v;
  B.g_upd_modifies_strong out (U32.v pos) v h;
  B.g_upd_seq_as_seq out (Seq.upd (B.as_seq h out) (U32.v pos) v) h;
  pos `U32.add` 1ul

#push-options "--z3rlimit 16"

inline_for_extraction
let serialize32_u16 : serializer32 #_ #_ #parse_u16 serialize_u16 =
  fun v (#rrel #rel: B.srel byte) out pos ->
  let h0 = HST.get () in
  serialize_u16_eq v;
  let b1 = Cast.uint16_to_uint8 v in
  let d0 = U16.div v 256us in
  let b0 = Cast.uint16_to_uint8 d0 in
  let h = HST.get () in
  writable_upd out (U32.v pos) (U32.v pos + 2) h (U32.v pos) b0;
  B.upd' out pos b0;
  B.g_upd_modifies_strong out (U32.v pos) b0 h;
  B.g_upd_seq_as_seq out (Seq.upd (B.as_seq h out) (U32.v pos) b0) h;
  let h = HST.get () in
  writable_upd out (U32.v pos) (U32.v pos + 2) h (U32.v pos + 1) b1;
  B.upd' out (pos `U32.add` 1ul) b1;
  B.g_upd_modifies_strong out (U32.v pos + 1) b1 h;
  B.g_upd_seq_as_seq out (Seq.upd (B.as_seq h out) (U32.v pos + 1) b1) h;
  B.loc_includes_loc_buffer_from_to out pos (pos `U32.add` 2ul) pos (pos `U32.add` 1ul);
  B.loc_includes_loc_buffer_from_to out pos (pos `U32.add` 2ul) (pos `U32.add` 1ul) (pos `U32.add` 2ul);
  pos `U32.add` 2ul

#pop-options

(*
inline_for_extraction
let serialize32_u32 : serializer32 #_ #_ #parse_u32 serialize_u32 =
  fun v out ->
  let out' = B.sub out 0ul 4ul in
  E.n_to_be_4 U32.t 32 (E.u32 ()) v out';
  4ul
