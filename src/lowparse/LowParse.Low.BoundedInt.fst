module LowParse.Low.BoundedInt
open LowParse.Low.Combinators
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module E = LowParse.BigEndianImpl.Low
module Cast = FStar.Int.Cast

friend LowParse.Spec.BoundedInt

(* bounded integers *)

let read_bounded_integer_1 () =
  [@inline_let] let _ =
    decode_bounded_integer_injective 1
  in
  make_total_constant_size_reader 1 1ul #(bounded_integer 1) (decode_bounded_integer 1) () (fun #rrel #rel input pos ->
    let h = HST.get () in
    let r = E.be_to_n_1 _ _ (E.u32 ()) input pos in
    E.lemma_be_to_n_is_bounded (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 1));
    r
  )

let read_bounded_integer_2 () =
  [@inline_let] let _ =
    decode_bounded_integer_injective 2
  in
  make_total_constant_size_reader 2 2ul #(bounded_integer 2) (decode_bounded_integer 2) () (fun #rrel #rel input pos ->
    let h = HST.get () in
    let r = E.be_to_n_2 _ _ (E.u32 ()) input pos in
    E.lemma_be_to_n_is_bounded (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 2));
    r
  )

#push-options "--z3rlimit 16"

let read_bounded_integer_3 () =
  [@inline_let] let _ =
    decode_bounded_integer_injective 3
  in
  make_total_constant_size_reader 3 3ul #(bounded_integer 3) (decode_bounded_integer 3) () (fun #rrel #rel input pos ->
    let h = HST.get () in
    let r = E.be_to_n_3 _ _ (E.u32 ()) input pos in
    E.lemma_be_to_n_is_bounded (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 3));
    r
  )

let read_bounded_integer_4 () =
  [@inline_let] let _ =
    decode_bounded_integer_injective 4
  in
  make_total_constant_size_reader 4 4ul #(bounded_integer 4) (decode_bounded_integer 4) () (fun #rrel #rel input pos ->
    let h = HST.get () in
    let r = E.be_to_n_4 _ _ (E.u32 ()) input pos in
    E.lemma_be_to_n_is_bounded (Seq.slice (B.as_seq h input) (U32.v pos) (U32.v pos + 4));
    r
  )

#pop-options

let serialize32_bounded_integer_1 () =
  fun (v: bounded_integer 1) #rrel #rel out pos ->
  E.n_to_be_1 _ _ (E.u32 ()) v out pos;
  1ul

let serialize32_bounded_integer_2 () =
  fun (v: bounded_integer 2) #rrel #rel out pos ->
  E.n_to_be_2 _ _ (E.u32 ()) v out pos;
  2ul

let serialize32_bounded_integer_3 () =
  fun (v: bounded_integer 3) #rrel #rel out pos ->
  E.n_to_be_3 _ _ (E.u32 ()) v out pos;
  3ul

let serialize32_bounded_integer_4 () =
  fun (v: bounded_integer 4) #rrel #rel out pos ->
  E.n_to_be_4 _ _ (E.u32 ()) v out pos;
  4ul

let read_bounded_integer_le_1 =
  [@inline_let] let _ = bounded_integer_of_le_injective 1 in
  make_total_constant_size_reader 1 1ul #(bounded_integer 1) (bounded_integer_of_le 1) () (fun #rrel #rel b pos ->
    let h = HST.get () in
    [@inline_let] let _ = bounded_integer_of_le_1_eq (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 1)) in
    let r = B.index b pos in
    Cast.uint8_to_uint32 r
  )

let read_bounded_integer_le_2 =
  [@inline_let] let _ = bounded_integer_of_le_injective 2 in
  make_total_constant_size_reader 2 2ul #(bounded_integer 2) (bounded_integer_of_le 2) () (fun #rrel #rel b pos ->
    let h = HST.get () in
    [@inline_let] let _ = bounded_integer_of_le_2_eq (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 2)) in
    let r0 = B.index b pos in
    let r1 = B.index b (pos `U32.add` 1ul) in
    Cast.uint8_to_uint32 r0 `U32.add` (256ul `U32.mul` Cast.uint8_to_uint32 r1)
  )

let read_bounded_integer_le_4 =
  [@inline_let] let _ = bounded_integer_of_le_injective 4 in
  make_total_constant_size_reader 4 4ul #(bounded_integer 4) (bounded_integer_of_le 4) () (fun #rrel #rel b pos ->
    let h = HST.get () in
    [@inline_let] let _ = bounded_integer_of_le_4_eq (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 4)) in
    let r0 = B.index b pos in
    let r1 = B.index b (pos `U32.add` 1ul) in
    let r2 = B.index b (pos `U32.add` 2ul) in
    let r3 = B.index b (pos `U32.add` 3ul) in
    Cast.uint8_to_uint32 r0 `U32.add` (256ul `U32.mul` (Cast.uint8_to_uint32 r1 `U32.add` (256ul `U32.mul` (Cast.uint8_to_uint32 r2 `U32.add` (256ul `U32.mul` Cast.uint8_to_uint32 r3)))))
  )

let read_u16_le =
  [@inline_let] let _ = synth_u16_le_injective in
  read_synth'
    _
    synth_u16_le
    read_bounded_integer_le_2
    ()

let read_u32_le =
  read_synth'
    _
    synth_u32_le
    read_bounded_integer_le_4
    ()

let serialize32_bounded_integer_le_1
= fun x #rrel #rel b pos ->
  [@inline_let]
  let _ = serialize_bounded_integer_le_1_eq x 0 in
  let r0 = (Cast.uint32_to_uint8 x <: U8.t) in
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 1)) pos r0;
  1ul

let write_bounded_integer_le_1
= leaf_writer_strong_of_serializer32 serialize32_bounded_integer_le_1 ()

#push-options "--z3rlimit 16"

let serialize32_bounded_integer_le_2
= fun x #rrel #rel b pos ->
  [@inline_let]
  let _ =
    serialize_bounded_integer_le_2_eq x 0;
    serialize_bounded_integer_le_2_eq x 1
  in
  let r0 = (Cast.uint32_to_uint8 x <: U8.t) in
  let d0 = x `U32.div` 256ul in
  let r1 = (Cast.uint32_to_uint8 d0 <: U8.t) in
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 2)) pos r0;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 2)) (pos `U32.add` 1ul) r1;
  2ul

let write_bounded_integer_le_2 = leaf_writer_strong_of_serializer32 serialize32_bounded_integer_le_2 ()

let serialize32_bounded_integer_le_4
= fun x #rrel #rel b pos ->
  [@inline_let]
  let _ =
    serialize_bounded_integer_le_4_eq x 0;
    serialize_bounded_integer_le_4_eq x 1;
    serialize_bounded_integer_le_4_eq x 2;
    serialize_bounded_integer_le_4_eq x 3
  in
  let r0 = (Cast.uint32_to_uint8 x <: U8.t) in
  let d0 = x `U32.div` 256ul in
  let r1 = (Cast.uint32_to_uint8 d0 <: U8.t) in
  let d1 = d0 `U32.div` 256ul in
  let r2 = (Cast.uint32_to_uint8 d1<: U8.t) in
  let d2 = d1 `U32.div` 256ul in
  let r3 = (Cast.uint32_to_uint8 d2<: U8.t) in
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 4)) pos r0;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 4)) (pos `U32.add` 1ul) r1;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 4)) (pos `U32.add` 2ul) r2;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 4)) (pos `U32.add` 3ul) r3;
  4ul

#pop-options

let write_bounded_integer_le_4 = leaf_writer_strong_of_serializer32 serialize32_bounded_integer_le_4 ()

let write_u16_le =
  [@inline_let] let _ = synth_u16_le_injective; synth_u16_le_inverse in
  write_synth write_bounded_integer_le_2 synth_u16_le synth_u16_le_recip (fun x -> synth_u16_le_recip x) ()

let write_u32_le =
  write_synth write_bounded_integer_le_4 synth_u32_le synth_u32_le_recip (fun x -> synth_u32_le_recip x) ()
