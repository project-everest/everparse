module LowParse.Spec.Int.Unique

module Aux = LowParse.Spec.Int.Aux
module I = LowParse.Spec.Int
module Seq = FStar.Seq

open LowParse.Spec.Base

let le_refl (x y: int) : Lemma (requires (x <= y /\ y <= x)) (ensures (x == y)) = ()

let parse_u8_unique
  (b: bytes)
: Lemma
  (parse Aux.parse_u8 b == parse I.parse_u8 b)
= parser_kind_prop_equiv (get_parser_kind Aux.parse_u8) Aux.parse_u8;
  parser_kind_prop_equiv (get_parser_kind I.parse_u8) I.parse_u8;
  if Seq.length b < 1
  then ()
  else begin
    I.parse_u8_spec b;
    Aux.parse_u8_spec b;
    let (Some (vI, consumedI)) = parse I.parse_u8 b in
    let (Some (vAux, consumedAux)) = parse Aux.parse_u8 b in
    le_refl consumedI 1;
    le_refl consumedAux 1;
    ()
  end

module U8 = FStar.UInt8

let serialize_u8_unique
  (x: U8.t)
: Lemma
  (serialize Aux.serialize_u8 x == serialize I.serialize_u8 x)
= Classical.forall_intro parse_u8_unique;
  let s : serializer I.parse_u8 = serialize_ext Aux.parse_u8 Aux.serialize_u8 I.parse_u8 in
  serializer_unique I.parse_u8 I.serialize_u8 s x

let parse_u16_unique
  (b: bytes)
: Lemma
  (parse Aux.parse_u16 b == parse I.parse_u16 b)
= parser_kind_prop_equiv (get_parser_kind Aux.parse_u16) Aux.parse_u16;
  parser_kind_prop_equiv (get_parser_kind I.parse_u16) I.parse_u16;
  if Seq.length b < 2
  then ()
  else begin
    I.parse_u16_spec b;
    Aux.parse_u16_spec b;
    let (Some (vI, consumedI)) = parse I.parse_u16 b in
    let (Some (vAux, consumedAux)) = parse Aux.parse_u16 b in
    le_refl consumedI 2;
    le_refl consumedAux 2;
    ()
  end

module U16 = FStar.UInt16

let serialize_u16_unique
  (x: U16.t)
: Lemma
  (serialize #_ #_ #Aux.parse_u16 Aux.serialize_u16 x == serialize I.serialize_u16 x)
= Classical.forall_intro parse_u16_unique;
  let s : serializer I.parse_u16 = serialize_ext Aux.parse_u16 Aux.serialize_u16 I.parse_u16 in
  serializer_unique I.parse_u16 I.serialize_u16 s x

let parse_u32_unique
  (b: bytes)
: Lemma
  (parse Aux.parse_u32 b == parse I.parse_u32 b)
= parser_kind_prop_equiv (get_parser_kind Aux.parse_u32) Aux.parse_u32;
  parser_kind_prop_equiv (get_parser_kind I.parse_u32) I.parse_u32;
  if Seq.length b < 4
  then ()
  else begin
    I.parse_u32_spec b;
    Aux.parse_u32_spec b;
    let (Some (vI, consumedI)) = parse I.parse_u32 b in
    let (Some (vAux, consumedAux)) = parse Aux.parse_u32 b in
    le_refl consumedI 4;
    le_refl consumedAux 4;
    ()
  end

module U32 = FStar.UInt32

let serialize_u32_unique
  (x: U32.t)
: Lemma
  (serialize #_ #_ #Aux.parse_u32 Aux.serialize_u32 x == serialize I.serialize_u32 x)
= Classical.forall_intro parse_u32_unique;
  let s : serializer I.parse_u32 = serialize_ext Aux.parse_u32 Aux.serialize_u32 I.parse_u32 in
  serializer_unique I.parse_u32 I.serialize_u32 s x
