module CBOR.Pulse.Raw.EverParse.Insert

open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8

val cbor_raw_map_insert_out_inv
  (off1: SZ.t)
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Tot prop

val cbor_raw_map_insert_out_inv_intro
  (off1: SZ.t)
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Lemma
  (requires (
    let sm = serialize_cbor_map m in
    let sk = serialize_cbor key in
    let sv = serialize_cbor value in
    SZ.v off1 + Seq.length sm == SZ.v off2 /\
    SZ.v off2 + Seq.length sk == SZ.v off3 /\
    SZ.v off3 + Seq.length sv == Seq.length v /\
    Seq.slice v (SZ.v off1) (SZ.v off2) `Seq.equal` sm /\
    Seq.slice v (SZ.v off2) (SZ.v off3) `Seq.equal` sk /\
    Seq.slice v (SZ.v off3) (Seq.length v) `Seq.equal` sv
  ))
  (ensures (cbor_raw_map_insert_out_inv off1 m off2 key off3 value v))

val cbor_raw_map_insert_post
  (m: list (raw_data_item & raw_data_item))
  (key: raw_data_item)
  (value: raw_data_item)
  (res: bool)
  (v': Seq.seq U8.t)
: Tot prop

val cbor_raw_map_insert_post_elim
  (m: list (raw_data_item & raw_data_item))
  (key: raw_data_item)
  (value: raw_data_item)
  (res: bool)
  (v': Seq.seq U8.t)
: Lemma
  (requires (cbor_raw_map_insert_post m key value res v'))
  (ensures (
    match cbor_map_insert m (key, value) with
    | None -> res == false
    | Some m' -> res == true /\ v' == serialize_cbor_map m'
  ))

val cbor_raw_map_insert
  (out: S.slice U8.t)
  (m: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off2: SZ.t)
  (key: Ghost.erased raw_data_item)
  (off3: SZ.t)
  (value: Ghost.erased raw_data_item)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt bool
    (pts_to out v ** pure (cbor_raw_map_insert_out_inv 0sz m off2 key off3 value v))
    (fun res -> exists* v' . pts_to out v' **
      pure (cbor_raw_map_insert_post m key value res v'))
