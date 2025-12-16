module CBOR.Pulse.Raw.Insert
#lang-pulse
include CBOR.Pulse.Raw.Format.Parse
include CBOR.Pulse.Raw.Compare.Bytes
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module R = CBOR.Spec.Raw.Valid

let cbor_raw_map_insert_out_inv'
  (off1: SZ.t)
  (m: (list (raw_data_item & raw_data_item)))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Tot prop
= let sm = serialize_cbor_map m in
  let sk = serialize_cbor key in
  let sv = serialize_cbor value in
  SZ.v off1 + Seq.length sm == SZ.v off2 /\
  SZ.v off2 + Seq.length sk == SZ.v off3 /\
  SZ.v off3 + Seq.length sv == Seq.length v /\
  Seq.slice v (SZ.v off1) (Seq.length v) `Seq.equal`
    (sm `Seq.append` (sk `Seq.append` sv))

let cbor_raw_map_insert_out_inv
  (off1: SZ.t)
  (m: (list (raw_data_item & raw_data_item)))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Tot prop
= let sm = serialize_cbor_map m in
  let sk = serialize_cbor key in
  let sv = serialize_cbor value in
  SZ.v off1 + Seq.length sm == SZ.v off2 /\
  SZ.v off2 + Seq.length sk == SZ.v off3 /\
  SZ.v off3 + Seq.length sv == Seq.length v /\
  Seq.slice v (SZ.v off1) (SZ.v off2) `Seq.equal` sm /\
  Seq.slice v (SZ.v off2) (SZ.v off3) `Seq.equal` sk /\
  Seq.slice v (SZ.v off3) (Seq.length v) `Seq.equal` sv

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver

let seq_slice_append
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures
    Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1 /\
    Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2) `Seq.equal` s2
  )
= ()

#restart-solver

let cbor_raw_map_insert_out_inv_equiv
  (off1: SZ.t)
  (m: (list (raw_data_item & raw_data_item)))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
: Lemma
  (cbor_raw_map_insert_out_inv off1 m off2 key off3 value v <==>
    cbor_raw_map_insert_out_inv' off1 m off2 key off3 value v
  )
= let sm = serialize_cbor_map m in
  let sk = serialize_cbor key in
  let sv = serialize_cbor value in
  if
    SZ.v off1 + Seq.length sm = SZ.v off2 &&
    SZ.v off2 + Seq.length sk = SZ.v off3 &&
    SZ.v off3 + Seq.length sv = Seq.length v
  then begin
    seq_slice_append sm (Seq.append sk sv);
    seq_slice_append sk sv;
    Seq.slice_slice v (SZ.v off1) (Seq.length v) 0 (Seq.length sm);
    Seq.slice_slice v (SZ.v off1) (Seq.length v) (Seq.length sm) (Seq.length sm + Seq.length (Seq.append sk sv));
    Seq.lemma_split (Seq.slice v (SZ.v off1) (Seq.length v)) (SZ.v off2 - SZ.v off1);
    Seq.slice_slice v (SZ.v off2) (Seq.length v) 0 (Seq.length sk);
    Seq.slice_slice v (SZ.v off2) (Seq.length v) (Seq.length sk) (Seq.length sk + Seq.length sv);
    Seq.lemma_split (Seq.slice v (SZ.v off2) (Seq.length v)) (SZ.v off3 - SZ.v off2);
    ()
  end
  else
    ()

#pop-options

let cbor_raw_map_insert_post
  (m: (list (raw_data_item & raw_data_item)))
  (key: raw_data_item)
  (value: raw_data_item)
  (res: bool)
  (v': Seq.seq U8.t)
: Tot prop
= match cbor_map_insert m (key, value) with
  | None -> res == false
  | Some m' -> res == true /\ v' == serialize_cbor_map m'

module GR = Pulse.Lib.GhostReference
module R = Pulse.Lib.Reference

type cbor_raw_map_insert_result =
  | CFailure
  | CInProgress
  | CSuccess

unfold
let cbor_raw_map_insert_inv_not_success
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
  (l1 l2: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (res: cbor_raw_map_insert_result)
: Tot prop
=
      let om' = cbor_map_insert m (key, value) in
      let om2' = cbor_map_insert l2 (key, value) in
      let sl1 = serialize_cbor_map l1 in
      cbor_raw_map_insert_out_inv off l2 off2 key off3 value v /\
      Seq.length sl1 == SZ.v off /\
      Seq.slice v 0 (SZ.v off) `Seq.equal` sl1 /\
      Some? om' == (CInProgress? res && Some? om2') /\
      begin match om', om2' with
      | None, None -> True
      | Some m', Some m2' -> m' == List.Tot.append l1 m2'
      | _ -> False
      end

unfold
let cbor_raw_map_insert_inv'
  (m: list (raw_data_item & raw_data_item))
  (off2: SZ.t)
  (key: raw_data_item)
  (off3: SZ.t)
  (value: raw_data_item)
  (v: Seq.seq U8.t)
  (l1 l2: list (raw_data_item & raw_data_item))
  (off: SZ.t)
  (res: cbor_raw_map_insert_result)
: Tot prop
=
  if res = CSuccess
  then cbor_raw_map_insert_post m key value true v
  else cbor_raw_map_insert_inv_not_success m off2 key off3 value v l1 l2 off res

let cbor_raw_map_insert_inv = cbor_raw_map_insert_inv'

let serialize_cbor_map_cons_equiv
  (m: list (raw_data_item & raw_data_item))
: Lemma
  (Cons? m <==> Seq.length (serialize_cbor_map m) > 0)
= match m with
  | [] -> serialize_cbor_map_nil ()
  | (key, value) :: q ->
    serialize_cbor_map_cons key value q;
    serialize_cbor_nonempty key

module I16 = FStar.Int16

inline_for_extraction
fn cbor_jump_append
  (input: slice U8.t)
  (c: Ghost.erased raw_data_item)
  (v: Ghost.erased (Seq.seq U8.t))
  (#pm: perm)
  (#v': Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v' ** pure (
      Ghost.reveal v' == Seq.append (serialize_cbor c) (Ghost.reveal v)
    ))
returns res: SZ.t
ensures
    (
      pts_to input #pm v' ** pure (
      SZ.v res == Seq.length (serialize_cbor c)
    ))
{
  seq_slice_append (serialize_cbor c) (Ghost.reveal v);
  cbor_jump () input 0sz c
}

let seq_append_assoc_1_23_4
  (#t: Type)
  (s1 s2 s3 s4: Seq.seq t)
: Lemma
  (Seq.append s1 (Seq.append (Seq.append s2 s3) s4) `Seq.equal`
    Seq.append (Seq.append s1 s2) (Seq.append s3 s4)
  )
= ()

#push-options "--z3rlimit 192"

#restart-solver

fn cbor_raw_map_insert
  (out: slice U8.t)
  (m: Ghost.erased (list (raw_data_item & raw_data_item)))
  (off2: SZ.t)
  (key: Ghost.erased raw_data_item)
  (off3: SZ.t)
  (value: Ghost.erased raw_data_item)
requires exists* v .
  pts_to out v **
  pure (cbor_raw_map_insert_out_inv 0sz m off2 key off3 value v)
returns res: bool
ensures exists* v .
  pts_to out v **
  pure (cbor_raw_map_insert_post m key value res v)
{
  with v . assert (pts_to out v);
  serialize_cbor_map_nil ();
  let pl1 = GR.alloc (Nil #(raw_data_item & raw_data_item));
  let pl2 = GR.alloc (Ghost.reveal m);
  let mut poff = 0sz;
  let mut pres = CInProgress;
  while (
    let res = !pres;
    if (CInProgress? res) {
      let off = !poff;
      (SZ.lt off off2)
    } else {
      false
    }
  ) invariant b . exists* v l1 l2 off res . (
    pts_to out v **
    GR.pts_to pl1 l1 **
    GR.pts_to pl2 l2 **
    R.pts_to poff off **
    R.pts_to pres res **
    pure (
      cbor_raw_map_insert_inv m off2 key off3 value v l1 l2 off res
    ) ** pure (
      b == (CInProgress? res && (SZ.v off < SZ.v off2))
    )
  ) {
    with l1 . assert (GR.pts_to pl1 l1);
    with l2 . assert (GR.pts_to pl2 l2);
    with v . assert (pts_to out v);
    pts_to_len out;
    let off = !poff;
    Seq.lemma_split v (SZ.v off);
    let (out1, out2kv) = split out off;
    let sl1 = Ghost.hide (serialize_cbor_map l1);
    assert (pts_to out1 sl1);
    Seq.lemma_split (Seq.slice v (SZ.v off) (Seq.length v)) (SZ.v off2 - SZ.v off);
    let (out2, outkv) = split out2kv (SZ.sub off2 off);
    Seq.lemma_split (Seq.slice v (SZ.v off2) (Seq.length v)) (SZ.v off3 - SZ.v off2);
    let (outk, outv) = split outkv (SZ.sub off3 off2);
    assert (pts_to outk (serialize_cbor key));
    assert (pts_to outv (serialize_cbor value));
    serialize_cbor_map_cons_equiv l2;
    let kv' = Ghost.hide (List.Tot.hd l2);
    let key' = Ghost.hide (fst kv');
    let value' = Ghost.hide (snd kv');
    let l2' = Ghost.hide (List.Tot.tl l2);
    serialize_cbor_map_cons key' value' l2';
    Seq.append_assoc (serialize_cbor key') (serialize_cbor value') (serialize_cbor_map l2');
    seq_slice_append (serialize_cbor key') (Seq.append (serialize_cbor value') (serialize_cbor_map l2'));
    let offk = cbor_jump_append out2 key' (Seq.append (serialize_cbor value') (serialize_cbor_map l2'));
    let (outk', outvq) = split out2 offk;
    assert (pts_to outk' (serialize_cbor key'));
    assert (pts_to outvq (Seq.append (serialize_cbor value') (serialize_cbor_map l2')));
    cbor_compare_correct key' key;
    let c = lex_compare_bytes outk' outk;
    serialize_cbor_map_singleton key' value';
    let sk = Ghost.hide (serialize_cbor key);
    let sv = Ghost.hide (serialize_cbor value);
    let slkv = Ghost.hide (Seq.append sk sv);
    if (I16.lt c 0s) {
      seq_slice_append (serialize_cbor value') (serialize_cbor_map l2');
      let offq = cbor_jump_append outvq value' (serialize_cbor_map l2');
      join _ _ outkv;
      join _ _ out2;
      join _ _ out2kv;
      join _ _ out;
      let lkv' = Ghost.hide [(Ghost.reveal key', Ghost.reveal value')];
      serialize_cbor_map_append l1 lkv';
      let slkv' = Ghost.hide (Seq.append (serialize_cbor key') (serialize_cbor value'));
      let sl2' = Ghost.hide (serialize_cbor_map l2');
      let sl1' = Ghost.hide (Seq.append sl1 slkv');
      seq_append_assoc_1_23_4 sl1 slkv' sl2' slkv;
      let v' = Ghost.hide (Seq.append sl1' (Seq.append sl2' slkv)); 
      assert (pts_to out v');
      let off' = SZ.add off (SZ.add offk offq);
      poff := off';
      seq_slice_append sl1' (Seq.append sl2' slkv);
      seq_slice_append sl2' slkv;
      Classical.forall_intro (List.Tot.append_assoc l1 lkv');
      GR.op_Colon_Equals pl1 (List.Tot.append l1 lkv');
      GR.op_Colon_Equals pl2 l2';
      assert (pure (
        SZ.v off + Seq.length (serialize_cbor_map l2) == SZ.v off2
      ));
      assert (pure (
        Seq.length slkv' + Seq.length sl2' == Seq.length (serialize_cbor_map l2)
      ));
      assert (pure (
        SZ.v off + (Seq.length slkv' + Seq.length sl2') == SZ.v off2
      ));
      assert (pure (
        SZ.v off' == SZ.v off + Seq.length slkv'
      ));
      assert (pure (
        SZ.v off' + Seq.length sl2' == SZ.v off2
      ));
      assert (pure (SZ.v off == Seq.length sl1));
      Seq.lemma_len_append sl1 slkv';
      assert (pure (SZ.v off' == Seq.length sl1'));
      assert (pure (
          cbor_raw_map_insert_out_inv' off' l2' off2 key off3 value v'
      ));
      cbor_raw_map_insert_out_inv_equiv off' l2' off2 key off3 value v';
      ()
    } else if (I16.gt c 0s) {
      join _ _ outkv;
      join _ _ out2;
      join _ _ out2kv;
      let sl2 = Ghost.hide (serialize_cbor_map l2);
      Pulse.Lib.Swap.Slice.slice_swap' out2kv (SZ.sub off2 off) sl2 slkv;
      serialize_cbor_map_cons key value l2;
      serialize_cbor_map_append l1 ((Ghost.reveal key, Ghost.reveal value) :: l2);
      join _ _ out;
      pres := CSuccess
    } else {
      join _ _ outkv;
      join _ _ out2;
      join _ _ out2kv;
      join _ _ out;
      pres := CFailure
    }
  };
  let res = !pres;
  with l1 . assert (GR.pts_to pl1 l1);
  with l2 . assert (GR.pts_to pl2 l2);
  GR.free pl1;
  GR.free pl2;
  match res {
    CSuccess -> {
      true
    }
    CFailure -> {
      false
    }
    CInProgress -> {
      with v . assert (pts_to out v);
      with off1 . assert (R.pts_to poff off1);
      serialize_cbor_map_cons_equiv l2;
      serialize_cbor_map_singleton key value;
      serialize_cbor_map_append l1 [(Ghost.reveal key, Ghost.reveal value)];
      cbor_raw_map_insert_out_inv_equiv off1 l2 off2 key off3 value v;
      assert (pure (Seq.append (serialize_cbor key) (serialize_cbor value) `Seq.equal` Seq.slice v (SZ.v off1) (Seq.length v)));
      Seq.lemma_split v (SZ.v off1);
      true
    }
  }
}

#pop-options
