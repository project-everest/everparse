module CBOR.Pulse.Raw.Format.Match
#lang-pulse
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.VCList
open LowParse.Pulse.Base

module U64 = FStar.UInt64

let cbor_match_serialized_payload_array
  c p r
= exists* n (r': nlist n raw_data_item) .
    pts_to_serialized (serialize_nlist n serialize_raw_data_item) c #p r' **
    pure (r == r')

let cbor_match_serialized_payload_map
  c p r
= exists* n (r' : nlist n (raw_data_item & raw_data_item)) .
    pts_to_serialized (serialize_nlist n (serialize_raw_data_item `serialize_nondep_then` serialize_raw_data_item)) c #p r' **
    pure (r == r')

let cbor_match_serialized_payload_tagged
  c p r
= pts_to_serialized serialize_raw_data_item c #p r

ghost
fn cbor_match_serialized_payload_array_share
  (c: slice U8.t)
  (p: perm)
  (r: list raw_data_item)
requires
    (cbor_match_serialized_payload_array c p r)
ensures
    (
      cbor_match_serialized_payload_array c (p /. 2.0R) r **
      cbor_match_serialized_payload_array c (p /. 2.0R) r
    )
{
  unfold (cbor_match_serialized_payload_array c p r);
  with n (r': nlist n raw_data_item) .
    assert (pts_to_serialized (serialize_nlist n serialize_raw_data_item) c #p r');
  pts_to_serialized_share (serialize_nlist n serialize_raw_data_item) c;
  fold (cbor_match_serialized_payload_array c (p /. 2.0R) r);
  fold (cbor_match_serialized_payload_array c (p /. 2.0R) r);
}

ghost
fn cbor_match_serialized_payload_array_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: list raw_data_item)
  (p2: perm)
  (r2: list raw_data_item)
requires
    (cbor_match_serialized_payload_array c p1 r1 **
      cbor_match_serialized_payload_array c p2 r2
    )
ensures
    (
      cbor_match_serialized_payload_array c (p1 +. p2) r1 **
      pure (r1 == r2)
    )
{
  unfold (cbor_match_serialized_payload_array c p1 r1);
  with n1 (r1': nlist n1 raw_data_item) .
    assert (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) c #p1 r1');
  unfold (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) c #p1 r1');
  serialize_nlist_serialize_list n1 serialize_raw_data_item r1';
  unfold (cbor_match_serialized_payload_array c p2 r2);
  with n2 (r2': nlist n2 raw_data_item) .
    assert (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) c #p2 r2');
  unfold (pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) c #p2 r2');
  serialize_nlist_serialize_list n2 serialize_raw_data_item r2';
  Pulse.Lib.Slice.gather c;
  serializer_injective _ (serialize_list _ serialize_raw_data_item) r1' r2';
  fold (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) c #(p1 +. p2) r1');
  fold (cbor_match_serialized_payload_array c (p1 +. p2) r1);
}

ghost
fn cbor_match_serialized_payload_map_share
  (c: slice U8.t)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
requires
    (cbor_match_serialized_payload_map c p r)
ensures
    (
      cbor_match_serialized_payload_map c (p /. 2.0R) r **
      cbor_match_serialized_payload_map c (p /. 2.0R) r
    )
{
  unfold (cbor_match_serialized_payload_map c p r);
  with n (r': nlist n (raw_data_item & raw_data_item)) .
    assert (pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p r');
  pts_to_serialized_share (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c;
  fold (cbor_match_serialized_payload_map c (p /. 2.0R) r);
  fold (cbor_match_serialized_payload_map c (p /. 2.0R) r);
}

ghost
fn cbor_match_serialized_payload_map_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: list (raw_data_item & raw_data_item))
  (p2: perm)
  (r2: list (raw_data_item & raw_data_item))
requires
    (cbor_match_serialized_payload_map c p1 r1 **
      cbor_match_serialized_payload_map c p2 r2
    )
ensures
    (
      cbor_match_serialized_payload_map c (p1 +. p2) r1 **
      pure (r1 == r2)
    )
{
  unfold (cbor_match_serialized_payload_map c p1 r1);
  with n1 (r1': nlist n1 (raw_data_item & raw_data_item)) .
    assert (pts_to_serialized (serialize_nlist n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p1 r1');
  unfold (pts_to_serialized (serialize_nlist n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p1 r1');
  serialize_nlist_serialize_list n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) r1';
  unfold (cbor_match_serialized_payload_map c p2 r2);
  with n2 (r2': nlist n2 (raw_data_item & raw_data_item)) .
    assert (pts_to_serialized (serialize_nlist n2 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p2 r2');
  unfold (pts_to_serialized (serialize_nlist n2 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p2 r2');
  serialize_nlist_serialize_list n2 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) r2';
  Pulse.Lib.Slice.gather c;
  serializer_injective _ (serialize_list _ (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) r1' r2';
  fold (pts_to_serialized (serialize_nlist n1 (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #(p1 +. p2) r1');
  fold (cbor_match_serialized_payload_map c (p1 +. p2) r1);
}

ghost
fn cbor_match_serialized_payload_tagged_share
  (c: slice U8.t)
  (p: perm)
  (r: raw_data_item)
requires
    (cbor_match_serialized_payload_tagged c p r)
ensures
    (
      cbor_match_serialized_payload_tagged c (p /. 2.0R) r **
      cbor_match_serialized_payload_tagged c (p /. 2.0R) r
    )
{
  unfold (cbor_match_serialized_payload_tagged c p r);
  pts_to_serialized_share serialize_raw_data_item c;
  fold (cbor_match_serialized_payload_tagged c (p /. 2.0R) r);
  fold (cbor_match_serialized_payload_tagged c (p /. 2.0R) r);
}

ghost
fn cbor_match_serialized_payload_tagged_gather
  (c: slice U8.t)
  (p1: perm)
  (r1: raw_data_item)
  (p2: perm)
  (r2: raw_data_item)
requires
    (cbor_match_serialized_payload_tagged c p1 r1 **
      cbor_match_serialized_payload_tagged c p2 r2
    )
ensures
    (
      cbor_match_serialized_payload_tagged c (p1 +. p2) r1 **
      pure (r1 == r2)
    )
{
  unfold (cbor_match_serialized_payload_tagged c p1 r1);
  unfold (cbor_match_serialized_payload_tagged c p2 r2);
  pts_to_serialized_gather serialize_raw_data_item c;
  fold (cbor_match_serialized_payload_tagged c (p1 +. p2) r1);
}

#set-options "--print_implicits"

fn cbor_match_serialized_payload_array_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list raw_data_item))
  (c': slice U8.t)
norewrite
requires
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_array c p r **
      pure (len c == len c')
    )
ensures
    (
      cbor_match_serialized_payload_array c p r **
      cbor_match_serialized_payload_array c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_array c' 1.0R r)
        (exists* v' . pts_to c' v')
    )
{
  unfold (cbor_match_serialized_payload_array c p r);
  with n r' . assert (
    pts_to_serialized (serialize_nlist n serialize_raw_data_item) c #p r'
  );
  pts_to_serialized_copy #(nlist n raw_data_item) #(parse_nlist_kind n parse_raw_data_item_kind) #(coerce_eq () (parse_nlist n parse_raw_data_item)) (coerce_eq () (serialize_nlist n serialize_raw_data_item <: serializer (parse_nlist n parse_raw_data_item))) c c';
  fold (cbor_match_serialized_payload_array c p r);
  fold (cbor_match_serialized_payload_array c' 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_payload_array c' 1.0R r)
      (exists* v' . pts_to c' v')
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_payload_array c' 1.0R r);
    with n r' . assert (
      pts_to_serialized (serialize_nlist n serialize_raw_data_item) c' r'
    );
    unfold (pts_to_serialized (serialize_nlist n serialize_raw_data_item) c' r')
  };
}

fn cbor_match_serialized_payload_map_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (list (raw_data_item & raw_data_item)))
  (c': slice U8.t)
norewrite
requires
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_map c p r **
      pure (len c == len c')
    )
ensures
    (
      cbor_match_serialized_payload_map c p r **
      cbor_match_serialized_payload_map c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_map c' 1.0R r)
        (exists* v' . pts_to c' v')
    )
{
  unfold (cbor_match_serialized_payload_map c p r);
  with n r' . assert (
    pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c #p r'
  );
  pts_to_serialized_copy #(nlist n (raw_data_item & raw_data_item)) #(parse_nlist_kind n (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)) #(coerce_eq () (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item))) (coerce_eq () (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item) <: serializer (parse_nlist n (nondep_then parse_raw_data_item parse_raw_data_item)))) c c';
  fold (cbor_match_serialized_payload_map c p r);
  fold (cbor_match_serialized_payload_map c' 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_payload_map c' 1.0R r)
      (exists* v' . pts_to c' v')
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_payload_map c' 1.0R r);
    with n r' . assert (
      pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c' r'
    );
    unfold (pts_to_serialized (serialize_nlist n (serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) c' r')
  };
}

fn cbor_match_serialized_payload_tagged_copy
  (c: slice U8.t)
  (p: perm)
  (r: Ghost.erased (raw_data_item))
  (c': slice U8.t)
norewrite
requires
    (exists* v' . pts_to c' v' **
      cbor_match_serialized_payload_tagged c p r **
      pure (len c == len c')
    )
ensures
    (
      cbor_match_serialized_payload_tagged c p r **
      cbor_match_serialized_payload_tagged c' 1.0R r **
      Trade.trade
        (cbor_match_serialized_payload_tagged c' 1.0R r)
        (exists* v' . pts_to c' v')
    )
{
  unfold (cbor_match_serialized_payload_tagged c p r);
  with r' . assert (
    pts_to_serialized (serialize_raw_data_item) c #p r'
  );
  pts_to_serialized_copy serialize_raw_data_item c c';
  fold (cbor_match_serialized_payload_tagged c p r);
  fold (cbor_match_serialized_payload_tagged c' 1.0R r);
  intro
    (Trade.trade
      (cbor_match_serialized_payload_tagged c' 1.0R r)
      (exists* v' . pts_to c' v')
    )
    #emp
    fn _
  {
    unfold (cbor_match_serialized_payload_tagged c' 1.0R r);
    with r' . assert (
      pts_to_serialized (serialize_raw_data_item) c' r'
    );
    unfold (pts_to_serialized (serialize_raw_data_item) c' r')
  };
}
