module CBOR.Pulse.Raw.EverParse.Det.Compare.Base
#lang-pulse
include CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open CBOR.Pulse.Raw.Compare.Base
open CBOR.Pulse.Raw.Compare.Bytes
open LowParse.Spec.VCList
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Iterator
open LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module U64 = FStar.UInt64
module I16 = FStar.Int16
module U8 = FStar.UInt8
module Spec = CBOR.Spec.Raw.Base
module NC = CBOR.Pulse.Raw.EverParse.Nondet.Compare
module LPS = LowParse.Pulse.Base
module SCE = CBOR.Pulse.Raw.EverParse.SerializeCborEq

#push-options "--z3rlimit 32"

```pulse
fn impl_raw_uint64_compare
  (_: unit)
: impl_compare_scalar_t u#0 #_ raw_uint64_compare
= (x1: _)
  (x2: _)
{
  let c = impl_uint8_compare () x1.size x2.size;
  if (c = 0s) {
    uint64_compare x1.value x2.value
  } else {
    c
  }
}
```

#pop-options

// === Byte-compare helpers ===

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

```pulse
fn byte_compare_pts_to_parsed_data_item
  (s1 s2: S.slice byte)
  (#p1: perm) (#v1: Ghost.erased raw_data_item)
  (#p2: perm) (#v2: Ghost.erased raw_data_item)
requires
  PPB.pts_to_parsed parse_raw_data_item s1 #p1 v1 **
  PPB.pts_to_parsed parse_raw_data_item s2 #p2 v2
returns res: I16.t
ensures
  PPB.pts_to_parsed parse_raw_data_item s1 #p1 v1 **
  PPB.pts_to_parsed parse_raw_data_item s2 #p2 v2 **
  pure (same_sign (I16.v res) (cbor_compare v1 v2))
{
  cbor_compare_correct (Ghost.reveal v1) (Ghost.reveal v2);
  SCE.serialize_cbor_eq_bare_serialize (Ghost.reveal v1);
  SCE.serialize_cbor_eq_bare_serialize (Ghost.reveal v2);
  PPB.pts_to_parsed_serialized serialize_raw_data_item s1;
  PPB.pts_to_parsed_serialized serialize_raw_data_item s2;
  unfold (LPS.pts_to_serialized serialize_raw_data_item s1 #p1 (Ghost.reveal v1));
  unfold (LPS.pts_to_serialized serialize_raw_data_item s2 #p2 (Ghost.reveal v2));
  let res = lex_compare_bytes s1 s2;
  fold (LPS.pts_to_serialized serialize_raw_data_item s1 #p1 (Ghost.reveal v1));
  fold (LPS.pts_to_serialized serialize_raw_data_item s2 #p2 (Ghost.reveal v2));
  Trade.elim (LPS.pts_to_serialized serialize_raw_data_item s1 #p1 (Ghost.reveal v1))
             (PPB.pts_to_parsed parse_raw_data_item s1 #p1 v1);
  Trade.elim (LPS.pts_to_serialized serialize_raw_data_item s2 #p2 (Ghost.reveal v2))
             (PPB.pts_to_parsed parse_raw_data_item s2 #p2 v2);
  res
}
```

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
```pulse
fn byte_compare_pts_to_parsed_strong_prefix_data_item
  (f64: squash SZ.fits_u64)
  (s1 s2: S.slice byte)
  (#p1: perm) (#v1: Ghost.erased raw_data_item)
  (#p2: perm) (#v2: Ghost.erased raw_data_item)
requires
  PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #p1 v1 **
  PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #p2 v2
returns res: I16.t
ensures
  PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #p1 v1 **
  PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #p2 v2 **
  pure (same_sign (I16.v res) (cbor_compare v1 v2))
{
  let ex1 = PPB.pts_to_parsed_strong_prefix_to_serialized_trade
              serialize_raw_data_item jump_raw_data_item_eta s1;
  let ex2 = PPB.pts_to_parsed_strong_prefix_to_serialized_trade
              serialize_raw_data_item jump_raw_data_item_eta s2;
  cbor_compare_correct (Ghost.reveal v1) (Ghost.reveal v2);
  SCE.serialize_cbor_eq_bare_serialize (Ghost.reveal v1);
  SCE.serialize_cbor_eq_bare_serialize (Ghost.reveal v2);
  unfold (LPS.pts_to_serialized serialize_raw_data_item ex1 #p1 (Ghost.reveal v1));
  unfold (LPS.pts_to_serialized serialize_raw_data_item ex2 #p2 (Ghost.reveal v2));
  let res = lex_compare_bytes ex1 ex2;
  fold (LPS.pts_to_serialized serialize_raw_data_item ex1 #p1 (Ghost.reveal v1));
  fold (LPS.pts_to_serialized serialize_raw_data_item ex2 #p2 (Ghost.reveal v2));
  Trade.elim (LPS.pts_to_serialized serialize_raw_data_item ex1 #p1 (Ghost.reveal v1))
             (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #p1 v1);
  Trade.elim (LPS.pts_to_serialized serialize_raw_data_item ex2 #p2 (Ghost.reveal v2))
             (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #p2 v2);
  res
}
```

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
```pulse
fn byte_compare_pts_to_parsed_pair_data_item
  (f64: squash SZ.fits_u64)
  (s1 s2: S.slice byte)
  (#p1: perm) (#kv1: Ghost.erased (raw_data_item & raw_data_item))
  (#p2: perm) (#kv2: Ghost.erased (raw_data_item & raw_data_item))
requires
  PPB.pts_to_parsed_strong_prefix
    (nondep_then parse_raw_data_item parse_raw_data_item)
    s1 #p1 kv1 **
  PPB.pts_to_parsed_strong_prefix
    (nondep_then parse_raw_data_item parse_raw_data_item)
    s2 #p2 kv2
returns res: I16.t
ensures
  PPB.pts_to_parsed_strong_prefix
    (nondep_then parse_raw_data_item parse_raw_data_item)
    s1 #p1 kv1 **
  PPB.pts_to_parsed_strong_prefix
    (nondep_then parse_raw_data_item parse_raw_data_item)
    s2 #p2 kv2 **
  pure (same_sign (I16.v res) (cbor_compare_pair kv1 kv2))
{
  let pair_ser = serialize_nondep_then serialize_raw_data_item serialize_raw_data_item;
  let pair_jmp = jump_nondep_then jump_raw_data_item_eta jump_raw_data_item_eta;
  let ex1 = PPB.pts_to_parsed_strong_prefix_to_serialized_trade pair_ser pair_jmp s1;
  let ex2 = PPB.pts_to_parsed_strong_prefix_to_serialized_trade pair_ser pair_jmp s2;
  SCE.pair_byte_compare_eq_cbor_compare_pair (Ghost.reveal kv1) (Ghost.reveal kv2);
  unfold (LPS.pts_to_serialized pair_ser ex1 #p1 (Ghost.reveal kv1));
  unfold (LPS.pts_to_serialized pair_ser ex2 #p2 (Ghost.reveal kv2));
  let res = lex_compare_bytes ex1 ex2;
  fold (LPS.pts_to_serialized pair_ser ex1 #p1 (Ghost.reveal kv1));
  fold (LPS.pts_to_serialized pair_ser ex2 #p2 (Ghost.reveal kv2));
  Trade.elim (LPS.pts_to_serialized pair_ser ex1 #p1 (Ghost.reveal kv1))
             (PPB.pts_to_parsed_strong_prefix
                (nondep_then parse_raw_data_item parse_raw_data_item)
                s1 #p1 kv1);
  Trade.elim (LPS.pts_to_serialized pair_ser ex2 #p2 (Ghost.reveal kv2))
             (PPB.pts_to_parsed_strong_prefix
                (nondep_then parse_raw_data_item parse_raw_data_item)
                s2 #p2 kv2);
  res
}
```

#pop-options
