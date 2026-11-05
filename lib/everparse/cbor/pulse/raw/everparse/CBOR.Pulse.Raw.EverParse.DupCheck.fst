module CBOR.Pulse.Raw.EverParse.DupCheck
#lang-pulse
open CBOR.Spec.Raw.EverParse.DupCheck
open CBOR.Pulse.Raw.EverParse.Format
open LowParse.Spec.Base
open LowParse.Pulse.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.Util

(* An offset-based, sort-based map key duplicate check over a buffer
   holding a well-formed (but not necessarily valid) CBOR raw data item,
   with map depth and map length bounds. Map keys are compared with the
   canonical order `cc` (which coincides with the basic data model
   equivalence on valid items.) Maps in keys are compared by sorting
   their entries in caller-provided scratch space, so this check
   allocates nothing. *)

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module I16 = FStar.Int16
module MS = LowParse.Pulse.MergeSort
module CB = CBOR.Pulse.Raw.Compare.Bytes
module Trade = Pulse.Lib.Trade.Util

let jump_item_end (b: bytes) (o r: SZ.t) : Lemma
  (requires validator_success parse_raw_data_item o b r)
  (ensures SZ.v r == item_end b (SZ.v o))
= item_at_eq b (SZ.v o)

(* Comparing the heads of two items with the same major type *)

inline_for_extraction
let u64_cmp (x y: U64.t) : Tot (r: I16.t {
  (I16.v r < 0 <==> U64.v x < U64.v y) /\
  (I16.v r == 0 <==> U64.v x == U64.v y)
}) =
  if U64.lt x y then (-1s) else if U64.gt x y then 1s else 0s

inline_for_extraction
let u8_cmp (x y: U8.t) : Tot (r: I16.t {
  (I16.v r < 0 <==> U8.v x < U8.v y) /\
  (I16.v r == 0 <==> U8.v x == U8.v y)
}) =
  if U8.lt x y then (-1s) else if U8.gt x y then 1s else 0s

inline_for_extraction
let impl_head_cmp (a1 a2: Ghost.erased raw_data_item) (h1 h2: header) : Pure I16.t
  (requires
    h1 == get_raw_data_item_header a1 /\
    h2 == get_raw_data_item_header a2 /\
    get_major_type a1 == get_major_type a2
  )
  (ensures fun r -> MS.same_sign (I16.v r) (head_compare a1 a2))
= header_major_type a1;
  header_major_type a2;
  let mt = get_header_major_type h1 in
  if mt = cbor_major_type_simple_value
  then u8_cmp (get_simple_value a1 h1) (get_simple_value a2 h2)
  else if mt = cbor_major_type_uint64 || mt = cbor_major_type_neg_int64
  then u64_cmp (get_int64_value a1 h1).value (get_int64_value a2 h2).value
  else if mt = cbor_major_type_byte_string || mt = cbor_major_type_text_string
  then u64_cmp (get_string_length a1 h1).value (get_string_length a2 h2).value
  else if mt = cbor_major_type_tagged
  then u64_cmp (get_tagged_tag a1 h1).value (get_tagged_tag a2 h2).value
  else if mt = cbor_major_type_array
  then u64_cmp (get_array_length a1 h1).value (get_array_length a2 h2).value
  else u64_cmp (get_map_length a1 h1).value (get_map_length a2 h2).value

(* Filling a slice with the offsets of the entries of a map *)

#push-options "--z3rlimit 32"

fn fill_offsets
  (b: S.slice U8.t) (#p: perm) (#bB: Ghost.erased bytes)
  (ks: S.slice SZ.t)
  (o0: SZ.t)
  (v: Ghost.erased (list (raw_data_item & raw_data_item)))
  (m: Ghost.erased nat)
  (q: Ghost.erased (list raw_data_item))
  (#s0: Ghost.erased (Seq.seq SZ.t))
requires
  pts_to b #p bB ** pts_to ks s0 ** pure (
    Seq.length s0 == List.Tot.length v /\
    items_at bB (SZ.v o0) (2 * List.Tot.length v + m) (List.Tot.append (list_of_pair_list v) q)
  )
returns o' : SZ.t
ensures exists* s . pts_to b #p bB ** pts_to ks s ** pure (
  Seq.length s == List.Tot.length v /\
  offsets_match bB s (Seq.length s) v /\
  (forall (j: nat) . j < Seq.length s ==> entry_struct bB (Seq.index s j)) /\
  items_at bB (SZ.v o') m q
)
{
  S.pts_to_len ks;
  let k = S.len ks;
  let mut pi = 0sz;
  let mut po = o0;
  fill_inv_init bB s0 (SZ.v o0) v m q;
  while (
    let i = !pi;
    SZ.lt i k
  )
  invariant exists* i o s . pts_to pi i ** pts_to po o ** pts_to ks s ** pts_to b #p bB ** pure (
    SZ.v i <= SZ.v k /\
    fill_inv bB s (SZ.v i) (SZ.v o) v m q
  )
  decreases (SZ.v k - SZ.v !pi)
  {
    let i = !pi;
    let o = !po;
    with s . assert (pts_to ks s);
    S.pts_to_len ks;
    assert (pure (SZ.v i < SZ.v k));
    fill_inv_step bB s (SZ.v i) o v m q;
    S.op_Dot_Lparen_Rparen_Less_Minus ks i o;
    let o1 = jump_raw_data_item () b o;
    jump_item_end bB o o1;
    let o2 = jump_raw_data_item () b o1;
    jump_item_end bB o1 o2;
    pi := SZ.add i 1sz;
    po := o2;
  };
  with s o . assert (pts_to ks s ** pts_to po o);
  fill_inv_end bB s (SZ.v o) v m q;
  !po
}

#pop-options
