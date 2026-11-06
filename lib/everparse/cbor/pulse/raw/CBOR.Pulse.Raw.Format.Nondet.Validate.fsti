module CBOR.Pulse.Raw.Format.Nondet.Validate
open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.Nondet
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Trade = Pulse.Lib.Trade.Util

unfold
let cbor_validate_nondet_post
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
=
  let r = parse_cbor v in
  if SZ.v res = 0
  then ((Some? r /\ valid_raw_data_item (fst (Some?.v r))) ==> (Some? map_key_bound /\ map_key_depth (fst (Some?.v r)) > SZ.v (Some?.v map_key_bound)))
  else (
    Some? r /\
    valid_raw_data_item (fst (Some?.v r)) /\
    SZ.v res == snd (Some?.v r) /\
    ((Some? map_key_bound /\ strict_check) ==> map_key_depth (fst (Some?.v r)) <= SZ.v (Some?.v map_key_bound))
  )

val cbor_validate_nondet
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_validate_nondet_post map_key_bound strict_check v res
    ))

unfold
let cbor_validate_nondet_map_length_bounded_post
  (map_length_bound: SZ.t)
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
=
  let r = parse_cbor v in
  if SZ.v res = 0
  then ((Some? r /\ valid_raw_data_item (fst (Some?.v r)) /\ CBOR.Spec.Raw.Base.map_length_bounded (SZ.v map_length_bound) (fst (Some?.v r))) ==> (Some? map_key_bound /\ map_key_depth (fst (Some?.v r)) > SZ.v (Some?.v map_key_bound)))
  else (
    Some? r /\
    valid_raw_data_item (fst (Some?.v r)) /\
    CBOR.Spec.Raw.Base.map_length_bounded (SZ.v map_length_bound) (fst (Some?.v r)) /\
    SZ.v res == snd (Some?.v r) /\
    ((Some? map_key_bound /\ strict_check) ==> map_key_depth (fst (Some?.v r)) <= SZ.v (Some?.v map_key_bound))
  )

val cbor_validate_nondet_map_length_bounded
  (map_length_bound: SZ.t)
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_validate_nondet_map_length_bounded_post map_length_bound map_key_bound strict_check v res
    ))

unfold
let cbor_validate_nondet_bounded_post
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
=
  let r = parse_cbor v in
  if SZ.v res = 0
  then ~ (Some? r /\ valid_raw_data_item (fst (Some?.v r)) /\ CBOR.Spec.Raw.Base.raw_data_item_bounded (SZ.v map_depth_bound) (SZ.v map_length_bound) (fst (Some?.v r)))
  else (
    Some? r /\
    valid_raw_data_item (fst (Some?.v r)) /\
    CBOR.Spec.Raw.Base.raw_data_item_bounded (SZ.v map_depth_bound) (SZ.v map_length_bound) (fst (Some?.v r)) /\
    SZ.v res == snd (Some?.v r)
  )

val cbor_validate_nondet_bounded
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_validate_nondet_bounded_post map_depth_bound map_length_bound v res
    ))

(* Sort-based variant of `cbor_validate_nondet_bounded`, checking map
   key duplicates with caller-provided scratch space and without
   allocating. The scratch slice must hold at least
   `3 * map_length_bound * map_depth_bound` elements; otherwise, the
   validator returns 0. *)

let cbor_validate_nondet_bounded_sort_scratch_ok
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (scratch_len: SZ.t)
: Tot bool
= 3 * SZ.v map_length_bound * SZ.v map_depth_bound <= SZ.v scratch_len

unfold
let cbor_validate_nondet_bounded_sort_post
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (scratch_len: SZ.t)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
= if cbor_validate_nondet_bounded_sort_scratch_ok map_depth_bound map_length_bound scratch_len
  then cbor_validate_nondet_bounded_post map_depth_bound map_length_bound v res
  else SZ.v res == 0

val cbor_validate_nondet_bounded_sort_scratch_ok_impl
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (scratch_len: SZ.t)
: Tot (res: bool { res == cbor_validate_nondet_bounded_sort_scratch_ok map_depth_bound map_length_bound scratch_len })

val cbor_validate_nondet_bounded_sort
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (input: slice U8.t)
  (scratch: slice SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#s: Ghost.erased (Seq.seq SZ.t))
: stt SZ.t
    (pts_to input #pm v ** pts_to scratch s)
    (fun res -> pts_to input #pm v ** (exists* s' . pts_to scratch s' ** pure (
      cbor_validate_nondet_bounded_sort_post map_depth_bound map_length_bound (len scratch) v res
    )))

(* Hash-based variant of `cbor_validate_nondet_bounded_sort`: map keys
   are sorted by their keyed SipHash-1-3 hash (under the key (k0, k1))
   first, and compared with the canonical order only when their hashes
   are equal. The scratch slice must hold at least
   `3 * map_length_bound * map_depth_bound + map_length_bound`
   elements, and the hash scratch slice at least `map_length_bound`
   elements; otherwise, the validator returns 0. *)

let cbor_validate_nondet_bounded_hash_scratch_ok
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (scratch_len: SZ.t)
  (hash_scratch_len: SZ.t)
: Tot bool
= 3 * SZ.v map_length_bound * SZ.v map_depth_bound + SZ.v map_length_bound <= SZ.v scratch_len &&
  SZ.v map_length_bound <= SZ.v hash_scratch_len

unfold
let cbor_validate_nondet_bounded_hash_post
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (scratch_len: SZ.t)
  (hash_scratch_len: SZ.t)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
= if cbor_validate_nondet_bounded_hash_scratch_ok map_depth_bound map_length_bound scratch_len hash_scratch_len
  then cbor_validate_nondet_bounded_post map_depth_bound map_length_bound v res
  else SZ.v res == 0

val cbor_validate_nondet_bounded_hash_scratch_ok_impl
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (scratch_len: SZ.t)
  (hash_scratch_len: SZ.t)
: Tot (res: bool { res == cbor_validate_nondet_bounded_hash_scratch_ok map_depth_bound map_length_bound scratch_len hash_scratch_len })

val cbor_validate_nondet_bounded_hash
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (k0 k1: U64.t)
  (input: slice U8.t)
  (scratch: slice SZ.t)
  (hash_scratch: slice U64.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#s: Ghost.erased (Seq.seq SZ.t))
  (#hs: Ghost.erased (Seq.seq U64.t))
: stt SZ.t
    (pts_to input #pm v ** pts_to scratch s ** pts_to hash_scratch hs)
    (fun res -> pts_to input #pm v ** (exists* s' hs' . pts_to scratch s' ** pts_to hash_scratch hs' ** pure (
      cbor_validate_nondet_bounded_hash_post map_depth_bound map_length_bound (len scratch) (len hash_scratch) v res
    )))
