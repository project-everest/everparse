(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module CBOR.Spec.Type
include CBOR.Spec.Constants

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module FS = FStar.FiniteSet.Base
module FSA = FStar.FiniteSet.Ambient
module R = CBOR.Spec.Raw.Valid
module U = CBOR.Spec.Util

(* The generic data model *)

val cbor: eqtype

val cbor_map: eqtype

val cbor_map_get: cbor_map -> cbor -> Tot (option cbor)

let cbor_map_equal (m1 m2: cbor_map) : Tot prop =
  (forall k . cbor_map_get m1 k == cbor_map_get m2 k)

val cbor_map_ext: (m1: cbor_map) -> (m2: cbor_map) -> Lemma
  (ensures (cbor_map_equal m1 m2 <==> m1 == m2))
  [SMTPat (cbor_map_equal m1 m2)]

val cbor_map_set_keys: (m: cbor_map) -> FS.set cbor

val cbor_map_set_keys_mem: (m: cbor_map) -> (k: cbor) -> Lemma
  (FS.mem k (cbor_map_set_keys m) <==> Some? (cbor_map_get m k))
  [SMTPat (FS.mem k (cbor_map_set_keys m))]

val cbor_map_length (m: cbor_map) : Pure nat
  (requires True)
  (ensures (fun n -> n == FS.cardinality (cbor_map_set_keys m)))

val cbor_map_empty: cbor_map

val cbor_map_get_empty: (k: cbor) -> Lemma
  (ensures (cbor_map_get cbor_map_empty k == None))
  [SMTPat (cbor_map_get cbor_map_empty k)]

let cbor_map_set_keys_empty : squash (cbor_map_set_keys cbor_map_empty == FS.emptyset) =
  assert (cbor_map_set_keys cbor_map_empty `FS.equal` FS.emptyset)

let cbor_map_length_empty: squash (cbor_map_length cbor_map_empty == 0) = ()

val cbor_map_singleton: cbor -> cbor -> cbor_map

val cbor_map_get_singleton: (k: cbor) -> (v: cbor) -> (k': cbor) -> Lemma
  (ensures (cbor_map_get (cbor_map_singleton k v) k' == (if k = k' then Some v else None)))
  [SMTPat (cbor_map_get (cbor_map_singleton k v) k')]

let cbor_map_set_keys_singleton (k: cbor) (v: cbor) : Lemma
  (ensures (cbor_map_set_keys (cbor_map_singleton k v) == FS.singleton k))
  [SMTPat (cbor_map_set_keys (cbor_map_singleton k v))]
= assert (cbor_map_set_keys (cbor_map_singleton k v) `FS.equal` FS.singleton k)

let cbor_map_length_singleton (k: cbor) (v: cbor) : Lemma
  (ensures (cbor_map_length (cbor_map_singleton k v) == 1))
= ()

val cbor_map_filter:
  (cbor -> cbor -> bool) ->
  cbor_map ->
  cbor_map

val cbor_map_get_filter: (f: (cbor -> cbor -> bool)) -> (m: cbor_map) -> (k: cbor) -> Lemma
  (ensures (cbor_map_get (cbor_map_filter f m) k == begin match cbor_map_get m k with
  | None -> None
  | Some v -> if f k v then Some v else None
  end))
  [SMTPat (cbor_map_get (cbor_map_filter f m) k)]

val cbor_map_union: cbor_map -> cbor_map -> cbor_map

val cbor_map_get_union: (m1: cbor_map) -> (m2: cbor_map) -> (k: cbor) -> Lemma
  (ensures (cbor_map_get (cbor_map_union m1 m2) k == begin match cbor_map_get m1 k with
    | None -> cbor_map_get m2 k
    | v -> v
    end
  ))
  [SMTPat (cbor_map_get (cbor_map_union m1 m2) k)]

let cbor_map_set_keys_union (m1 m2: cbor_map) : Lemma
  (ensures (cbor_map_set_keys (cbor_map_union m1 m2) == (cbor_map_set_keys m1 `FS.union` cbor_map_set_keys m2)))
  [SMTPat (cbor_map_set_keys (cbor_map_union m1 m2))]
= assert (cbor_map_set_keys (cbor_map_union m1 m2) `FS.equal` (cbor_map_set_keys m1 `FS.union` cbor_map_set_keys m2))

let cbor_map_disjoint (m1 m2: cbor_map) : Tot prop =
  forall k . ~ (Some? (cbor_map_get m1 k) /\ Some? (cbor_map_get m2 k))

let cbor_map_length_disjoint_union (m1 m2: cbor_map) : Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures (
    cbor_map_length (cbor_map_union m1 m2) == cbor_map_length m1 + cbor_map_length m2
  ))
= 
  assert (FS.intersection (cbor_map_set_keys m1) (cbor_map_set_keys m2) `FS.equal` FS.emptyset);
  assert (FS.cardinality (FS.union (cbor_map_set_keys m1) (cbor_map_set_keys m2)) == FS.cardinality (cbor_map_set_keys m1) + FS.cardinality (cbor_map_set_keys m2))

type cbor_case =
  | CSimple: (v: simple_value) -> cbor_case
  | CInt64: (typ: major_type_uint64_or_neg_int64) -> (v: U64.t) -> cbor_case
  | CString: (typ: major_type_byte_string_or_text_string) -> (v: Seq.seq U8.t { FStar.UInt.fits (Seq.length v) U64.n }) -> cbor_case // Section 3.1: "a string containing an invalid UTF-8 sequence is well-formed but invalid", so we don't care about UTF-8 specifics here.
  | CArray: (v: list cbor { FStar.UInt.fits (List.Tot.length v) U64.n }) -> cbor_case
  | CMap: (c: cbor_map { FStar.UInt.fits (cbor_map_length c) U64.n }) -> cbor_case
  | CTagged: (tag: U64.t) -> (v: cbor) -> cbor_case

val unpack: cbor -> cbor_case

val pack: cbor_case -> cbor

val unpack_pack: (c: cbor_case) -> Lemma
  (ensures (unpack (pack c) == c))
  [SMTPat (pack c)]

val pack_unpack: (c: cbor) -> Lemma
  (ensures (pack (unpack c) == c))
  [SMTPat (unpack c)]

val mk_cbor (r: R.raw_data_item) : Tot cbor

val mk_cbor_equiv (r1 r2: R.raw_data_item) : Lemma
  (requires (
    R.valid_raw_data_item r1 == true /\
    R.valid_raw_data_item r2 == true
  ))
  (ensures (
    R.raw_equiv r1 r2 <==> mk_cbor r1 == mk_cbor r2
  ))

let mk_cbor_match_map_elem
  (r: list (R.raw_data_item & R.raw_data_item))
  (m: cbor_map)
  (x: R.raw_data_item)
: Tot prop
= R.valid_raw_data_item x ==>
  begin match U.list_setoid_assoc R.raw_equiv x r, cbor_map_get m (mk_cbor x) with
  | None, None -> True
  | Some v1, Some v2 -> R.valid_raw_data_item v1 /\ mk_cbor v1 == v2
  | _ -> False
  end

let mk_cbor_match_map
  (r: list (R.raw_data_item & R.raw_data_item))
  (m: cbor_map)
: Tot prop
= forall (x: R.raw_data_item) . mk_cbor_match_map_elem r m x

val mk_cbor_eq
  (r: R.raw_data_item)
: Lemma
  (requires (R.valid_raw_data_item r == true))
  (ensures (match r, unpack (mk_cbor r) with
  | R.Simple v1, CSimple v2 -> v1 == v2
  | R.Int64 ty1 v1, CInt64 ty2 v2 -> ty1 == ty2 /\ v1.value == v2
  | R.String ty1 _ v1, CString ty2 v2 -> ty1 == ty2 /\ v1 == v2
  | R.Tagged tag1 v1, CTagged tag2 v2 -> tag1.value == tag2 /\ mk_cbor v1 == v2
  | R.Map _ v1, CMap v2 -> mk_cbor_match_map v1 v2
  | R.Array _ v1, CArray v2 -> List.Tot.map mk_cbor v1 == v2
  | _ -> False
  ))
