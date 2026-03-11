module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux1
#lang-pulse
include CDDL.Pulse.Serialize.Gen.MapGroup.Base
include Pulse.Lib.Pervasives
include CBOR.Spec.API.Type
include CBOR.Pulse.API.Base
include CDDL.Pulse.Serialize.Gen.MapGroup.Aux
include CDDL.Pulse.Serialize.Gen.MapGroup.Choice

module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

module SM = Pulse.Lib.SeqMatch

let impl_serialize_map_zero_or_more_iterator_inv_gen
    (p: bare_cbor_map_parser) (minl: cbor -> nat) (maxl: cbor -> option nat)
    (#key: typ) (#tkey: Type0)
    (sp1: spec key tkey true)
    (#value: typ) (#tvalue: Type0) (#inj: bool)
    (sp2: spec value tvalue inj)
    (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
  (v0: Map.t tkey (list tvalue))
  (l: cbor_map)
  (res: bool)
  (w: Seq.seq U8.t)
  (m1 m2 m2': Map.t tkey (list tvalue))
  (count: U64.t)
  (size: SZ.t)
: Tot prop
=
  let sp = (mg_zero_or_more_match_item sp1 sp2 except) in
      map_of_list_is_append m1 m2' v0 /\
      map_of_list_maps_to_nonempty m1 /\
      sp.mg_serializable m1 /\
      cbor_map_disjoint l (sp.mg_serializer m1) /\
      (res == true ==> (
        m2' == m2 /\
        impl_serialize_map_group_pre p count size (cbor_map_union l (sp.mg_serializer m1)) w
      )) /\
      impl_serialize_map_group_valid maxl l sp v0 (Seq.length w) == (if res then impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' (Seq.length w) else false)

val map_of_list_serializable_disjoint
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2) ==>
    (Map.disjoint m1 m2 <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2))
  ))

val map_of_list_is_append_serializable_intro_serializable
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2 /\ Map.disjoint m1 m2) ==>
      sp.mg_serializable m
  ))

val map_of_list_is_append_serializable_intro
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2 /\ (Map.disjoint m1 m2 \/ cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2))) ==>
    (Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2) /\
      sp.mg_serializable m /\
      sp.mg_serializer m == (sp.mg_serializer m1 `cbor_map_union` sp.mg_serializer m2)
    )
  ))

val map_of_list_is_append_snoc
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
: Lemma
  (map_of_list_is_append
    m1
    (Map.singleton k (key_eq k) [v])
    (map_of_list_snoc key_eq m1 k v)
  )

val map_of_list_is_append_cons
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (m1: Map.t key (list value))
: Lemma
  (map_of_list_is_append
    (Map.singleton k (key_eq k) [v])
    m1
    (map_of_list_cons key_eq k v m1)
  )

val map_of_list_is_append_serializable_elim
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m /\
    map_of_list_maps_to_nonempty m1 /\
    map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m
    ) ==> (sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
    )
  ))

val map_of_list_is_append_serializable_elim'
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
  (sq: squash (map_of_list_is_append m1 m2 m))
  (sq1: squash (map_of_list_maps_to_nonempty m1))
  (sq2: squash (map_of_list_maps_to_nonempty m2))
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m
    ) ==> (sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
    )
  ))

val map_of_list_is_append_serializable_singleton
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (k: key)
  (k_eq: EqTest.eq_test_for k)
  (v: value)
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m = EqTest.map_singleton k k_eq [v] in
    (sp.mg_serializable m <==> (
      sp1.serializable k /\
      sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v)))
    )) /\
    (sp.mg_serializable m ==> (
    sp.mg_serializer m == cbor_map_singleton (sp1.serializer k) (sp2.serializer v)
  ))))

val map_of_list_maps_to_nonempty_singleton
  (#key: Type)
  (#value: Type)
  (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: list value)
  (sq: squash (Cons? v))
: Lemma
  (map_of_list_maps_to_nonempty (Map.singleton k k_eq v))

val map_of_list_maps_to_nonempty_cons
  (#key: Type)
  (#value: Type)
  (k_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (m: Map.t key (list value))
  (sq: squash (map_of_list_maps_to_nonempty m))
: Lemma
  (map_of_list_maps_to_nonempty (map_of_list_cons k_eq k v m))

val impl_serialize_map_group_valid_map_zero_or_more_snoc_length
  (ll lm1 lkv lm2: nat)
: Lemma
  ((ll + lm1) + (lkv + lm2) == (ll + (lm1 + lkv)) + lm2)

val map_of_list_sub
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m: Map.t key (list value))
  (k: key)
  (v: value)
  (lv': list value)
: Pure (Map.t key (list value))
  (requires (
    Map.get m k == Some (v :: lv')
  ))
  (ensures fun m' ->
    (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m') /\
    m == map_of_list_cons key_eq k v m'
  )

val seq_slice_append_pat (#t: Type) (s1 s2: Seq.seq t)
: Lemma
  (ensures Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
  [SMTPat (Seq.append s1 s2)]

let slice_split_post
  (#t: Type)
  (i: SZ.t)
  (v v1 v2: Seq.seq t)
: Tot prop
= SZ.v i <= Seq.length v /\
  v1 == Seq.slice v 0 (SZ.v i) /\
  v2 == Seq.slice v (SZ.v i) (Seq.length v) /\
  Seq.length v1 == SZ.v i /\
  Seq.length v2 == Seq.length v - SZ.v i /\
  v == Seq.append v1 v2

inline_for_extraction noextract [@@noextract_to "krml"]
fn slice_split (#t: Type) (s: S.slice t) (#p: perm) (i: SZ.t) (#v: Ghost.erased (Seq.seq t))
    requires pts_to s #p v ** pure (
      SZ.v i <= Seq.length v
    )
    returns res: (S.slice t & S.slice t)
    ensures (let (s1, s2) = res in exists* v1 v2 .
      pts_to s1 #p v1 **
      pts_to s2 #p v2 **
      S.is_split s s1 s2 **
      pure (slice_split_post i v v1 v2)
    )

(* Gen iterator type alias *)

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more_iterator_gen_t
    (p: bare_cbor_map_parser) (minl: cbor -> nat) (maxl: cbor -> option nat)
    (#key: Ghost.erased typ) (#tkey: Type0)
    (sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0) (r1: rel ikey tkey)
    (#value: Ghost.erased typ) (#tvalue: Type0) (#inj: Ghost.erased bool)
    (sp2: Ghost.erased (spec value tvalue inj))
    (except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (#ivalue: Type0) (r2: rel ivalue tvalue)
    (iterator: (Ghost.erased (Iterator.type_spec ikey) -> Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
= impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_
    (mg_zero_or_more_match_item sp1 sp2 except) #_ (r (Iterator.mk_spec r1) (Iterator.mk_spec r2))

val map_of_list_maps_to_nonempty_snoc
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m: Map.t key (list value))
  (k: key)
  (v: value)
: Lemma
  (requires map_of_list_maps_to_nonempty m)
  (ensures map_of_list_maps_to_nonempty (map_of_list_snoc key_eq m k v))

val cbor_parse_prefix_apply
  (pe: cbor_parser)
  (x: Seq.seq U8.t)
  (n: nat)
: Lemma
  (requires (
    n <= Seq.length x /\
    Some? (pe (Seq.slice x 0 n))
  ))
  (ensures (
    pe x == pe (Seq.slice x 0 n)
  ))
