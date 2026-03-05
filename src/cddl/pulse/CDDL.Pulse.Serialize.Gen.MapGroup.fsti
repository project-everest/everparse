module CDDL.Pulse.Serialize.Gen.MapGroup
include CDDL.Pulse.Serialize.Gen.MapGroup.Base
include CDDL.Pulse.Serialize.Gen.MapGroup.Map
include CDDL.Pulse.Serialize.Gen.MapGroup.Ext
include CDDL.Pulse.Serialize.Gen.MapGroup.Choice
include CDDL.Pulse.Serialize.Gen.MapGroup.Concat
include CDDL.Pulse.Serialize.Gen.MapGroup.MatchItemFor

open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_zero_or_more
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop) (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (map_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (map_entry_share: share_t vmatch2)
  (map_entry_gather: gather_t vmatch2)
  (#ty' #ty2': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#[@@@erasable]except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_either_left (rel_slice_of_table key_eq r1 r2) (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2)))
