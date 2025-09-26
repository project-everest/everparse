module CDDL.Pulse.Bundle.MapGroup
include CDDL.Pulse.Bundle.Base
include CDDL.Pulse.Parse.MapGroup
include CDDL.Pulse.Serialize.MapGroup
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module EqTest = CDDL.Spec.EqTest

inline_for_extraction noextract [@@noextract_to "krml"]
noeq
type map_bundle
  (#ty: Type0)
  (vmatch: perm -> ty -> cbor -> slprop)
= {
  [@@@erasable] mb_typ: Ghost.erased (det_map_group);
  [@@@erasable] mb_footprint: Ghost.erased map_constraint;
  [@@@erasable] mb_footprint_correct: squash (map_group_footprint mb_typ mb_footprint);
  mb_spec_type: Type0;
  [@@@erasable] mb_spec_type_eq: Ghost.erased (EqTest.eq_test mb_spec_type);
  [@@@erasable] mb_spec: Ghost.erased (mg_spec mb_typ mb_footprint mb_spec_type true);
  mb_impl_type: Type0;
  mb_rel: rel mb_impl_type mb_spec_type;
  mb_parser: impl_zero_copy_map_group vmatch mb_spec.mg_parser mb_rel;
  mb_serializer: impl_serialize_map_group mb_spec mb_rel;
}

unfold
let impl_serialize_map_ext_precond
    (#t1: (det_map_group))
    (#fp1: map_constraint)
    (#tgt1: Type0)
    (#inj1: bool)
    (ps1: (mg_spec t1 fp1 tgt1 inj1))
    (#t2: det_map_group)
    (#fp2: map_constraint)
    (#inj2: bool)
    (ps2: (mg_spec t2 fp2 tgt1 inj2))
: Tot prop
=
      t2 == t1 /\
      (forall (x: tgt1) . (ps2).mg_serializable x <==> (ps1).mg_serializable x) /\
      (forall (x: tgt1) . (ps2).mg_serializable x ==> (
        (ps1).mg_serializable x /\
        (ps2).mg_serializer x `cbor_map_equal` (ps1).mg_serializer x
      )) /\
      (forall (x: tgt1) . (ps2).mg_size x == (ps1).mg_size x)

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr ]
let bundle_map
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_serialize_map: cbor_det_serialize_map_t)
  (mb: map_bundle vmatch)
: Tot (bundle vmatch)
= match mb with
  | Mkmap_bundle mb_typ mb_footprint mb_footprint_correct mb_spec_type mb_spec_type_eq mb_spec mb_impl_type mb_rel mb_parser mb_serializer ->
{
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = mb_spec_type_eq;
  b_spec = spec_map_group mb_spec;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_zero_copy_map mb_parser ();
  b_serializer = impl_serialize_map cbor_serialize_map mb_serializer ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_ext
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (mb1: map_bundle vmatch)
  (#[@@@erasable] t2: Ghost.erased det_map_group)
  (#[@@@erasable] fp2: Ghost.erased map_constraint)
  ([@@@erasable] sp2: Ghost.erased (mg_spec t2 fp2 mb1.mb_spec_type true))
  ([@@@erasable] sq: squash (
    impl_zero_copy_map_ext_precond (Ghost.reveal mb1.mb_typ) (mb1.mb_spec.mg_parser) (Ghost.reveal t2) sp2.mg_parser /\
    impl_serialize_map_ext_precond (Ghost.reveal mb1.mb_spec) (Ghost.reveal sp2)
  ))
: Tot (map_bundle vmatch)
= match mb1 with
  | Mkmap_bundle mb_typ mb_footprint mb_footprint_correct mb_spec_type mb_spec_type_eq mb_spec mb_impl_type mb_rel mb_parser mb_serializer ->
{
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type_eq = mb_spec_type_eq;
  mb_spec_type = _;
  mb_spec = sp2;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_map_ext #_ #_ #_ #_ #_ #_ #_ #mb_spec.mg_parser mb_parser #_ #_ #sp2.mg_size #sp2.mg_serializable sp2.mg_parser ();
  mb_serializer = impl_serialize_map_group_ext mb_serializer sp2 ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_ext'
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (mb1: map_bundle vmatch)
  ([@@@erasable] fp2: Ghost.erased map_constraint)
  ([@@@erasable] sq: squash (
    map_constraint_equiv mb1.mb_footprint fp2
  ))
: Tot (map_bundle vmatch)
= bundle_map_ext mb1 (mg_spec_ext mb1.mb_spec fp2 mb1.mb_spec.mg_size mb1.mb_spec.mg_serializable) ()

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_nop
  (#ty: Type0)
  (vmatch: perm -> ty -> cbor -> slprop)
: Tot (map_bundle vmatch)
= {
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = _;
  mb_spec_type_eq = EqTest.eqtype_eq unit;
  mb_spec = mg_spec_nop;
  mb_impl_type = _;
  mb_rel = rel_unit;
  mb_parser = impl_zero_copy_map_nop vmatch;
  mb_serializer = impl_serialize_map_group_nop ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_choice
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (mb1: map_bundle vmatch)
  (v1: impl_map_group_t vmatch mb1.mb_typ mb1.mb_footprint)
  (mb2: map_bundle vmatch)
  (sq: squash (
    map_group_choice_compatible mb1.mb_typ mb2.mb_typ
  ))
: Tot (map_bundle vmatch)
= match mb1 with
  | Mkmap_bundle mb_typ1 mb_footprint1 mb_footprint_correct1 mb_spec_type1 mb_spec_type_eq1 mb_spec1 mb_impl_type1 mb_rel1 mb_parser1 mb_serializer1 ->
  match mb2 with
  | Mkmap_bundle mb_typ2 mb_footprint2 mb_footprint_correct2 mb_spec_type2 mb_spec_type_eq2 mb_spec2 mb_impl_type2 mb_rel2 mb_parser2 mb_serializer2 ->
{
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = _;
  mb_spec_type_eq = EqTest.either_eq mb_spec_type_eq1 mb_spec_type_eq2;
  mb_spec = mg_spec_choice mb_spec1 mb_spec2;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_map_choice #_ #_ #_ #_ #_ #_ #_ #mb_spec1.mg_parser v1 mb_parser1 mb_parser2 ();
  mb_serializer = impl_serialize_map_group_choice mb_serializer1 mb_serializer2 ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_zero_or_one
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (mb1: map_bundle vmatch)
  (v1: impl_map_group_t vmatch mb1.mb_typ mb1.mb_footprint)
  (nm : option string)
  ([@@@erasable] sq: squash (
    MapGroupFail? (apply_map_group_det mb1.mb_typ cbor_map_empty)
  ))
: Tot (map_bundle vmatch)
= match mb1 with
  | Mkmap_bundle mb_typ mb_footprint mb_footprint_correct mb_spec_type mb_spec_type_eq mb_spec mb_impl_type mb_rel mb_parser mb_serializer ->
{
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type =  maybe_named nm (option mb_spec_type);
  mb_spec_type_eq = coerce_eq () (Ghost.hide (EqTest.option_eq mb_spec_type_eq));
  mb_spec = mg_spec_zero_or_one mb_spec;
  mb_impl_type = maybe_named nm (option mb_impl_type);
  mb_rel = _;
  mb_parser = impl_zero_copy_map_zero_or_one #_ #_ #_ #_ #_ #_ #_ #mb_spec.mg_parser v1 mb_parser ();
  mb_serializer = impl_serialize_map_group_zero_or_one mb_serializer ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_concat
  (#ty: Type0)
  (#[@@@erasable] vmatch: perm -> ty -> cbor -> slprop)
  ([@@@erasable] share: share_t vmatch)
  ([@@@erasable] gather: gather_t vmatch)
  (mb1: map_bundle vmatch)
  (mb2: map_bundle vmatch)
  ([@@@erasable] sq: squash (
    map_constraint_disjoint mb1.mb_footprint mb2.mb_footprint
  ))
: Tot (map_bundle vmatch)
= match mb1 with
  | Mkmap_bundle mb_typ1 mb_footprint1 mb_footprint_correct1 mb_spec_type1 mb_spec_type_eq1 mb_spec1 mb_impl_type1 mb_rel1 mb_parser1 mb_serializer1 ->
  match mb2 with
  | Mkmap_bundle mb_typ2 mb_footprint2 mb_footprint_correct2 mb_spec_type2 mb_spec_type_eq2 mb_spec2 mb_impl_type2 mb_rel2 mb_parser2 mb_serializer2 ->
{
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = _;
  mb_spec_type_eq = EqTest.pair_eq mb_spec_type_eq1 mb_spec_type_eq2;
  mb_spec = mg_spec_concat mb_spec1 mb_spec2;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_map_concat share gather mb_spec1.mg_serializer mb_parser1 mb_spec2.mg_serializer mb_parser2 ();
  mb_serializer = impl_serialize_map_group_concat mb_serializer1 mb_serializer2 ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_match_item_for
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (get: map_get_t vmatch)
  (insert: cbor_det_serialize_map_insert_t)
  (serialize: cbor_det_serialize_t vmatch)
  (#[@@@erasable] key: Ghost.erased cbor)
  (lkey: with_cbor_literal_t vmatch (Ghost.reveal key))
  ([@@@erasable] cut: Ghost.erased bool)
  (value: bundle vmatch)
  (nm : option string)
: Tot (map_bundle vmatch)
= match value with
  | Mkbundle b_typ b_spec_type b_spec_type_eq b_spec b_impl_type b_rel b_parser b_serializer ->
{
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = maybe_named nm b_spec_type;
  mb_spec_type_eq = b_spec_type_eq;
  mb_spec = mg_spec_match_item_for cut key b_spec;
  mb_impl_type = maybe_named nm b_impl_type;
  mb_rel = _;
  mb_parser = impl_zero_copy_match_item_for get lkey cut b_parser;
  mb_serializer = impl_serialize_match_item_for insert (CDDL.Pulse.Serialize.Misc.impl_serialize_literal serialize lkey) cut b_serializer;
}

module EqTest = CDDL.Spec.EqTest

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_zero_or_more
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_iterator_start: map_iterator_start_t vmatch cbor_map_iterator_match)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (map_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (map_entry_share: share_t vmatch2)
  (map_entry_gather: gather_t vmatch2)
  (parse: cbor_det_parse_t vmatch)
  (mk_map_entry: mk_map_entry_t  vmatch vmatch2)
  (insert: cbor_det_serialize_map_insert_t)
  (key: bundle vmatch) // MUST contain function pointers ONLY
  (va1: impl_typ vmatch key.b_typ) // MUST be a function pointer
  (value: bundle vmatch) // MUST contain function pointers ONLY
  (va2: impl_typ vmatch value.b_typ) // MUST be a function pointer
  (#[@@@erasable] except: Ghost.erased map_constraint)
  (va_ex: impl_map_entry_cond vmatch2 except) // MUST be a function pointer
: Tot (map_bundle vmatch)
= match key with
  | Mkbundle b_typ1 b_spec_type1 b_spec_type_eq1 b_spec1 b_impl_type1 b_rel1 b_parser1 b_serializer1 ->
  match value with
  | Mkbundle b_typ2 b_spec_type2 b_spec_type_eq2 b_spec2 b_impl_type2 b_rel2 b_parser2 b_serializer2 ->
{
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = _;
  mb_spec_type_eq = EqTest.map_eq _ (EqTest.list_eq b_spec_type_eq2);
  mb_spec = mg_zero_or_more_match_item b_spec1 b_spec2 except;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_map_zero_or_more map_iterator_start map_share map_gather b_spec_type_eq1 b_spec1 va1 b_parser1 b_spec2 va2 b_parser2  va_ex;
  mb_serializer = impl_serialize_map_zero_or_more map_share map_gather map_is_empty map_next map_entry_key map_entry_value map_entry_share map_entry_gather parse mk_map_entry insert #b_typ1 #b_spec_type1 b_spec_type_eq1 #b_spec1 #b_impl_type1 #b_rel1 b_serializer1 b_serializer2 va_ex;
}
