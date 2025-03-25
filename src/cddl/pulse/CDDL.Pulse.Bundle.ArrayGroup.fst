module CDDL.Pulse.Bundle.ArrayGroup
include CDDL.Pulse.Bundle.Base
include CDDL.Pulse.Parse.ArrayGroup
include CDDL.Pulse.Serialize.ArrayGroup
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module EqTest = CDDL.Spec.EqTest

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
noeq
type array_bundle
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
= {
  [@@@erasable] ab_typ: Ghost.erased (array_group None);
  [@@@erasable] ab_spec_type: Type0;
  [@@@erasable] ab_spec_type_eq: Ghost.erased (EqTest.eq_test ab_spec_type);
  [@@@erasable] ab_spec: Ghost.erased (ag_spec ab_typ ab_spec_type true);
  ab_impl_type: Type0;
  [@@@erasable] ab_rel: rel ab_impl_type ab_spec_type;
  ab_parser: impl_zero_copy_array_group cbor_array_iterator_match ab_spec.ag_parser ab_rel;
  ab_serializer: impl_serialize_array_group ab_spec ab_rel;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let get_array_bundle_impl_type
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (b: array_bundle cbor_array_iterator_match)
: Pure Type0
  (requires True)
  (ensures fun t -> t == b.ab_impl_type) // guard if the number of fields changes
= match b with
  | Mkarray_bundle _ _ _ _ ab_impl_type _ _ _ -> ab_impl_type

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let array_bundle_set_parser_and_serializer
  (#cbor_array_iterator_t: Type0)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  ([@@@erasable] b: Ghost.erased (array_bundle cbor_array_iterator_match))
  (t: Type0)
  ([@@@erasable] t_eq: squash (t == b.ab_impl_type))
  (#[@@@erasable] t': Type)
  (p: t')
  ([@@@erasable] p_eq: squash (t' == impl_zero_copy_array_group cbor_array_iterator_match b.ab_spec.ag_parser b.ab_rel))
  (#[@@@erasable] ts: Type)
  (s: ts)
  ([@@@erasable] s_eq: squash (ts == impl_serialize_array_group b.ab_spec b.ab_rel))
: Tot (array_bundle cbor_array_iterator_match)
= {
    ab_typ = b.ab_typ;
    ab_spec_type = b.ab_spec_type;
    ab_spec_type_eq = b.ab_spec_type_eq;
    ab_spec = b.ab_spec;
    ab_impl_type = t;
    ab_rel = coerce_eq () b.ab_rel;
    ab_parser = p;
    ab_serializer = s;
  }

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr ]
let bundle_array
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_array_iterator_start: array_iterator_start_t vmatch cbor_array_iterator_match)
  (cbor_serialize_array: cbor_det_serialize_array_t)
  (ab: array_bundle cbor_array_iterator_match)
: Tot (bundle vmatch)
= match ab with
  | Mkarray_bundle ab_typ ab_spec_type ab_spec_type_eq ab_spec ab_impl_type ab_rel ab_parser ab_serializer ->
{
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = ab_spec_type_eq;
  b_spec = spec_array_group ab_spec;
  b_impl_type = ab_impl_type;
  b_rel = _;
  b_parser = impl_zero_copy_array cbor_array_iterator_start ab_parser;
  b_serializer = impl_serialize_array cbor_serialize_array ab_serializer;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_ext
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (ab: array_bundle cbor_array_iterator_match)
  (#[@@@erasable] g2: Ghost.erased (array_group None))
  ([@@@erasable] sp2: Ghost.erased (ag_spec g2 ab.ab_spec_type true))
  ([@@@erasable] sq: squash (
    array_group_equiv g2 ab.ab_typ /\
    (forall (x: list cbor) . array_group_parser_spec_refinement g2 x ==> (
       (sp2.ag_parser x <: ab.ab_spec_type) == (ab.ab_spec.ag_parser x <: ab.ab_spec_type)
    ))
  ))
= match ab with
  | Mkarray_bundle ab_typ ab_spec_type ab_spec_type_eq ab_spec ab_impl_type ab_rel ab_parser ab_serializer ->
{
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = ab_spec_type_eq;
  ab_spec = sp2;
  ab_impl_type = ab_impl_type;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_ext ab_parser #_ #sp2.ag_size #sp2.ag_serializable sp2.ag_parser ();
  ab_serializer = impl_serialize_array_group_ext ab_serializer _ ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_ext'
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (ab: array_bundle cbor_array_iterator_match)
  ([@@@erasable] g2: Ghost.erased (array_group None))
  ([@@@erasable] sq: squash (
    array_group_equiv g2 ab.ab_typ
  ))
= bundle_array_group_ext
    ab
    (ag_spec_ext ab.ab_spec g2)
    ()

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_item
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_array_iterator_next: array_iterator_next_t vmatch cbor_array_iterator_match)
  (b: bundle vmatch)
: Tot (array_bundle cbor_array_iterator_match)
= match b with
  | Mkbundle b_typ b_spec_type b_spec_type_eq b_spec b_impl_type b_rel b_parser b_serializer ->
{
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = b_spec_type_eq;
  ab_spec = ag_spec_item b_spec;
  ab_impl_type = b_impl_type;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_item cbor_array_iterator_next b_parser;
  ab_serializer = impl_serialize_array_group_item b_serializer
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_concat
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
  (b1: array_bundle cbor_array_iterator_match)
  (v1: impl_array_group cbor_array_iterator_match b1.ab_typ)
  (b2: array_bundle cbor_array_iterator_match)
  ([@@@erasable] sq: squash (
    array_group_concat_unique_weak b1.ab_typ b2.ab_typ
  ))
: Tot (array_bundle cbor_array_iterator_match)
= match b1 with
  | Mkarray_bundle ab_typ1 ab_spec_type1 ab_spec_type_eq1 ab_spec1 ab_impl_type1 ab_rel1 ab_parser1 ab_serializer1 ->
  match b2 with
  | Mkarray_bundle ab_typ2 ab_spec_type2 ab_spec_type_eq2 ab_spec2 ab_impl_type2 ab_rel2 ab_parser2 ab_serializer2 ->
{
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.pair_eq ab_spec_type_eq1 ab_spec_type_eq2;
  ab_spec = ag_spec_concat ab_spec1 ab_spec2;
  ab_impl_type = (ab_impl_type1 & ab_impl_type2);
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_concat length share gather truncate ab_parser1 v1 ab_parser2 ();
  ab_serializer = impl_serialize_array_group_concat ab_serializer1 ab_serializer2 ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_choice
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (b1: array_bundle cbor_array_iterator_match)
  (v1: impl_array_group cbor_array_iterator_match b1.ab_typ)
  (b2: array_bundle cbor_array_iterator_match)
  ([@@@erasable] sq: squash (
    array_group_disjoint b1.ab_typ (close_array_group b2.ab_typ)
  ))
: Tot (array_bundle cbor_array_iterator_match)
= match b1 with
  | Mkarray_bundle ab_typ1 ab_spec_type1 ab_spec_type_eq1 ab_spec1 ab_impl_type1 ab_rel1 ab_parser1 ab_serializer1 ->
  match b2 with
  | Mkarray_bundle ab_typ2 ab_spec_type2 ab_spec_type_eq2 ab_spec2 ab_impl_type2 ab_rel2 ab_parser2 ab_serializer2 ->
{
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.either_eq ab_spec_type_eq1 ab_spec_type_eq2;
  ab_spec = ag_spec_choice' ab_spec1 ab_spec2;
  ab_impl_type = either ab_impl_type1 ab_impl_type2;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_choice ab_parser1 v1 ab_parser2;
  ab_serializer = impl_serialize_array_group_choice' ab_serializer1 ab_serializer2 ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_zero_or_one
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (b1: array_bundle cbor_array_iterator_match)
  (v1: impl_array_group cbor_array_iterator_match b1.ab_typ)
  ([@@@erasable] sq: squash (
    array_group_is_nonempty b1.ab_typ
  ))
: Tot (array_bundle cbor_array_iterator_match)
= match b1 with
  | Mkarray_bundle ab_typ ab_spec_type ab_spec_type_eq ab_spec ab_impl_type ab_rel ab_parser ab_serializer ->
{  
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.option_eq ab_spec_type_eq;
  ab_spec = ag_spec_zero_or_one ab_spec;
  ab_impl_type = option ab_impl_type;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_zero_or_one ab_parser v1;
  ab_serializer = impl_serialize_array_group_zero_or_one ab_serializer ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_zero_or_more
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
  (b1: array_bundle cbor_array_iterator_match)
  (v1: impl_array_group cbor_array_iterator_match b1.ab_typ)
  ([@@@erasable] sq: squash (
    array_group_concat_unique_strong b1.ab_typ b1.ab_typ /\
    array_group_is_nonempty b1.ab_typ
  ))
: array_bundle cbor_array_iterator_match
= match b1 with
  | Mkarray_bundle ab_typ ab_spec_type ab_spec_type_eq ab_spec ab_impl_type ab_rel ab_parser ab_serializer ->
{  
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.list_eq ab_spec_type_eq;
  ab_spec = ag_spec_zero_or_more ab_spec;
  ab_impl_type = _;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_zero_or_more share gather #_ #_ #_ #_ #ab_spec.ag_parser v1 ab_parser ();
  ab_serializer = impl_serialize_array_group_zero_or_more is_empty length share gather truncate ab_serializer ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_one_or_more
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (is_empty: array_iterator_is_empty_t cbor_array_iterator_match)
  (length: array_iterator_length_t cbor_array_iterator_match)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (truncate: array_iterator_truncate_t cbor_array_iterator_match)
  (b1: array_bundle cbor_array_iterator_match)
  (v1: impl_array_group cbor_array_iterator_match b1.ab_typ)
  ([@@@erasable] sq: squash (
    array_group_concat_unique_strong b1.ab_typ b1.ab_typ /\
    array_group_is_nonempty b1.ab_typ
  ))
: array_bundle cbor_array_iterator_match
= match b1 with
  | Mkarray_bundle ab_typ ab_spec_type ab_spec_type_eq ab_spec ab_impl_type ab_rel ab_parser ab_serializer ->
{  
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.list_eq ab_spec_type_eq;
  ab_spec = ag_spec_one_or_more ab_spec;
  ab_impl_type = _;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_one_or_more share gather #_ #_ #_ #_ #ab_spec.ag_parser v1 ab_parser ();
  ab_serializer = impl_serialize_array_group_one_or_more is_empty length share gather truncate ab_serializer ();
}
