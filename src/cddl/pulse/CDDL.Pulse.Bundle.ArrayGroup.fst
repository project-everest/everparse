module CDDL.Pulse.Bundle.ArrayGroup
include CDDL.Pulse.Bundle.Base
include CDDL.Pulse.Parse.ArrayGroup
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module EqTest = CDDL.Spec.EqTest

inline_for_extraction noextract [@@noextract_to "krml"]
noeq
type array_bundle
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
= {
  ab_typ: Ghost.erased (array_group None);
  ab_spec_type: Type0;
  ab_spec_type_eq: Ghost.erased (EqTest.eq_test ab_spec_type);
  ab_spec: Ghost.erased (ag_spec ab_typ ab_spec_type true);
  ab_impl_type: Type0;
  ab_rel: rel ab_impl_type ab_spec_type;
  ab_parser: impl_zero_copy_array_group cbor_array_iterator_match ab_spec.ag_parser ab_rel;
}

inline_for_extraction [@@bundle_get_impl_type_attr]
let get_array_bundle_impl_type
  (#cbor_array_iterator_t: Type0)
  (cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (b: array_bundle cbor_array_iterator_match)
: Pure Type0
  (requires True)
  (ensures fun t -> t == b.ab_impl_type) // guard if the number of fields changes
= match b with
  | Mkarray_bundle _ _ _ _ ab_impl_type _ _ -> ab_impl_type

inline_for_extraction [@@bundle_get_impl_type_attr]
let array_bundle_set_parser
  (#cbor_array_iterator_t: Type0)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (b: array_bundle cbor_array_iterator_match)
  (p: impl_zero_copy_array_group cbor_array_iterator_match b.ab_spec.ag_parser b.ab_rel)
: Tot (array_bundle cbor_array_iterator_match)
= { b with
    ab_parser = p;
  }

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr ]
let bundle_array
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (cbor_array_iterator_start: array_iterator_start_t vmatch cbor_array_iterator_match)
  (ab: array_bundle cbor_array_iterator_match)
: Tot (bundle vmatch)
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = ab.ab_spec_type_eq;
  b_spec = spec_array_group ab.ab_spec;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_zero_copy_array cbor_array_iterator_start ab.ab_parser;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_ext
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (ab: array_bundle cbor_array_iterator_match)
  (#g2: Ghost.erased (array_group None))
  (sp2: Ghost.erased (ag_spec g2 ab.ab_spec_type true))
  (sq: squash (
    array_group_included g2 ab.ab_typ /\
    (forall (x: list cbor) . array_group_parser_spec_refinement g2 x ==> (
       (sp2.ag_parser x <: ab.ab_spec_type) == (ab.ab_spec.ag_parser x <: ab.ab_spec_type)
    ))
  ))
= {
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = ab.ab_spec_type_eq;
  ab_spec = sp2;
  ab_impl_type = _;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_ext ab.ab_parser sp2.ag_parser ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_ext'
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (ab: array_bundle cbor_array_iterator_match)
  (g2: Ghost.erased (array_group None))
  (sq: squash (
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
= {
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = b.b_spec_type_eq;
  ab_spec = ag_spec_item b.b_spec;
  ab_impl_type = _;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_item cbor_array_iterator_next b.b_parser;
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
  (sq: squash (
    array_group_concat_unique_weak b1.ab_typ b2.ab_typ
  ))
: Tot (array_bundle cbor_array_iterator_match)
= {
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.pair_eq b1.ab_spec_type_eq b2.ab_spec_type_eq;
  ab_spec = ag_spec_concat b1.ab_spec b2.ab_spec;
  ab_impl_type = _;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_concat length share gather truncate b1.ab_parser v1 b2.ab_parser ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_choice
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (b1: array_bundle cbor_array_iterator_match)
  (v1: impl_array_group cbor_array_iterator_match b1.ab_typ)
  (b2: array_bundle cbor_array_iterator_match)
  (sq: squash (
    array_group_disjoint b1.ab_typ (close_array_group b2.ab_typ)
  ))
: Tot (array_bundle cbor_array_iterator_match)
= {
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.either_eq b1.ab_spec_type_eq b2.ab_spec_type_eq;
  ab_spec = ag_spec_choice' b1.ab_spec b2.ab_spec;
  ab_impl_type = _;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_choice b1.ab_parser v1 b2.ab_parser;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_zero_or_one
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (b1: array_bundle cbor_array_iterator_match)
  (v1: impl_array_group cbor_array_iterator_match b1.ab_typ)
  (sq: squash (
    array_group_is_nonempty b1.ab_typ
  ))
: Tot (array_bundle cbor_array_iterator_match)
= {
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.option_eq b1.ab_spec_type_eq;
  ab_spec = ag_spec_zero_or_one b1.ab_spec;
  ab_impl_type = _;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_zero_or_one b1.ab_parser v1;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_zero_or_more
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (b1: array_bundle cbor_array_iterator_match)
  (v1: impl_array_group cbor_array_iterator_match b1.ab_typ)
  (sq: squash (
    array_group_concat_unique_strong b1.ab_typ b1.ab_typ /\
    array_group_is_nonempty b1.ab_typ
  ))
: array_bundle cbor_array_iterator_match
= {
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.list_eq b1.ab_spec_type_eq;
  ab_spec = ag_spec_zero_or_more b1.ab_spec;
  ab_impl_type = _;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_zero_or_more share gather v1 b1.ab_parser ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_array_group_one_or_more
  (#cbor_array_iterator_t: Type)
  (#cbor_array_iterator_match: perm -> cbor_array_iterator_t -> list cbor -> slprop)
  (share: share_t cbor_array_iterator_match)
  (gather: gather_t cbor_array_iterator_match)
  (b1: array_bundle cbor_array_iterator_match)
  (v1: impl_array_group cbor_array_iterator_match b1.ab_typ)
  (sq: squash (
    array_group_concat_unique_strong b1.ab_typ b1.ab_typ /\
    array_group_is_nonempty b1.ab_typ
  ))
: array_bundle cbor_array_iterator_match
= {
  ab_typ = _;
  ab_spec_type = _;
  ab_spec_type_eq = EqTest.list_eq b1.ab_spec_type_eq;
  ab_spec = ag_spec_one_or_more b1.ab_spec;
  ab_impl_type = _;
  ab_rel = _;
  ab_parser = impl_zero_copy_array_group_one_or_more share gather v1 b1.ab_parser ();
}
