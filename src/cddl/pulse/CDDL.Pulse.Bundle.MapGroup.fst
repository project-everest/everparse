module CDDL.Pulse.Bundle.MapGroup
include CDDL.Pulse.Bundle.Base
include CDDL.Pulse.Parse.MapGroup
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
  [@@@erasable] mb_footprint: Ghost.erased typ;
  [@@@erasable] mb_footprint_correct: squash (map_group_footprint mb_typ mb_footprint);
  [@@@erasable] mb_spec_type: Type0;
  [@@@erasable] mb_spec_type_eq: Ghost.erased (EqTest.eq_test mb_spec_type);
  [@@@erasable] mb_spec: Ghost.erased (mg_spec mb_typ mb_footprint mb_spec_type true);
  mb_impl_type: Type0;
  [@@@erasable] mb_rel: rel mb_impl_type mb_spec_type;
  mb_parser: impl_zero_copy_map_group vmatch mb_spec.mg_parser mb_rel;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr ]
let bundle_map
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (mb: map_bundle vmatch)
: Tot (bundle vmatch)
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = mb.mb_spec_type_eq;
  b_spec = spec_map_group mb.mb_spec;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_zero_copy_map mb.mb_parser ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_ext
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (mb1: map_bundle vmatch)
  (#[@@@erasable] t2: Ghost.erased det_map_group)
  (#[@@@erasable] fp2: Ghost.erased typ)
  ([@@@erasable] sp2: Ghost.erased (mg_spec t2 fp2 mb1.mb_spec_type true))
  ([@@@erasable] sq: squash (
    impl_zero_copy_map_ext_precond (Ghost.reveal mb1.mb_typ) (mb1.mb_spec.mg_parser) (Ghost.reveal t2) sp2.mg_parser
  ))
: Tot (map_bundle vmatch)
= {
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type_eq = mb1.mb_spec_type_eq;
  mb_spec_type = _;
  mb_spec = sp2;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_map_ext mb1.mb_parser sp2.mg_parser ()
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_ext'
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (mb1: map_bundle vmatch)
  ([@@@erasable] fp2: Ghost.erased typ)
  ([@@@erasable] sq: squash (
    typ_equiv mb1.mb_footprint fp2
  ))
: Tot (map_bundle vmatch)
= bundle_map_ext mb1 (mg_spec_ext mb1.mb_spec fp2 mb1.mb_spec.mg_size mb1.mb_spec.mg_serializable) ()

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
= {
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = _;
  mb_spec_type_eq = EqTest.either_eq mb1.mb_spec_type_eq mb2.mb_spec_type_eq;
  mb_spec = mg_spec_choice mb1.mb_spec mb2.mb_spec;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_map_choice v1 mb1.mb_parser mb2.mb_parser ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_zero_or_one
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (mb1: map_bundle vmatch)
  (v1: impl_map_group_t vmatch mb1.mb_typ mb1.mb_footprint)
  ([@@@erasable] sq: squash (
    MapGroupFail? (apply_map_group_det mb1.mb_typ cbor_map_empty)
  ))
: Tot (map_bundle vmatch)
= {
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = _;
  mb_spec_type_eq = EqTest.option_eq mb1.mb_spec_type_eq;
  mb_spec = mg_spec_zero_or_one mb1.mb_spec;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_map_zero_or_one v1 mb1.mb_parser ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_concat
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (share: share_t vmatch)
  (gather: gather_t vmatch)
  (mb1: map_bundle vmatch)
  (mb2: map_bundle vmatch)
  ([@@@erasable] sq: squash (
    typ_disjoint mb1.mb_footprint mb2.mb_footprint
  ))
: Tot (map_bundle vmatch)
= {
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = _;
  mb_spec_type_eq = EqTest.pair_eq mb1.mb_spec_type_eq mb2.mb_spec_type_eq;
  mb_spec = mg_spec_concat mb1.mb_spec mb2.mb_spec;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_map_concat share gather mb1.mb_parser mb2.mb_parser ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_match_item_for
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (get: map_get_t vmatch)
  (#[@@@erasable] key: Ghost.erased cbor)
  (lkey: with_cbor_literal_t vmatch (Ghost.reveal key))
  ([@@@erasable] cut: Ghost.erased bool)
  (value: bundle vmatch)
: Tot (map_bundle vmatch)
= {
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = _;
  mb_spec_type_eq = value.b_spec_type_eq;
  mb_spec = mg_spec_match_item_for cut key value.b_spec;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_match_item_for get lkey cut value.b_parser;
}

module EqTest = CDDL.Spec.EqTest

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_map_zero_or_more
  (#ty: Type0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_map_iterator_t: Type0)
  (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (map_iterator_start: map_iterator_start_t vmatch cbor_map_iterator_match)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (key: bundle vmatch) // MUST contain function pointers ONLY
  (va1: impl_typ vmatch key.b_typ) // MUST be a function pointer
  (#[@@@erasable] key_except: Ghost.erased typ)
  (va_ex: impl_typ vmatch key_except) // MUST be a function pointer
  (value: bundle vmatch) // MUST contain function pointers ONLY
  (va2: impl_typ vmatch value.b_typ) // MUST be a function pointer
: Tot (map_bundle vmatch)
= {
  mb_typ = _;
  mb_footprint = _;
  mb_footprint_correct = ();
  mb_spec_type = _;
  mb_spec_type_eq = EqTest.map_eq _ (EqTest.list_eq value.b_spec_type_eq);
  mb_spec = mg_zero_or_more_match_item key.b_spec key_except value.b_spec;
  mb_impl_type = _;
  mb_rel = _;
  mb_parser = impl_zero_copy_map_zero_or_more map_iterator_start map_share map_gather key.b_spec_type_eq key.b_spec va1 key.b_parser va_ex value.b_spec va2 value.b_parser
}
