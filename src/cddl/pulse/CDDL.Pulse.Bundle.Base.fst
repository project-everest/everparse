module CDDL.Pulse.Bundle.Base
include CDDL.Pulse.Attr
include CDDL.Pulse.Parse.Base
include CDDL.Pulse.Serialize.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
module EqTest = CDDL.Spec.EqTest

inline_for_extraction noextract [@@noextract_to "krml"]
noeq
type bundle
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> cbor -> slprop)
= {
  [@@@erasable] b_typ: Ghost.erased typ;
  [@@@erasable] b_spec_type: Type0;
  [@@@erasable] b_spec_type_eq: Ghost.erased (EqTest.eq_test b_spec_type);
  [@@@erasable] b_spec: Ghost.erased (spec b_typ b_spec_type true);
  b_impl_type: Type0;
  [@@@erasable] b_rel: rel b_impl_type b_spec_type;
  b_parser: impl_zero_copy_parse vmatch b_spec.parser b_rel;
  b_serializer: impl_serialize b_spec b_rel;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let get_bundle_impl_type
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (b: bundle vmatch)
: Pure Type0
  (requires True)
  (ensures fun t -> t == b.b_impl_type) // guard if the number of fields changes
= match b with
  | Mkbundle _ _ _ _ b_impl_type _ _ _ -> b_impl_type

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_set_parser_and_serializer
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  ([@@@erasable] b: Ghost.erased (bundle vmatch))
  (t: Type0)
  ([@@@erasable] t_eq: squash (t == b.b_impl_type))
  (#[@@@erasable] t': Type)
  (p: t')
  ([@@@erasable] p_eq: squash (t' == impl_zero_copy_parse vmatch b.b_spec.parser b.b_rel))
  (#[@@@erasable] ts: Type)
  (s: ts)
  ([@@@erasable] s_eq: squash (ts == impl_serialize b.b_spec b.b_rel))
: Tot (bundle vmatch)
= {
    b_typ = b.b_typ;
    b_spec_type = b.b_spec_type;
    b_spec_type_eq = b.b_spec_type_eq;
    b_spec = b.b_spec;
    b_impl_type = t;
    b_rel = coerce_eq () b.b_rel;
    b_parser = p;
    b_serializer = s;
  }

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_always_false
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> cbor -> slprop)
  (#[@@@erasable] ty: Ghost.erased typ)
  ([@@@erasable] sp: Ghost.erased (spec ty (squash False) true))
: bundle vmatch
= {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.eqtype_eq _;
  b_spec = sp;
  b_impl_type = _;
  b_rel = _;
  b_parser = impl_zero_copy_always_false _ _;
  b_serializer = impl_serialize_always_false _;
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_ext
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (b: bundle vmatch)
  (#[@@@erasable] t': Ghost.erased typ)
  ([@@@erasable] sp': Ghost.erased (spec t' b.b_spec_type true))
  ([@@@erasable] sq: squash (
    typ_equiv t' b.b_typ /\
    (forall (x: cbor) . Ghost.reveal t' x ==> ((sp'.parser x <: b.b_spec_type) == b.b_spec.parser x))
  ))
= match b with
  | Mkbundle b_typ b_spec_type b_spec_type_eq b_spec b_impl_type b_rel b_parser b_serializer ->
  {
  b_typ = t';
  b_spec_type = b_spec_type;
  b_spec_type_eq = b_spec_type_eq;
  b_spec = sp';
  b_impl_type = b_impl_type;
  b_rel = b_rel;
  b_parser = impl_zero_copy_ext b_parser #_ #sp'.serializable sp'.parser ();
  b_serializer = impl_serialize_ext b_serializer _ ();
}

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_type_ext
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (b: bundle vmatch)
  ([@@@erasable] t': Ghost.erased typ)
  ([@@@erasable] sq: squash (
    typ_equiv t' b.b_typ
  ))
: Tot (bundle vmatch)
= bundle_ext b (spec_ext b.b_spec t') ()

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_choice
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (b1: bundle vmatch)
  (v1: impl_typ vmatch b1.b_typ)
  (b2: bundle vmatch)
  ([@@@erasable] sq: squash (
    typ_disjoint b1.b_typ b2.b_typ
  ))
= match b1 with
  | Mkbundle b_typ1 b_spec_type1 b_spec_type_eq1 b_spec1 b_impl_type1 b_rel1 b_parser1 b_serializer1 ->
  match b2 with
  | Mkbundle b_typ2 b_spec_type2 b_spec_type_eq2 b_spec2 b_impl_type2 b_rel2 b_parser2 b_serializer2 ->
  {
  b_typ = _;
  b_spec_type = _;
  b_spec_type_eq = EqTest.either_eq b_spec_type_eq1 b_spec_type_eq2;
  b_spec = spec_choice b_spec1 b_spec2;
  b_impl_type = either b_impl_type1 b_impl_type2;
  b_rel = _;
  b_parser = impl_zero_copy_choice #_ #_ #_ #_ #_ #b_spec1.parser v1 b_parser1 b_parser2;
  b_serializer = impl_serialize_choice b_serializer1 b_serializer2 ();
}
