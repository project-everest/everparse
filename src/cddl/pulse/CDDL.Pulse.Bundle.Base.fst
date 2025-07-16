module CDDL.Pulse.Bundle.Base
include CDDL.Pulse.Attr
include CDDL.Pulse.Parse.Base
include CDDL.Pulse.Serialize.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
module EqTest = CDDL.Spec.EqTest
open FStar.List.Tot.Base { (@) }

let allowed (c: Char.char) : bool =
  let open FStar.UInt32 in
  let code = FStar.Char.u32_of_char c in
  (code `gte` FStar.Char.u32_of_char 'a' &&
    code `lte` FStar.Char.u32_of_char 'Z') ||
  (code `gte` FStar.Char.u32_of_char 'a' &&
    code `lte` FStar.Char.u32_of_char 'z') ||
  (code `gte` FStar.Char.u32_of_char '0' &&
    code `lte` FStar.Char.u32_of_char '9') ||
  code = FStar.Char.u32_of_char '_'

let escape (c: Char.char) : list Char.char =
  (* Escape '-' as '_', for the rest use character codes. *)
  if c = '-' then
    ['_']
  else
    let code = FStar.Char.u32_of_char c |> FStar.UInt32.v in
    let s = string_of_int code in
    let s = FStar.String.list_of_string s in
    '_' :: s

[@@bundle_attr] // so it inlines
let rec sanitize_aux (s : list Char.char) : list Char.char =
  match s with
  | [] -> []
  | x :: xs ->
    if allowed x
    then x :: sanitize_aux xs
    else escape x @ sanitize_aux xs

[@@bundle_attr] // so it inlines
let sanitize_name (s:string) : string =
  s
  |> FStar.String.list_of_string
  |> sanitize_aux
  |> FStar.String.string_of_list

[@@bundle_attr] // so it inlines
unfold noextract
let maybe_named (s : option string) (t : Type u#aa) : Type u#aa =
  match s with
  | Some n ->
    (* normalize_term below is important to actually
       compute the concrete string. I though having this
       here would mean I can elide the @@bundle_attrs above,
       but it seems not. *)
    FStar.Tactics.PrettifyType.named
      (normalize_term (sanitize_name n))
      t
  | None -> t

inline_for_extraction noextract [@@noextract_to "krml"]
noeq
type bundle
  (#cbor_t: Type)
  (vmatch: perm -> cbor_t -> cbor -> slprop)
= {
  [@@@erasable] b_typ: Ghost.erased typ;
  b_spec_type: Type0;
  [@@@erasable] b_spec_type_eq: Ghost.erased (EqTest.eq_test b_spec_type);
  [@@@erasable] b_spec: Ghost.erased (spec b_typ b_spec_type true);
  b_impl_type: Type0;
  b_rel: rel b_impl_type b_spec_type;
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

let mk_eq_test_bij
  (#tgt: Type0)
  (#tgt' : Type0)
  (f12: (tgt -> tgt'))
  (f21: (tgt' -> tgt))
  ([@@@erasable]fprf_21_12: (x: tgt) -> squash (f21 (f12 x) == x))
  ([@@@erasable]fprf_12_21: (x: tgt') -> squash (f12 (f21 x) == x))
  (eq': EqTest.eq_test tgt)
: EqTest.eq_test tgt'
= EqTest.mk_eq_test (fun x1' x2' -> 
    fprf_12_21 x1'; fprf_12_21 x2'; 
    let b = eq' (f21 x1') (f21 x2') in
    if b then (
      assert (f21 x1' == f21 x2');
      b
    ) else (
      assert (f21 x1' =!= f21 x2');
      b
    ))


inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_bij
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (b: bundle vmatch)
  (#tgt: Type0)
  (#tgt' : Type0)
  (f12: (tgt -> tgt'))
  (f21: (tgt' -> tgt))
  ([@@@erasable]fprf_21_12: (x: tgt) -> squash (f21 (f12 x) == x))
  ([@@@erasable]fprf_12_21: (x: tgt') -> squash (f12 (f21 x) == x))
  ([@@@erasable] tgt_eq: squash (tgt == b.b_spec_type))
  (#impl_tgt: Type0)
  (#impl_tgt' : Type0)
  (g12: (impl_tgt -> impl_tgt'))
  (g21: (impl_tgt' -> impl_tgt))
  ([@@@erasable]gprf_21_12: (x: impl_tgt) -> squash (g21 (g12 x) == x))
  ([@@@erasable]gprf_12_21: (x: impl_tgt') -> squash (g12 (g21 x) == x))
  ([@@@erasable] impl_tgt_eq: squash (impl_tgt == b.b_impl_type))
: Tot (bundle vmatch)
= match b with
  | Mkbundle b_typ b_spec_type b_spec_type_eq b_spec b_impl_type b_rel b_parser b_serializer ->
    {
      b_typ = b_typ;
      b_spec_type = tgt';
      b_spec_type_eq = Ghost.hide (mk_eq_test_bij f12 f21 fprf_21_12 fprf_12_21 b_spec_type_eq);
      b_spec = spec_inj b_spec f12 f21 fprf_21_12 fprf_12_21;
      b_impl_type = impl_tgt';
      b_rel = rel_fun b_rel g21 f21;
      b_parser = impl_zero_copy_bij b_parser f12 f21 fprf_21_12 g12 g21 gprf_21_12;
      b_serializer = impl_serialize_bij b_serializer f12 f21 fprf_21_12 fprf_12_21 g12 g21 gprf_21_12 gprf_12_21;
    }

let bundle_parser_t
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (b: bundle vmatch)
: Tot Type
= impl_zero_copy_parse vmatch b.b_spec.parser b.b_rel

let bundle_parser_eq_intro
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (#t0 #t: Type)
  (sq0: squash (t0 == t))
  (b1: bundle vmatch)
  (sq1: squash (bundle_parser_t b1 == t0))
  (b2: bundle vmatch)
  (sq2: squash (b1 == b2))
: Tot (squash (bundle_parser_t b2 == t))
= ()

unfold
let bundle_serializer_t
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (b: bundle vmatch)
: Tot Type
= impl_serialize b.b_spec b.b_rel

let bundle_serializer_eq_intro
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (#t0 #t: Type)
  (sq0: squash (t0 == t))
  (b1: bundle vmatch)
  (sq1: squash (bundle_serializer_t b1 == t0))
  (b2: bundle vmatch)
  (sq2: squash (b1 == b2))
: Tot (squash (bundle_serializer_t b2 == t))
= ()

inline_for_extraction noextract [@@noextract_to "krml"; bundle_get_impl_type_attr]
let bundle_set_parser_and_serializer
  (#cbor_t: Type)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  ([@@@erasable] b: Ghost.erased (bundle vmatch))
  (t: Type0)
  ([@@@erasable] t_eq: squash (b.b_impl_type == t))
  (spect: Type0)
  ([@@@erasable] spect_eq: squash (b.b_spec_type == spect))
  (r: rel t spect)
  ([@@@erasable] r_eq: squash (r == coerce_eq () b.b_rel))
  (#[@@@erasable] t': Type)
  (p: t')
  ([@@@erasable] p_eq: squash (bundle_parser_t b == t'))
  (#[@@@erasable] ts: Type)
  (s: ts)
  ([@@@erasable] s_eq: squash (bundle_serializer_t b == ts))
: Tot (bundle vmatch)
= {
    b_typ = b.b_typ;
    b_spec_type = spect;
    b_spec_type_eq = b.b_spec_type_eq;
    b_spec = b.b_spec;
    b_impl_type = t;
    b_rel = r;
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
