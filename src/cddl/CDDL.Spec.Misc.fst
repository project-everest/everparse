module CDDL.Spec.Misc
include CDDL.Spec.Base
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Appendix D

let uint : typ = (fun x -> Cbor.Int64? x && Cbor.Int64?.typ x = Cbor.cbor_major_type_uint64)
let nint : typ = (fun x -> Cbor.Int64? x && Cbor.Int64?.typ x = Cbor.cbor_major_type_neg_int64)
let t_int : typ = uint `t_choice` nint

let bstr : typ = (fun x -> Cbor.String? x && Cbor.String?.typ x = Cbor.cbor_major_type_byte_string)
let bytes = bstr
let tstr : typ = (fun x -> Cbor.String? x && Cbor.String?.typ x = Cbor.cbor_major_type_text_string)
let text = tstr

[@@CMacro]
let simple_value_false : Cbor.simple_value = 20uy
[@@CMacro]
let simple_value_true : Cbor.simple_value = 21uy
[@@CMacro]
let simple_value_nil : Cbor.simple_value = 22uy
[@@CMacro]
let simple_value_undefined : Cbor.simple_value = 23uy

let t_simple_value_literal (s: Cbor.simple_value) : typ =
  t_literal (Cbor.Simple s)

let t_false : typ = t_simple_value_literal simple_value_false
let t_true : typ = t_simple_value_literal simple_value_true
let t_bool : typ = t_choice t_false t_true
let t_nil : typ = t_simple_value_literal simple_value_nil
let t_null : typ = t_nil
let t_undefined : typ = t_simple_value_literal simple_value_undefined

let t_uint_literal (v: U64.t) : typ =
  t_literal (Cbor.Int64 Cbor.cbor_major_type_uint64 v)

// 2.1 specifies "names that turn into the map key text string"

noextract
let string64 = (s: Seq.seq U8.t {FStar.UInt.fits (Seq.length s) 64})

let name_as_text_string (s: string64) : typ =
  t_literal (Cbor.String Cbor.cbor_major_type_text_string s)

// Section 3.6: Tags

let t_tag (#b: option Cbor.raw_data_item) (tag: U64.t) (t: bounded_typ_gen b) : bounded_typ_gen b = fun x ->
  Cbor.Tagged? x &&
  Cbor.Tagged?.tag x = tag &&
  t (Cbor.Tagged?.v x)

let rec t_tag_rec
  (tag: U64.t)
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> bounded_typ b))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
= Cbor.Tagged? x &&
  Cbor.Tagged?.tag x = tag &&
  phi x (t_tag_rec tag phi) (Cbor.Tagged?.v x)

let spec_tag
  (tag: U64.t)
  (#t: typ)
  (#target: Type)
  (p: spec t target)
: Tot (spec (t_tag tag t) target)
= {
  serializable = p.serializable;
  parser = (function Cbor.Tagged _ v -> p.parser v);
  serializer = (fun x -> Cbor.Tagged tag (p.serializer x));
}

// Section 3.8.1: Control .size

let str_size (ty: Cbor.major_type_byte_string_or_text_string) (sz: nat) : typ = fun x ->
  Cbor.String? x &&
  Cbor.String?.typ x = ty &&
  Seq.length (Cbor.String?.v x) = sz

let uint_size (sz: nat) : typ = fun x ->
  Cbor.Int64? x &&
  Cbor.Int64?.typ x = Cbor.cbor_major_type_uint64 &&
  U64.v (Cbor.Int64?.v x) < pow2 sz

// Section 3.8.4: Control .cbor
// We parameterize over the CBOR order on which the CBOR parser depends

let bstr_cbor
  (data_item_order: (Cbor.raw_data_item -> Cbor.raw_data_item -> bool))
  (ty: typ) // TODO: enable recursion for this construct? If so, we need to replace << with some serialization size
: typ = fun x ->
  Cbor.String? x &&
  Cbor.String?.typ x = Cbor.cbor_major_type_byte_string &&
  FStar.StrongExcludedMiddle.strong_excluded_middle (
    exists y . Cbor.serialize_cbor y == Cbor.String?.v x /\
    Cbor.data_item_wf data_item_order y /\
    ty y == true
  )

let parser_spec_bool (p: bool -> prop { forall x . p x }) : parser_spec t_bool bool p =
  (fun x -> let Cbor.Simple v = x in
    v = simple_value_true
  )

let serializer_spec_bool (p: bool -> prop { forall x . p x }) : serializer_spec (parser_spec_bool p) =
  (fun x -> Cbor.Simple (if x then simple_value_true else simple_value_false))

let parser_spec_bstr (p: string64 -> prop { forall x . p x }) : parser_spec bstr string64 p =
  (fun x -> let Cbor.String _ v = x in v)

let serializer_spec_bstr (p: string64 -> prop { forall x . p x }) : serializer_spec (parser_spec_bstr p) =
  (fun x -> Cbor.String Cbor.cbor_major_type_byte_string x)

let parser_spec_tstr (p: string64 -> prop { forall x . p x }) : parser_spec tstr string64 p =
  (fun x -> let Cbor.String _ v = x in v)

let serializer_spec_tstr (p: string64 -> prop { forall x . p x }) : serializer_spec (parser_spec_tstr p) =
  (fun x -> Cbor.String Cbor.cbor_major_type_text_string x)
