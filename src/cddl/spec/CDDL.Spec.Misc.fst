module CDDL.Spec.Misc
include CDDL.Spec.Base
module Cbor = CBOR.Spec.API.Format
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Appendix D

let uint : typ = (fun w -> let x = Cbor.unpack w in Cbor.CInt64? x && Cbor.CInt64?.typ x = Cbor.cbor_major_type_uint64)
let nint : typ = (fun w -> let x = Cbor.unpack w in Cbor.CInt64? x && Cbor.CInt64?.typ x = Cbor.cbor_major_type_neg_int64)
let t_int : typ = uint `t_choice` nint

let bstr : typ = (fun w -> let x = Cbor.unpack w in Cbor.CString? x && Cbor.CString?.typ x = Cbor.cbor_major_type_byte_string)
let bytes = bstr
let tstr : typ = (fun w -> let x = Cbor.unpack w in Cbor.CString? x && Cbor.CString?.typ x = Cbor.cbor_major_type_text_string)
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
  t_literal (Cbor.pack (Cbor.CSimple s))

let t_false : typ = t_simple_value_literal simple_value_false
let t_true : typ = t_simple_value_literal simple_value_true
let t_bool : typ = t_choice t_false t_true
let t_simple : typ = (fun w -> let x = Cbor.unpack w in Cbor.CSimple? x)
let t_nil : typ = t_simple_value_literal simple_value_nil
let t_null : typ = t_nil
let t_undefined : typ = t_simple_value_literal simple_value_undefined

let t_uint_literal (v: U64.t) : typ =
  t_literal (Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_uint64 v))

// 2.1 specifies "names that turn into the map key text string"

noextract
let string64 = (s: Seq.seq U8.t {FStar.UInt.fits (Seq.length s) 64})

let name_as_text_string (s: string64 { CBOR.Spec.API.UTF8.correct s }) : typ =
  t_literal (Cbor.pack (Cbor.CString Cbor.cbor_major_type_text_string s))

// Section 3.6: Tags

(*
let t_tag (#b: option Cbor.cbor) (tag: U64.t) (t: bounded_typ_gen b) : bounded_typ_gen b = fun w -> let x = Cbor.unpack w in
  Cbor.CTagged? x &&
  Cbor.CTagged?.tag x = tag &&
  t (Cbor.CTagged?.v x)

let rec t_tag_rec
  (tag: U64.t)
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> bounded_typ b))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
= Cbor.Tagged? x &&
  Cbor.Tagged?.tag x = tag &&
  phi x (t_tag_rec tag phi) (Cbor.Tagged?.v x)
*)
let t_tag (tag: option U64.t) (t: typ) : typ = fun w -> let x = Cbor.unpack w in
  Cbor.CTagged? x &&
  begin match tag with
  | None -> true
  | Some tag -> Cbor.CTagged?.tag x = tag
  end &&
  t (Cbor.CTagged?.v x)

let spec_tag_some
  (tag: U64.t)
  (#t: typ)
  (#target: Type)
  (#inj: bool)
  (p: spec t target inj)
: Tot (spec (t_tag (Some tag) t) target inj)
= {
  serializable = p.serializable;
  parser = (function w -> let Cbor.CTagged _ v = Cbor.unpack w in p.parser v);
  serializer = (fun x -> Cbor.pack (Cbor.CTagged tag (p.serializer x)));
  parser_inj = ();
}

let spec_tag_none
  (#t: typ)
  (#target: Type)
  (#inj: bool)
  (p: spec t target inj)
: Tot (spec (t_tag None t) (U64.t & target) inj)
= {
  serializable = (fun x -> p.serializable (snd x));
  parser = (function w -> let Cbor.CTagged tag v = Cbor.unpack w in (tag, p.parser v));
  serializer = (fun (tag, x) -> Cbor.pack (Cbor.CTagged tag (p.serializer x)));
  parser_inj = ();
}

// Section 3.8.1: Control .size

let str_size (ty: Cbor.major_type_byte_string_or_text_string) (sz: nat) : typ = fun w -> let x = Cbor.unpack w in
  Cbor.CString? x &&
  Cbor.CString?.typ x = ty &&
  Seq.length (Cbor.CString?.v x) = sz

let uint_size (sz: nat) : typ = fun w -> let x = Cbor.unpack w in
  Cbor.CInt64? x &&
  Cbor.CInt64?.typ x = Cbor.cbor_major_type_uint64 &&
  U64.v (Cbor.CInt64?.v x) < pow2 sz

// Section 3.8.4: Control .cbor

let bstr_cbor
  (ty: typ) // TODO: enable recursion for this construct? If so, we need to replace << with some serialization size
: typ = fun w -> let x = Cbor.unpack w in
  Cbor.CString? x &&
  Cbor.CString?.typ x = Cbor.cbor_major_type_byte_string &&
  begin match Cbor.cbor_parse (Cbor.CString?.v x) with
  | None -> false
  | Some (y, consumed) -> consumed = Seq.length (Cbor.CString?.v x) && ty y
  end

let bstr_cbor_det
  (ty: typ) // TODO: enable recursion for this construct? If so, we need to replace << with some serialization size
: typ = fun w -> let x = Cbor.unpack w in
  Cbor.CString? x &&
  Cbor.CString?.typ x = Cbor.cbor_major_type_byte_string &&
  begin match Cbor.cbor_det_parse (Cbor.CString?.v x) with
  | None -> false
  | Some (y, consumed) -> consumed = Seq.length (Cbor.CString?.v x) && ty y
  end

let parser_spec_always_false (p: squash False -> bool) : parser_spec t_always_false (squash False) p =
  (fun x -> false_elim ())

let serializer_spec_always_false (p: squash False -> bool) : serializer_spec (parser_spec_always_false p) =
  (fun x -> false_elim ())

let spec_always_false
  (p: (squash False -> bool))
: spec t_always_false (squash False) true
= {
  serializable = p;
  parser = parser_spec_always_false p;
  serializer = serializer_spec_always_false p;
  parser_inj = ();
}

let parser_spec_any (p: Cbor.cbor -> bool { forall x . p x }) : parser_spec any Cbor.cbor p =
  (fun x -> x)

let serializer_spec_any (p: Cbor.cbor -> bool { forall x . p x }) : serializer_spec (parser_spec_any p) =
  (fun x -> x)

let spec_any
  (p: Cbor.cbor -> bool { forall x . p x })
: spec any Cbor.cbor true
= {
  serializable = p;
  parser = parser_spec_any p;
  serializer = serializer_spec_any p;
  parser_inj = ();
}

let parser_spec_bool (p: bool -> bool { forall x . p x }) : parser_spec t_bool bool p =
  (fun x -> let Cbor.CSimple v = Cbor.unpack x in
    v = simple_value_true
  )

let serializer_spec_bool (p: bool -> bool { forall x . p x }) : serializer_spec (parser_spec_bool p) =
  (fun x -> Cbor.pack (Cbor.CSimple (if x then simple_value_true else simple_value_false)))

let spec_bool
  (p: bool -> bool { forall x . p x })
: spec t_bool bool true
= {
  serializable = p;
  parser = parser_spec_bool p;
  serializer = serializer_spec_bool p;
  parser_inj = ();
}

let parser_spec_simple (p: U8.t -> bool { forall x . p x <==> Cbor.simple_value_wf x }) : parser_spec t_simple U8.t p =
  (fun x -> let Cbor.CSimple v = Cbor.unpack x in v)

let serializer_spec_simple (p: U8.t -> bool { forall x . p x <==> Cbor.simple_value_wf x }) : serializer_spec (parser_spec_simple p) =
  (fun x -> Cbor.pack (Cbor.CSimple x))

let spec_simple
  (p: U8.t -> bool { forall x . p x <==> Cbor.simple_value_wf x })
: spec t_simple U8.t true
= {
  serializable = p;
  parser = parser_spec_simple p;
  serializer = serializer_spec_simple p;
  parser_inj = ();
}

let parser_spec_uint (p: U64.t -> bool { forall x . p x }) : parser_spec uint U64.t p =
  (fun x -> let Cbor.CInt64 _ v = Cbor.unpack x in v)

let serializer_spec_uint (p: U64.t -> bool { forall x . p x }) : serializer_spec (parser_spec_uint p) =
  (fun x -> Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_uint64 x))

let spec_uint
  (p: U64.t -> bool { forall x . p x })
: spec uint U64.t true
= {
  serializable = p;
  parser = parser_spec_uint p;
  serializer = serializer_spec_uint p;
  parser_inj = ();
}

let parser_spec_nint (p: U64.t -> bool { forall x . p x }) : parser_spec nint U64.t p =
  (fun x -> let Cbor.CInt64 _ v = Cbor.unpack x in v)

let serializer_spec_nint (p: U64.t -> bool { forall x . p x }) : serializer_spec (parser_spec_nint p) =
  (fun x -> Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_neg_int64 x))

let spec_nint
  (p: U64.t -> bool { forall x . p x })
: spec nint U64.t true
= {
  serializable = p;
  parser = parser_spec_nint p;
  serializer = serializer_spec_nint p;
  parser_inj = ();
}

let parser_spec_bstr (p: string64 -> bool { forall x . p x }) : parser_spec bstr string64 p =
  (fun x -> let Cbor.CString _ v = Cbor.unpack x in v)

let serializer_spec_bstr (p: string64 -> bool { forall x . p x }) : serializer_spec (parser_spec_bstr p) =
  (fun x -> Cbor.pack (Cbor.CString Cbor.cbor_major_type_byte_string x))

let spec_bstr
  (p: string64 -> bool { forall x . p x })
: spec bstr string64 true
= {
  serializable = p;
  parser = parser_spec_bstr p;
  serializer = serializer_spec_bstr p;
  parser_inj = ();
}

let parser_spec_tstr (p: string64 -> bool { forall x . p x <==> CBOR.Spec.API.UTF8.correct x }) : parser_spec tstr string64 p =
  (fun x -> let Cbor.CString _ v = Cbor.unpack x in v)

let serializer_spec_tstr (p: string64 -> bool { forall x . p x <==> CBOR.Spec.API.UTF8.correct x }) : serializer_spec (parser_spec_tstr p) =
  (fun x -> Cbor.pack (Cbor.CString Cbor.cbor_major_type_text_string x))

let spec_tstr
  (p: string64 -> bool { forall x . p x <==> CBOR.Spec.API.UTF8.correct x })
: spec tstr string64 true
= {
  serializable = p;
  parser = parser_spec_tstr p;
  serializer = serializer_spec_tstr p;
  parser_inj = ();
}
