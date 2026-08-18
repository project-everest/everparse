module CDDL.Spec.Misc
include CDDL.Spec.Base
module Cbor = CBOR.Spec.API.Format
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Appendix D

let uint : typ = (fun w -> let x = Cbor.unpack w in Cbor.CInt64? x && Cbor.CInt64?.typ x = Cbor.cbor_major_type_uint64)
let nint : typ = (fun w -> let x = Cbor.unpack w in Cbor.CInt64? x && Cbor.CInt64?.typ x = Cbor.cbor_major_type_neg_int64)
let t_int : typ = uint `t_choice` nint

let t_int_range (lo hi: int) = (fun w -> let x = Cbor.unpack w in
  match x with
  | Cbor.CInt64 ty v ->
    let w = if ty = Cbor.cbor_major_type_uint64 then U64.v v else -1 - U64.v v in
    lo <= w && w <= hi
  | _ -> false
)

let str_gen (k: Cbor.major_type_byte_string_or_text_string) : typ = (fun w -> let x = Cbor.unpack w in Cbor.CString? x && Cbor.CString?.typ x = k)
let bstr : typ = str_gen Cbor.cbor_major_type_byte_string
let bytes = bstr
let tstr : typ = str_gen Cbor.cbor_major_type_text_string
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

let parser_spec_tag_some
  (tag: U64.t)
  (#t: typ)
  (#target: Type)
  (#ser: (target -> bool))
  (p: parser_spec t target ser)
: Tot (parser_spec (t_tag (Some tag) t) target ser)
= (function w -> let Cbor.CTagged _ v = Cbor.unpack w in p v)

let spec_tag_some
  (tag: U64.t)
  (#t: typ)
  (#target: Type)
  (#inj: bool)
  (p: spec t target inj)
: Tot (spec (t_tag (Some tag) t) target inj)
= {
  serializable = p.serializable;
  parser = parser_spec_tag_some _ p.parser;
  serializer = (fun x -> Cbor.pack (Cbor.CTagged tag (p.serializer x)));
  parser_inj = ();
}

let serializable_spec_tag_none
  (#target: Type)
  (ser: (target -> bool))
  (x: (U64.t & target))
: Tot bool
= ser (snd x)

let parser_spec_tag_none
  (#t: typ)
  (#target: Type)
  (#ser: (target -> bool))
  (p: parser_spec t target ser)
: Tot (parser_spec (t_tag None t) (U64.t & target) (serializable_spec_tag_none ser))
= (function w -> let Cbor.CTagged tag v = Cbor.unpack w in (tag, p v))

let spec_tag_none
  (#t: typ)
  (#target: Type)
  (#inj: bool)
  (p: spec t target inj)
: Tot (spec (t_tag None t) (U64.t & target) inj)
= {
  serializable = serializable_spec_tag_none p.serializable;
  parser = parser_spec_tag_none p.parser;
  serializer = (fun (tag, x) -> Cbor.pack (Cbor.CTagged tag (p.serializer x)));
  parser_inj = ();
}

// Section 3.8.1: Control .size

let str_size_serializable
  (ty: Cbor.major_type_byte_string_or_text_string)
  (lo hi: nat)
  (x: Seq.seq U8.t)
: Tot bool
= let len = Seq.length x in
  len < pow2 64 &&
  lo <= len && len <= hi &&
  (if ty = Cbor.cbor_major_type_text_string then CBOR.Spec.API.UTF8.correct x else true)

let str_size (ty: Cbor.major_type_byte_string_or_text_string) (lo hi: nat) : typ = fun w -> let x = Cbor.unpack w in
  Cbor.CString? x &&
  Cbor.CString?.typ x = ty &&
  str_size_serializable ty lo hi (Cbor.CString?.v x)

let spec_str_size
  (ty: Cbor.major_type_byte_string_or_text_string)
  (lo hi: U64.t)
: Tot (spec (str_size ty (U64.v lo) (U64.v hi)) (Seq.seq U8.t) true)
= {
  serializable = str_size_serializable ty (U64.v lo) (U64.v hi);
  parser = (fun x -> let Cbor.CString _ v = Cbor.unpack x in (v <: (v: Seq.seq U8.t { str_size_serializable ty (U64.v lo) (U64.v hi) v })));
  serializer = (fun (x: Seq.seq U8.t { str_size_serializable ty (U64.v lo) (U64.v hi) x }) -> Cbor.pack (Cbor.CString ty x));
  parser_inj = ();
}

let uint_size (sz: nat) : typ = fun w -> let x = Cbor.unpack w in
  Cbor.CInt64? x &&
  Cbor.CInt64?.typ x = Cbor.cbor_major_type_uint64 &&
  U64.v (Cbor.CInt64?.v x) < pow2 (let open FStar.Mul in 8 * sz)

let spec_uint_size
  (sz: nat)
: Tot (spec (uint_size sz) U64.t true)
= {
  serializable = (fun x -> U64.v x < pow2 (let open FStar.Mul in 8 * sz));
  parser = (fun x -> let Cbor.CInt64 _ v = Cbor.unpack x in v);
  serializer = (fun x -> Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_uint64 x));
  parser_inj = ();
}

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

let spec_bstr_cbor_small_parser
  (#t: Type)
  (#ty: typ)
  (#inj: bool)
  (sp: spec ty t inj {
    forall (x: t) .
    sp.serializable x ==>
    Seq.length (Cbor.cbor_det_serialize (sp.serializer x)) < pow2 64
  })
: Tot (parser_spec (bstr_cbor ty) t sp.serializable)
=
  fun (x: Cbor.cbor { bstr_cbor ty x }) ->
    let s = Cbor.CString?.v (Cbor.unpack x) in
    let Some (y, _) = Cbor.cbor_parse s in
    Cbor.cbor_det_serialize_parse y;
    (sp.parser y <: t)
    
let spec_bstr_cbor_small
  (#t: Type)
  (#ty: typ)
  (#inj: bool)
  (sp: spec ty t inj {
    forall (x: t) .
    sp.serializable x ==>
    Seq.length (Cbor.cbor_det_serialize (sp.serializer x)) < pow2 64
  })
: Tot (spec (bstr_cbor ty) t false)
= {
  serializable = sp.serializable;
  parser = spec_bstr_cbor_small_parser sp;
  serializer = (fun (x: t { sp.serializable x }) ->
    let y1 = sp.serializer x in
    let y2 = Cbor.cbor_det_serialize y1 in
    let y3 = Cbor.CString Cbor.cbor_major_type_byte_string y2 in
    let y = Cbor.pack y3 in
    Cbor.unpack_pack y3;
    Cbor.cbor_det_serialize_parse y1;
    y
  );
  parser_inj = ();
}

let spec_bstr_cbor_big_serializable
  (#t: Type)
  (#ty: typ)
  (#inj: bool)
  (sp: spec ty t inj)
  (x: t)
: Tot bool
= sp.serializable x && Seq.length (Cbor.cbor_det_serialize (sp.serializer x)) < pow2 64 // the length condition imposes `inj = true` for the parser

let cbor_parse_det_serialize_size_t =
  (x: Seq.seq U8.t) ->
  Lemma
  (match Cbor.cbor_parse x with
  | Some (y, consumed) ->
    Seq.length (Cbor.cbor_det_serialize y) <= consumed
  | _ -> True
  )

let spec_bstr_cbor_big_parser
  (lemma: cbor_parse_det_serialize_size_t)
  (#t: Type)
  (#ty: typ)
  (sp: spec ty t true)
: Tot (parser_spec (bstr_cbor ty) t (spec_bstr_cbor_big_serializable sp))
=
  fun (x: Cbor.cbor { bstr_cbor ty x }) ->
    let s = Cbor.CString?.v (Cbor.unpack x) in
    let Some (y, _) = Cbor.cbor_parse s in
    lemma s;
    Cbor.cbor_det_serialize_parse y;
    (sp.parser y <: t)
    
let spec_bstr_cbor_big
  (lemma: cbor_parse_det_serialize_size_t)
  (#t: Type)
  (#ty: typ)
  (sp: spec ty t true)
: Tot (spec (bstr_cbor ty) t false)
= {
  serializable = spec_bstr_cbor_big_serializable sp;
  parser = spec_bstr_cbor_big_parser lemma sp;
  serializer = (fun (x: t { spec_bstr_cbor_big_serializable sp x }) ->
    let y1 = sp.serializer x in
    let y2 = Cbor.cbor_det_serialize y1 in
    let y3 = Cbor.CString Cbor.cbor_major_type_byte_string y2 in
    let y = Cbor.pack y3 in
    Cbor.unpack_pack y3;
    Cbor.cbor_det_serialize_parse y1;
    y
  );
  parser_inj = ();
}

let bstr_cbor_det
  (ty: typ) // TODO: enable recursion for this construct? If so, we need to replace << with some serialization size
: typ = fun w -> let x = Cbor.unpack w in
  Cbor.CString? x &&
  Cbor.CString?.typ x = Cbor.cbor_major_type_byte_string &&
  begin match Cbor.cbor_det_parse (Cbor.CString?.v x) with
  | None -> false
  | Some (y, consumed) -> consumed = Seq.length (Cbor.CString?.v x) && ty y
  end

let spec_bstr_cbor_det_serializable
  (#t: Type)
  (#ty: typ)
  (sp: spec ty t true)
  (x: t)
: Tot bool
= sp.serializable x && Seq.length (Cbor.cbor_det_serialize (sp.serializer x)) < pow2 64 // the length condition imposes `inj = true`

let spec_bstr_cbor_det_parser
  (#t: Type)
  (#ty: typ)
  (sp: spec ty t true)
: Tot (parser_spec (bstr_cbor_det ty) t (spec_bstr_cbor_det_serializable sp))
=
  fun (x: Cbor.cbor { bstr_cbor_det ty x }) ->
    let Some (y, _) = Cbor.cbor_det_parse (Cbor.CString?.v (Cbor.unpack x)) in
    (sp.parser y <: t)
    
let spec_bstr_cbor_det
  (#t: Type)
  (#ty: typ)
  (sp: spec ty t true)
: Tot (spec (bstr_cbor_det ty) t true)
= {
  serializable = spec_bstr_cbor_det_serializable sp;
  parser = spec_bstr_cbor_det_parser sp;
  serializer = (fun (x: t { spec_bstr_cbor_det_serializable sp x }) ->
    let y1 = sp.serializer x in
    let y2 = Cbor.cbor_det_serialize y1 in
    let y3 = Cbor.CString Cbor.cbor_major_type_byte_string y2 in
    let y = Cbor.pack y3 in
    Cbor.unpack_pack y3;
    Cbor.cbor_det_serialize_parse y1;
    y
  );
  parser_inj = ();
}

let parser_spec_any (p: Cbor.cbor -> bool { forall x . p x }) : parser_spec any Cbor.cbor p =
  (fun x -> x)

let serializer_spec_any (p: Cbor.cbor -> bool { forall x . p x }) : serializer_spec (parser_spec_any p) =
  (fun x -> x)

let spec_any
: spec any Cbor.cbor true
= {
  serializable = (fun _ -> true);
  parser = parser_spec_any _;
  serializer = serializer_spec_any _;
  parser_inj = ();
}

let parser_spec_bool (p: bool -> bool { forall x . p x }) : parser_spec t_bool bool p =
  (fun x -> let Cbor.CSimple v = Cbor.unpack x in
    v = simple_value_true
  )

let serializer_spec_bool (p: bool -> bool { forall x . p x }) : serializer_spec (parser_spec_bool p) =
  (fun x -> Cbor.pack (Cbor.CSimple (if x then simple_value_true else simple_value_false)))

let spec_bool
: spec t_bool bool true
= {
  serializable = (fun _ -> true);
  parser = parser_spec_bool _;
  serializer = serializer_spec_bool _;
  parser_inj = ();
}

let parser_spec_simple (p: U8.t -> bool { forall x . p x <==> Cbor.simple_value_wf x }) : parser_spec t_simple U8.t p =
  (fun x -> let Cbor.CSimple v = Cbor.unpack x in v)

let serializer_spec_simple (p: U8.t -> bool { forall x . p x <==> Cbor.simple_value_wf x }) : serializer_spec (parser_spec_simple p) =
  (fun x -> Cbor.pack (Cbor.CSimple x))

let spec_simple
: spec t_simple U8.t true
= {
  serializable = Cbor.simple_value_wf;
  parser = parser_spec_simple _;
  serializer = serializer_spec_simple _;
  parser_inj = ();
}

let parser_spec_uint (p: U64.t -> bool { forall x . p x }) : parser_spec uint U64.t p =
  (fun x -> let Cbor.CInt64 _ v = Cbor.unpack x in v)

let serializer_spec_uint (p: U64.t -> bool { forall x . p x }) : serializer_spec (parser_spec_uint p) =
  (fun x -> Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_uint64 x))

let spec_uint
: spec uint U64.t true
= {
  serializable = (fun _ -> true);
  parser = parser_spec_uint _;
  serializer = serializer_spec_uint _;
  parser_inj = ();
}

let parser_spec_nint (p: U64.t -> bool { forall x . p x }) : parser_spec nint U64.t p =
  (fun x -> let Cbor.CInt64 _ v = Cbor.unpack x in v)

let serializer_spec_nint (p: U64.t -> bool { forall x . p x }) : serializer_spec (parser_spec_nint p) =
  (fun x -> Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_neg_int64 x))

let spec_nint
: spec nint U64.t true
= {
  serializable = (fun _ -> true);
  parser = parser_spec_nint _;
  serializer = serializer_spec_nint _;
  parser_inj = ();
}

let spec_int_range_uint64
  (lo hi: U64.t)
: spec (t_int_range (U64.v lo) (U64.v hi)) U64.t true
= {
  serializable = (fun x -> U64.lte lo x && U64.lte x hi);
  parser = (fun (x: Cbor.cbor { t_int_range (U64.v lo) (U64.v hi) x }) -> let Cbor.CInt64 ty v = Cbor.unpack x in
    v
  );
  serializer = (fun x -> Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_uint64 x));
  parser_inj = ();
}

module I64 = FStar.Int64

let uint64_to_int64
  (x: U64.t { - pow2 63 <= U64.v x /\ U64.v x < pow2 63 })
: Tot (y: I64.t { I64.v y == U64.v x })
= FStar.Int.Cast.uint64_to_int64 x

let spec_int_range_int64
  (lo hi: I64.t)
: spec (t_int_range (I64.v lo) (I64.v hi)) I64.t true
= {
  serializable = (fun x -> I64.lte lo x && I64.lte x hi);
  parser = (fun (x: Cbor.cbor { t_int_range (I64.v lo) (I64.v hi) x }) -> let Cbor.CInt64 ty v = Cbor.unpack x in
    let w = uint64_to_int64 v in
    if ty = Cbor.cbor_major_type_uint64 then w else ((-1L) `I64.sub` w)
  );
  serializer = (fun (x: I64.t { I64.lte lo x && I64.lte x hi }) ->
    if I64.lt x 0L
    then Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_neg_int64 (FStar.Int.Cast.int64_to_uint64 ((-1L) `I64.sub` x)))
    else Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_uint64 (FStar.Int.Cast.int64_to_uint64 x))
  );
  parser_inj = ();
}

let spec_int_range_neg_int64
  (lo hi: U64.t)
: spec (t_int_range (-1 - U64.v lo) (-1 - U64.v hi)) U64.t true
= {
  serializable = (fun x -> U64.lte hi x && U64.lte x lo);
  parser = (fun (x: Cbor.cbor { t_int_range (-1 - U64.v lo) (-1 - U64.v hi) x }) -> let Cbor.CInt64 ty v = Cbor.unpack x in
    v
  );
  serializer = (fun x -> Cbor.pack (Cbor.CInt64 Cbor.cbor_major_type_neg_int64 x));
  parser_inj = ();
}

let parser_spec_bstr (p: Seq.seq U8.t -> bool { forall x . p x <==> Seq.length x < pow2 64 }) : parser_spec bstr (Seq.seq U8.t) p =
  (fun x -> let Cbor.CString _ v = Cbor.unpack x in v)

let serializer_spec_bstr (p: Seq.seq U8.t -> bool { forall x . p x <==> Seq.length x < pow2 64 }) : serializer_spec (parser_spec_bstr p) =
  (fun x -> Cbor.pack (Cbor.CString Cbor.cbor_major_type_byte_string x))

let spec_bstr
: spec bstr (Seq.seq U8.t) true
= {
  serializable = (fun x -> Seq.length x < pow2 64);
  parser = parser_spec_bstr _;
  serializer = serializer_spec_bstr _;
  parser_inj = ();
}

let parser_spec_tstr (p: Seq.seq U8.t -> bool { forall x . p x <==> (Seq.length x < pow2 64 /\ CBOR.Spec.API.UTF8.correct x) }) : parser_spec tstr (Seq.seq U8.t) p =
  (fun x -> let Cbor.CString _ v = Cbor.unpack x in v)

let serializer_spec_tstr (p: Seq.seq U8.t -> bool { forall x . p x <==> (Seq.length x < pow2 64 /\ CBOR.Spec.API.UTF8.correct x) }) : serializer_spec (parser_spec_tstr p) =
  (fun x -> Cbor.pack (Cbor.CString Cbor.cbor_major_type_text_string x))

let spec_tstr
: spec tstr (Seq.seq U8.t) true
= {
  serializable = (fun x -> Seq.length x < pow2 64 && CBOR.Spec.API.UTF8.correct x);
  parser = parser_spec_tstr _;
  serializer = serializer_spec_tstr _;
  parser_inj = ();
}
