module CDDL.Pulse.Misc
include CDDL.Spec.Misc
include CDDL.Pulse.Base
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module AST = CDDL.Spec.AST.Base

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_uint
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
: impl_typ u#0 #ty vmatch #None uint
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    (mt = cbor_major_type_uint64)
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_neg_int
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
: impl_typ u#0 #ty vmatch #None nint
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    (mt = cbor_major_type_neg_int64)
}
```

module U64 = FStar.UInt64

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_uint_literal
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_int64: read_uint64_t vmatch)
    (n: U64.t)
: impl_typ u#0 #ty vmatch #None (t_uint_literal n)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let is_uint = impl_uint cbor_get_major_type c;
    if (is_uint) {
        let i = cbor_destr_int64 c;
        (i = n)
    } else {
        false
    }
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_neg_int_literal
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_int64: read_uint64_t vmatch)
    (n: U64.t)
: impl_typ u#0 #ty vmatch #None (t_literal (pack (CInt64 cbor_major_type_neg_int64 n)))
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let is_uint = impl_neg_int cbor_get_major_type c;
    if (is_uint) {
        let i = cbor_destr_int64 c;
        (i = n)
    } else {
        false
    }
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_bytes
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
: impl_typ u#0 #ty vmatch #None bytes
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    (mt = cbor_major_type_byte_string)
}
```

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_str_size
    (#t: Type u#0)
    (#vmatch: perm -> t -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_string: get_string_t vmatch)
    (ty: major_type_byte_string_or_text_string)
    (lo hi: SZ.t)
: impl_typ u#0 #t vmatch #None (str_size ty (SZ.v lo) (SZ.v hi))
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    if (mt = ty) {
        let str = cbor_destr_string c;
        S.pts_to_len str;
        let len = S.len str;
        Trade.elim _ _;
        let z = (lo `SZ.lte` len && len `SZ.lte` hi);
        z
    } else {
        false
    }
}
```

module U8 = FStar.UInt8

inline_for_extraction noextract
let slice_u8_eq_list_ascii_char_t
  (l: list FStar.Char.char)
: Tot Type
= (s: S.slice U8.t) ->
  (i: SZ.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (pts_to s #p v **
      pure (
        SZ.v i + List.Tot.length l <= Seq.length v /\
True //        List.Tot.for_all AST.char_is_ascii l
      )
    )
    (fun res ->
      pts_to s #p v **
      pure (
        SZ.v i + List.Tot.length l <= Seq.length v /\
True /\ //        List.Tot.for_all AST.char_is_ascii l /\
        (res == true <==> Seq.equal
          (Seq.slice v (SZ.v i) (SZ.v i + List.Tot.length l))
          (Seq.seq_of_list (AST.byte_list_of_char_list l))
        )
      )
    )

inline_for_extraction
```pulse
fn slice_u8_eq_list_ascii_char_nil (_: unit) : slice_u8_eq_list_ascii_char_t []
= (s: _)
  (i: _)
  (#p: _)
  (#v: _)
  {
    true
  }
```

let list_map_cons
  (#t #t': Type)
  (f: t -> t')
  (a: t)
  (q: list t)
: Lemma
  (List.Tot.map f (a :: q) == f a :: List.Tot.map f q)
= ()

module U32 = FStar.UInt32

inline_for_extraction
```pulse
fn slice_u8_eq_list_ascii_char_cons (a: FStar.Char.char) (a' : U8.t) (sq: squash (a' == AST.uint32_to_uint8 (AST.u32_of_char a) /\ AST.char_is_ascii a)) (q: list FStar.Char.char) (f: slice_u8_eq_list_ascii_char_t q) : slice_u8_eq_list_ascii_char_t (a :: q)
= (s: _)
  (i: _)
  (#p: _)
  (#v: _)
  {
    S.pts_to_len s;
    FStar.Math.Lemmas.small_mod (FStar.UInt32.v (AST.u32_of_char a)) 256;
    Seq.lemma_seq_of_list_cons (a' <: U8.t) (AST.byte_list_of_char_list q);
    list_map_cons AST.u32_of_char a q;
    list_map_cons AST.uint32_to_uint8 (AST.u32_of_char a) (List.Tot.map AST.u32_of_char q);
    assert (pure (AST.byte_list_of_char_list (a :: q) == AST.uint32_to_uint8 (AST.u32_of_char a) :: AST.byte_list_of_char_list q));
    assert (pure (AST.byte_list_of_char_list (a :: q) == a' :: AST.byte_list_of_char_list q));
    assert (pure (Seq.equal (Seq.seq_of_list (AST.byte_list_of_char_list (a :: q))) (Seq.cons a' (Seq.seq_of_list (AST.byte_list_of_char_list q)))));
    let x = S.op_Array_Access s i;
    let i' = SZ.add i 1sz;
    assert (pure (Seq.equal (Seq.slice v (SZ.v i) (SZ.v i + List.Tot.length (a :: q))) (Seq.cons x (Seq.slice v (SZ.v i') (SZ.v i' + List.Tot.length q)))));
    Classical.move_requires (Seq.lemma_cons_inj x a' (Seq.slice v (SZ.v i') (SZ.v i' + List.Tot.length q))) (Seq.seq_of_list (AST.byte_list_of_char_list q));
    if (x = a') {
      f s i'
    } else {
      false
    }
  }
```

let rec slice_u8_eq_list_ascii_char
  (l: list FStar.Char.char)
  (sq: squash (List.Tot.for_all AST.char_is_ascii l))
: Tot (slice_u8_eq_list_ascii_char_t l)
= match l with
  | [] -> slice_u8_eq_list_ascii_char_nil ()
  | a :: q -> slice_u8_eq_list_ascii_char_cons a (AST.uint32_to_uint8 (AST.u32_of_char a)) () q (slice_u8_eq_list_ascii_char q ())

inline_for_extraction noextract
let slice_u8_eq_ascii_string_t
  (x: AST.ascii_string)
: Tot Type
= (s: S.slice U8.t) ->
  (i: SZ.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (pts_to s #p v **
      pure (
        SZ.v i + FStar.String.length x <= Seq.length v
      )
    )
    (fun res ->
      pts_to s #p v **
      pure (
        SZ.v i + FStar.String.length x <= Seq.length v /\
        (res == true <==> Seq.equal
          (Seq.slice v (SZ.v i) (SZ.v i + FStar.String.length x))
          (AST.byte_seq_of_ascii_string x)
        )
      )
    )

inline_for_extraction noextract
```pulse
fn slice_u8_eq_ascii_string_intro
  (x: AST.ascii_string)
  (f: slice_u8_eq_list_ascii_char_t (FStar.String.list_of_string x))
: slice_u8_eq_ascii_string_t x
= (s: S.slice U8.t)
  (i: SZ.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  f s i
}
```

let slice_u8_eq_ascii_string
  (x: AST.ascii_string)
: Tot (slice_u8_eq_ascii_string_t x)
= slice_u8_eq_ascii_string_intro x (slice_u8_eq_list_ascii_char (FStar.String.list_of_string x) ())
