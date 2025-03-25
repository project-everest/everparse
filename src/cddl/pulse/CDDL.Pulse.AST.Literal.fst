module CDDL.Pulse.AST.Literal
#lang-pulse
include CDDL.Pulse.Misc
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module AST = CDDL.Spec.AST.Base
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

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
        SZ.v i + List.Tot.length l <= Seq.length v
      )
    )
    (fun res ->
      pts_to s #p v **
      pure (
        SZ.v i + List.Tot.length l <= Seq.length v /\
        (res == true <==> Seq.equal
          (Seq.slice v (SZ.v i) (SZ.v i + List.Tot.length l))
          (Seq.seq_of_list (AST.byte_list_of_char_list l))
        )
      )
    )

inline_for_extraction
fn slice_u8_eq_list_ascii_char_nil (_: unit) : slice_u8_eq_list_ascii_char_t []
= (s: _)
  (i: _)
  (#p: _)
  (#v: _)
  {
    true
  }

let list_map_cons
  (#t #t': Type)
  (f: t -> t')
  (a: t)
  (q: list t)
: Lemma
  (List.Tot.map f (a :: q) == f a :: List.Tot.map f q)
= ()

inline_for_extraction
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

[@@AST.base_attr]
let rec slice_u8_eq_list_ascii_char
  (l: list FStar.Char.char)
  (sq: squash (List.Tot.for_all AST.char_is_ascii l))
: Tot (slice_u8_eq_list_ascii_char_t l)
= match l with
  | [] -> slice_u8_eq_list_ascii_char_nil ()
  | a :: q -> slice_u8_eq_list_ascii_char_cons a (AST.uint32_to_uint8 (AST.u32_of_char a)) () q (slice_u8_eq_list_ascii_char q ())

inline_for_extraction noextract
let slice_u8_eq_ascii_string_t
  (x: string)
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

[@@AST.base_attr]
let slice_u8_eq_ascii_string
  (x: AST.ascii_string)
: Tot (slice_u8_eq_ascii_string_t x)
= slice_u8_eq_ascii_string_intro x (slice_u8_eq_list_ascii_char (FStar.String.list_of_string x) ())

inline_for_extraction
fn impl_string_literal
  (#ty: Type0)
  (vmatch: (perm -> ty -> cbor -> slprop))
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_get_string: get_string_t vmatch)
  (s: Ghost.erased AST.ascii_string)
  (len: U64.t { String.length s == U64.v len })
  (f: slice_u8_eq_ascii_string_t s)
: impl_typ u#0 #_ vmatch #None (t_literal (pack (CString cbor_major_type_text_string (AST.byte_seq_of_ascii_string s))))
= (c: ty)
  (#p: perm)
  (#v: Ghost.erased cbor)
{
  assume (pure (SZ.fits_u64));
  let test = impl_text cbor_get_major_type c;
  if (test) {
    let s = cbor_get_string c;
    S.pts_to_len s;
    if (S.len s <> SZ.uint64_to_sizet len) {
      Trade.elim _ _;
      false
    } else {
      with ps vs . assert (pts_to s #ps vs);
      Seq.slice_length vs;
      let res = f s 0sz;
      Trade.elim _ _;
      res
    }
  } else {
    false
  }
}

[@@AST.base_attr]
let string_length
  (x: string)
: Tot nat
= List.Tot.length (String.list_of_string x)

[@@AST.base_attr]
let impl_literal
  (#ty: Type0)
  (vmatch: (perm -> ty -> cbor -> slprop))
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_destr_int64: read_uint64_t vmatch)
  (cbor_get_string: get_string_t vmatch)
  (cbor_destr_simple: read_simple_value_t vmatch)
  (l: AST.literal { AST.wf_literal l })
: Tot (impl_typ vmatch (AST.spec_type_of_literal l))
= match l with
  | AST.LTextString s ->
    impl_string_literal vmatch cbor_get_major_type cbor_get_string s (U64.uint_to_t (string_length s)) (slice_u8_eq_ascii_string s)
  | AST.LInt n ->
    if n >= 0
    then impl_uint_literal cbor_get_major_type cbor_destr_int64 (U64.uint_to_t n) 
    else impl_neg_int_literal cbor_get_major_type cbor_destr_int64 (U64.uint_to_t ((-1) - n))
  | AST.LSimple n ->
    impl_simple_literal cbor_get_major_type cbor_destr_simple (U8.uint_to_t n)

inline_for_extraction noextract
let slice_u8_fill_list_ascii_char_t
  (l: list FStar.Char.char)
: Tot Type
= (s: S.slice U8.t) ->
  (i: SZ.t) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt unit
    (pts_to s v **
      pure (
        SZ.v i + List.Tot.length l == Seq.length v
      )
    )
    (fun res -> exists* v' .
      pts_to s v' **
      pure (
        SZ.v i + List.Tot.length l == Seq.length v /\
        Seq.length v' == Seq.length v /\
        Seq.equal v' (Seq.append (Seq.slice v 0 (SZ.v i)) (Seq.seq_of_list (AST.byte_list_of_char_list l)))
      )
    )

inline_for_extraction
fn slice_u8_fill_list_ascii_char_nil (_: unit) : slice_u8_fill_list_ascii_char_t []
= (s: _)
  (i: _)
  (#v: _)
  {
    ()
  }

inline_for_extraction
fn slice_u8_fill_list_ascii_char_cons (a: FStar.Char.char) (a' : U8.t) (sq: squash (a' == AST.uint32_to_uint8 (AST.u32_of_char a) /\ AST.char_is_ascii a)) (q: list FStar.Char.char) (f: slice_u8_fill_list_ascii_char_t q) : slice_u8_fill_list_ascii_char_t (a :: q)
= (s: _)
  (i: _)
  (#v: _)
  {
    S.pts_to_len s;
    S.op_Array_Assignment s i a';
    let i' = SZ.add i 1sz;
    f s i'
  }

[@@AST.base_attr]
let rec slice_u8_fill_list_ascii_char
  (l: list FStar.Char.char)
  (sq: squash (List.Tot.for_all AST.char_is_ascii l))
: Tot (slice_u8_fill_list_ascii_char_t l)
= match l with
  | [] -> slice_u8_fill_list_ascii_char_nil ()
  | a :: q -> slice_u8_fill_list_ascii_char_cons a (AST.uint32_to_uint8 (AST.u32_of_char a)) () q (slice_u8_fill_list_ascii_char q ())

inline_for_extraction noextract
let slice_u8_fill_ascii_string_t
  (x: string)
: Tot Type
= (s: S.slice U8.t) ->
  stt unit
    (exists* v . pts_to s v **
      pure (
        FStar.String.length x == Seq.length v
      )
    )
    (fun res ->
      pts_to s (AST.byte_seq_of_ascii_string x)
    )

inline_for_extraction noextract
fn slice_u8_fill_ascii_string_intro
  (x: AST.ascii_string)
  (f: slice_u8_fill_list_ascii_char_t (FStar.String.list_of_string x))
: slice_u8_fill_ascii_string_t x
= (s: S.slice U8.t)
{
  f s 0sz;
  with v' . assert (pts_to s v');
  assert (pure (Seq.equal v' (AST.byte_seq_of_ascii_string x)));
  rewrite (pts_to s v') as (pts_to s (AST.byte_seq_of_ascii_string x))
}

[@@AST.base_attr]
let slice_u8_fill_ascii_string
  (x: AST.ascii_string)
: Tot (slice_u8_fill_ascii_string_t x)
= slice_u8_fill_ascii_string_intro x (slice_u8_fill_list_ascii_char (FStar.String.list_of_string x) ())

inline_for_extraction
fn with_cbor_literal_text_string
  (#ty: Type0)
  (#vmatch: (perm -> ty -> cbor -> slprop))
  (cbor_mk_string: mk_string_t vmatch)
  (str: Ghost.erased AST.ascii_string)
  (len: U64.t { String.length str == U64.v len })
  (f: slice_u8_fill_ascii_string_t str)
: with_cbor_literal_t #_ vmatch (pack (CString cbor_major_type_text_string (AST.byte_seq_of_ascii_string str)))
= (pre: _)
  (t': _)
  (post: _)
  (cont: _)
{
  assume (pure (SZ.fits_u64));
  let mut a = [| 0uy; SZ.uint64_to_sizet len |]; // I cannot use `len_sz` here because of non-constant-size C stack arrays; `inline_let` would solve that
  let len_sz = SZ.uint64_to_sizet len;
  let s = S.from_array a len_sz;
  f s;
  let c = cbor_mk_string cbor_major_type_text_string s;
  with z . assert (vmatch 1.0R c z);
  Trade.rewrite_with_trade (vmatch 1.0R c z) (vmatch 1.0R c (pack (CString cbor_major_type_text_string (AST.byte_seq_of_ascii_string str))));
  Trade.trans _ (vmatch 1.0R c z) _;
  let res = cont _ c;
  Trade.elim _ _;
  S.to_array s;
  res
}

[@@AST.base_attr]
let with_literal
  (#ty: Type0)
  (#vmatch: (perm -> ty -> cbor -> slprop))
  (mk_int64: mk_int64_t vmatch)
  (elim_int64: elim_int64_t vmatch)
  (mk_simple: mk_simple_t vmatch)
  (elim_simple: elim_simple_t vmatch)
  (cbor_mk_string: mk_string_t vmatch)
  (l: AST.literal { AST.wf_literal l })
: Tot (with_cbor_literal_t vmatch (AST.eval_literal l))
= match l with
  | AST.LTextString s ->
    with_cbor_literal_text_string cbor_mk_string s (U64.uint_to_t (string_length s)) (slice_u8_fill_ascii_string s)
  | AST.LInt n ->
    if n >= 0
    then with_cbor_literal_int mk_int64 elim_int64 cbor_major_type_uint64 (U64.uint_to_t n) 
    else with_cbor_literal_int mk_int64 elim_int64 cbor_major_type_neg_int64 (U64.uint_to_t ((-1) - n))
  | AST.LSimple n ->
    with_cbor_literal_simple mk_simple elim_simple (U8.uint_to_t n)
