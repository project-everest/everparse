module CDDL.Pulse.AST.Literal
include CDDL.Pulse.Misc
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module AST = CDDL.Spec.AST.Base
module U8 = FStar.UInt8
module U32 = FStar.UInt32
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

[@@AST.sem_attr]
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

[@@AST.sem_attr]
let slice_u8_eq_ascii_string
  (x: AST.ascii_string)
: Tot (slice_u8_eq_ascii_string_t x)
= slice_u8_eq_ascii_string_intro x (slice_u8_eq_list_ascii_char (FStar.String.list_of_string x) ())
