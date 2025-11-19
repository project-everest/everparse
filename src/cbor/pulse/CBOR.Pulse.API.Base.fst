module CBOR.Pulse.API.Base
#lang-pulse
open CBOR.Spec.API.Type
open Pulse.Lib.Pervasives
module T = CBOR.Spec.API.Type
module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module PM = Pulse.Lib.SeqMatch

(** Destructors *)

let cbor_major_type (c: cbor) : Tot T.major_type_t =
  match unpack c with
  | CSimple _ -> cbor_major_type_simple_value
  | CInt64 ty _
  | CString ty _ -> ty
  | CArray _ -> cbor_major_type_array
  | CMap _ -> cbor_major_type_map
  | CTagged _ _ -> cbor_major_type_tagged

inline_for_extraction
let equal_for_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (v1: cbor)
= (x2: t) ->
  (#p2: perm) ->
  (#v2: Ghost.erased cbor) ->
  stt bool
    (vmatch p2 x2 v2)
    (fun res -> vmatch p2 x2 v2 ** pure (res == (v1 = Ghost.reveal v2)))

inline_for_extraction
let equal_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x1: t) ->
  (x2: t) ->
  (#p1: perm) ->
  (#p2: perm) ->
  (#v1: Ghost.erased cbor) ->
  (#v2: Ghost.erased cbor) ->
  stt bool
    (vmatch p1 x1 v1 ** vmatch p2 x2 v2)
    (fun res -> vmatch p1 x1 v1 ** vmatch p2 x2 v2 ** pure (res == true <==> (Ghost.reveal v1 == Ghost.reveal v2)))

inline_for_extraction
let ghost_get_size_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (vmatch_with_size: nat -> perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#x': cbor) ->
  stt_ghost unit emp_inames
    (vmatch p x x')
    (fun _ -> exists* p' v . vmatch_with_size v p' x x' **
      Trade.trade
        (vmatch_with_size v p' x x')
        (vmatch p x x')
    )

inline_for_extraction
let get_size_t
  (#t: Type)
  (vmatch_with_size: nat -> perm -> t -> cbor -> slprop)
= (x: t) ->
  (bound: SZ.t) ->
  (#p: perm) ->
  (#x': Ghost.erased cbor) ->
  (#v: Ghost.erased nat) ->
  stt SZ.t
    (vmatch_with_size v p x x')
    (fun res -> vmatch_with_size v p x x' ** pure (
      (SZ.v res = 0 <==> Ghost.reveal v > SZ.v bound) /\
      (SZ.v res > 0 ==> Ghost.reveal v == SZ.v res)
    ))

inline_for_extraction
let ignore_size_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (vmatch_with_size: nat -> perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#x': cbor) ->
  (#v: nat) ->
  stt_ghost unit emp_inames
    (vmatch_with_size v p x x')
    (fun _ -> exists* p' . vmatch p' x x' **
      Trade.trade
        (vmatch p' x x')
        (vmatch_with_size v p x x')
    )

inline_for_extraction
let get_major_type_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt T.major_type_t
    (vmatch p x y)
    (fun res -> vmatch p x y ** pure (res == cbor_major_type y))

inline_for_extraction
let read_simple_value_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt T.simple_value
    (vmatch p x y ** pure (CSimple? (unpack y)))
    (fun res -> vmatch p x y ** pure (unpack y == CSimple res))

inline_for_extraction
let elim_simple_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: cbor) ->
  stt_ghost unit emp_inames
    (vmatch p x y ** pure (CSimple? (unpack y)))
    (fun _ -> emp)

let read_uint64_post
  (y: cbor)
  (res: FStar.UInt64.t)
: Tot prop
= match unpack y with
    | CInt64 _ v -> res == v
    | _ -> False

inline_for_extraction
let read_uint64_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt FStar.UInt64.t
    (vmatch p x y ** pure (CInt64? (unpack y)))
    (fun res -> vmatch p x y ** pure (read_uint64_post y res))

inline_for_extraction
let elim_int64_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: cbor) ->
  stt_ghost unit emp_inames
    (vmatch p x y ** pure (CInt64? (unpack y)))
    (fun _ -> emp)

let get_string_length_post
  (y: cbor)
  (v' : U64.t)
: Tot prop
= match unpack y with
      | CString _ v -> Seq.length v == U64.v v'
      | _ -> False

inline_for_extraction
let get_string_length_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt U64.t
    (vmatch p x y ** pure (CString? (unpack y)))
    (fun res ->
      vmatch p x y ** 
      pure (get_string_length_post y res)
    )

let get_string_post
  (y: cbor)
  (v' : Seq.seq FStar.UInt8.t)
: Tot prop
= match unpack y with
      | CString _ v -> v == v'
      | _ -> False

inline_for_extraction
let get_string_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt (S.slice FStar.UInt8.t)
    (vmatch p x y ** pure (CString? (unpack y)))
    (fun res -> exists* p' v' .
      pts_to res #p' v' **
      Trade.trade
        (pts_to res #p' v')
        (vmatch p x y) **
      pure (get_string_post y v')
    )

let get_tagged_tag_post
  (y: cbor)
  (res: FStar.UInt64.t)
: Tot prop
= match unpack y with
    | CTagged tag _ -> res == tag
    | _ -> False

inline_for_extraction
let get_tagged_tag_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt FStar.UInt64.t
    (vmatch p x y ** pure (CTagged? (unpack y)))
    (fun res -> vmatch p x y ** pure (
      get_tagged_tag_post y res
    ))

let get_tagged_payload_post
  (y: cbor)
  (v' : cbor)
: Tot prop
= match unpack y with
      | CTagged _ v -> v == v'
      | _ -> False

inline_for_extraction
let get_tagged_payload_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt t
    (vmatch p x y ** pure (CTagged? (unpack y)))
    (fun res -> exists* p' v' .
      vmatch p' res v' **
      Trade.trade
        (vmatch p' res v')
        (vmatch p x y) **
      pure (get_tagged_payload_post y v')
    )

let get_array_length_post
  (y: cbor)
  (res: FStar.UInt64.t)
: Tot prop
= match unpack y with
      | CArray v -> FStar.UInt64.v res == List.Tot.length v
      | _ -> False

inline_for_extraction
let get_array_length_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt FStar.UInt64.t
    (vmatch p x y ** pure (CArray? (unpack y)))
    (fun res -> vmatch p x y ** pure (
       get_array_length_post y res
      )
    )

let get_array_item_pre
  (i: FStar.UInt64.t)
  (y: cbor)
: Tot prop
= match unpack y with
    | CArray v -> U64.v i < List.Tot.length v
    | _ -> False

let get_array_item_post
  (i: FStar.UInt64.t)
  (y: cbor)
  (y' : cbor)
: Tot prop
= match unpack y with
      | CArray v -> U64.v i < List.Tot.length v /\
        List.Tot.index v (U64.v i) == y'
      | _ -> False

inline_for_extraction
let get_array_item_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (i: FStar.UInt64.t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt t
    (vmatch p x y ** pure (get_array_item_pre i y))
    (fun res -> exists* p' y' .
      vmatch p' res y' **
      Trade.trade (vmatch p' res y') (vmatch p x y) **
      pure (get_array_item_post i y y')
    )

inline_for_extraction
let array_iterator_start_t
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt t'
    (vmatch p x y ** pure (CArray? (unpack y)))
    (fun res -> exists* p' l' .
      iter p' res l' **
      Trade.trade
        (iter p' res l')
        (vmatch p x y) **
      pure (
        unpack y == CArray l'
    ))

inline_for_extraction
let array_iterator_is_empty_t
  (#t': Type)
  (iter: perm -> t' -> list cbor -> slprop)
= (x: t') ->
  (#p: perm) ->
  (#y: Ghost.erased (list cbor)) ->
  stt bool
    (iter p x y)
    (fun res -> iter p x y ** pure (res == Nil? y))

inline_for_extraction
let array_iterator_length_t
  (#t': Type)
  (iter: perm -> t' -> list cbor -> slprop)
= (x: t') ->
  (#p: perm) ->
  (#y: Ghost.erased (list cbor)) ->
  stt U64.t
    (iter p x y)
    (fun res -> iter p x y ** pure (U64.v res == List.Tot.length y))

inline_for_extraction
let array_iterator_next_t
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list cbor -> slprop)
= (x: R.ref t') ->
  (#y: Ghost.erased t') ->
  (#py: perm) ->
  (#z: Ghost.erased (list cbor)) ->
  stt t
    (R.pts_to x y ** iter py y z ** pure (Cons? z))
    (fun res -> exists* p' v' y' z' .
      vmatch p' res v' **
      R.pts_to x y' **
      iter py y' z' **
      Trade.trade
        (vmatch p' res v' ** iter py y' z')
        (iter py y z) **
      pure (Ghost.reveal z == v' :: z')
    )

inline_for_extraction
let array_iterator_truncate_t
  (#t': Type)
  (iter: perm -> t' -> list cbor -> slprop)
= (x: t') ->
  (len: U64.t) ->
  (#p: perm) ->
  (#y: Ghost.erased (list cbor)) ->
  stt t'
    (iter p x y **
      pure (U64.v len <= List.Tot.length y)
    )
    (fun res ->
      iter 1.0R res (fst (List.Tot.splitAt (U64.v len) y)) **
      Trade.trade
        (iter 1.0R res (fst (List.Tot.splitAt (U64.v len) y)))
        (iter p x y)
    )

inline_for_extraction
let array_iterator_get_length_t
  (#t': Type)
  (iter: perm -> t' -> list cbor -> slprop)
= (x: t') ->
  (#p: perm) ->
  (#y: Ghost.erased (list cbor)) ->
  stt U64.t
    (iter p x y)
    (fun res ->
      iter p x y **
      pure (U64.v res == List.Tot.length y)
    )

let get_map_length_post
  (y: cbor)
  (res: FStar.UInt64.t)
: Tot prop
= match unpack y with
      | CMap v -> FStar.UInt64.v res == cbor_map_length v
      | _ -> False

inline_for_extraction
let get_map_length_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt FStar.UInt64.t
    (vmatch p x y ** pure (CMap? (unpack y)))
    (fun res -> vmatch p x y ** pure (
       get_map_length_post y res
      )
    )

let map_iterator_start_post
  (y: cbor)
  (l' : list (cbor & cbor))
: Tot prop
= match unpack y with
      | CMap l -> (forall k . cbor_map_get l k == List.Tot.assoc k l') /\
        List.Tot.length l' == cbor_map_length l /\
        List.Tot.no_repeats_p (List.Tot.map fst l')
      | _ -> False

inline_for_extraction
let map_iterator_start_t
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt t'
    (vmatch p x y ** pure (CMap? (unpack y)))
    (fun res -> exists* p' l' .
      iter p' res l' **
      Trade.trade
        (iter p' res l')
        (vmatch p x y) **
      pure (
        map_iterator_start_post y l'
    ))

inline_for_extraction
let map_iterator_is_empty_t
  (#t': Type)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
= (x: t') ->
  (#p: perm) ->
  (#y: Ghost.erased (list (cbor & cbor))) ->
  stt bool
    (iter p x y)
    (fun res -> iter p x y ** pure (res == Nil? y))

inline_for_extraction
let map_iterator_next_t
  (#t #t': Type)
  (vmatch2: perm -> t -> cbor & cbor -> slprop)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
= (x: R.ref t') ->
  (#y: Ghost.erased t') ->
  (#py: perm) ->
  (#z: Ghost.erased (list (cbor & cbor))) ->
  stt t
    (R.pts_to x y ** iter py y z ** pure (Cons? z))
    (fun res -> exists* p' v' y' z' .
      vmatch2 p' res v' **
      R.pts_to x y' **
      iter py y' z' **
      Trade.trade
        (vmatch2 p' res v' ** iter py y' z')
        (iter py y z) **
      pure (Ghost.reveal z == v' :: z')
    )

inline_for_extraction
let map_entry_key_t
  (#t2 #t: Type)
  (vmatch2: perm -> t2 -> cbor & cbor -> slprop)
  (vmatch: perm -> t -> cbor -> slprop)
= (x2: t2) ->
  (#p: perm) ->
  (#v2: Ghost.erased (cbor & cbor)) ->
  stt t
    (vmatch2 p x2 v2)
    (fun res -> exists* p' .
      vmatch p' res (fst v2) **
      Trade.trade (vmatch p' res (fst v2)) (vmatch2 p x2 v2)
    )

inline_for_extraction
let map_entry_value_t
  (#t2 #t: Type)
  (vmatch2: perm -> t2 -> cbor & cbor -> slprop)
  (vmatch: perm -> t -> cbor -> slprop)
= (x2: t2) ->
  (#p: perm) ->
  (#v2: Ghost.erased (cbor & cbor)) ->
  stt t
    (vmatch2 p x2 v2)
    (fun res -> exists* p' .
      vmatch p' res (snd v2) **
      Trade.trade (vmatch p' res (snd v2)) (vmatch2 p x2 v2)
    )

(** Permissions *)

inline_for_extraction
let share_t
  (#t1 #t2: Type)
  (vmatch: perm -> t1 -> t2 -> slprop)
=
  (x1: t1) ->
  (#p: perm) ->
  (#x2: t2) ->
  stt_ghost unit emp_inames
  (vmatch p x1 x2)
  (fun _ ->
    let open FStar.Real in
    vmatch (p /. 2.0R) x1 x2 ** vmatch (p /. 2.0R) x1 x2
  )

inline_for_extraction
let gather_t
  (#t1 #t2: Type)
  (vmatch: perm -> t1 -> t2 -> slprop)
=
  (x1: t1) ->
  (#p: perm) ->
  (#x2: t2) ->
  (#p': perm) ->
  (#x2': t2) ->
  stt_ghost unit emp_inames
  (vmatch p x1 x2 ** vmatch p' x1 x2')
  (fun _ ->
    let open FStar.Real in
    vmatch (p +. p') x1 x2 **
    pure (x2 == x2')
  )

inline_for_extraction
let reset_perm_t
  (#t1 #t2: Type)
  (vmatch: perm -> t1 -> t2 -> slprop)
=
  (x1: t1) ->
  (#p: perm) ->
  (#x2: Ghost.erased t2) ->
  stt t1
    (vmatch p x1 x2)
    (fun res -> vmatch 1.0R res x2 **
      Trade.trade (vmatch 1.0R res x2) (vmatch p x1 x2)
    )

(** Constructors *)

inline_for_extraction
let mk_simple_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
=
  (v: simple_value) ->
  stt t
    (emp)
    (fun res -> vmatch 1.0R res (pack (CSimple v)))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_simple_value_trade
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (cbor_mk_simple: mk_simple_t vmatch)
  (cbor_elim_simple: elim_simple_t vmatch)
  (v: simple_value)
requires emp
returns res: t
ensures
    vmatch 1.0R res (pack (CSimple v)) **
    Trade.trade
      (vmatch 1.0R res (pack (CSimple v)))
      emp
{
  let res = cbor_mk_simple v;
  intro
    (Trade.trade
      (vmatch 1.0R res (pack (CSimple v)))
      emp
    )
    #emp
    fn _
  {
    cbor_elim_simple res
  };
  res
}

inline_for_extraction
let mk_int64_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (ty: major_type_uint64_or_neg_int64) ->
  (v: U64.t) ->
  stt t
    (emp)
    (fun res -> vmatch 1.0R res (pack (CInt64 ty v)))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_int64_trade
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
  (ty: major_type_uint64_or_neg_int64)
  (v: U64.t)
requires emp
returns res: t
ensures
    vmatch 1.0R res (pack (CInt64 ty v)) **
    Trade.trade
      (vmatch 1.0R res (pack (CInt64 ty v)))
      emp
{
  let res = cbor_mk_int64 ty v;
  intro
    (Trade.trade
      (vmatch 1.0R res (pack (CInt64 ty v)))
      emp
    )
    #emp
    fn _
  {
    cbor_elim_int64 res
  };
  res
}

inline_for_extraction
let impl_utf8_correct_t =
  (s: S.slice U8.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (pts_to s #p v)
    (fun res -> pts_to s #p v ** pure (res == CBOR.Spec.API.UTF8.correct v))

inline_for_extraction
let mk_string_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (ty: major_type_byte_string_or_text_string) ->
  (s: S.slice U8.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt t
    (pts_to s #p v ** pure (
      FStar.UInt.fits (Seq.length v) 64 /\
      (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v)
    ))
    (fun res -> exists* v' .
      vmatch 1.0R res (pack (CString ty v')) **
      Trade.trade
        (vmatch 1.0R res (pack (CString ty v')))
        (pts_to s #p v) **
      pure (v' == Ghost.reveal v)
    )

module A = Pulse.Lib.Array
module AP = Pulse.Lib.ArrayPtr

inline_for_extraction
noextract [@@noextract_to "krml"]
let mk_string_from_array_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
=
  (ty: major_type_byte_string_or_text_string) ->
  (a: A.array U8.t) ->
  (len: U64.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt t
    (pts_to a #p v ** pure (
      Seq.length v == U64.v len /\
      (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v)
    ))
    (fun res -> exists* v' .
      vmatch 1.0R res v' **
      Trade.trade
        (vmatch 1.0R res v')
        (pts_to a #p v) **
      pure (
        CString? (unpack v') /\
        CString?.typ (unpack v') == ty /\
        Ghost.reveal v == CString?.v (unpack v')
      )
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_string_from_array
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_string: mk_string_t vmatch)
: mk_string_from_array_t u#0 #_ vmatch
=
  (ty: major_type_byte_string_or_text_string)
  (a: A.array U8.t)
  (len: U64.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  A.pts_to_len a;
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
  let s = S.from_array a (SZ.uint64_to_sizet len);
  intro
    (Trade.trade
      (pts_to s #p v)
      (A.pts_to a #p v)
    )
    #(S.is_from_array a s)
    fn _
  {
    S.to_array s;
  };
  S.pts_to_len s;
  let res = mk_string ty s;
  with p' v' . assert (vmatch p' res (pack (CString ty v')));
  Trade.trans (vmatch p' res (pack (CString ty v'))) _ _;
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
let mk_string_from_arrayptr_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
=
  (ty: major_type_byte_string_or_text_string) ->
  (a: AP.ptr U8.t) ->
  (len: U64.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt t
    (pts_to a #p v ** pure (
      Seq.length v == U64.v len /\
      (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v)
    ))
    (fun res -> exists* v' .
      vmatch 1.0R res v' **
      Trade.trade
        (vmatch 1.0R res v')
        (pts_to a #p v) **
      pure (
        CString? (unpack v') /\
        CString?.typ (unpack v') == ty /\
        Ghost.reveal v == CString?.v (unpack v')
      )
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_string_from_arrayptr
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_string: mk_string_t vmatch)
: mk_string_from_arrayptr_t u#0 #_ vmatch
=
  (ty: major_type_byte_string_or_text_string)
  (a: AP.ptr U8.t)
  (len: U64.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
  let s = S.arrayptr_to_slice_intro_trade a (SZ.uint64_to_sizet len);
  S.pts_to_len s;
  let res = mk_string ty s;
  with p' v' . assert (vmatch p' res (pack (CString ty v')));
  Trade.trans (vmatch p' res (pack (CString ty v'))) _ _;
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_string_from_slice
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_string: mk_string_from_arrayptr_t vmatch)
: mk_string_t u#0 #_ vmatch
=
  (ty: major_type_byte_string_or_text_string)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len s;
  let a = S.slice_to_arrayptr_intro_trade s;
  let res = mk_string ty a (SZ.sizet_to_uint64 (S.len s));
  Trade.trans _ _ (S.pts_to s #p v);
  with v' . assert (vmatch 1.0R res v');
  Trade.rewrite_with_trade
    (vmatch 1.0R res v')
    (vmatch 1.0R res (pack (CString ty v)));
  Trade.trans _ _ (S.pts_to s #p v);
  res
}

inline_for_extraction
let mk_tagged_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (tag: U64.t) ->
  (r: R.ref t) ->
  (#pr: perm) ->
  (#v: Ghost.erased t) ->
  (#pv: perm) ->
  (#v': Ghost.erased cbor) ->
  stt t
    (R.pts_to r #pr v ** vmatch pv v v')
    (fun res ->
      vmatch 1.0R res (pack (CTagged tag v')) **
      Trade.trade
        (vmatch 1.0R res (pack (CTagged tag v')))
        (R.pts_to r #pr v ** vmatch pv v v')
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
let mk_array_from_array_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
=
  (a: A.array t) ->
  (len: U64.t) ->
  (#pa: perm) ->
  (#va: Ghost.erased (Seq.seq t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list cbor)) ->
  stt t
    (A.pts_to a #pa va **
      PM.seq_list_match va vv (vmatch pv) **
      pure (A.length a == U64.v len)
    )
    (fun res -> exists* v' .
      vmatch 1.0R res v' **
      Trade.trade
        (vmatch 1.0R res v')
        (A.pts_to a #pa va **
          PM.seq_list_match va vv (vmatch pv)
        ) **
        pure (
          CArray? (unpack v') /\
          Ghost.reveal vv == CArray?.v (unpack v')
        )
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_array_from_array'
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_array_from_array: mk_array_from_array_t vmatch)
  (a: A.array t)
  (len: U64.t)
  (va0: Ghost.erased (Seq.seq t))
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq t))
  (#pv: perm)
  (#vv: Ghost.erased (list cbor))
requires
    (A.pts_to a #pa va **
      PM.seq_list_match va0 vv (vmatch pv) **
      pure (A.length a == U64.v len /\
        Seq.equal va0 va
      )
    )
returns res: t
ensures
    (exists* v' .
      vmatch 1.0R res v' **
      Trade.trade
        (vmatch 1.0R res v')
        (A.pts_to a #pa va **
          PM.seq_list_match va0 vv (vmatch pv)
        ) **
        pure (
          CArray? (unpack v') /\
          Ghost.reveal vv == CArray?.v (unpack v')
        )
    )
{
  Trade.rewrite_with_trade
    (PM.seq_list_match va0 vv (vmatch pv))
    (PM.seq_list_match va vv (vmatch pv));
  let res = mk_array_from_array a len;
  Trade.trans_concl_r _ _ _ (PM.seq_list_match va0 vv (vmatch pv));
  res
}

inline_for_extraction
let mk_array_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (a: S.slice t) ->
  (#pa: perm) ->
  (#va: Ghost.erased (Seq.seq t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list cbor)) ->
  stt t
    (pts_to a #pa va **
      PM.seq_list_match va vv (vmatch pv) **
      pure (FStar.UInt.fits (SZ.v (S.len a)) U64.n)
    )
    (fun res -> exists* v' .
      vmatch 1.0R res (pack (CArray v')) **
      Trade.trade
        (vmatch 1.0R res (pack (CArray v')))
        (pts_to a #pa va **
          PM.seq_list_match va vv (vmatch pv)
        ) **
        pure (v' == Ghost.reveal vv)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_array'
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_array: mk_array_t vmatch)
  (a: S.slice t)
  (va0: Ghost.erased (Seq.seq t))
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq t))
  (#pv: perm)
  (#vv: Ghost.erased (list cbor))
requires
    (pts_to a #pa va **
      PM.seq_list_match va0 vv (vmatch pv) **
      pure (FStar.UInt.fits (SZ.v (S.len a)) U64.n /\
        Seq.equal va va0
      )
    )
returns res: t
ensures
    (exists* v' .
      vmatch 1.0R res (pack (CArray v')) **
      Trade.trade
        (vmatch 1.0R res (pack (CArray v')))
        (pts_to a #pa va **
          PM.seq_list_match va0 vv (vmatch pv)
        ) **
        pure ((v' <: list cbor) == Ghost.reveal vv)
    )
{
  Trade.rewrite_with_trade
    (PM.seq_list_match va0 vv (vmatch pv))
    (PM.seq_list_match va vv (vmatch pv));
  let res = mk_array a;
  Trade.trans_concl_r _ _ _ (PM.seq_list_match va0 vv (vmatch pv));
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_array_from_array
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_array: mk_array_t vmatch)
: mk_array_from_array_t #_ vmatch
=
  (a: A.array t)
  (len: U64.t)
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq t))
  (#pv: perm)
  (#vv: Ghost.erased (list cbor))
{
  A.pts_to_len a;
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
  let s = S.from_array a (SZ.uint64_to_sizet len);
  intro
    (Trade.trade
      (pts_to s #pa va)
      (A.pts_to a #pa va)
    )
    #(S.is_from_array a s)
    fn _
  {
    S.to_array s;
  };
  Trade.reg_r (pts_to s #pa va) (A.pts_to a #pa va) (PM.seq_list_match va vv (vmatch pv));
  S.pts_to_len s;
  let res = mk_array s;
  with p' v' . assert (vmatch p' res (pack (CArray v')));
  Trade.trans (vmatch p' res (pack (CArray v'))) _ _;
  res
}

inline_for_extraction
let mk_map_entry_t
  (#t #t2: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (vmatch2: perm -> t2 -> cbor & cbor -> slprop)
= (xk: t) ->
  (xv: t) ->
  (#pk: perm) ->
  (#vk: Ghost.erased cbor) ->
  (#pv: perm) ->
  (#vv: Ghost.erased cbor) ->
  stt t2
    (vmatch pk xk vk ** vmatch pv xv vv)
    (fun res ->
      vmatch2 1.0R res (Ghost.reveal vk, Ghost.reveal vv) **
      Trade.trade
        (vmatch2 1.0R res (Ghost.reveal vk, Ghost.reveal vv))
        (vmatch pk xk vk ** vmatch pv xv vv)
    )

let mk_map_gen_none_postcond
  (#t2: Type)
  (va: Seq.seq t2)
  (vv: list (cbor & cbor))
  (va': Seq.seq t2)
  (vv': list (cbor & cbor))
: Tot prop
=
      (forall x . List.Tot.memP x vv' <==> List.Tot.memP x vv) /\
      List.Tot.length vv' == List.Tot.length vv /\
      (List.Tot.length vv > pow2 64 - 1 \/ ~ (List.Tot.no_repeats_p (List.Tot.map fst vv))) /\
      (List.Tot.length vv > pow2 64 - 1 ==> (va' == va /\ vv' == vv))

let mk_map_gen_post
  (#t1 #t2: Type)
  (vmatch1: perm -> t1 -> cbor -> slprop)
  (vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
  (a: S.slice t2)
  (va: (Seq.seq t2))
  (pv: perm)
  (vv: (list (cbor & cbor)))
  (res: option t1)
: Tot slprop
= match res with
  | None -> exists* va' vv' .
    pts_to a va' **
    PM.seq_list_match va' vv' (vmatch2 pv) **
    Trade.trade 
      (PM.seq_list_match va' vv' (vmatch2 pv))
      (PM.seq_list_match va vv (vmatch2 pv)) **
    pure (
      mk_map_gen_none_postcond va vv va' vv'
    )
  | Some res -> exists* (v': cbor_map {FStar.UInt.fits (cbor_map_length v') 64}) va' .
      vmatch1 1.0R res (pack (CMap v')) **
      Trade.trade
        (vmatch1 1.0R res (pack (CMap v')))
        (pts_to a va' ** // this function potentially sorts the input array, so we lose the link to the initial array contents
          PM.seq_list_match va vv (vmatch2 pv) // but we keep the permissions on each element
        ) **
        pure (
          List.Tot.no_repeats_p (List.Tot.map fst vv) /\
          (forall x . List.Tot.assoc x vv == cbor_map_get v' x) /\
          cbor_map_length v' == Seq.length va
        )

let mk_map_gen_by_ref_postcond
  (#t1: Type)
  (vdest0: t1)
  (res: option t1)
  (vdest: t1)
  (bres: bool)
: Tot prop
= bres == Some? res /\
  vdest == begin match res with
  | None -> vdest0
  | Some v -> v
  end

inline_for_extraction
let mk_map_gen_by_ref_t
  (#t1 #t2: Type)
  (vmatch1: perm -> t1 -> cbor -> slprop)
  (vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
= (a: S.slice t2) ->
  (dest: R.ref t1) -> 
  (#va: Ghost.erased (Seq.seq t2)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list (cbor & cbor))) ->
  (#vdest0: Ghost.erased t1) ->
  stt bool
    (pts_to a va ** pts_to dest vdest0 **
      PM.seq_list_match va vv (vmatch2 pv)
    )
    (fun bres -> exists* res vdest . mk_map_gen_post vmatch1 vmatch2 a va pv vv res **
      pts_to dest vdest **
      pure (
        mk_map_gen_by_ref_postcond (Ghost.reveal vdest0) res vdest bres /\ (
        Some? res <==> (
        FStar.UInt.fits (SZ.v (S.len a)) U64.n /\
        List.Tot.no_repeats_p (List.Tot.map fst vv)      
      )))
    )

inline_for_extraction
let mk_map_gen_t
  (#t1 #t2: Type)
  (vmatch1: perm -> t1 -> cbor -> slprop)
  (vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
= (a: S.slice t2) ->
  (#va: Ghost.erased (Seq.seq t2)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list (cbor & cbor))) ->
  stt (option t1)
    (pts_to a va **
      PM.seq_list_match va vv (vmatch2 pv)
    )
    (fun res -> mk_map_gen_post vmatch1 vmatch2 a va pv vv res **
      pure (Some? res <==> (
        FStar.UInt.fits (SZ.v (S.len a)) U64.n /\
        List.Tot.no_repeats_p (List.Tot.map fst vv)      
      ))
    )

inline_for_extraction
fn mk_map_gen
  (#t1 #t2: Type0)
  (#vmatch1: perm -> t1 -> cbor -> slprop)
  (#vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
  (dummy: t1)
  (mk_map_gen_by_ref: mk_map_gen_by_ref_t vmatch1 vmatch2)
: mk_map_gen_t u#0 #_ #_ vmatch1 vmatch2
= (a: S.slice t2)
  (#va: Ghost.erased (Seq.seq t2))
  (#pv: perm)
  (#vv: Ghost.erased (list (cbor & cbor)))
{
  let mut dest = dummy;
  S.pts_to_len a;
  PM.seq_list_match_length (vmatch2 pv) va vv;
  let bres = mk_map_gen_by_ref a dest;
  if bres {
    let res = !dest;
    with res' . rewrite mk_map_gen_post vmatch1 vmatch2 a va pv vv res' as mk_map_gen_post vmatch1 vmatch2 a va pv vv (Some res);
    Some res
  } else {
    with res' . rewrite mk_map_gen_post vmatch1 vmatch2 a va pv vv res' as mk_map_gen_post vmatch1 vmatch2 a va pv vv None;
    None #t1
  }
}

inline_for_extraction
let mk_map_t
  (#t1 #t2: Type)
  (vmatch1: perm -> t1 -> cbor -> slprop)
  (vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
= (a: S.slice t2) ->
  (#va: Ghost.erased (Seq.seq t2)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list (cbor & cbor))) ->
  stt t1
    (pts_to a va **
      PM.seq_list_match va vv (vmatch2 pv) **
      pure (FStar.UInt.fits (SZ.v (S.len a)) U64.n /\
        List.Tot.no_repeats_p (List.Tot.map fst vv)
      )
    )
    (fun res -> exists* (v': cbor_map {FStar.UInt.fits (cbor_map_length v') 64}) va' .
      vmatch1 1.0R res (pack (CMap v')) **
      Trade.trade
        (vmatch1 1.0R res (pack (CMap v')))
        (pts_to a va' ** // this function potentially sorts the input array, so we lose the link to the initial array contents
          PM.seq_list_match va vv (vmatch2 pv) // but we keep the permissions on each element
        ) **
        pure (
          (forall x . List.Tot.assoc x vv == cbor_map_get v' x) /\
          cbor_map_length v' == Seq.length va
        )
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
let mk_map_from_array_t
  (#cbor_t: Type0)
  (#cbor_map_entry_t: Type0)
  (cbor_match: perm -> cbor_t -> cbor -> slprop)
  (cbor_map_entry_match: perm -> cbor_map_entry_t -> (cbor & cbor) -> slprop)
=
  (a: A.array cbor_map_entry_t) ->
  (len: U64.t) ->
  (#va: Ghost.erased (Seq.seq cbor_map_entry_t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list (cbor & cbor))) ->
  stt cbor_t
    (A.pts_to a va **
      PM.seq_list_match va vv (cbor_map_entry_match pv) **
      pure (A.length a == U64.v len /\
        List.Tot.no_repeats_p (List.Tot.map fst vv)
      )
    )
    (fun res -> exists* v' va' .
      cbor_match 1.0R res v' **
      Trade.trade
        (cbor_match 1.0R res v')
        (A.pts_to a va' **
          PM.seq_list_match va vv (cbor_map_entry_match pv)
        ) **
        pure (
          CMap? (unpack v') /\
          (forall x . List.Tot.assoc x vv == cbor_map_get (CMap?.c (unpack v')) x) /\
          cbor_map_length (CMap?.c (unpack v')) == Seq.length va
        )
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_map_from_array
  (#cbor_t: Type0)
  (#cbor_map_entry_t: Type0)
  (#cbor_match: perm -> cbor_t -> cbor -> slprop)
  (#cbor_map_entry_match: perm -> cbor_map_entry_t -> (cbor & cbor) -> slprop)
  (cbor_mk_map: mk_map_t cbor_match cbor_map_entry_match)
: mk_map_from_array_t #_ #_ cbor_match cbor_map_entry_match
=
  (a: A.array cbor_map_entry_t)
  (len: U64.t)
  (#va: Ghost.erased (Seq.seq cbor_map_entry_t))
  (#pv: perm)
  (#vv: Ghost.erased (list (cbor & cbor)))
{
  A.pts_to_len a;
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
  let s = S.from_array a (SZ.uint64_to_sizet len);
  S.pts_to_len s;
  let res = cbor_mk_map s;
  with p' v' va' . assert (
      Trade.trade
        (cbor_match p' res (pack (CMap v')))
        (pts_to s va' **
          PM.seq_list_match va vv (cbor_map_entry_match pv)
        )
  );
  intro
    (Trade.trade
      (pts_to s va')
      (A.pts_to a va')
    )
    #(S.is_from_array a s)
    fn _
  {
    S.to_array s;
  };
  Trade.reg_r (pts_to s va') (A.pts_to a va') (PM.seq_list_match va vv (cbor_map_entry_match pv));
  Trade.trans (cbor_match p' res (pack (CMap v'))) _ _;
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_map_from_array'
  (#cbor_t: Type0)
  (#cbor_map_entry_t: Type0)
  (#cbor_match: perm -> cbor_t -> cbor -> slprop)
  (#cbor_map_entry_match: perm -> cbor_map_entry_t -> (cbor & cbor) -> slprop)
  (cbor_mk_map_from_array: mk_map_from_array_t cbor_match cbor_map_entry_match)
  (a: A.array cbor_map_entry_t)
  (len: U64.t)
  (va0: Ghost.erased (Seq.seq cbor_map_entry_t))
  (#va: Ghost.erased (Seq.seq cbor_map_entry_t))
  (#pv: perm)
  (#vv: Ghost.erased (list (cbor & cbor)))
requires
    (A.pts_to a va **
      PM.seq_list_match va0 vv (cbor_map_entry_match pv) **
      pure (A.length a == U64.v len /\
        List.Tot.no_repeats_p (List.Tot.map fst vv) /\
        Seq.equal va0 va
      )
    )
returns res: cbor_t
ensures
    (exists* v' va' .
      cbor_match 1.0R res v' **
      Trade.trade
        (cbor_match 1.0R res v')
        (A.pts_to a va' **
          PM.seq_list_match va0 vv (cbor_map_entry_match pv)
        ) **
        pure (
          CMap? (unpack v') /\
          (forall x . List.Tot.assoc x vv == cbor_map_get (CMap?.c (unpack v')) x) /\
          cbor_map_length (CMap?.c (unpack v')) == Seq.length va
        )
    )
{
  Trade.rewrite_with_trade
    (PM.seq_list_match va0 vv (cbor_map_entry_match pv))
    (PM.seq_list_match va vv (cbor_map_entry_match pv));
  let res = cbor_mk_map_from_array a len;
  Trade.trans_concl_r _ _ _ (PM.seq_list_match va0 vv (cbor_map_entry_match pv));
  res
}

let mk_map_from_array_safe_post
  (#t1 #t2: Type)
  (vmatch1: perm -> t1 -> cbor -> slprop)
  (vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
  (a: A.array t2)
  (va: (Seq.seq t2))
  (pv: perm)
  (vv: (list (cbor & cbor)))
  (vres: t1)
  (res: bool)
: Tot slprop
= if res
  then
    exists* (v': cbor_map {FStar.UInt.fits (cbor_map_length v') 64}) va' .
      vmatch1 1.0R vres (pack (CMap v')) **
      Trade.trade
        (vmatch1 1.0R vres (pack (CMap v')))
        (pts_to a va' ** // this function potentially sorts the input array, so we lose the link to the initial array contents
          PM.seq_list_match va vv (vmatch2 pv) // but we keep the permissions on each element
        ) **
        pure (
          List.Tot.no_repeats_p (List.Tot.map fst vv) /\
          (forall x . List.Tot.assoc x vv == cbor_map_get v' x) /\
          cbor_map_length v' == Seq.length va
        )
  else
    exists* va' vv' .
    pts_to a va' **
    PM.seq_list_match va' vv' (vmatch2 pv) **
    Trade.trade 
      (PM.seq_list_match va' vv' (vmatch2 pv))
      (PM.seq_list_match va vv (vmatch2 pv)) **
    pure (
      mk_map_gen_none_postcond va vv va' vv'
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
let mk_map_from_array_safe_t
  (#cbor_t: Type0)
  (#cbor_map_entry_t: Type0)
  (cbor_match: perm -> cbor_t -> cbor -> slprop)
  (cbor_map_entry_match: perm -> cbor_map_entry_t -> (cbor & cbor) -> slprop)
=
  (a: A.array cbor_map_entry_t) ->
  (len: U64.t) ->
  (dest: R.ref cbor_t) ->
  (#va: Ghost.erased (Seq.seq cbor_map_entry_t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list (cbor & cbor))) ->
  stt bool
    (A.pts_to a va **
      PM.seq_list_match va vv (cbor_map_entry_match pv) **
      (exists* vdest . R.pts_to dest vdest) **
      pure (A.length a == U64.v len)
    )
    (fun res -> exists* vdest .
      R.pts_to dest vdest **
      mk_map_from_array_safe_post cbor_match cbor_map_entry_match a va pv vv vdest res
    )

inline_for_extraction
fn mk_map_from_option
  (#t1 #t2: Type0)
  (#vmatch1: perm -> t1 -> cbor -> slprop)
  (#vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
  (mk_map_gen: mk_map_gen_t vmatch1 vmatch2)
: mk_map_t u#0 #_ #_ vmatch1 vmatch2
= (a: S.slice t2)
  (#va: Ghost.erased (Seq.seq t2))
  (#pv: perm)
  (#vv: Ghost.erased (list (cbor & cbor)))
{
  S.pts_to_len a;
  PM.seq_list_match_length (vmatch2 pv) va vv;
  let sres = mk_map_gen a;
  let Some res = sres;
  unfold (mk_map_gen_post vmatch1 vmatch2 a va pv vv (Some res));
  res
}

inline_for_extraction
fn mk_map_from_ref
  (#t1 #t2: Type0)
  (#vmatch1: perm -> t1 -> cbor -> slprop)
  (#vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
  (dummy: t1)
  (mk_map_gen: mk_map_gen_by_ref_t vmatch1 vmatch2)
: mk_map_t u#0 #_ #_ vmatch1 vmatch2
= (a: S.slice t2)
  (#va: Ghost.erased (Seq.seq t2))
  (#pv: perm)
  (#vv: Ghost.erased (list (cbor & cbor)))
{
  let mut dest = dummy;
  S.pts_to_len a;
  PM.seq_list_match_length (vmatch2 pv) va vv;
  let _ = mk_map_gen a dest;
  let res = !dest;
  with res' . rewrite (mk_map_gen_post vmatch1 vmatch2 a va pv vv res') as (mk_map_gen_post vmatch1 vmatch2 a va pv vv (Some res));
  unfold (mk_map_gen_post vmatch1 vmatch2 a va pv vv (Some res));
  res
}

let map_get_post_none
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (px: perm)
  (vx: cbor)
  (vk: cbor)
: Tot slprop
=
  vmatch px x vx ** pure (CMap? (unpack vx) /\ None? (cbor_map_get (CMap?.c (unpack vx)) vk))

let map_get_post_some
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (px: perm)
  (vx: cbor)
  (vk: cbor)
  (x' : t)
: Tot slprop
= exists* px' vx' .
      vmatch px' x' vx' **
      Trade.trade
        (vmatch px' x' vx')
        (vmatch px x vx) **
      pure (CMap? (unpack vx) /\ cbor_map_get (CMap?.c (unpack vx)) vk == Some vx')

let map_get_post
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (px: perm)
  (vx: cbor)
  (vk: cbor)
  (res: option t)
: Tot slprop
= match res with
  | None -> map_get_post_none vmatch x px vx vk
  | Some x' -> map_get_post_some vmatch x px vx vk x'

inline_for_extraction
let map_get_by_ref_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (k: t) ->
  (dest: R.ref t) ->
  (#px: perm) ->
  (#vx: Ghost.erased cbor) ->
  (#pk: perm) ->
  (#vk: Ghost.erased cbor) ->
  (#vdest0: Ghost.erased t) ->
  stt bool
    (vmatch px x vx ** vmatch pk k vk ** pts_to dest vdest0 ** pure (CMap? (unpack vx)))
    (fun bres -> exists* vdest res .
      vmatch pk k vk **
      map_get_post vmatch x px vx vk res **
      pts_to dest vdest **
      pure (CMap? (unpack vx) /\ (Some? (cbor_map_get (CMap?.c (unpack vx)) vk) == Some? res) /\
        mk_map_gen_by_ref_postcond (Ghost.reveal vdest0) res vdest bres
      )
    )

inline_for_extraction
let map_get_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (k: t) ->
  (#px: perm) ->
  (#vx: Ghost.erased cbor) ->
  (#pk: perm) ->
  (#vk: Ghost.erased cbor) ->
  stt (option t)
    (vmatch px x vx ** vmatch pk k vk ** pure (CMap? (unpack vx)))
    (fun res ->
      vmatch pk k vk **
      map_get_post vmatch x px vx vk res **
      pure (CMap? (unpack vx) /\ (Some? (cbor_map_get (CMap?.c (unpack vx)) vk) == Some? res))
    )

inline_for_extraction
fn map_get_as_option
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (m: map_get_by_ref_t vmatch)
: map_get_t u#0 #t vmatch
=
  (x: _)
  (k: _)
  (#px: _)
  (#vx: _)
  (#pk: _)
  (#vk: _)
{
  let mut dest = k;
  let bres = m x k dest;
  if bres {
    let res = !dest;
    with res' . rewrite map_get_post vmatch x px vx vk res' as map_get_post vmatch x px vx vk (Some res);
    Some res
  } else {
    with res' . rewrite map_get_post vmatch x px vx vk res' as map_get_post vmatch x px vx vk None;
    None #t
  }
}

module Spec = CBOR.Spec.API.Format

noextract [@@noextract_to "krml"]
let cbor_det_validate_post
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
=
      if SZ.v res = 0
      then (~ (exists v1 v2 . v == Spec.cbor_det_serialize v1 `Seq.append` v2))
      else (exists v1 v2 . v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v res == Seq.length (Spec.cbor_det_serialize v1))

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_validate_t
=
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_det_validate_post v res
    ))

let cbor_det_parse_postcond_some
  (v: Seq.seq U8.t)
  (v': Spec.cbor)
  (vrem: Seq.seq U8.t)
: Tot prop
= let s = Spec.cbor_det_serialize v' in
  let len = Seq.length s in
  len <= Seq.length v /\
  Seq.slice v 0 len == s /\
  Seq.slice v len (Seq.length v) == vrem /\
  v == Seq.append (Seq.slice v 0 len) (Seq.slice v len (Seq.length v))

noextract [@@noextract_to "krml"]
let cbor_det_parse_post_some
  (#cbordet: Type)
  (cbor_det_match: perm -> cbordet -> Spec.cbor -> slprop)
  (input: S.slice U8.t)
  (pm: perm)
  (v: Seq.seq U8.t)
  (res: cbordet)
  (rem: S.slice U8.t)
: Tot slprop
= exists* v' vrem .
     cbor_det_match 1.0R res v' **
     pts_to rem #pm vrem **
     Trade.trade // FIXME: I would need a forall_vrem here
       (cbor_det_match 1.0R res v' ** pts_to rem #pm vrem)
       (pts_to input #pm v) **
     pure (
       cbor_det_parse_postcond_some v v' vrem
     )

noextract [@@noextract_to "krml"]
let cbor_det_parse_post
  (#cbordet: Type)
  (cbor_det_match: perm -> cbordet -> Spec.cbor -> slprop)
  (input: S.slice U8.t)
  (pm: perm)
  (v: Seq.seq U8.t)
  (res: option (cbordet & S.slice U8.t))
: Tot slprop
= match res with
  | None -> pts_to input #pm v ** pure (~ (exists v1 v2 . v == Spec.cbor_det_serialize v1 `Seq.append` v2))
  | Some (res, rem) -> cbor_det_parse_post_some cbor_det_match input pm v res rem

inline_for_extraction
let cbor_det_parse_t
  (#cbordet: Type)
  (cbor_det_match: perm -> cbordet -> Spec.cbor -> slprop)
=
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt (option (cbordet & S.slice U8.t))
    (pts_to input #pm v)
    (fun res ->
      cbor_det_parse_post cbor_det_match input pm v res **
      pure (Some? res == Some? (Spec.cbor_det_parse v))
    )

let cbor_det_parse_aux1
  (v1: Spec.cbor)
: Lemma
  (let s = Spec.cbor_det_serialize v1 in s == s `Seq.append` Seq.empty)
= Seq.append_empty_r (Spec.cbor_det_serialize v1)

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_parse_valid_t
  (#cbor_det_t: Type)
  (cbor_det_match: perm -> cbor_det_t -> Spec.cbor -> slprop)
=
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt cbor_det_t
    (pts_to input #pm v ** pure (
      exists v1 . Ghost.reveal v == Spec.cbor_det_serialize v1 /\ SZ.v (S.len input) == Seq.length (Spec.cbor_det_serialize v1)
    ))
    (fun res -> exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade (cbor_det_match 1.0R res v') (pts_to input #pm v) ** pure (
        Ghost.reveal v == Spec.cbor_det_serialize v'
    ))

let seq_length_append_l
  (#t: Type)
  (v1 v2: Seq.seq t)
: Lemma
  (Seq.slice (Seq.append v1 v2) 0 (Seq.length v1) == v1)
= assert (Seq.slice (Seq.append v1 v2) 0 (Seq.length v1) `Seq.equal` v1)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_parse_full
  (#cbor_det_t: Type)
  (#cbor_det_match: perm -> cbor_det_t -> Spec.cbor -> slprop)
  (cbor_det_validate: cbor_det_validate_t)
  (cbor_det_parse: cbor_det_parse_valid_t cbor_det_match)
: cbor_det_parse_t u#0 #_ cbor_det_match
=
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let len = cbor_det_validate input;
  Spec.cbor_det_parse_none_equiv v;
  if (len = 0sz) {
    fold (cbor_det_parse_post cbor_det_match input pm v None);
    None #(cbor_det_t & S.slice U8.t)
  } else {
    Seq.lemma_split v (SZ.v len);
    let input2, rem = S.split_trade input len;
    Classical.forall_intro_2 (seq_length_append_l #U8.t);
    S.pts_to_len input2;
    let res = cbor_det_parse input2;
    Trade.trans_hyp_l _ _ _ (pts_to input #pm v);
    fold (cbor_det_parse_post_some cbor_det_match input pm v res rem);
    fold (cbor_det_parse_post cbor_det_match input pm v (Some (res, rem)));
    Some (res, rem)
  }
}

noextract [@@noextract_to "krml"]
let cbor_det_size_post
  (bound: SZ.t)
  (y: Spec.cbor)
  (res: SZ.t)
: Tot prop
=
      let s = Seq.length (Spec.cbor_det_serialize y) in
      (SZ.v res == 0 <==> s > SZ.v bound) /\
      (SZ.v res > 0 ==> SZ.v res == s)

noextract [@@noextract_to "krml"]
let cbor_det_serialize_fits_postcond
  (y: Spec.cbor)
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
=
      let s = Spec.cbor_det_serialize y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))

noextract [@@noextract_to "krml"]
let cbor_det_serialize_postcond
  (y: Spec.cbor)
  (v: Seq.seq U8.t)
  (v': Seq.seq U8.t)
  (res: option SZ.t)
: Tot prop
= let s = Spec.cbor_det_serialize y in
  match res with
  | None -> Seq.length s > Seq.length v /\ v' == v
  | Some len ->
    Seq.length s == SZ.v len /\
    SZ.v len <= Seq.length v /\
    Seq.length v' == Seq.length v /\
    Seq.slice v' 0 (SZ.v len) == s /\
    Seq.slice v' (SZ.v len) (Seq.length v) == Seq.slice v (SZ.v len) (Seq.length v) /\
    v' `Seq.equal` (s `Seq.append` Seq.slice v (SZ.v len) (Seq.length v))

noextract [@@noextract_to "krml"]
let cbor_det_serialize_postcond_c
  (y: Spec.cbor)
  (v: Seq.seq U8.t)
  (v': Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
= cbor_det_serialize_postcond y v v' (if res = 0sz then None else Some res)

inline_for_extraction
let cbor_det_serialize_t
  (#cbordet: Type)
  (cbor_det_match: perm -> cbordet -> Spec.cbor -> slprop)
=
  (x: cbordet) ->
  (output: S.slice U8.t) ->
  (#y: Ghost.erased Spec.cbor) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt (option SZ.t)
    (cbor_det_match pm x y ** pts_to output v)
    (fun res -> exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      cbor_det_serialize_postcond y v v' res
    ))

inline_for_extraction
let cbor_copy_t
  (#t: Type)
  (#tf: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (freeable: tf -> slprop)
  (get_cbor: (tf -> t))
=
  (x: t) ->
  (#p: perm) ->
  (#v: Ghost.erased cbor) ->
  stt tf
    (vmatch p x v)
    (fun res ->
      vmatch p x v **
      vmatch 1.0R (get_cbor res) v **
      Trade.trade
        (vmatch 1.0R (get_cbor res) v)
        (freeable res)
    )

inline_for_extraction
let cbor_free_t
  (#tf: Type)
  (freeable: tf -> slprop)
=
  (x: tf) ->
  stt unit
    (freeable x)
    (fun _ -> emp)

noextract [@@noextract_to "krml"]
let cbor_det_serialize_tag_postcond
  (tag: U64.t)
  (output_len: SZ.t)
  (res: SZ.t)
  (v': Seq.seq U8.t)
: Tot prop
= let s = Spec.cbor_det_serialize_tag tag in
  let len = Seq.length s in
  SZ.v output_len == Seq.length v' /\
  SZ.v res <= Seq.length v' /\
  (res == 0sz <==> len > Seq.length v') /\
  (len <= Seq.length v' ==> (Seq.slice v' 0 (SZ.v res) == s))

inline_for_extraction
let cbor_det_serialize_tag_t =
  (tag: U64.t) ->
  (output: S.slice U8.t) ->
  stt SZ.t
    (exists* v . pts_to output v)
    (fun res -> exists* v . pts_to output v ** pure (
      cbor_det_serialize_tag_postcond tag (S.len output) res v
    ))

let cbor_det_serialize_array_precond
  (len: U64.t)
  (l: list cbor)
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= U64.v len == List.Tot.length l /\
  SZ.v off <= Seq.length v /\
  Seq.slice v 0 (SZ.v off) == Spec.cbor_det_serialize_list l

let cbor_det_serialize_array_postcond
  (l: list cbor)
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= FStar.UInt.fits (List.Tot.length l) 64 /\
  SZ.v res <= Seq.length v /\
  (res == 0sz <==> Seq.length (Spec.cbor_det_serialize (pack (CArray l))) > Seq.length v) /\
  (SZ.v res > 0 ==> Seq.slice v 0 (SZ.v res) `Seq.equal` Spec.cbor_det_serialize (pack (CArray l)))

inline_for_extraction
let cbor_det_serialize_array_t =
  (len: U64.t) ->
  (out: S.slice U8.t) ->
  (l: Ghost.erased (list cbor)) ->
  (off: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_det_serialize_array_precond len l off v)
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_det_serialize_array_postcond l res v)
  )

let cbor_det_serialize_string_precond
  (ty: major_type_byte_string_or_text_string)
  (off: U64.t)
  (v: Seq.seq U8.t)
: Tot prop
= U64.v off <= Seq.length v /\
  (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct (Seq.slice v 0 (U64.v off)))

let cbor_det_serialize_string_postcond
  (ty: major_type_byte_string_or_text_string)
  (off: U64.t)
  (v: Seq.seq U8.t)
  (res: SZ.t)
  (v': Seq.seq U8.t)
: Tot prop
= cbor_det_serialize_string_precond ty off v /\
  begin let l = Seq.slice v 0 (U64.v off) in
  Seq.length v' == Seq.length v /\
  SZ.v res <= Seq.length v' /\
  (res == 0sz <==> Seq.length (Spec.cbor_det_serialize (pack (CString ty l))) > Seq.length v') /\
  (SZ.v res > 0 ==> Seq.slice v' 0 (SZ.v res) `Seq.equal` Spec.cbor_det_serialize (pack (CString ty l)))
  end

inline_for_extraction
let cbor_det_serialize_string_t =
  (ty: major_type_byte_string_or_text_string) ->
  (off: U64.t) ->
  (out: S.slice U8.t) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
  (pts_to out v **
    pure (cbor_det_serialize_string_precond ty off v)
  )
  (fun res -> exists* v' .
    pts_to out v' **
    pure (cbor_det_serialize_string_postcond ty off v res v')
  )

let cbor_det_serialize_map_insert_pre
  (m: cbor_map)
  (off2: SZ.t)
  (key: cbor)
  (off3: SZ.t)
  (value: cbor)
  (v: Seq.seq U8.t)
: Tot prop
= let sm = Spec.cbor_det_serialize_map m in
  let sk = Spec.cbor_det_serialize key in
  let sv = Spec.cbor_det_serialize value in
  Seq.length sm == SZ.v off2 /\
  SZ.v off2 + Seq.length sk == SZ.v off3 /\
  SZ.v off3 + Seq.length sv == Seq.length v /\
  Seq.slice v 0 (SZ.v off2) `Seq.equal` sm /\
  Seq.slice v (SZ.v off2) (SZ.v off3) `Seq.equal` sk /\
  Seq.slice v (SZ.v off3) (Seq.length v) `Seq.equal` sv

let cbor_det_serialize_map_insert_post
  (m: cbor_map)
  (key: cbor)
  (value: cbor)
  (res: bool)
  (v': Seq.seq U8.t)
: Tot prop
= (res == false <==> cbor_map_defined key m) /\
  (res == true ==> v' == Spec.cbor_det_serialize_map (cbor_map_union m (cbor_map_singleton key value)))

inline_for_extraction
let cbor_det_serialize_map_insert_t =
  (out: S.slice U8.t) ->
  (m: Ghost.erased cbor_map) ->
  (off2: SZ.t) ->
  (key: Ghost.erased cbor) ->
  (off3: SZ.t) ->
  (value: Ghost.erased cbor) ->
  stt bool
    (exists* v .
      pts_to out v **
      pure (cbor_det_serialize_map_insert_pre m off2 key off3 value v)
    )
    (fun res -> exists* v .
      pts_to out v **
      pure (cbor_det_serialize_map_insert_post m key value res v)
    )

let cbor_det_serialize_map_precond
  (len: U64.t)
  (l: cbor_map)
  (off: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= U64.v len == cbor_map_length l /\
  SZ.v off <= Seq.length v /\
  Seq.slice v 0 (SZ.v off) == Spec.cbor_det_serialize_map l

let cbor_det_serialize_map_postcond
  (l: cbor_map)
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
= FStar.UInt.fits (cbor_map_length l) 64 /\
  SZ.v res <= Seq.length v /\
  (res == 0sz <==> Seq.length (Spec.cbor_det_serialize (pack (CMap l))) > Seq.length v) /\
  (SZ.v res > 0 ==> Seq.slice v 0 (SZ.v res) `Seq.equal` Spec.cbor_det_serialize (pack (CMap l)))

inline_for_extraction
let cbor_det_serialize_map_t =
  (len: U64.t) ->
  (out: S.slice U8.t) ->
  (l: Ghost.erased (cbor_map)) ->
  (off: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_det_serialize_map_precond len l off v)
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_det_serialize_map_postcond l res v)
  )
