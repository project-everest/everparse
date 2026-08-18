module CBOR.Pulse.API.Nondet.Rust
open CBOR.Spec.Constants
open Pulse.Lib.Pervasives
module Spec = CBOR.Spec.API.Format
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Base = CBOR.Pulse.API.Base

val cbornondet: Type0

noextract [@@noextract_to "krml"]
val cbor_nondet_match: perm -> cbornondet -> Spec.cbor -> slprop

val cbor_nondet_reset_perm () : Base.reset_perm_t cbor_nondet_match

val cbor_nondet_share () : Base.share_t cbor_nondet_match
val cbor_nondet_gather () : Base.gather_t cbor_nondet_match

val cbor_nondet_parse (_: unit) : Base.cbor_nondet_parse_t cbor_nondet_match

val cbor_nondet_match_with_size
  (size: nat)
  (p: perm)
  (c: cbornondet)
  (v: Spec.cbor)
: Tot slprop

val cbor_nondet_match_with_size_intro (_: unit) : Base.ghost_get_size_t #_ cbor_nondet_match cbor_nondet_match_with_size

val cbor_nondet_size (_: unit) : Base.get_size_t #_ cbor_nondet_match_with_size

val cbor_nondet_serialize
  (_: unit)
: Base.cbor_nondet_serialize_t #cbornondet cbor_nondet_match_with_size

(* Constructors *)

noextract [@@noextract_to "krml"]
let cbor_nondet_mk_simple_value_post
  (v: U8.t)
  (res: option cbornondet)
: Tot slprop
= match res with
  | None -> emp
  | Some res' -> exists* v' . cbor_nondet_match 1.0R res' v' ** pure (simple_value_wf v /\ v' == Spec.pack (Spec.CSimple v))

val cbor_nondet_mk_simple_value
  (v: U8.t)
: stt (option cbornondet)
    emp
    (fun res ->
      cbor_nondet_mk_simple_value_post v res **
      pure (Some? res <==> simple_value_wf v)
    )

[@@no_auto_projectors]
type cbor_nondet_int_kind =
 | UInt64
 | NegInt64

val cbor_nondet_mk_int64
  (ty: cbor_nondet_int_kind)
  (v: U64.t)
: stt cbornondet
    emp
    (fun res -> cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v))
    )

[@@no_auto_projectors]
type cbor_nondet_string_kind =
| ByteString
| TextString

noextract [@@noextract_to "krml"]
let cbor_nondet_mk_string_post
  (ty: major_type_byte_string_or_text_string)
  (s: S.slice U8.t)
  (p: perm)
  (v: Seq.seq U8.t)
  (res: option cbornondet)
= match res with
  | None -> pts_to s #p v
  | Some res' -> exists* v' .
    cbor_nondet_match 1.0R res' (Spec.pack (Spec.CString ty v')) **
    Trade.trade
      (cbor_nondet_match 1.0R res' (Spec.pack (Spec.CString ty v')))
      (pts_to s #p v) **
    pure (v' == v)

val cbor_impl_utf8_correct (_: unit) : Base.impl_utf8_correct_t

val cbor_nondet_mk_string
  (ty: cbor_nondet_string_kind)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt (option cbornondet)
    (pts_to s #p v)
    (fun res ->
      cbor_nondet_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v res **
      pure (Some? res <==> (FStar.UInt.fits (SZ.v (S.len s)) U64.n /\ (ty == TextString ==> CBOR.Spec.API.UTF8.correct v))) // this is true for Rust's str/String, but we will check anyway
    )

val cbor_nondet_mk_tagged: Base.mk_tagged_t cbor_nondet_match

val cbor_nondet_map_entry: Type0

noextract [@@noextract_to "krml"]
val cbor_nondet_map_entry_match: perm -> cbor_nondet_map_entry -> (Spec.cbor & Spec.cbor) -> slprop

val cbor_nondet_mk_map_entry : Base.mk_map_entry_t cbor_nondet_match cbor_nondet_map_entry_match

module PM = Pulse.Lib.SeqMatch

noextract [@@noextract_to "krml"]
let cbor_nondet_mk_array_post
  (a: S.slice cbornondet)
  (pa: perm)
  (va: (Seq.seq cbornondet))
  (pv: perm)
  (vv: (list Spec.cbor))
  (res: option cbornondet)
: Tot slprop
= match res with
  | None ->
    pts_to a #pa va **
    PM.seq_list_match va vv (cbor_nondet_match pv)
  | Some res ->
    exists* v' .
      cbor_nondet_match 1.0R res (Spec.pack (Spec.CArray v')) **
      Trade.trade
        (cbor_nondet_match 1.0R res (Spec.pack (Spec.CArray v')))
        (pts_to a #pa va **
          PM.seq_list_match va vv (cbor_nondet_match pv)
        ) **
        pure (
          v' == vv
        )

val cbor_nondet_mk_array
  (a: S.slice cbornondet)
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq cbornondet))
  (#pv: perm)
  (#vv: Ghost.erased (list Spec.cbor))
: stt (option cbornondet)
    (pts_to a #pa va **
      PM.seq_list_match va vv (cbor_nondet_match pv)
    )
    (fun res ->
      cbor_nondet_mk_array_post a pa va pv vv res **
      pure (Some? res <==> FStar.UInt.fits (SZ.v (S.len a)) U64.n)
    )

val cbor_nondet_mk_map (_: unit): Base.mk_map_gen_t cbor_nondet_match cbor_nondet_map_entry_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_mk_map_from_array : Base.mk_map_from_array_t cbor_nondet_match cbor_nondet_map_entry_match =
  Base.mk_map_from_array (CBOR.Pulse.API.Base.mk_map_from_option (cbor_nondet_mk_map ()))


(* Destructors *)

val cbor_nondet_equal : Base.equal_t cbor_nondet_match

val cbor_nondet_major_type () : Base.get_major_type_t cbor_nondet_match

noextract [@@noextract_to "krml"]
let cbor_nondet_tagged_match (p: perm) (tag: U64.t) (payload: cbornondet) (v: Spec.cbor) : Tot slprop =
  exists* v' .
    cbor_nondet_match p payload v' **
    pure (Spec.unpack v == Spec.CTagged tag v')

[@@CAbstractStruct; no_auto_projectors]
val cbor_nondet_array: Type0

noextract [@@noextract_to "krml"]
val cbor_nondet_array_match (p: perm) (a: cbor_nondet_array) (v: Spec.cbor) : Tot slprop

[@@CAbstractStruct; no_auto_projectors]
val cbor_nondet_map: Type0

noextract [@@noextract_to "krml"]
val cbor_nondet_map_match (p: perm) (a: cbor_nondet_map) (v: Spec.cbor) : Tot slprop

noeq [@@no_auto_projectors]
type cbor_nondet_view =
| Int64: (kind: cbor_nondet_int_kind) -> (value: U64.t) -> cbor_nondet_view
| String: (kind: cbor_nondet_string_kind) -> (payload: S.slice U8.t) -> cbor_nondet_view
| Array of cbor_nondet_array
| Map of cbor_nondet_map
| Tagged: (tag: U64.t) -> (payload: cbornondet) -> cbor_nondet_view
| SimpleValue of simple_value

noextract [@@noextract_to "krml"]
let cbor_nondet_string_match (t: major_type_byte_string_or_text_string) (p: perm) (a: S.slice U8.t) (v: Spec.cbor) : Tot slprop =
  exists* (v': Seq.seq U8.t) .
    pts_to a #p v' **
    pure (
      Spec.CString? (Spec.unpack v) /\ v' == Spec.CString?.v (Spec.unpack v) /\ t == Spec.CString?.typ (Spec.unpack v) /\
      (t == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v')
    )

noextract [@@noextract_to "krml"]
let cbor_nondet_view_match
  (p: perm)
  (x: cbor_nondet_view)
  (v: Spec.cbor)
: Tot slprop
= match x with
  | Int64 k i -> pure (v == Spec.pack (Spec.CInt64 (if UInt64? k then cbor_major_type_uint64 else cbor_major_type_neg_int64) i))
  | String k s -> cbor_nondet_string_match (if ByteString? k then cbor_major_type_byte_string else cbor_major_type_text_string)  p s v
  | Tagged tag pl -> cbor_nondet_tagged_match p tag pl v
  | Array a -> cbor_nondet_array_match p a v
  | Map m -> cbor_nondet_map_match p m v
  | SimpleValue i -> pure (v == Spec.pack (Spec.CSimple i))

noextract [@@noextract_to "krml"]
let cbor_nondet_destruct_postcond
  (x: cbor_nondet_view)
  (v: Spec.cbor)
: Tot prop
= match x, Spec.unpack v with
  | Int64 _ _, Spec.CInt64 _ _
  | String _ _, Spec.CString _ _
  | Tagged _ _, Spec.CTagged _ _
  | Array _, Spec.CArray _
  | Map _, Spec.CMap _
  | SimpleValue _, Spec.CSimple _
  -> True
  | _ -> False

val cbor_nondet_destruct
  (c: cbornondet)
  (#p: perm)
  (#v: Ghost.erased Spec.cbor)
: stt cbor_nondet_view
    (cbor_nondet_match p c v)
    (fun w -> exists* p' .
      cbor_nondet_view_match p' w v **
      Trade.trade
        (cbor_nondet_view_match p' w v)
        (cbor_nondet_match p c v) **
      pure (cbor_nondet_destruct_postcond w v)
    )

val cbor_nondet_elim_int64 () : Base.elim_int64_t cbor_nondet_match

val cbor_nondet_elim_simple_value () : Base.elim_simple_t cbor_nondet_match

val cbor_nondet_get_array_length
  (x: cbor_nondet_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt U64.t
    (cbor_nondet_array_match p x y)
    (fun res ->
      cbor_nondet_array_match p x y ** pure (
        Base.get_array_length_post y res
      )
    )

val cbor_nondet_array_iterator_t: Type0

noextract [@@noextract_to "krml"]
val cbor_nondet_array_iterator_match: perm -> cbor_nondet_array_iterator_t -> list Spec.cbor -> slprop

val cbor_nondet_array_iterator_start
  (x: cbor_nondet_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt cbor_nondet_array_iterator_t
  (cbor_nondet_array_match p x y)
  (fun res ->
    (exists* p' l' .
      cbor_nondet_array_iterator_match p' res l' **
      Trade.trade
        (cbor_nondet_array_iterator_match p' res l')
        (cbor_nondet_array_match p x y) **
      pure (
        Spec.CArray? (Spec.unpack y) /\
        l' == Spec.CArray?.v (Spec.unpack y)
    ))
  )

val cbor_nondet_array_iterator_is_empty  : Base.array_iterator_is_empty_t cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_next : Base.array_iterator_next_t cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_share : Base.share_t cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_gather : Base.gather_t cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_length: Base.array_iterator_length_t cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_truncate : Base.array_iterator_truncate_t cbor_nondet_array_iterator_match

noextract [@@noextract_to "krml"]
let safe_get_array_item_post
  (x: cbor_nondet_array)
  (i: U64.t)
  (p: perm)
  (y: Spec.cbor)
  (res: option cbornondet)
: Tot slprop
= match res with
  | None -> cbor_nondet_array_match p x y ** pure (Spec.CArray? (Spec.unpack y) /\ U64.v i >= List.Tot.length (Spec.CArray?.v (Spec.unpack y)))
  | Some res' -> exists* p' y' .
    cbor_nondet_match p' res' y' **
    Trade.trade (cbor_nondet_match p' res' y') (cbor_nondet_array_match p x y) **
    pure (Base.get_array_item_post i y y')

noextract [@@noextract_to "krml"]
let cbor_nondet_get_array_item_postcond
  (i: U64.t)
  (y: Spec.cbor)
  (res: option cbornondet)
: Tot prop
= Spec.CArray? (Spec.unpack y) /\
  (Some? res <==> U64.v i < List.Tot.length (Spec.CArray?.v (Spec.unpack y)))

val cbor_nondet_get_array_item
  (x: cbor_nondet_array)
  (i: U64.t)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt (option cbornondet)
    (cbor_nondet_array_match p x y)
    (fun res ->
      safe_get_array_item_post x i p y res **
      pure (cbor_nondet_get_array_item_postcond i y res)
    )

val cbor_nondet_map_length
  (x: cbor_nondet_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt U64.t
    (cbor_nondet_map_match p x y)
    (fun res ->
      cbor_nondet_map_match p x y ** pure (
        Base.get_map_length_post y res
      )
    )

val cbor_nondet_map_iterator_t: Type0

noextract [@@noextract_to "krml"]
val cbor_nondet_map_iterator_match: perm -> cbor_nondet_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_nondet_map_iterator_start
  (x: cbor_nondet_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt cbor_nondet_map_iterator_t
  (cbor_nondet_map_match p x y)
  (fun res ->
    (exists* p' l' .
      cbor_nondet_map_iterator_match p' res l' **
      Trade.trade
        (cbor_nondet_map_iterator_match p' res l')
        (cbor_nondet_map_match p x y) **
      pure (
        Base.map_iterator_start_post y l'
    ))
  )

val cbor_nondet_map_iterator_is_empty : Base.map_iterator_is_empty_t cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_next : Base.map_iterator_next_t cbor_nondet_map_entry_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_share : Base.share_t cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_gather : Base.gather_t cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_key : Base.map_entry_key_t cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_entry_value : Base.map_entry_value_t cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_entry_share : Base.share_t cbor_nondet_map_entry_match

val cbor_nondet_map_entry_gather : Base.gather_t cbor_nondet_map_entry_match

noextract [@@noextract_to "krml"]
let safe_map_get_post
  (x: cbor_nondet_map)
  (px: perm)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (res: option cbornondet)
: Tot slprop
= match res with
  | None ->
    cbor_nondet_map_match px x vx ** pure (Spec.CMap? (Spec.unpack vx) /\ None? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk))
  | Some x' ->
    exists* px' vx' .
      cbor_nondet_match px' x' vx' **
      Trade.trade
        (cbor_nondet_match px' x' vx')
        (cbor_nondet_map_match px x vx) **
      pure (Spec.CMap? (Spec.unpack vx) /\ Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk == Some vx')  

val cbor_nondet_map_get
  (x: cbor_nondet_map)
  (k: cbornondet)
  (#px: perm)
  (#vx: Ghost.erased Spec.cbor)
  (#pk: perm)
  (#vk: Ghost.erased Spec.cbor)
: stt (option cbornondet)
    (cbor_nondet_map_match px x vx ** cbor_nondet_match pk k vk)
    (fun res ->
      cbor_nondet_match pk k vk **
      safe_map_get_post x px vx vk res **
      pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res))
    )

val dummy_cbor_nondet_t (_: unit) : cbornondet
