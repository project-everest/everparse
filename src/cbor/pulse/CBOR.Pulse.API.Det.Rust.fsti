module CBOR.Pulse.API.Det.Rust
open CBOR.Spec.Constants
open Pulse.Lib.Pervasives
module Spec = CBOR.Spec.API.Format
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Base = CBOR.Pulse.API.Base

val cbordet: Type0

noextract [@@noextract_to "krml"]
val cbor_det_match: perm -> cbordet -> Spec.cbor -> slprop

val cbor_det_reset_perm () : Base.reset_perm_t cbor_det_match

val cbor_det_share () : Base.share_t cbor_det_match
val cbor_det_gather () : Base.gather_t cbor_det_match

val cbor_det_parse (_: unit) : Base.cbor_det_parse_t cbor_det_match

noextract [@@noextract_to "krml"]
let cbor_det_size_postcond
  (y: Spec.cbor)
  (bound: SZ.t)
  (res: option SZ.t)
: Tot prop
= let s = Spec.cbor_det_serialize y in
  match res with
  | None -> Seq.length s > SZ.v bound
  | Some len -> Seq.length s == SZ.v len /\ SZ.v len <= SZ.v bound

val cbor_det_size
  (x: cbordet)
  (bound: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
: stt (option SZ.t)
    (cbor_det_match pm x y)
    (fun res -> cbor_det_match pm x y **
      pure (cbor_det_size_postcond y bound res)
    )

val cbor_det_serialize (_: unit) : Base.cbor_det_serialize_t cbor_det_match

(* Constructors *)

noextract [@@noextract_to "krml"]
let cbor_det_mk_simple_value_post
  (v: U8.t)
  (res: option cbordet)
: Tot slprop
= match res with
  | None -> emp
  | Some res' -> exists* v' . cbor_det_match 1.0R res' v' ** pure (simple_value_wf v /\ v' == Spec.pack (Spec.CSimple v))

val cbor_det_mk_simple_value
  (v: U8.t)
: stt (option cbordet)
    emp
    (fun res ->
      cbor_det_mk_simple_value_post v res **
      pure (Some? res <==> simple_value_wf v)
    )

[@@no_auto_projectors]
type cbor_det_int_kind =
 | UInt64
 | NegInt64

val cbor_det_mk_int64
  (ty: cbor_det_int_kind)
  (v: U64.t)
: stt cbordet
    emp
    (fun res -> cbor_det_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v))
    )

[@@no_auto_projectors]
type cbor_det_string_kind =
| ByteString
| TextString

noextract [@@noextract_to "krml"]
let cbor_det_mk_string_post
  (ty: major_type_byte_string_or_text_string)
  (s: S.slice U8.t)
  (p: perm)
  (v: Seq.seq U8.t)
  (res: option cbordet)
= match res with
  | None -> pts_to s #p v
  | Some res' -> exists* v' .
    cbor_det_match 1.0R res' (Spec.pack (Spec.CString ty v')) **
    Trade.trade
      (cbor_det_match 1.0R res' (Spec.pack (Spec.CString ty v')))
      (pts_to s #p v) **
    pure (v' == v)

val cbor_impl_utf8_correct (_: unit) : Base.impl_utf8_correct_t

val cbor_det_mk_string
  (ty: cbor_det_string_kind)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt (option cbordet)
    (pts_to s #p v)
    (fun res ->
      cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v res **
      pure (Some? res <==> (FStar.UInt.fits (SZ.v (S.len s)) U64.n /\ (ty == TextString ==> CBOR.Spec.API.UTF8.correct v))) // this is true for Rust's str/String, but we will check anyway
    )

val cbor_det_mk_tagged: Base.mk_tagged_t cbor_det_match

val cbor_det_map_entry: Type0

noextract [@@noextract_to "krml"]
val cbor_det_map_entry_match: perm -> cbor_det_map_entry -> (Spec.cbor & Spec.cbor) -> slprop

val cbor_det_mk_map_entry : Base.mk_map_entry_t cbor_det_match cbor_det_map_entry_match

module PM = Pulse.Lib.SeqMatch

noextract [@@noextract_to "krml"]
let cbor_det_mk_array_post
  (a: S.slice cbordet)
  (pa: perm)
  (va: (Seq.seq cbordet))
  (pv: perm)
  (vv: (list Spec.cbor))
  (res: option cbordet)
: Tot slprop
= match res with
  | None ->
    pts_to a #pa va **
    PM.seq_list_match va vv (cbor_det_match pv)
  | Some res ->
    exists* v' .
      cbor_det_match 1.0R res (Spec.pack (Spec.CArray v')) **
      Trade.trade
        (cbor_det_match 1.0R res (Spec.pack (Spec.CArray v')))
        (pts_to a #pa va **
          PM.seq_list_match va vv (cbor_det_match pv)
        ) **
        pure (
          v' == vv
        )

val cbor_det_mk_array
  (a: S.slice cbordet)
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq cbordet))
  (#pv: perm)
  (#vv: Ghost.erased (list Spec.cbor))
: stt (option cbordet)
    (pts_to a #pa va **
      PM.seq_list_match va vv (cbor_det_match pv)
    )
    (fun res ->
      cbor_det_mk_array_post a pa va pv vv res **
      pure (Some? res <==> FStar.UInt.fits (SZ.v (S.len a)) U64.n)
    )

val cbor_det_mk_map (_: unit): Base.mk_map_gen_t cbor_det_match cbor_det_map_entry_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_map_from_array : Base.mk_map_from_array_t cbor_det_match cbor_det_map_entry_match =
  Base.mk_map_from_array (CBOR.Pulse.API.Base.mk_map_from_option (cbor_det_mk_map ()))


(* Destructors *)

val cbor_det_equal : Base.equal_t cbor_det_match

val cbor_det_major_type () : Base.get_major_type_t cbor_det_match

noextract [@@noextract_to "krml"]
let cbor_det_tagged_match (p: perm) (tag: U64.t) (payload: cbordet) (v: Spec.cbor) : Tot slprop =
  exists* v' .
    cbor_det_match p payload v' **
    pure (Spec.unpack v == Spec.CTagged tag v')

[@@CAbstractStruct; no_auto_projectors]
val cbor_det_array: Type0

noextract [@@noextract_to "krml"]
val cbor_det_array_match (p: perm) (a: cbor_det_array) (v: Spec.cbor) : Tot slprop

[@@CAbstractStruct; no_auto_projectors]
val cbor_det_map: Type0

noextract [@@noextract_to "krml"]
val cbor_det_map_match (p: perm) (a: cbor_det_map) (v: Spec.cbor) : Tot slprop

noeq [@@no_auto_projectors]
type cbor_det_view =
| Int64: (kind: cbor_det_int_kind) -> (value: U64.t) -> cbor_det_view
| String: (kind: cbor_det_string_kind) -> (payload: S.slice U8.t) -> cbor_det_view
| Array of cbor_det_array
| Map of cbor_det_map
| Tagged: (tag: U64.t) -> (payload: cbordet) -> cbor_det_view
| SimpleValue of simple_value

noextract [@@noextract_to "krml"]
let cbor_det_string_match (t: major_type_byte_string_or_text_string) (p: perm) (a: S.slice U8.t) (v: Spec.cbor) : Tot slprop =
  exists* (v': Seq.seq U8.t) .
    pts_to a #p v' **
    pure (
      Spec.CString? (Spec.unpack v) /\ v' == Spec.CString?.v (Spec.unpack v) /\ t == Spec.CString?.typ (Spec.unpack v) /\
      (t == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v')
    )

noextract [@@noextract_to "krml"]
let cbor_det_view_match
  (p: perm)
  (x: cbor_det_view)
  (v: Spec.cbor)
: Tot slprop
= match x with
  | Int64 k i -> pure (v == Spec.pack (Spec.CInt64 (if UInt64? k then cbor_major_type_uint64 else cbor_major_type_neg_int64) i))
  | String k s -> cbor_det_string_match (if ByteString? k then cbor_major_type_byte_string else cbor_major_type_text_string)  p s v
  | Tagged tag pl -> cbor_det_tagged_match p tag pl v
  | Array a -> cbor_det_array_match p a v
  | Map m -> cbor_det_map_match p m v
  | SimpleValue i -> pure (v == Spec.pack (Spec.CSimple i))

noextract [@@noextract_to "krml"]
let cbor_det_destruct_postcond
  (x: cbor_det_view)
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

val cbor_det_destruct
  (c: cbordet)
  (#p: perm)
  (#v: Ghost.erased Spec.cbor)
: stt cbor_det_view
    (cbor_det_match p c v)
    (fun w -> exists* p' .
      cbor_det_view_match p' w v **
      Trade.trade
        (cbor_det_view_match p' w v)
        (cbor_det_match p c v) **
      pure (cbor_det_destruct_postcond w v)
    )

val cbor_det_elim_int64 () : Base.elim_int64_t cbor_det_match

val cbor_det_elim_simple_value () : Base.elim_simple_t cbor_det_match

val cbor_det_get_array_length
  (x: cbor_det_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt U64.t
    (cbor_det_array_match p x y)
    (fun res ->
      cbor_det_array_match p x y ** pure (
        Base.get_array_length_post y res
      )
    )

val cbor_det_array_iterator_t: Type0

noextract [@@noextract_to "krml"]
val cbor_det_array_iterator_match: perm -> cbor_det_array_iterator_t -> list Spec.cbor -> slprop

val cbor_det_array_iterator_start
  (x: cbor_det_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt cbor_det_array_iterator_t
  (cbor_det_array_match p x y)
  (fun res ->
    (exists* p' l' .
      cbor_det_array_iterator_match p' res l' **
      Trade.trade
        (cbor_det_array_iterator_match p' res l')
        (cbor_det_array_match p x y) **
      pure (
        Spec.CArray? (Spec.unpack y) /\
        l' == Spec.CArray?.v (Spec.unpack y)
    ))
  )

val cbor_det_array_iterator_is_empty  : Base.array_iterator_is_empty_t cbor_det_array_iterator_match

val cbor_det_array_iterator_next : Base.array_iterator_next_t cbor_det_match cbor_det_array_iterator_match

val cbor_det_array_iterator_share : Base.share_t cbor_det_array_iterator_match

val cbor_det_array_iterator_gather : Base.gather_t cbor_det_array_iterator_match

val cbor_det_array_iterator_length: Base.array_iterator_length_t cbor_det_array_iterator_match

val cbor_det_array_iterator_truncate : Base.array_iterator_truncate_t cbor_det_array_iterator_match

noextract [@@noextract_to "krml"]
let safe_get_array_item_post
  (x: cbor_det_array)
  (i: U64.t)
  (p: perm)
  (y: Spec.cbor)
  (res: option cbordet)
: Tot slprop
= match res with
  | None -> cbor_det_array_match p x y ** pure (Spec.CArray? (Spec.unpack y) /\ U64.v i >= List.Tot.length (Spec.CArray?.v (Spec.unpack y)))
  | Some res' -> exists* p' y' .
    cbor_det_match p' res' y' **
    Trade.trade (cbor_det_match p' res' y') (cbor_det_array_match p x y) **
    pure (Base.get_array_item_post i y y')

noextract [@@noextract_to "krml"]
let cbor_det_get_array_item_postcond
  (i: U64.t)
  (y: Spec.cbor)
  (res: option cbordet)
: Tot prop
= Spec.CArray? (Spec.unpack y) /\
  (Some? res <==> U64.v i < List.Tot.length (Spec.CArray?.v (Spec.unpack y)))

val cbor_det_get_array_item
  (x: cbor_det_array)
  (i: U64.t)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt (option cbordet)
    (cbor_det_array_match p x y)
    (fun res ->
      safe_get_array_item_post x i p y res **
      pure (cbor_det_get_array_item_postcond i y res)
    )

val cbor_det_map_length
  (x: cbor_det_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt U64.t
    (cbor_det_map_match p x y)
    (fun res ->
      cbor_det_map_match p x y ** pure (
        Base.get_map_length_post y res
      )
    )

val cbor_det_map_iterator_t: Type0

noextract [@@noextract_to "krml"]
val cbor_det_map_iterator_match: perm -> cbor_det_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_det_map_iterator_start
  (x: cbor_det_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
: stt cbor_det_map_iterator_t
  (cbor_det_map_match p x y)
  (fun res ->
    (exists* p' l' .
      cbor_det_map_iterator_match p' res l' **
      Trade.trade
        (cbor_det_map_iterator_match p' res l')
        (cbor_det_map_match p x y) **
      pure (
        Base.map_iterator_start_post y l'
    ))
  )

val cbor_det_map_iterator_is_empty : Base.map_iterator_is_empty_t cbor_det_map_iterator_match

val cbor_det_map_iterator_next : Base.map_iterator_next_t cbor_det_map_entry_match cbor_det_map_iterator_match

val cbor_det_map_iterator_share : Base.share_t cbor_det_map_iterator_match

val cbor_det_map_iterator_gather : Base.gather_t cbor_det_map_iterator_match

val cbor_det_map_entry_key : Base.map_entry_key_t cbor_det_map_entry_match cbor_det_match

val cbor_det_map_entry_value : Base.map_entry_value_t cbor_det_map_entry_match cbor_det_match

val cbor_det_map_entry_share : Base.share_t cbor_det_map_entry_match

val cbor_det_map_entry_gather : Base.gather_t cbor_det_map_entry_match

noextract [@@noextract_to "krml"]
let safe_map_get_post
  (x: cbor_det_map)
  (px: perm)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (res: option cbordet)
: Tot slprop
= match res with
  | None ->
    cbor_det_map_match px x vx ** pure (Spec.CMap? (Spec.unpack vx) /\ None? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk))
  | Some x' ->
    exists* px' vx' .
      cbor_det_match px' x' vx' **
      Trade.trade
        (cbor_det_match px' x' vx')
        (cbor_det_map_match px x vx) **
      pure (Spec.CMap? (Spec.unpack vx) /\ Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk == Some vx')  

val cbor_det_map_get
  (x: cbor_det_map)
  (k: cbordet)
  (#px: perm)
  (#vx: Ghost.erased Spec.cbor)
  (#pk: perm)
  (#vk: Ghost.erased Spec.cbor)
: stt (option cbordet)
    (cbor_det_map_match px x vx ** cbor_det_match pk k vk)
    (fun res ->
      cbor_det_match pk k vk **
      safe_map_get_post x px vx vk res **
      pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res))
    )

(* NOTE: the following functions have nontrivial hypotheses. They are intended to be used only by the CDDL code generator, or by verified code. *)

val cbor_det_serialize_string: Base.cbor_det_serialize_string_t
val cbor_det_serialize_tag: Base.cbor_det_serialize_tag_t
val cbor_det_serialize_array: Base.cbor_det_serialize_array_t
val cbor_det_serialize_map_insert: Base.cbor_det_serialize_map_insert_t
val cbor_det_serialize_map: Base.cbor_det_serialize_map_t

val dummy_cbor_det_t (_: unit) : cbordet