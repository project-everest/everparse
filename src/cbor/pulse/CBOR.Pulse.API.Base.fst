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
module PM = Pulse.Lib.SeqMatch.Util
module AP = Pulse.Lib.ArrayPtr

let ref_pts_to_or_null
  (#t: Type)
  (r: ref t)
  (p: perm)
  (v: t)
: Tot slprop
= if R.is_null r then emp else pts_to r #p v

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

let read_simple_value_safe_postcond
  (dest: ref U8.t)
  (y: cbor)
  (vdest: U8.t)
  (res: bool)
  (vdest': U8.t)
: Tot prop
=
      res == (CSimple? (unpack y) && not (R.is_null dest)) /\
      (if res
      then CSimple? (unpack y) /\ (CSimple?.v (unpack y) <: U8.t) == vdest'
      else vdest' == Ghost.reveal vdest
      )

inline_for_extraction
let read_simple_value_safe_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (dest: ref U8.t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased U8.t) ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest)
    (fun res -> exists* vdest' . vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest' ** pure (
      read_simple_value_safe_postcond dest y vdest res vdest'
    ))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn read_simple_value_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: read_simple_value_t vmatch)
: read_simple_value_safe_t #_ vmatch
=
  (x: _)
  (dest: _)
  (#p: _)
  (#y: _)
  (#vdest: _)
{
  if (R.is_null dest) {
    false
  } else if (mt x <> cbor_major_type_simple_value) {
    false
  } else {
    rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
    let res = f x;
    dest := res;
    rewrite pts_to dest (res <: U8.t) as ref_pts_to_or_null dest 1.0R res;
    true
  }
}

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

let read_uint64_safe_postcond
  (dest: ref U64.t)
  (y: cbor)
  (vdest: U64.t)
  (res: bool)
  (vdest': U64.t)
: Tot prop
=
      res == (CInt64? (unpack y) && not (R.is_null dest)) /\
      (if res
      then CInt64? (unpack y) /\ (CInt64?.v (unpack y)) == vdest'
      else vdest' == Ghost.reveal vdest
      )

inline_for_extraction
let read_uint64_safe_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (dest: ref U64.t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased U64.t) ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest)
    (fun res -> exists* vdest' . vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest' ** pure (
      read_uint64_safe_postcond dest y vdest res vdest'
    ))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn read_uint64_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: read_uint64_t vmatch)
: read_uint64_safe_t #_ vmatch
=
  (x: _)
  (dest: _)
  (#p: _)
  (#y: _)
  (#vdest: _)
{
  if (R.is_null dest) {
    false
  } else {
    let ty = mt x;
    if (ty <> cbor_major_type_uint64 && ty <> cbor_major_type_neg_int64) {
      false
    } else {
      rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
      let res = f x;
      dest := res;
      rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
      true
    }
  }
}

module I64 = FStar.Int64

let read_int64_safe_postcond
  (dest: ref I64.t)
  (y: cbor)
  (vdest: I64.t)
  (res: bool)
  (vdest': I64.t)
: Tot prop
=
      res == (match unpack y with
      | CInt64 ty v ->
        not (R.is_null dest) && FStar.Int.fits (if ty = cbor_major_type_neg_int64 then -1 - U64.v v else U64.v v) 64
      | _ -> false
      ) /\
      (if res
      then
        let CInt64 ty v = unpack y in
        I64.v vdest' == (if ty = cbor_major_type_neg_int64 then -1 - U64.v v else U64.v v)
      else vdest' == Ghost.reveal vdest
      )

inline_for_extraction
let read_int64_safe_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (dest: ref I64.t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased I64.t) ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest)
    (fun res -> exists* vdest' . vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest' ** pure (
      read_int64_safe_postcond dest y vdest res vdest'
    ))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn read_int64_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: read_uint64_t vmatch)
: read_int64_safe_t #_ vmatch
=
  (x: _)
  (dest: _)
  (#p: _)
  (#y: _)
  (#vdest: _)
{
  if (R.is_null dest) {
    false
  } else {
    let ty = mt x;
    if (ty = cbor_major_type_uint64) {
      let raw = f x;
      if (U64.gt raw 9223372036854775807UL) {
        false
      } else {
        rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
        let res : I64.t = FStar.Int.Cast.uint64_to_int64 raw;
        dest := res;
        rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
        true
      }
    } else if (ty = cbor_major_type_neg_int64) {
      let raw = f x;
      if (U64.gt raw 9223372036854775807UL) {
        false
      } else {
        rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
        let res : I64.t = I64.sub (-1L) (FStar.Int.Cast.uint64_to_int64 raw);
        dest := res;
        rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
        true
      }
    } else {
      false
    }
  }
}

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

inline_for_extraction
let get_string_as_arrayptr_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt (AP.ptr FStar.UInt8.t)
    (vmatch p x y ** pure (CString? (unpack y)))
    (fun res -> exists* p' v' .
      pts_to res #p' v' **
      Trade.trade
        (pts_to res #p' v')
        (vmatch p x y) **
      pure (get_string_post y v')
    )

inline_for_extraction
fn get_string_as_arrayptr
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (f: get_string_t vmatch)
: get_string_as_arrayptr_t #_ vmatch
=
  (x: _)
  (#p: _)
  (#y: _)
{
  let s = f x;
  let res = S.slice_to_arrayptr_intro_trade s;
  Trade.trans _ _ (vmatch p x y);
  res
}

let get_string_as_arrayptr_safe_res
  (ty: option major_type_byte_string_or_text_string)
  (dest: R.ref (AP.ptr U8.t))
  (dlen: R.ref U64.t)
  (y: cbor)
: GTot bool
= (not (R.is_null dest)) &&
  (not (R.is_null dlen)) &&
  CString? (unpack y) &&
  begin if Some? ty then CString?.typ (unpack y) = Some?.v ty else true end

let get_string_as_arrayptr_safe_post_true
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (p: perm)
  (y: cbor)
  (vdest': AP.ptr U8.t)
  (vlen': U64.t)
: Tot slprop
= exists* p' v' .
      pts_to vdest' #p' v' **
      Trade.trade
        (pts_to vdest' #p' v')
        (vmatch p x y) **
      pure (get_string_post y v' /\
        U64.v vlen' == Seq.length v'
      )

let get_string_as_arrayptr_safe_post_false
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (p: perm)
  (y: Ghost.erased cbor)
  (vdest: (AP.ptr U8.t))
  (vlen: U64.t)
  (vdest': AP.ptr U8.t)
  (vlen': U64.t)
: slprop
= vmatch p x y ** pure (vdest' == vdest /\ vlen' == vlen)

let get_string_as_arrayptr_safe_post
  (ty: option major_type_byte_string_or_text_string)
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (dest: R.ref (AP.ptr U8.t))
  (dlen: R.ref U64.t)
  (p: perm)
  (y: cbor)
  (vdest: (AP.ptr U8.t))
  (vlen: U64.t)
  (vdest': AP.ptr U8.t)
  (vlen': U64.t)
: Tot slprop
= if get_string_as_arrayptr_safe_res ty dest dlen y
  then get_string_as_arrayptr_safe_post_true vmatch x p y vdest' vlen'
  else get_string_as_arrayptr_safe_post_false vmatch x p y vdest vlen vdest' vlen'

inline_for_extraction
let get_string_as_arrayptr_safe_gen_t
  (ty: option major_type_byte_string_or_text_string)
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (dest: R.ref (AP.ptr U8.t)) ->
  (dlen: R.ref U64.t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased (AP.ptr U8.t)) ->
  (#vlen: Ghost.erased U64.t) ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest ** ref_pts_to_or_null dlen 1.0R vlen)
    (fun res -> exists* vdest' vlen' .
      ref_pts_to_or_null dest 1.0R vdest' ** ref_pts_to_or_null dlen 1.0R vlen' **
      get_string_as_arrayptr_safe_post ty vmatch x dest dlen p y vdest vlen vdest' vlen' **
      pure (res == get_string_as_arrayptr_safe_res ty dest dlen y)
    )

inline_for_extraction
let get_string_as_arrayptr_safe_t = get_string_as_arrayptr_safe_gen_t None

inline_for_extraction
noextract [@@noextract_to "krml"]
fn get_string_as_arrayptr_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: get_string_length_t vmatch)
  (g: get_string_as_arrayptr_t vmatch)
: get_string_as_arrayptr_safe_t #_ vmatch
=
  (x: _)
  (dest: _)
  (dlen: _)
  (#p: _)
  (#y: _)
  (#vdest: _)
  (#vlen: _)
{
  if (R.is_null dest || R.is_null dlen) {
    fold (get_string_as_arrayptr_safe_post_false vmatch x p y vdest vlen vdest vlen);
    rewrite (get_string_as_arrayptr_safe_post_false vmatch x p y vdest vlen vdest vlen)
      as (get_string_as_arrayptr_safe_post None vmatch x dest dlen p y vdest vlen vdest vlen);
    false
  } else {
    let ty = mt x;
    if (ty <> cbor_major_type_byte_string && ty <> cbor_major_type_text_string) {
      fold (get_string_as_arrayptr_safe_post_false vmatch x p y vdest vlen vdest vlen);
      rewrite (get_string_as_arrayptr_safe_post_false vmatch x p y vdest vlen vdest vlen)
        as (get_string_as_arrayptr_safe_post None vmatch x dest dlen p y vdest vlen vdest vlen);
      false
    } else {
      rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
      rewrite ref_pts_to_or_null dlen 1.0R vlen as pts_to dlen vlen;
      let len = f x;
      let res = g x;
      dlen := len;
      dest := res;
      rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
      rewrite pts_to dlen len as ref_pts_to_or_null dlen 1.0R len;
      fold (get_string_as_arrayptr_safe_post_true vmatch x p y res len);
      rewrite (get_string_as_arrayptr_safe_post_true vmatch x p y res len) as
        (get_string_as_arrayptr_safe_post None vmatch x dest dlen p y vdest vlen res len);
      true
    }
  }
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn get_string_as_arrayptr_safe_gen
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: get_string_as_arrayptr_safe_t vmatch)
  (ty: major_type_byte_string_or_text_string)
: get_string_as_arrayptr_safe_gen_t (Some ty) #_ vmatch
=
  (x: _)
  (dest: _)
  (dlen: _)
  (#p: _)
  (#y: _)
  (#vdest: _)
  (#vlen: _)
{
  if (mt x <> ty) {
    fold (get_string_as_arrayptr_safe_post_false vmatch x p y vdest vlen vdest vlen);
    rewrite (get_string_as_arrayptr_safe_post_false vmatch x p y vdest vlen vdest vlen)
      as (get_string_as_arrayptr_safe_post (Some ty) vmatch x
      dest dlen p y vdest vlen vdest vlen);
    false
  } else {
    let res = f x dest dlen;
    with vdest' vlen' . rewrite (get_string_as_arrayptr_safe_post None vmatch x dest dlen p y vdest vlen
      vdest' vlen')
    as (get_string_as_arrayptr_safe_post (Some ty) vmatch x dest dlen p y vdest vlen
      vdest' vlen');
    res
  }
}


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

let get_tagged_safe_res
  (#t: Type)
  (dest: R.ref t)
  (dtag: R.ref U64.t)
  (y: cbor)
: GTot bool
= (not (R.is_null dest)) &&
  (not (R.is_null dtag)) &&
  CTagged? (unpack y)

let get_tagged_safe_post_true
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (p: perm)
  (y: cbor)
  (vdest': t)
  (vtag': U64.t)
: Tot slprop
= exists* p' v' .
      vmatch p' vdest' v' **
      Trade.trade
        (vmatch p' vdest' v')
        (vmatch p x y) **
      pure (y == pack (CTagged vtag' v'))

let get_tagged_safe_post_false
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (p: perm)
  (y: cbor)
  (vdest: t)
  (vtag: U64.t)
  (vdest': t)
  (vtag': U64.t)
: slprop
= vmatch p x y ** pure (vdest' == vdest /\ vtag' == vtag)

let get_tagged_safe_post
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (dest: R.ref t)
  (dtag: R.ref U64.t)
  (p: perm)
  (y: cbor)
  (vdest: t)
  (vtag: U64.t)
  (vdest': t)
  (vtag': U64.t)
: Tot slprop
= if get_tagged_safe_res dest dtag y
  then get_tagged_safe_post_true vmatch x p y vdest' vtag'
  else get_tagged_safe_post_false vmatch x p y vdest vtag vdest' vtag'

inline_for_extraction
let get_tagged_safe_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (dest: R.ref t) ->
  (dtag: R.ref U64.t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased t) ->
  (#vtag: Ghost.erased U64.t) ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest ** ref_pts_to_or_null dtag 1.0R vtag)
    (fun res -> exists* vdest' vtag' .
      ref_pts_to_or_null dest 1.0R vdest' ** ref_pts_to_or_null dtag 1.0R vtag' **
      get_tagged_safe_post vmatch x dest dtag p y vdest vtag vdest' vtag' **
      pure (res == get_tagged_safe_res dest dtag y)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn get_tagged_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: get_tagged_tag_t vmatch)
  (g: get_tagged_payload_t vmatch)
: get_tagged_safe_t #_ vmatch
=
  (x: _)
  (dest: _)
  (dtag: _)
  (#p: _)
  (#y: _)
  (#vdest: _)
  (#vtag: _)
{
  if (R.is_null dest || R.is_null dtag) {
    fold (get_tagged_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vtag) (Ghost.reveal vdest) (Ghost.reveal vtag));
    rewrite (get_tagged_safe_post_false vmatch x p y vdest vtag vdest vtag)
      as (get_tagged_safe_post vmatch x dest dtag p y vdest vtag vdest vtag);
    false
  } else if (mt x <> cbor_major_type_tagged) {
    fold (get_tagged_safe_post_false vmatch x p y vdest vtag vdest vtag);
    rewrite (get_tagged_safe_post_false vmatch x p y vdest vtag vdest vtag)
      as (get_tagged_safe_post vmatch x dest dtag p y vdest vtag vdest vtag);
    false
  } else {
    rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
    rewrite ref_pts_to_or_null dtag 1.0R vtag as pts_to dtag vtag;
    let tag = f x;
    let res = g x;
    dtag := tag;
    dest := res;
    rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
    rewrite pts_to dtag tag as ref_pts_to_or_null dtag 1.0R tag;
    fold (get_tagged_safe_post_true vmatch x p y res tag);
    rewrite (get_tagged_safe_post_true vmatch x p y res tag) as
      (get_tagged_safe_post vmatch x dest dtag p y vdest vtag res tag);
    true
  }
}

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

inline_for_extraction
let get_array_length_safe_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (dest: R.ref U64.t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased U64.t) ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest)
    (fun b ->
      exists* vdest' . vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest' ** pure (
        b == ((not (R.is_null dest)) && CArray? (unpack y)) /\
        (b == true ==> get_array_length_post y vdest') /\
        (b == false ==> vdest' == Ghost.reveal vdest)
      )
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn get_array_length_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: get_array_length_t vmatch)
: get_array_length_safe_t #_ vmatch
= (x: t)
  (dest: R.ref U64.t)
  (#p: perm)
  (#y: Ghost.erased cbor)
  (#vdest: Ghost.erased U64.t)
{
  if (R.is_null dest) {
    false
  } else if (mt x <> cbor_major_type_array) {
    false
  } else {
    rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
    let len = f x;
    dest := len;
    rewrite pts_to dest len as ref_pts_to_or_null dest 1.0R len;
    true
  }
}

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

let get_array_item_safe_res
  (#t: Type)
  (i: U64.t)
  (dest: R.ref t)
  (y: cbor)
: GTot bool
= (not (R.is_null dest)) &&
  CArray? (unpack y) &&
  U64.v i < List.Tot.length (CArray?.v (unpack y))

let get_array_item_safe_post_true
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (i: U64.t)
  (p: perm)
  (y: cbor)
  (vdest': t)
: Tot slprop
= exists* p' y' .
      vmatch p' vdest' y' **
      Trade.trade (vmatch p' vdest' y') (vmatch p x y) **
      pure (get_array_item_post i y y')

let get_array_item_safe_post_false
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (p: perm)
  (y: cbor)
  (vdest: t)
  (vdest': t)
: slprop
= vmatch p x y ** pure (vdest' == vdest)

let get_array_item_safe_post
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (i: U64.t)
  (dest: R.ref t)
  (p: perm)
  (y: cbor)
  (vdest: t)
  (vdest': t)
: Tot slprop
= if get_array_item_safe_res i dest y
  then get_array_item_safe_post_true vmatch x i p y vdest'
  else get_array_item_safe_post_false vmatch x p y vdest vdest'

inline_for_extraction
let get_array_item_safe_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (i: U64.t) ->
  (dest: R.ref t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased t) ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest)
    (fun res -> exists* vdest' .
      ref_pts_to_or_null dest 1.0R vdest' **
      get_array_item_safe_post vmatch x i dest p y vdest vdest' **
      pure (res == get_array_item_safe_res i dest y)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn get_array_item_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: get_array_length_t vmatch)
  (g: get_array_item_t vmatch)
: get_array_item_safe_t #_ vmatch
=
  (x: _)
  (i: _)
  (dest: _)
  (#p: _)
  (#y: _)
  (#vdest: _)
{
  if (R.is_null dest) {
    fold (get_array_item_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest));
    rewrite (get_array_item_safe_post_false vmatch x p y vdest vdest)
      as (get_array_item_safe_post vmatch x i dest p y vdest vdest);
    false
  } else if (mt x <> cbor_major_type_array) {
    fold (get_array_item_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest));
    rewrite (get_array_item_safe_post_false vmatch x p y vdest vdest)
      as (get_array_item_safe_post vmatch x i dest p y vdest vdest);
    false
  } else if (U64.lte (f x) i) {
    fold (get_array_item_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest));
    rewrite (get_array_item_safe_post_false vmatch x p y vdest vdest)
      as (get_array_item_safe_post vmatch x i dest p y vdest vdest);
    false
  } else {
    rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
    let res = g x i;
    dest := res;
    rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
    fold (get_array_item_safe_post_true vmatch x i p y res);
    rewrite (get_array_item_safe_post_true vmatch x i p y res) as
      (get_array_item_safe_post vmatch x i dest p y vdest res);
    true
  }
}

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

let array_iterator_start_safe_res
  (#t': Type)
  (dest: R.ref t')
  (y: cbor)
: GTot bool
= (not (R.is_null dest)) &&
  CArray? (unpack y)

let array_iterator_start_safe_post_true
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list cbor -> slprop)
  (x: t)
  (p: perm)
  (y: cbor)
  (vdest': t')
: Tot slprop
= exists* p' l' .
      iter p' vdest' l' **
      Trade.trade
        (iter p' vdest' l')
        (vmatch p x y) **
      pure (
        unpack y == CArray l'
    )

let array_iterator_start_safe_post_false
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (p: perm)
  (y: cbor)
  (vdest: t')
  (vdest': t')
: slprop
= vmatch p x y ** pure (vdest' == vdest)

let array_iterator_start_safe_post
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list cbor -> slprop)
  (x: t)
  (dest: R.ref t')
  (p: perm)
  (y: cbor)
  (vdest: t')
  (vdest': t')
: Tot slprop
= if array_iterator_start_safe_res dest y
  then array_iterator_start_safe_post_true vmatch iter x p y vdest'
  else array_iterator_start_safe_post_false vmatch x p y vdest vdest'

inline_for_extraction
let array_iterator_start_safe_t
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list cbor -> slprop)
= (x: t) ->
  (dest: R.ref t') ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased t') ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest)
    (fun res -> exists* vdest' .
      ref_pts_to_or_null dest 1.0R vdest' **
      array_iterator_start_safe_post vmatch iter x dest p y vdest vdest' **
      pure (res == array_iterator_start_safe_res dest y)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn array_iterator_start_safe
  (#t #t': Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#iter: perm -> t' -> list cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (g: array_iterator_start_t vmatch iter)
: array_iterator_start_safe_t #_ #_ vmatch iter
=
  (x: _)
  (dest: _)
  (#p: _)
  (#y: _)
  (#vdest: _)
{
  if (R.is_null dest) {
    fold (array_iterator_start_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest));
    rewrite (array_iterator_start_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest))
      as (array_iterator_start_safe_post vmatch iter x dest p y vdest vdest);
    false
  } else if (mt x <> cbor_major_type_array) {
    fold (array_iterator_start_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest));
    rewrite (array_iterator_start_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest))
      as (array_iterator_start_safe_post vmatch iter x dest p y vdest vdest);
    false
  } else {
    rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
    let res = g x;
    dest := res;
    rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
    fold (array_iterator_start_safe_post_true vmatch iter x p y res);
    rewrite (array_iterator_start_safe_post_true vmatch iter x p y res) as
      (array_iterator_start_safe_post vmatch iter x dest p y vdest res);
    true
  }
}

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
    (fun res -> exists* p' py' v' y' z' .
      vmatch p' res v' **
      R.pts_to x y' **
      iter py' y' z' **
      Trade.trade
        (vmatch p' res v' ** iter py' y' z')
        (iter py y z) **
      pure (Ghost.reveal z == v' :: z')
    )

let array_iterator_next_safe_res
  (#t #t': Type)
  (x: R.ref t')
  (dest: R.ref t)
  (y: list cbor)
: GTot bool
= (not (R.is_null x)) &&
  (not (R.is_null dest)) &&
  Cons? y

let array_iterator_next_safe_post_true
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list cbor -> slprop)
  (y: t')
  (p: perm)
  (z: list cbor)
  (y': t')
  (vdest': t)
: Tot slprop
= exists* p' py' v' z' .
      vmatch p' vdest' v' **
      iter py' y' z' **
      Trade.trade
        (vmatch p' vdest' v' ** iter py' y' z')
        (iter p y z) **
      pure (z == v' :: z')

let array_iterator_next_safe_post_false
  (#t #t': Type)
  (iter: perm -> t' -> list cbor -> slprop)
  (y: t')
  (p: perm)
  (z: list cbor)
  (vdest: t)
  (y': t')
  (vdest': t)
: slprop
= iter p y z ** pure (y' == y /\ vdest' == vdest)

let array_iterator_next_safe_post
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list cbor -> slprop)
  (x: R.ref t')
  (dest: R.ref t)
  (y: t')
  (p: perm)
  (z: list cbor)
  (vdest: t)
  (y': t')
  (vdest': t)
: Tot slprop
= if array_iterator_next_safe_res x dest z
  then array_iterator_next_safe_post_true vmatch iter y p z y' vdest'
  else array_iterator_next_safe_post_false iter y p z vdest y' vdest'

inline_for_extraction
let array_iterator_next_safe_t
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list cbor -> slprop)
= (x: R.ref t') ->
  (dest: R.ref t) ->
  (#y: Ghost.erased t') ->
  (#p: perm) ->
  (#z: Ghost.erased (list cbor)) ->
  (#vdest: Ghost.erased t) ->
  stt bool
    (ref_pts_to_or_null x 1.0R y ** iter p y z ** ref_pts_to_or_null dest 1.0R vdest)
    (fun res -> exists* y' vdest' .
      ref_pts_to_or_null x 1.0R y' **
      ref_pts_to_or_null dest 1.0R vdest' **
      array_iterator_next_safe_post vmatch iter x dest y p z vdest y' vdest' **
      pure (res == array_iterator_next_safe_res x dest z)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn array_iterator_next_safe
  (#t #t': Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#iter: perm -> t' -> list cbor -> slprop)
  (f: array_iterator_is_empty_t iter)
  (g: array_iterator_next_t vmatch iter)
: array_iterator_next_safe_t #_ #_ vmatch iter
=
  (x: _)
  (dest: _)
  (#y: _)
  (#p: _)
  (#z: _)
  (#vdest: _)
{
  if (R.is_null x || R.is_null dest) {
    fold (array_iterator_next_safe_post_false iter y p z (Ghost.reveal vdest) y (Ghost.reveal vdest));
    rewrite (array_iterator_next_safe_post_false iter y p z (Ghost.reveal vdest) y (Ghost.reveal vdest))
      as array_iterator_next_safe_post vmatch iter x dest y p z vdest y vdest;
    false
  } else {
    rewrite ref_pts_to_or_null x 1.0R y as pts_to x y;
    let y = !x;
    if f y {
      rewrite pts_to x y as ref_pts_to_or_null x 1.0R y;
      fold (array_iterator_next_safe_post_false iter y p z (Ghost.reveal vdest) y (Ghost.reveal vdest));
      rewrite (array_iterator_next_safe_post_false iter y p z (Ghost.reveal vdest) y (Ghost.reveal vdest))
        as array_iterator_next_safe_post vmatch iter x dest y p z vdest y vdest;
      false
    } else {
      rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
      let res = g x;
      dest := res;
      rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
      with p' y' z' . assert (pts_to x y' ** iter p' y' z');
      rewrite pts_to x y' as ref_pts_to_or_null x 1.0R y';
      fold (array_iterator_next_safe_post_true vmatch iter y p z y' res);
      rewrite (array_iterator_next_safe_post_true vmatch iter y p z y' res) as
        array_iterator_next_safe_post vmatch iter x dest y p z vdest y' res;
      true
    }
  }
}

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
    (fun res -> exists* p' .
      iter p' res (fst (List.Tot.splitAt (U64.v len) y)) **
      Trade.trade
        (iter p' res (fst (List.Tot.splitAt (U64.v len) y)))
        (iter p x y)
    )

(* TODO: array_iterator_truncate_safe_t *)

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

inline_for_extraction
let get_map_length_safe_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (dest: R.ref U64.t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased U64.t) ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest)
    (fun b ->
      exists* vdest' . vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest' ** pure (
        b == ((not (R.is_null dest)) && CMap? (unpack y)) /\
        (b == true ==> get_map_length_post y vdest') /\
        (b == false ==> vdest' == Ghost.reveal vdest)
      )
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn get_map_length_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: get_map_length_t vmatch)
: get_map_length_safe_t #_ vmatch
= (x: t)
  (dest: R.ref U64.t)
  (#p: perm)
  (#y: Ghost.erased cbor)
  (#vdest: Ghost.erased U64.t)
{
  if (R.is_null dest) {
    false
  } else if (mt x <> cbor_major_type_map) {
    false
  } else {
    rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
    let len = f x;
    dest := len;
    rewrite pts_to dest len as ref_pts_to_or_null dest 1.0R len;
    true
  }
}

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

let map_iterator_start_safe_res
  (#t': Type)
  (dest: R.ref t')
  (y: cbor)
: GTot bool
= (not (R.is_null dest)) &&
  CMap? (unpack y)

let map_iterator_start_safe_post_true
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
  (x: t)
  (p: perm)
  (y: cbor)
  (vdest': t')
: Tot slprop
= exists* p' l' .
      iter p' vdest' l' **
      Trade.trade
        (iter p' vdest' l')
        (vmatch p x y) **
      pure (
        map_iterator_start_post y l'
    )

let map_iterator_start_safe_post_false
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (x: t)
  (p: perm)
  (y: cbor)
  (vdest: t')
  (vdest': t')
: slprop
= vmatch p x y ** pure (vdest' == vdest)

let map_iterator_start_safe_post
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
  (x: t)
  (dest: R.ref t')
  (p: perm)
  (y: cbor)
  (vdest: t')
  (vdest': t')
: Tot slprop
= if map_iterator_start_safe_res dest y
  then map_iterator_start_safe_post_true vmatch iter x p y vdest'
  else map_iterator_start_safe_post_false vmatch x p y vdest vdest'

inline_for_extraction
let map_iterator_start_safe_t
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
= (x: t) ->
  (dest: R.ref t') ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  (#vdest: Ghost.erased t') ->
  stt bool
    (vmatch p x y ** ref_pts_to_or_null dest 1.0R vdest)
    (fun res -> exists* vdest' .
      ref_pts_to_or_null dest 1.0R vdest' **
      map_iterator_start_safe_post vmatch iter x dest p y vdest vdest' **
      pure (res == map_iterator_start_safe_res dest y)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn map_iterator_start_safe
  (#t #t': Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#iter: perm -> t' -> list (cbor & cbor) -> slprop)
  (mt: get_major_type_t vmatch)
  (g: map_iterator_start_t vmatch iter)
: map_iterator_start_safe_t #_ #_ vmatch iter
=
  (x: _)
  (dest: _)
  (#p: _)
  (#y: _)
  (#vdest: _)
{
  if (R.is_null dest) {
    fold (map_iterator_start_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest));
    rewrite (map_iterator_start_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest))
      as (map_iterator_start_safe_post vmatch iter x dest p y vdest vdest);
    false
  } else if (mt x <> cbor_major_type_map) {
    fold (map_iterator_start_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest));
    rewrite (map_iterator_start_safe_post_false vmatch x p y (Ghost.reveal vdest) (Ghost.reveal vdest))
      as (map_iterator_start_safe_post vmatch iter x dest p y vdest vdest);
    false
  } else {
    rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
    let res = g x;
    dest := res;
    rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
    fold (map_iterator_start_safe_post_true vmatch iter x p y res);
    rewrite (map_iterator_start_safe_post_true vmatch iter x p y res) as
      (map_iterator_start_safe_post vmatch iter x dest p y vdest res);
    true
  }
}

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
    (fun res -> exists* py' p' v' y' z' .
      vmatch2 p' res v' **
      R.pts_to x y' **
      iter py' y' z' **
      Trade.trade
        (vmatch2 p' res v' ** iter py' y' z')
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

let map_iterator_next_safe_res
  (#t #t': Type)
  (x: R.ref t')
  (dest_key dest_value: R.ref t)
  (y: list (cbor & cbor))
: GTot bool
= (not (R.is_null x)) &&
  (not (R.is_null dest_key)) &&
  (not (R.is_null dest_value)) &&
  Cons? y

let map_iterator_next_safe_post_true
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
  (y: t')
  (p: perm)
  (z: list (cbor & cbor))
  (y': t')
  (vdest_key': t)
  (vdest_value': t)
: Tot slprop
= exists* pkey pvalue py' vk' vv' z' .
      vmatch pkey vdest_key' vk' **
      vmatch pvalue vdest_value' vv' **
      iter py' y' z' **
      Trade.trade
        ((vmatch pkey vdest_key' vk' ** vmatch pvalue vdest_value' vv') ** iter py' y' z')
        (iter p y z) **
      pure (z == (vk', vv') :: z')

let map_iterator_next_safe_post_false
  (#t #t': Type)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
  (y: t')
  (p: perm)
  (z: list (cbor & cbor))
  (vdest_key: t)
  (vdest_value: t)
  (y': t')
  (vdest_key': t)
  (vdest_value': t)
: slprop
= iter p y z ** pure (y' == y /\ vdest_key' == vdest_key /\ vdest_value' == vdest_value)

let map_iterator_next_safe_post
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
  (x: R.ref t')
  (dest_key: R.ref t)
  (dest_value: R.ref t)
  (y: t')
  (p: perm)
  (z: list (cbor & cbor))
  (vdest_key vdest_value: t)
  (y': t')
  (vdest_key' vdest_value': t)
: Tot slprop
= if map_iterator_next_safe_res x dest_key dest_value z
  then map_iterator_next_safe_post_true vmatch iter y p z y' vdest_key' vdest_value'
  else map_iterator_next_safe_post_false iter y p z vdest_key vdest_value y' vdest_key' vdest_value'

inline_for_extraction
let map_iterator_next_safe_t
  (#t #t': Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (iter: perm -> t' -> list (cbor & cbor) -> slprop)
= (x: R.ref t') ->
  (dest_key: R.ref t) ->
  (dest_value: R.ref t) ->
  (#y: Ghost.erased t') ->
  (#p: perm) ->
  (#z: Ghost.erased (list (cbor & cbor))) ->
  (#vdest_key: Ghost.erased t) ->
  (#vdest_value: Ghost.erased t) ->
  stt bool
    (ref_pts_to_or_null x 1.0R y ** iter p y z ** 
      ref_pts_to_or_null dest_key 1.0R vdest_key **
      ref_pts_to_or_null dest_value 1.0R vdest_value
    )
    (fun res -> exists* y' vdest_key' vdest_value' .
      ref_pts_to_or_null x 1.0R y' **
      ref_pts_to_or_null dest_key 1.0R vdest_key' **
      ref_pts_to_or_null dest_value 1.0R vdest_value' **
      map_iterator_next_safe_post vmatch iter x dest_key dest_value y p z vdest_key vdest_value y' vdest_key' vdest_value' **
      pure (res == map_iterator_next_safe_res x dest_key dest_value z)
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

ghost fn share_gather_trade
  (#t1 #t2: Type0)
  (#vmatch: perm -> t1 -> t2 -> slprop)
  (share: share_t vmatch)
  (gather: gather_t vmatch)
  (x1: t1)
  (#p: perm)
  (#x2: t2)
requires
  vmatch p x1 x2
returns p': Ghost.erased perm // FIXME: Pulse should detect perm as erasable type, but currently doesn't
ensures
  vmatch p' x1 x2 ** vmatch p' x1 x2 **
  Trade.trade
    (vmatch p' x1 x2 ** vmatch p' x1 x2)
    (vmatch p x1 x2)
{
  share x1;
  intro
    (Trade.trade
      (vmatch (p /. 2.0R) x1 x2 ** vmatch (p /. 2.0R) x1 x2)
      (vmatch p x1 x2)
    )
    fn _ {
      gather x1;
      rewrite vmatch (p /. 2.0R +. p /. 2.0R) x1 x2 as vmatch p x1 x2
    };
  (p /. 2.0R)
}  

inline_for_extraction
noextract [@@noextract_to "krml"]
fn map_iterator_next_safe
  (#t #t' #t2: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (#vmatch2: perm -> t2 -> cbor & cbor -> slprop)
  (#iter: perm -> t' -> list (cbor & cbor) -> slprop)
  (f: map_iterator_is_empty_t iter)
  (g: map_iterator_next_t vmatch2 iter)
  (gshare: share_t vmatch2)
  (ggather: gather_t vmatch2)
  (gkey: map_entry_key_t vmatch2 vmatch)
  (gvalue: map_entry_value_t vmatch2 vmatch)
: map_iterator_next_safe_t #_ #_ vmatch iter
=
  (x: _)
  (dest_key: _)
  (dest_value: _)
  (#y: _)
  (#p: _)
  (#z: _)
  (#vdest_key: _)
  (#vdest_value: _)
{
  if (R.is_null x || R.is_null dest_key || R.is_null dest_value) {
    fold (map_iterator_next_safe_post_false iter y p z (Ghost.reveal vdest_key) (Ghost.reveal vdest_value) y (Ghost.reveal vdest_key) (Ghost.reveal vdest_value));
    rewrite (map_iterator_next_safe_post_false iter y p z (Ghost.reveal vdest_key) (Ghost.reveal vdest_value) y (Ghost.reveal vdest_key) (Ghost.reveal vdest_value))
      as map_iterator_next_safe_post vmatch iter x dest_key dest_value y p z vdest_key vdest_value y vdest_key vdest_value;
    false
  } else {
    rewrite ref_pts_to_or_null x 1.0R y as pts_to x y;
    let y = !x;
    if f y {
      rewrite pts_to x y as ref_pts_to_or_null x 1.0R y;
      fold (map_iterator_next_safe_post_false iter y p z (Ghost.reveal vdest_key) (Ghost.reveal vdest_value) y (Ghost.reveal vdest_key) (Ghost.reveal vdest_value));
      rewrite (map_iterator_next_safe_post_false iter y p z (Ghost.reveal vdest_key) (Ghost.reveal vdest_value) y (Ghost.reveal vdest_key) (Ghost.reveal vdest_value))
        as map_iterator_next_safe_post vmatch iter x dest_key dest_value y p z vdest_key vdest_value y vdest_key vdest_value;
      false
    } else {
      rewrite ref_pts_to_or_null dest_key 1.0R vdest_key as pts_to dest_key vdest_key;
      rewrite ref_pts_to_or_null dest_value 1.0R vdest_value as pts_to dest_value vdest_value;
      let res = g x;
      with pres vres . assert (vmatch2 pres res vres);
      gshare res;
      intro
        (Trade.trade
          (vmatch2 (pres /. 2.0R) res vres ** vmatch2 (pres /. 2.0R) res vres)
          (vmatch2 pres res vres)
        )
        fn _ {
          ggather res;
          rewrite vmatch2 (pres /. 2.0R +. pres /. 2.0R) res vres
            as vmatch2 pres res vres
        };
      let res_key = gkey res;
      Trade.trans_hyp_l _ _ _ (vmatch2 pres res vres);
      let res_value = gvalue res;
      Trade.trans_hyp_r _ _ _ (vmatch2 pres res vres);
      Trade.trans_hyp_l _ (vmatch2 pres res vres) _ _;
      dest_key := res_key;
      dest_value := res_value;
      rewrite pts_to dest_key res_key as ref_pts_to_or_null dest_key 1.0R res_key;
      rewrite pts_to dest_value res_value as ref_pts_to_or_null dest_value 1.0R res_value;
      with p' y' z' . assert (pts_to x y' ** iter p' y' z');
      rewrite pts_to x y' as ref_pts_to_or_null x 1.0R y';
      fold (map_iterator_next_safe_post_true vmatch iter y p z y' res_key res_value);
      rewrite (map_iterator_next_safe_post_true vmatch iter y p z y' res_key res_value) as
        map_iterator_next_safe_post vmatch iter x dest_key dest_value y p z vdest_key vdest_value y' res_key res_value;
      true
    }
  }
}

inline_for_extraction
let reset_perm_t
  (#t1 #t2: Type)
  (vmatch: perm -> t1 -> t2 -> slprop)
=
  (x1: t1) ->
  (#p: perm) ->
  (#x2: Ghost.erased t2) ->
  (q: perm) ->
  stt t1
    (vmatch p x1 x2)
    (fun res -> vmatch q res x2 **
      Trade.trade (vmatch q res x2) (vmatch p x1 x2)
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

let mk_simple_safe_res
  (#t: Type)
  (v: U8.t)
  (dest: R.ref t)
: GTot bool
= simple_value_wf v && not (R.is_null dest)

let mk_simple_safe_post
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (v: U8.t)
  (dest: R.ref t)
  (w: t)
  (w': t)
: Tot slprop
= if mk_simple_safe_res v dest
  then vmatch 1.0R w' (pack (CSimple v))
  else pure (w' == w)

inline_for_extraction
let mk_simple_safe_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
=
  (v: U8.t) ->
  (dest: R.ref t) ->
  (#w: Ghost.erased t) ->
  stt bool
    (ref_pts_to_or_null dest 1.0R w)
    (fun res -> exists* w' .
      ref_pts_to_or_null dest 1.0R w' **
      mk_simple_safe_post vmatch v dest w w' **
      pure (res == mk_simple_safe_res v dest)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_simple_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (f: mk_simple_t vmatch)
: mk_simple_safe_t #_ vmatch
=
  (v: _)
  (dest: _)
  (#w: _)
{
  if (R.is_null dest || not (simple_value_wf v)) {
    rewrite (pure (Ghost.reveal w == Ghost.reveal w)) as (mk_simple_safe_post vmatch v dest w w);
    false
  } else {
    rewrite ref_pts_to_or_null dest 1.0R w as pts_to dest w;
    let res = f v;
    dest := res;
    rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
    rewrite (vmatch 1.0R res (pack (CSimple v))) as (mk_simple_safe_post vmatch v dest w res);
    true
  }
}

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
let mk_int64_gen_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (ty: major_type_uint64_or_neg_int64)
= (v: U64.t) ->
  stt t
    (emp)
    (fun res -> vmatch 1.0R res (pack (CInt64 ty v)))

inline_for_extraction
let mk_int64_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (ty: major_type_uint64_or_neg_int64) ->
  mk_int64_gen_t vmatch ty

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_int64_dispatch
  (#t: Type0)
  (vmatch: perm -> t -> cbor -> slprop)
  (mk_uint64: mk_int64_gen_t #_ vmatch cbor_major_type_uint64)
  (mk_neg_int64: mk_int64_gen_t #_ vmatch cbor_major_type_neg_int64)
: mk_int64_t #_ vmatch
= (ty: _)
  (v: _)
{
  let ty2 = ty;
  if (ty2 = cbor_major_type_uint64) {
    let res = mk_uint64 v;
    rewrite (vmatch 1.0R res (pack (CInt64 cbor_major_type_uint64 v))) as (vmatch 1.0R res (pack (CInt64 ty v)));
    res
  } else {
    let res = mk_neg_int64 v;
    rewrite (vmatch 1.0R res (pack (CInt64 cbor_major_type_neg_int64 v))) as (vmatch 1.0R res (pack (CInt64 ty v)));
    res
  }
}

let major_int_type_of_int (x: int) : major_type_uint64_or_neg_int64 =
  if x < 0 then cbor_major_type_neg_int64 else cbor_major_type_uint64

let int_as_ones_complement_nat (x: int) : nat =
  if x < 0 then -1 - x else x

inline_for_extraction
let mk_signed_int64_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (v: I64.t) ->
  stt t
    (emp)
    (fun res -> vmatch 1.0R res (pack (CInt64 (major_int_type_of_int (I64.v v)) (U64.uint_to_t (int_as_ones_complement_nat (I64.v v))))))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_signed_int64
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (f: mk_int64_t vmatch)
: mk_signed_int64_t #_ vmatch
= (v: _)
{
  if (I64.lt v 0L) {
    let res = f cbor_major_type_neg_int64 (FStar.Int.Cast.int64_to_uint64 (I64.sub (-1L) v));
    rewrite vmatch 1.0R res (pack (CInt64 cbor_major_type_neg_int64 (FStar.Int.Cast.int64_to_uint64 (I64.sub (-1L) v))))
    as vmatch 1.0R res (pack (CInt64 (major_int_type_of_int (I64.v v)) (U64.uint_to_t (int_as_ones_complement_nat (I64.v v)))));
    res
  } else {
    let res = f cbor_major_type_uint64 (FStar.Int.Cast.int64_to_uint64 v);
    rewrite vmatch 1.0R res (pack (CInt64 cbor_major_type_uint64 (FStar.Int.Cast.int64_to_uint64 v)))
    as vmatch 1.0R res (pack (CInt64 (major_int_type_of_int (I64.v v)) (U64.uint_to_t (int_as_ones_complement_nat (I64.v v)))));
    res
  }
}

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

let mk_string_from_arrayptr_res
  (#t: Type)
  (ty: major_type_byte_string_or_text_string)
  (a: AP.ptr U8.t)
  (dest: R.ref t)
  (v: Seq.seq U8.t)
: GTot bool
= (not (AP.g_is_null a)) &&
  (not (R.is_null dest)) &&
  FStar.UInt.fits (Seq.length v) 64 &&
  begin if ty = cbor_major_type_text_string
  then CBOR.Spec.API.UTF8.correct v
  else true
  end

let mk_string_from_arrayptr_post_true
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (ty: major_type_byte_string_or_text_string)
  (a: AP.ptr U8.t)
  (p: perm)
  (dest: R.ref t)
  (v: Seq.seq U8.t)
  (w': t)
  (sq: squash (mk_string_from_arrayptr_res ty a dest v))
: Tot slprop
= vmatch 1.0R w' (pack (CString ty v)) **
  Trade.trade
    (vmatch 1.0R w' (pack (CString ty v)))
    (pts_to a #p v)

let mk_string_from_arrayptr_post_false
  (#t: Type)
  (a: AP.ptr U8.t)
  (p: perm)
  (v: Seq.seq U8.t)
  (w: t)
  (w': t)
: Tot slprop
= AP.pts_to_or_null a #p v ** pure (w' == w)

let mk_string_from_arrayptr_post
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (ty: major_type_byte_string_or_text_string)
  (a: AP.ptr U8.t)
  (p: perm)
  (dest: R.ref t)
  (v: Seq.seq U8.t)
  (w: t)
  (w': t)
: Tot slprop
= if mk_string_from_arrayptr_res ty a dest v
  then mk_string_from_arrayptr_post_true vmatch ty a p dest v w' ()
  else mk_string_from_arrayptr_post_false a p v w w'

let mk_string_from_arrayptr_post_eq_false
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (ty: major_type_byte_string_or_text_string)
  (a: AP.ptr U8.t)
  (p: perm)
  (dest: R.ref t)
  (v: Seq.seq U8.t)
  (w: t)
  (w': t)
  (sq: squash (mk_string_from_arrayptr_res ty a dest v == false))
: Tot (squash (mk_string_from_arrayptr_post vmatch ty a p dest v w w' == mk_string_from_arrayptr_post_false a p v w w'))
= ()

inline_for_extraction
noextract [@@noextract_to "krml"]
let mk_string_from_arrayptr_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (ty: major_type_byte_string_or_text_string)
=
  (a: AP.ptr U8.t) ->
  (len: U64.t) ->
  (dest: R.ref t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  (#w: Ghost.erased t) ->
  stt bool
    (AP.pts_to_or_null a #p v ** 
      ref_pts_to_or_null dest 1.0R w ** pure (
      Seq.length v == U64.v len
    ))
    (fun res -> exists* w' .
      ref_pts_to_or_null dest 1.0R w' **
      mk_string_from_arrayptr_post vmatch ty a p dest v w w' **
      pure (res == mk_string_from_arrayptr_res ty a dest v)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn impl_utf8_correct_if_text_string
  (ty: major_type_byte_string_or_text_string)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to s #p v)
returns res: bool
ensures
    (pts_to s #p v ** pure (res == true <==> (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v)))
{
  if (ty = cbor_major_type_text_string) {
    CBOR.Pulse.API.UTF8.impl_utf8_correct s
  } else {
    true
  }
}


inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_string_from_arrayptr
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_string: mk_string_t vmatch)
  (ty: major_type_byte_string_or_text_string)
: mk_string_from_arrayptr_t #_ vmatch ty
=
  (a: AP.ptr U8.t)
  (len: U64.t)
  (dest: _)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#w: _)
{
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
  if (AP.is_null a || R.is_null dest) {
    fold (mk_string_from_arrayptr_post_false a p v (Ghost.reveal w) (Ghost.reveal w));
    rewrite (mk_string_from_arrayptr_post_false a p v (Ghost.reveal w) (Ghost.reveal w))
      as (mk_string_from_arrayptr_post vmatch ty a p dest v w w);
    false
  } else {
    rewrite (AP.pts_to_or_null a #p v)
      as (AP.pts_to a #p v);
    let s = S.arrayptr_to_slice_intro_trade a (SZ.uint64_to_sizet len);
    S.pts_to_len s;
    if (impl_utf8_correct_if_text_string ty s) {
      let res = mk_string ty s;
      with p' v' . assert (vmatch p' res (pack (CString ty v')));
      Trade.trans (vmatch p' res (pack (CString ty v'))) _ _;
      Trade.rewrite_with_trade
        (vmatch p' res (pack (CString ty v')))
        (vmatch p' res (pack (CString ty v)));
      Trade.trans (vmatch p' res (pack (CString ty v))) _ _;
      rewrite (ref_pts_to_or_null dest 1.0R w) as (pts_to dest w);
      dest := res;
      fold (mk_string_from_arrayptr_post_true vmatch ty a p dest v res ());
      rewrite (mk_string_from_arrayptr_post_true vmatch ty a p dest v res ())
        as (mk_string_from_arrayptr_post vmatch ty a p dest v w res);
      rewrite (pts_to dest res) as (ref_pts_to_or_null dest 1.0R res);
      true
    } else {
      Trade.elim _ _;
      rewrite (AP.pts_to a #p v) as (AP.pts_to_or_null a #p v);
      fold (mk_string_from_arrayptr_post_false a p v (Ghost.reveal w) (Ghost.reveal w));
      rewrite (mk_string_from_arrayptr_post_false a p v (Ghost.reveal w) (Ghost.reveal w))
        as (mk_string_from_arrayptr_post vmatch ty a p dest v (Ghost.reveal w) (Ghost.reveal w));
      false
    }
  }
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_string_from_arrayptr_dispatch
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_byte: mk_string_from_arrayptr_t vmatch cbor_major_type_byte_string)
  (mk_text: mk_string_from_arrayptr_t vmatch cbor_major_type_text_string)
  (ty: major_type_byte_string_or_text_string)
: mk_string_from_arrayptr_t #_ vmatch ty
= (a: _)
  (len: _)
  (dest: _)
  (#p: _)
  (#v: _)
  (#w: _)
{
  if (ty = cbor_major_type_byte_string) {
    let res = mk_byte a len dest;
    rewrite each cbor_major_type_byte_string as ty;
    res
  } else {
    let res = mk_text a len dest;
    rewrite each cbor_major_type_text_string as ty;
    res
  }
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_string_from_slice
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_string: (ty: major_type_byte_string_or_text_string) -> mk_string_from_arrayptr_t vmatch ty)
  (dummy: t)
: mk_string_t u#0 #_ vmatch
=
  (ty: major_type_byte_string_or_text_string)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len s;
  let a = S.slice_to_arrayptr_intro_trade s;
  let mut pres = dummy;
  R.pts_to_not_null pres;
  rewrite (pts_to pres dummy) as (ref_pts_to_or_null pres 1.0R dummy);
  AP.pts_to_not_null a;
  rewrite (AP.pts_to a #p v) as (AP.pts_to_or_null a #p v);
  mk_string ty a (SZ.sizet_to_uint64 (S.len s)) pres;
  with gres . rewrite (ref_pts_to_or_null pres 1.0R gres)
    as (pts_to pres gres);
  let res = !pres;
  rewrite (mk_string_from_arrayptr_post vmatch ty a p pres v dummy res)
    as (mk_string_from_arrayptr_post_true vmatch ty a p pres v res ());
  unfold (mk_string_from_arrayptr_post_true vmatch ty a p pres v res ());
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

let mk_tagged_safe_res
  (#t: Type)
  (r: R.ref t)
  (dest: R.ref t)
: GTot bool
= (not (R.is_null r)) &&
  (not (R.is_null dest))

let mk_tagged_safe_post_true
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (tag: U64.t)
  (r: R.ref t)
  (pr: perm)
  (v: t)
  (pv: perm)
  (v': cbor)
  (w: t)
  (w': t)
: Tot slprop
=
  vmatch 1.0R w' (pack (CTagged tag v')) **
  Trade.trade
    (vmatch 1.0R w' (pack (CTagged tag v')))
    (R.pts_to r #pr v ** vmatch pv v v')

let mk_tagged_safe_post_false
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (r: R.ref t)
  (pr: perm)
  (v: t)
  (pv: perm)
  (v': cbor)
  (w: t)
  (w': t)
: Tot slprop
= ref_pts_to_or_null r pr v **
  vmatch pv v v' **
  pure (w' == w)

let mk_tagged_safe_post
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (tag: U64.t)
  (r: R.ref t)
  (dest: R.ref t)
  (pr: perm)
  (v: t)
  (pv: perm)
  (v': cbor)
  (w: t)
  (w': t)
: Tot slprop
= if mk_tagged_safe_res r dest
  then mk_tagged_safe_post_true vmatch tag r pr v pv v' w w'
  else mk_tagged_safe_post_false vmatch r pr v pv v' w w'

inline_for_extraction
let mk_tagged_safe_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (tag: U64.t) ->
  (r: R.ref t) ->
  (dest: R.ref t) ->
  (#pr: perm) ->
  (#v: Ghost.erased t) ->
  (#pv: perm) ->
  (#v': Ghost.erased cbor) ->
  (#w: Ghost.erased t) ->
  stt bool
    (ref_pts_to_or_null r pr v **
      ref_pts_to_or_null dest 1.0R w **
      vmatch pv v v'
    )
    (fun res -> exists* w' .
      ref_pts_to_or_null dest 1.0R w' **
      mk_tagged_safe_post vmatch tag r dest pr v pv v' w w' **
      pure (res == mk_tagged_safe_res r dest)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_tagged_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_tagged: mk_tagged_t vmatch)
: mk_tagged_safe_t #_ vmatch
=
  (tag: _)
  (r: _)
  (dest: _)
  (#pr: _)
  (#v: _)
  (#pv: _)
  (#v': _)
  (#w: _)
{
  if (R.is_null r || R.is_null dest) {
    fold (mk_tagged_safe_post_false vmatch r pr v pv v' (Ghost.reveal w) (Ghost.reveal w));
    rewrite (mk_tagged_safe_post_false vmatch r pr v pv v' (Ghost.reveal w) (Ghost.reveal w))
      as (mk_tagged_safe_post vmatch tag r dest pr v pv v' (Ghost.reveal w) (Ghost.reveal w));
    false
  } else {
    rewrite (ref_pts_to_or_null r pr v) as (pts_to r #pr v);
    rewrite (ref_pts_to_or_null dest 1.0R w) as (pts_to dest w);
    dest := mk_tagged tag r;
    with res . assert (pts_to dest res);
    fold (mk_tagged_safe_post_true vmatch tag r pr v pv v' w res);
    rewrite (mk_tagged_safe_post_true vmatch tag r pr v pv v' w res)
      as (mk_tagged_safe_post vmatch tag r dest pr v pv v' w res);
    rewrite (pts_to dest res) as (ref_pts_to_or_null dest 1.0R res);
    true
  }
}

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

let mk_array_from_arrayptr_res
  (#t: Type)
  (a: AP.ptr t)
  (dest: R.ref t)
: GTot bool
= (not (AP.g_is_null a)) &&
  (not (R.is_null dest))

let mk_array_from_arrayptr_post_true
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (a: AP.ptr t)
  (pa: perm)
  (va: (Seq.seq t))
  (pv: perm)
  (vv: (list cbor))
  (res: t)
: Tot slprop
= exists* v' .
      vmatch 1.0R res v' **
      Trade.trade
        (vmatch 1.0R res v')
        (AP.pts_to a #pa va **
          PM.seq_list_match va vv (vmatch pv)
        ) **
        pure (
          CArray? (unpack v') /\
          vv == CArray?.v (unpack v')
        )

let mk_array_from_arrayptr_post_false
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (a: AP.ptr t)
  (pa: perm)
  (va: (Seq.seq t))
  (pv: perm)
  (vv: (list cbor))
  (w: t)
  (res: t)
: Tot slprop
=
  AP.pts_to_or_null a #pa va **
  PM.seq_list_match va vv (vmatch pv) **
  pure (res == w)

let mk_array_from_arrayptr_post
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (a: AP.ptr t)
  (dest: R.ref t)
  (pa: perm)
  (va: (Seq.seq t))
  (pv: perm)
  (vv: (list cbor))
  (w: t)
  (res: t)
: Tot slprop
= if mk_array_from_arrayptr_res a dest
  then mk_array_from_arrayptr_post_true vmatch a pa va pv vv res
  else mk_array_from_arrayptr_post_false vmatch a pa va pv vv w res

inline_for_extraction
noextract [@@noextract_to "krml"]
let mk_array_from_arrayptr_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
=
  (a: AP.ptr t) ->
  (len: U64.t) ->
  (dest: R.ref t) ->
  (#pa: perm) ->
  (#va: Ghost.erased (Seq.seq t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list cbor)) ->
  (#w: Ghost.erased t) ->
  stt bool
    (AP.pts_to_or_null a #pa va **
      PM.seq_list_match va vv (vmatch pv) **
      ref_pts_to_or_null dest 1.0R w **
      pure (Seq.length va == U64.v len)
    )
    (fun b -> exists* res .
      ref_pts_to_or_null dest 1.0R res **
      mk_array_from_arrayptr_post vmatch a dest pa va pv vv w res **
      pure (b == mk_array_from_arrayptr_res a dest)
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn mk_array_from_arrayptr
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mk_array: mk_array_t vmatch)
: mk_array_from_arrayptr_t #_ vmatch
=
  (a: AP.ptr t)
  (len: U64.t)
  (dest: _)
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq t))
  (#pv: perm)
  (#vv: Ghost.erased (list cbor))
  (#w: _)
{
  if (AP.is_null a || R.is_null dest) {
    fold (mk_array_from_arrayptr_post_false vmatch a pa va pv vv w w);
    rewrite (mk_array_from_arrayptr_post_false vmatch a pa va pv vv w w)
      as (mk_array_from_arrayptr_post vmatch a dest pa va pv vv w w);
    false
  } else {
    let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;
    rewrite (AP.pts_to_or_null a #pa va) as (AP.pts_to a #pa va);
    rewrite (ref_pts_to_or_null dest 1.0R w) as (pts_to dest w);
    let s = S.arrayptr_to_slice_intro a (SZ.uint64_to_sizet len);
    intro
      (Trade.trade
        (pts_to s #pa va)
        (AP.pts_to a #pa va)
      )
      #(S.arrayptr_to_slice a s)
      fn _
    {
      S.arrayptr_to_slice_elim s;
    };
    Trade.reg_r (pts_to s #pa va) (AP.pts_to a #pa va) (PM.seq_list_match va vv (vmatch pv));
    S.pts_to_len s;
    let res = mk_array s;
    with p' v' . assert (vmatch p' res (pack (CArray v')));
    Trade.trans (vmatch p' res (pack (CArray v'))) _ _;
    dest := res;
    rewrite (pts_to dest res) as (ref_pts_to_or_null dest 1.0R res);
    fold (mk_array_from_arrayptr_post_true vmatch a pa va pv vv res);
    rewrite (mk_array_from_arrayptr_post_true vmatch a pa va pv vv res)
      as (mk_array_from_arrayptr_post vmatch a dest pa va pv vv w res);
    true
  }
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
fn mk_map_gen_by_ref
  (#t1 #t2: Type0)
  (#vmatch1: perm -> t1 -> cbor -> slprop)
  (#vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
  (m: mk_map_gen_t vmatch1 vmatch2)
: mk_map_gen_by_ref_t #_ #_ vmatch1 vmatch2
=
  (a: S.slice t2)
  (dest: R.ref t1)
  (#va: Ghost.erased (Seq.seq t2))
  (#pv: perm)
  (#vv: Ghost.erased (list (cbor & cbor)))
  (#vdest0: Ghost.erased t1)
{
  match m a {
    None -> {
      false
    }
    Some res -> {
      dest := res;
      true
    }
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

let mk_map_from_arrayptr_none_postcond
  (#t1: Type)
  (#t2: Type)
  (a: AP.ptr t2)
  (va: Seq.seq t2)
  (vv: list (cbor & cbor))
  (va': Seq.seq t2)
  (vv': list (cbor & cbor))
  (dest: R.ref t1)
: Tot prop
= AP.g_is_null a \/
  R.is_null dest \/
  mk_map_gen_none_postcond va vv va' vv'

let mk_map_from_arrayptr_safe_post
  (#t1 #t2: Type)
  (vmatch1: perm -> t1 -> cbor -> slprop)
  (vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
  (a: AP.ptr t2)
  (dest: R.ref t1)
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
    AP.pts_to_or_null a va' **
    PM.seq_list_match va' vv' (vmatch2 pv) **
    Trade.trade 
      (PM.seq_list_match va' vv' (vmatch2 pv))
      (PM.seq_list_match va vv (vmatch2 pv)) **
    pure (
      mk_map_from_arrayptr_none_postcond a va vv va' vv' dest
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
let mk_map_from_arrayptr_safe_t
  (#cbor_t: Type0)
  (#cbor_map_entry_t: Type0)
  (cbor_match: perm -> cbor_t -> cbor -> slprop)
  (cbor_map_entry_match: perm -> cbor_map_entry_t -> (cbor & cbor) -> slprop)
=
  (a: AP.ptr cbor_map_entry_t) ->
  (len: U64.t) ->
  (dest: R.ref cbor_t) ->
  (#va: Ghost.erased (Seq.seq cbor_map_entry_t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list (cbor & cbor))) ->
  stt bool
    (AP.pts_to_or_null a va **
      PM.seq_list_match va vv (cbor_map_entry_match pv) **
      (exists* vdest . ref_pts_to_or_null dest 1.0R vdest) **
      pure (Seq.length va == U64.v len)
    )
    (fun res -> exists* vdest .
      ref_pts_to_or_null dest 1.0R vdest **
      mk_map_from_arrayptr_safe_post cbor_match cbor_map_entry_match a dest va pv vv vdest res
    )

ghost fn map_gen_post_to_arrayptr
  (#t1 #t2: Type0)
  (vmatch1: perm -> t1 -> cbor -> slprop)
  (vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
  (a: AP.ptr t2)
  (dest: R.ref t1)
  (s: S.slice t2)
  (va: (Seq.seq t2))
  (pv: perm)
  (vv: (list (cbor & cbor)))
  (vdest0: t1)
  (bres: bool)
  (res: option t1)
  (vdest: t1)
requires
  mk_map_gen_post vmatch1 vmatch2 s va pv vv res **  
  S.arrayptr_to_slice a s **
  pure (mk_map_gen_by_ref_postcond vdest0 res vdest bres /\
    mk_map_gen_by_ref_postcond vdest0 res vdest bres
  )
ensures
  mk_map_from_arrayptr_safe_post vmatch1 vmatch2 a dest va pv vv vdest bres
{
  match res {
    None -> {
      unfold (mk_map_gen_post vmatch1 vmatch2 s va pv vv None);
      S.arrayptr_to_slice_elim s;
      AP.pts_to_not_null a;
      with va' . rewrite (AP.pts_to a va') as (AP.pts_to_or_null a #1.0R va');
      fold (mk_map_from_arrayptr_safe_post vmatch1 vmatch2 a dest va pv vv vdest false);
      rewrite (mk_map_from_arrayptr_safe_post vmatch1 vmatch2 a dest va pv vv vdest false)
        as (mk_map_from_arrayptr_safe_post vmatch1 vmatch2 a dest va pv vv vdest bres)
    }
    Some vres -> {
      unfold (mk_map_gen_post vmatch1 vmatch2 s va pv vv (Some vres));
      with w va' . assert (Trade.trade (vmatch1 1.0R vres w) (pts_to s va' ** PM.seq_list_match va vv (vmatch2 pv)));
      intro
        (Trade.trade
          (S.pts_to s va')
          (AP.pts_to a va')
        )
        #(S.arrayptr_to_slice a s)
        fn _
      {
        S.arrayptr_to_slice_elim s;
      };
      Trade.trans_concl_l _ _ _ _;
      rewrite each vres as vdest;
      fold (mk_map_from_arrayptr_safe_post vmatch1 vmatch2 a dest va pv vv vdest true);
      rewrite (mk_map_from_arrayptr_safe_post vmatch1 vmatch2 a dest va pv vv vdest true)
        as (mk_map_from_arrayptr_safe_post vmatch1 vmatch2 a dest va pv vv vdest bres);
    }
  }
}

inline_for_extraction
fn cbor_mk_map_from_arrayptr_safe
  (#cbor_t: Type0)
  (#cbor_map_entry_t: Type0)
  (#cbor_match: perm -> cbor_t -> cbor -> slprop)
  (#cbor_map_entry_match: perm -> cbor_map_entry_t -> cbor & cbor -> slprop)
  (cbor_mk_map_gen: mk_map_gen_by_ref_t cbor_match cbor_map_entry_match)
 :
  mk_map_from_arrayptr_safe_t #_ #_ cbor_match cbor_map_entry_match
=
  (a: _)
  (len: _)
  (dest: _)
  (#va: _)
  (#pv: _)
  (#vv: _)
{
  with vdest0 . assert (ref_pts_to_or_null dest 1.0R vdest0);
  if (AP.is_null a || R.is_null dest) {
    Trade.refl (PM.seq_list_match va vv (cbor_map_entry_match pv));
    fold (mk_map_from_arrayptr_safe_post cbor_match cbor_map_entry_match a dest va pv vv vdest0 false);
    false
  } else {
    rewrite (ref_pts_to_or_null dest 1.0R vdest0) as (pts_to dest vdest0);
    rewrite (AP.pts_to_or_null a va) as (AP.pts_to a va);
    let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;  
    let s = S.arrayptr_to_slice_intro a (SZ.uint64_to_sizet len);
    S.pts_to_len s;
    PM.seq_list_match_length (cbor_map_entry_match pv) va vv;
    let bres = cbor_mk_map_gen s dest;
    with res . assert (mk_map_gen_post cbor_match cbor_map_entry_match s va pv vv res);
    with vdest . assert (pts_to dest vdest);
    map_gen_post_to_arrayptr _ _ a dest s va pv vv vdest0 bres res vdest;
    rewrite (pts_to dest vdest) as (ref_pts_to_or_null dest 1.0R vdest);
    bres
  }
}

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
  vmatch px x vx

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

let map_get_by_ref_safe_postcond
  (#t: Type)
  (dest: R.ref t)
  (vx: cbor)
  (vk: cbor)
  (vdest0: t)
  (vdest: t)
  (res: option t)
  (bres: bool)
: Tot prop
= bres == ((not (R.is_null dest)) && CMap? (unpack vx) && Some? (cbor_map_get (CMap?.c (unpack vx)) vk)) /\
  mk_map_gen_by_ref_postcond vdest0 res vdest bres

inline_for_extraction
let map_get_by_ref_safe_t
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
    (vmatch px x vx ** vmatch pk k vk ** ref_pts_to_or_null dest 1.0R vdest0)
    (fun bres -> exists* vdest res .
      vmatch pk k vk **
      map_get_post vmatch x px vx vk res **
      ref_pts_to_or_null dest 1.0R vdest **
      pure (
        map_get_by_ref_safe_postcond dest vx vk vdest0 vdest res bres
      )
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn map_get_by_ref_safe
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (mt: get_major_type_t vmatch)
  (f: map_get_by_ref_t vmatch)
: map_get_by_ref_safe_t #_ vmatch
= (x: t)
  (k: t)
  (dest: R.ref t)
  (#px: perm)
  (#vx: Ghost.erased cbor)
  (#pk: perm)
  (#vk: Ghost.erased cbor)
  (#vdest0: Ghost.erased t)
{
  if R.is_null dest {
    fold (map_get_post_none vmatch x px vx vk);
    fold (map_get_post vmatch x px vx vk None);
    false
  } else if (mt x <> cbor_major_type_map) {
    fold (map_get_post_none vmatch x px vx vk);
    fold (map_get_post vmatch x px vx vk None);
    false
  } else {
    rewrite ref_pts_to_or_null dest 1.0R vdest0 as pts_to dest vdest0;
    let bres = f x k dest;
    with vdest . rewrite pts_to dest vdest as ref_pts_to_or_null dest 1.0R vdest;
    bres
  }
}

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

inline_for_extraction
fn map_get_as_ref
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (m: map_get_t u#0 #t vmatch)
: map_get_by_ref_t vmatch
= (x: t)
  (k: t)
  (dest: R.ref t)
  (#px: perm)
  (#vx: Ghost.erased cbor)
  (#pk: perm)
  (#vk: Ghost.erased cbor)
  (#vdest0: Ghost.erased t)
{
  match m x k {
    None -> {
      false
    }
    Some res -> {
      dest := res;
      true
    }
  }
}

module Spec = CBOR.Spec.API.Format

noextract [@@noextract_to "krml"]
let cbor_nondet_validate_post
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: GTot bool
=
  let r = Spec.cbor_parse v in
  if SZ.v res = 0
  then
    if Some? r
    then (Some? map_key_bound && Spec.cbor_map_key_depth (fst (Some?.v r)) > SZ.v (Some?.v map_key_bound))
    else true
  else (
    Some? r &&
    SZ.v res = snd (Some?.v r) &&
    begin if Some? map_key_bound && strict_check
    then Spec.cbor_map_key_depth (fst (Some?.v r)) <= SZ.v (Some?.v map_key_bound)
    else true
    end
  )

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_validate_t
=
  (map_key_bound: option SZ.t) ->
  (strict_check: bool) ->
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_nondet_validate_post map_key_bound strict_check v res
    ))

inline_for_extraction
noextract [@@noextract_to "krml"]
let mk_map_key_bound
  (check_map_key_bound: bool)
  (map_key_bound: SZ.t)
: Tot (option SZ.t)
= if check_map_key_bound then Some map_key_bound else None

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_validate_from_arrayptr_t
=
  (check_map_key_bound: bool) ->
  (map_key_bound: SZ.t) ->
  (strict_check: bool) ->
  (input: AP.ptr U8.t) ->
  (len: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
    (pts_to input #pm v ** pure (
      Seq.length v == SZ.v len
    ))
    (fun res -> pts_to input #pm v ** pure (
      cbor_nondet_validate_post (mk_map_key_bound check_map_key_bound map_key_bound) strict_check v res
    ))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_validate_from_arrayptr
  (f: cbor_nondet_validate_t)
: cbor_nondet_validate_from_arrayptr_t
=
  (check_map_key_bound: bool)
  (map_key_bound: SZ.t)
  (strict_check: bool)
  (input: AP.ptr U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let s = S.arrayptr_to_slice_intro input len;
  let res = f (mk_map_key_bound check_map_key_bound map_key_bound) strict_check s;
  S.arrayptr_to_slice_elim s;
  res
}

noextract [@@noextract_to "krml"]
let cbor_nondet_parse_valid_post
  (v: Seq.seq U8.t)
  (v': Spec.cbor)
: Tot prop
= let w = Spec.cbor_parse v in
  Some? w /\
  v' == fst (Some?.v w)

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_parse_valid_t
  (#cbor_nondet_t: Type)
  (cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop)
=
  (input: S.slice U8.t) ->
  (len: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt cbor_nondet_t
    (pts_to input #pm v ** pure (
      cbor_nondet_validate_post None false v len /\
      SZ.v len > 0
    ))
    (fun res -> exists* p' v' .
      cbor_nondet_match p' res v' **
      Trade.trade (cbor_nondet_match p' res v') (pts_to input #pm v) ** pure (
        cbor_nondet_parse_valid_post v v'
    ))

let cbor_nondet_parse_postcond_some
  (v: Seq.seq U8.t)
  (v': Spec.cbor)
  (vrem: Seq.seq U8.t)
: Tot prop
= match Spec.cbor_parse v with
  | None -> False
  | Some (x, len) ->
    x == v' /\
    Seq.slice v len (Seq.length v) == vrem /\
    v == Seq.append (Seq.slice v 0 len) (Seq.slice v len (Seq.length v))

noextract [@@noextract_to "krml"]
let cbor_nondet_parse_post_some
  (#cbornondet: Type)
  (cbor_nondet_match: perm -> cbornondet -> Spec.cbor -> slprop)
  (input: S.slice U8.t)
  (pm: perm)
  (v: Seq.seq U8.t)
  (res: cbornondet)
  (rem: S.slice U8.t)
: Tot slprop
= exists* p' v' vrem .
     cbor_nondet_match p' res v' **
     pts_to rem #pm vrem **
     Trade.trade // FIXME: I would need a forall_vrem here
       (cbor_nondet_match p' res v' ** pts_to rem #pm vrem)
       (pts_to input #pm v) **
     pure (
       cbor_nondet_parse_postcond_some v v' vrem
     )

noextract [@@noextract_to "krml"]
let cbor_nondet_parse_post
  (#cbornondet: Type)
  (cbor_nondet_match: perm -> cbornondet -> Spec.cbor -> slprop)
  (input: S.slice U8.t)
  (pm: perm)
  (v: Seq.seq U8.t)
  (res: option (cbornondet & S.slice U8.t))
: Tot slprop
= match res with
  | None -> pts_to input #pm v
  | Some (res, rem) -> cbor_nondet_parse_post_some cbor_nondet_match input pm v res rem

let cbor_nondet_parse_postcond
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (v: Seq.seq U8.t)
  (res: bool)
: Tot prop
= begin match Spec.cbor_parse v with
  | None -> res == false
  | Some (x, _) ->
    if Some? map_key_bound && Spec.cbor_map_key_depth x > SZ.v (Some?.v map_key_bound)
    then res == true ==> strict_check == false
    else res == true
  end

inline_for_extraction
let cbor_nondet_parse_t
  (#cbornondet: Type)
  (cbor_nondet_match: perm -> cbornondet -> Spec.cbor -> slprop)
=
  (map_key_bound: option SZ.t) ->
  (strict_check: bool) ->
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt (option (cbornondet & S.slice U8.t))
    (pts_to input #pm v)
    (fun res ->
      cbor_nondet_parse_post cbor_nondet_match input pm v res **
      pure (cbor_nondet_parse_postcond map_key_bound strict_check v (Some? res))
    )

let cbor_nondet_parse_from_arrayptr_postcond
  (#cbor_nondet_t: Type)
  (check_map_key_bound: bool)
  (map_key_bound: SZ.t)
  (pinput: R.ref (AP.ptr U8.t))
  (plen: R.ref SZ.t)
  (input: AP.ptr U8.t)
  (v: Seq.seq U8.t)
  (dest: R.ref cbor_nondet_t)
  (res: SZ.t)
: GTot bool
= if (R.is_null pinput || R.is_null plen || AP.g_is_null input || R.is_null dest)
  then res = 0sz
  else cbor_nondet_validate_post (if check_map_key_bound then Some map_key_bound else None) check_map_key_bound v res

let cbor_nondet_parse_from_arrayptr_post_true
  (#cbor_nondet_t: Type)
  (cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop)
  (input: AP.ptr U8.t)
  (input': AP.ptr U8.t)
  (pm: perm)
  (v: Seq.seq U8.t)
  (res: cbor_nondet_t)
: Tot slprop
=
     exists* p' v' v1 .
      cbor_nondet_match p' res v' **
      Trade.trade (cbor_nondet_match p' res v') (pts_to input #pm v1) ** pure (
        AP.adjacent input (Seq.length v1) input' /\
        not (AP.g_is_null input') /\
        Seq.length v1 <= Seq.length v /\
        v1 == Seq.slice v 0 (Seq.length v1) /\
        Spec.cbor_parse v1 == Some (v', Seq.length v1) /\
        Spec.cbor_parse v == Some (v', Seq.length v1)
    )

let cbor_nondet_parse_from_arrayptr_post
  (#cbor_nondet_t: Type)
  (cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop)
  (input: AP.ptr U8.t)
  (input': AP.ptr U8.t)
  (pm: perm)
  (v: Seq.seq U8.t)
  (res: cbor_nondet_t)
  (b: bool)
: Tot slprop
= if b
  then cbor_nondet_parse_from_arrayptr_post_true cbor_nondet_match input input' pm v res
  else emp

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_parse_from_arrayptr_t
  (#cbor_nondet_t: Type)
  (cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop)
=
  (check_map_key_bound: bool) ->
  (map_key_bound: SZ.t) ->
  (pinput: R.ref (AP.ptr U8.t)) ->
  (plen: R.ref SZ.t) ->
  (dest: R.ref cbor_nondet_t) ->
  (#input: Ghost.erased (AP.ptr U8.t)) ->
  (#len: Ghost.erased SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  (#vdest: Ghost.erased cbor_nondet_t) ->
  stt bool
    (
      ref_pts_to_or_null pinput 1.0R input **
      AP.pts_to_or_null input #pm v **
      ref_pts_to_or_null plen 1.0R len **
      ref_pts_to_or_null dest 1.0R vdest **
      pure (
      SZ.v len == Seq.length v
    ))
    (fun b -> exists* input' len' v' res .
      ref_pts_to_or_null pinput 1.0R input' **
      AP.pts_to_or_null input' #pm v' **
      ref_pts_to_or_null plen 1.0R len' **
      ref_pts_to_or_null dest 1.0R res **
      cbor_nondet_parse_from_arrayptr_post cbor_nondet_match input input' pm v res b **
      pure (
        SZ.v len == Seq.length v /\
        SZ.v len' <= SZ.v len /\
        v' == Seq.slice v (SZ.v len - SZ.v len') (Seq.length v) /\
        b == (SZ.v len' < SZ.v len) /\
        (b == false ==> input' == Ghost.reveal input) /\
        cbor_nondet_parse_from_arrayptr_postcond check_map_key_bound map_key_bound pinput plen input v dest (SZ.sub len len')
      )
    )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_parse_from_arrayptr
  (#cbor_nondet_t: Type0)
  (#cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop)
  (validate: cbor_nondet_validate_t)
  (f: cbor_nondet_parse_valid_t cbor_nondet_match)
: cbor_nondet_parse_from_arrayptr_t #_ cbor_nondet_match
=
  (check_map_key_bound: bool)
  (map_key_bound: SZ.t)
  (pinput: R.ref (AP.ptr U8.t))
  (plen: R.ref SZ.t)
  (dest: R.ref cbor_nondet_t)
  (#input: Ghost.erased (AP.ptr U8.t))
  (#len: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#vdest: Ghost.erased cbor_nondet_t)
{
  if (R.is_null pinput || R.is_null plen || R.is_null dest) {
    fold (cbor_nondet_parse_from_arrayptr_post cbor_nondet_match input input pm v vdest false);
    false
  } else {
    rewrite ref_pts_to_or_null pinput 1.0R input as pts_to pinput input;
    let input = !pinput;
    if (AP.is_null !pinput) {
      rewrite pts_to pinput input as ref_pts_to_or_null pinput 1.0R input;
      fold (cbor_nondet_parse_from_arrayptr_post cbor_nondet_match input input pm v vdest false);
      false
    } else {
      rewrite AP.pts_to_or_null input #pm v as AP.pts_to input #pm v;
      rewrite ref_pts_to_or_null plen 1.0R len as pts_to plen len;
      let len = !plen;
      let s = S.arrayptr_to_slice_intro_trade input len;
      S.pts_to_len s;
      let consume = validate (if check_map_key_bound then Some map_key_bound else None) check_map_key_bound s;
      Trade.elim _ _;
      if (consume = 0sz) {
        rewrite pts_to plen len as ref_pts_to_or_null plen 1.0R len;
        rewrite AP.pts_to input #pm v as AP.pts_to_or_null input #pm v;
        rewrite pts_to pinput input as ref_pts_to_or_null pinput 1.0R input;
        fold (cbor_nondet_parse_from_arrayptr_post cbor_nondet_match input input pm v vdest false);
        false
      } else {
        Seq.lemma_split v (SZ.v consume);
        Spec.cbor_parse_prefix v (Seq.slice v 0 (SZ.v consume));
        let input' = AP.split input consume;
        pinput := input';
        let len' = SZ.sub len consume;
        plen := len';
        let s = S.arrayptr_to_slice_intro_trade input consume;
        let res = f s consume;
        Trade.trans _ _ (pts_to input #pm _);
        rewrite ref_pts_to_or_null dest 1.0R vdest as pts_to dest vdest;
        dest := res;
        rewrite pts_to dest res as ref_pts_to_or_null dest 1.0R res;
        rewrite pts_to plen len' as ref_pts_to_or_null plen 1.0R len';
        AP.pts_to_not_null input';
        with v' . rewrite AP.pts_to input' #pm v' as AP.pts_to_or_null input' #pm v';
        rewrite pts_to pinput input' as ref_pts_to_or_null pinput 1.0R input';
        fold (cbor_nondet_parse_from_arrayptr_post_true cbor_nondet_match input input' pm v res);
        rewrite (cbor_nondet_parse_from_arrayptr_post_true cbor_nondet_match input input' pm v res)
          as (cbor_nondet_parse_from_arrayptr_post cbor_nondet_match input input' pm v res true);
        true
      }
    }
  }
}

noextract [@@noextract_to "krml"]
let cbor_nondet_serialize_postcond
  (size: nat)
  (y: Spec.cbor)
  (v: Seq.seq U8.t)
  (v': Seq.seq U8.t)
  (res: option SZ.t)
: Tot prop
= match res with
  | None ->
    v' == v /\
    Seq.length v < size
  | Some len ->
    SZ.v len == size /\
    SZ.v len <= Seq.length v' /\
    Seq.length v' == Seq.length v /\
    Seq.equal (Seq.slice v' (SZ.v len) (Seq.length v)) (Seq.slice v (SZ.v len) (Seq.length v)) /\
    Spec.cbor_parse v' == Some (y, SZ.v len)

noextract [@@noextract_to "krml"]
let cbor_nondet_serialize_postcond_c
  (output: AP.ptr U8.t)
  (size: nat)
  (y: Spec.cbor)
  (v: Seq.seq U8.t)
  (v': Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
= if AP.g_is_null output
  then res == 0sz
  else cbor_nondet_serialize_postcond size y v v' (if res = 0sz then None else Some res)

inline_for_extraction
let cbor_nondet_serialize_t
  (#cbordet: Type)
  (cbor_det_match: nat -> perm -> cbordet -> Spec.cbor -> slprop)
=
  (x: cbordet) ->
  (output: S.slice U8.t) ->
  (#size: Ghost.erased nat) ->
  (#y: Ghost.erased Spec.cbor) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt (option SZ.t)
    (cbor_det_match size pm x y ** pts_to output v)
    (fun res -> exists* v' . cbor_det_match size pm x y ** pts_to output v' ** pure (
      cbor_nondet_serialize_postcond size y v v' res
    ))

inline_for_extraction
let cbor_nondet_serialize_to_arrayptr_t
  (#cbordet: Type)
  (cbor_det_match: nat -> perm -> cbordet -> Spec.cbor -> slprop)
=
  (x: cbordet) ->
  (output: AP.ptr U8.t) ->
  (len: SZ.t) ->
  (#size: Ghost.erased nat) ->
  (#y: Ghost.erased Spec.cbor) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt (SZ.t)
    (cbor_det_match size pm x y ** AP.pts_to_or_null output v ** pure (Seq.length v == SZ.v len))
    (fun res -> exists* v' . cbor_det_match size pm x y ** AP.pts_to_or_null output v' ** pure (
      Seq.length v' == SZ.v len /\
      cbor_nondet_serialize_postcond_c output size y v v' res
    ))

noextract [@@noextract_to "krml"]
inline_for_extraction
fn cbor_nondet_serialize_to_arrayptr
  (#cbordet: Type0)
  (#cbor_nondet_match: nat -> perm -> cbordet -> Spec.cbor -> slprop)
  (f: cbor_nondet_serialize_t cbor_nondet_match)
: cbor_nondet_serialize_to_arrayptr_t #_ cbor_nondet_match
=
  (x: cbordet)
  (output: AP.ptr U8.t)
  (len: SZ.t)
  (#size: Ghost.erased nat)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  if (AP.is_null output) {
    0sz
  } else {
    rewrite AP.pts_to_or_null output v as AP.pts_to output v;
    let s = S.arrayptr_to_slice_intro output len;
    S.pts_to_len s;
    let res = f x s;
    S.pts_to_len s;
    S.arrayptr_to_slice_elim s;
    with v' . rewrite AP.pts_to output v' as AP.pts_to_or_null output v';
    match res {
      None -> {
        0sz
      }
      Some res -> {
        res
      }
    }
  }
}

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

noeq
type cbor_map_get_multiple_entry_t (t: Type) = {
  key: t;
  value: t;
  found: bool
}

let cbor_map_get_multiple_entry_match_fst
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (px: perm)
  (x: cbor_map_get_multiple_entry_t t)
  (y: Spec.cbor)
: slprop
= vmatch px x.key y

let cbor_map_get_multiple_entry_match_snd
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (res: bool)
  (x: cbor_map_get_multiple_entry_t t)
  (y: option Spec.cbor)
: slprop
= if res
  then match x.found, y with
  | true, Some v -> vmatch 1.0R x.value v
  | false, None -> emp
  | _ -> pure False
  else emp

let cbor_map_get_multiple_entry_match
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (res: bool)
  (px: perm)
  (x: cbor_map_get_multiple_entry_t t)
  (y: Spec.cbor & option Spec.cbor)
: slprop
= vmatch px x.key (fst y) **
  cbor_map_get_multiple_entry_match_snd vmatch res x (snd y)

let seq_map
  (#t1 #t2: Type)
  (f: t1 -> t2)
  (s: Seq.seq t1)
: Tot (Seq.seq t2)
= Seq.init (Seq.length s) (fun i -> f (Seq.index s i))

let cbor_map_get_multiple_postcond
  (#t: Type)
  (vmap: Spec.cbor)
  (s: Seq.seq (cbor_map_get_multiple_entry_t t))
  (v: list Spec.cbor)
  (s': Seq.seq (cbor_map_get_multiple_entry_t t))
  (v': list (Spec.cbor & option Spec.cbor))
  (res: bool)
: Tot prop
=
  Seq.equal (seq_map Mkcbor_map_get_multiple_entry_t?.key s') (seq_map Mkcbor_map_get_multiple_entry_t?.key s) /\
  List.Tot.map fst v' == Ghost.reveal v /\
  (forall x . (List.Tot.memP x v' /\ res) ==> (Spec.CMap? (Spec.unpack vmap) /\ Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vmap)) (fst x) == snd x))

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_map_get_multiple_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
=
  (map: t) ->
  (dest: S.slice (cbor_map_get_multiple_entry_t t)) ->
  (#pmap: perm) ->
  (#vmap: Ghost.erased Spec.cbor) ->
  (#s: Ghost.erased (Seq.seq (cbor_map_get_multiple_entry_t t))) ->
  (#ps: perm) ->
  (#v: Ghost.erased (list (Spec.cbor & option Spec.cbor))) ->
  stt unit
    (
      S.pts_to dest s **
      vmatch pmap map vmap **
      PM.seq_list_match s v (cbor_map_get_multiple_entry_match vmatch false ps) **
      pure (Spec.CMap? (Spec.unpack vmap))
    )
    (fun _ -> exists* s' v' .
      S.pts_to dest s' **
      PM.seq_list_match s' v' (cbor_map_get_multiple_entry_match vmatch true ps) **
      Trade.trade
        (PM.seq_list_match s' v' (cbor_map_get_multiple_entry_match vmatch true ps))
        (vmatch pmap map vmap ** PM.seq_list_match s v (cbor_map_get_multiple_entry_match vmatch false ps)) **
      pure (
        cbor_map_get_multiple_postcond vmap s (List.Tot.map fst v) s' v' true
      )
    )

ghost fn trade_concl_intro_l
  (a b c: slprop)
requires
  a ** Trade.trade b c
ensures
  Trade.trade b (a ** c)
{
  intro
    (Trade.trade b (a ** c))
    #(a ** Trade.trade b c)
    fn _ {
      Trade.elim _ _
    }
}

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_map_get_multiple_as_arrayptr_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
  (t': Type { t' == cbor_map_get_multiple_entry_t t})
=
  (map: t) ->
  (dest: AP.ptr t') ->
  (len: SZ.t) ->
  (#pmap: perm) ->
  (#vmap: Ghost.erased Spec.cbor) ->
  (#s: Ghost.erased (Seq.seq (cbor_map_get_multiple_entry_t t))) ->
  (#ps: perm) ->
  (#v: Ghost.erased (list (Spec.cbor & option Spec.cbor))) ->
  stt bool
    (
      AP.pts_to_or_null dest s **
      vmatch pmap map vmap **
      PM.seq_list_match s v (cbor_map_get_multiple_entry_match vmatch false ps) **
      pure (SZ.v len == Seq.length s)
    )
    (fun res -> exists* s' v' .
      AP.pts_to_or_null dest s' **
      PM.seq_list_match s' v' (cbor_map_get_multiple_entry_match vmatch res ps) **
      Trade.trade
        (PM.seq_list_match s' v' (cbor_map_get_multiple_entry_match vmatch res ps))
        (vmatch pmap map vmap ** PM.seq_list_match s v (cbor_map_get_multiple_entry_match vmatch false ps)) **
      pure (
        cbor_map_get_multiple_postcond vmap s (List.Tot.map fst v) s' v' res /\
        (res == (Spec.CMap? (Spec.unpack vmap) && not (AP.g_is_null dest)))
      )
    )

#push-options "--print_implicits"

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_map_get_multiple_as_arrayptr
  (#t: Type0)
  (#vmatch: perm -> t -> cbor -> slprop)
  (t': Type { t' == cbor_map_get_multiple_entry_t t})
  (mt: get_major_type_t vmatch)
  (f: cbor_map_get_multiple_t vmatch)
: cbor_map_get_multiple_as_arrayptr_t #_ vmatch t'
= (map: _)
  (dest: _)
  (len: _)
  (#pmap: _)
  (#vmap: _)
  (#s: _)
  (#ps: _)
  (#v: _)
{
  if (AP.is_null dest) {
    Trade.refl (PM.seq_list_match s v (cbor_map_get_multiple_entry_match vmatch false ps));
    trade_concl_intro_l (vmatch _ _ _) _ _;
    rewrite
    Trade.trade #emp_inames
      (Pulse.Lib.SeqMatch.seq_list_match #(cbor_map_get_multiple_entry_t t)
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps))
      (vmatch pmap map (reveal #T.cbor vmap) **
        Pulse.Lib.SeqMatch.seq_list_match #(cbor_map_get_multiple_entry_t t)
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps))
      as
        Trade.trade #emp_inames
      (Pulse.Lib.SeqMatch.seq_list_match #t'
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps))
      (vmatch pmap map (reveal #T.cbor vmap) **
        Pulse.Lib.SeqMatch.seq_list_match #(cbor_map_get_multiple_entry_t t)
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps));
    false
  } else if (mt map <> cbor_major_type_map) {
    Trade.refl (PM.seq_list_match s v (cbor_map_get_multiple_entry_match vmatch false ps));
    trade_concl_intro_l (vmatch _ _ _) _ _;
    rewrite
    Trade.trade #emp_inames
      (Pulse.Lib.SeqMatch.seq_list_match #(cbor_map_get_multiple_entry_t t)
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps))
      (vmatch pmap map (reveal #T.cbor vmap) **
        Pulse.Lib.SeqMatch.seq_list_match #(cbor_map_get_multiple_entry_t t)
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps))
      as
        Trade.trade #emp_inames
      (Pulse.Lib.SeqMatch.seq_list_match #t'
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps))
      (vmatch pmap map (reveal #T.cbor vmap) **
        Pulse.Lib.SeqMatch.seq_list_match #(cbor_map_get_multiple_entry_t t)
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps));
    false
  } else {
    rewrite AP.pts_to_or_null dest s as AP.pts_to dest s;
    let dests = S.arrayptr_to_slice_intro dest len;
    f map dests;
    S.arrayptr_to_slice_elim dests;
    with s' . rewrite AP.pts_to dest s' as AP.pts_to_or_null dest s';
    with s' v' . rewrite
    Trade.trade #emp_inames
      (Pulse.Lib.SeqMatch.seq_list_match #(cbor_map_get_multiple_entry_t t)
          #(T.cbor & option T.cbor)
          s'
          (reveal #(list (T.cbor & option T.cbor)) v')
          (cbor_map_get_multiple_entry_match #t vmatch true ps))
      (vmatch pmap map (reveal #T.cbor vmap) **
        Pulse.Lib.SeqMatch.seq_list_match #(cbor_map_get_multiple_entry_t t)
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps))
      as
     Trade.trade #emp_inames
      (Pulse.Lib.SeqMatch.seq_list_match #t'
          #(T.cbor & option T.cbor)
          s'
          (reveal #(list (T.cbor & option T.cbor)) v')
          (cbor_map_get_multiple_entry_match #t vmatch true ps))
      (vmatch pmap map (reveal #T.cbor vmap) **
        Pulse.Lib.SeqMatch.seq_list_match #(cbor_map_get_multiple_entry_t t)
          #(T.cbor & option T.cbor)
          (reveal #(Seq.Base.seq (cbor_map_get_multiple_entry_t t)) s)
          (reveal #(list (T.cbor & option T.cbor)) v)
          (cbor_map_get_multiple_entry_match #t vmatch false ps));
    true
  } 
}
