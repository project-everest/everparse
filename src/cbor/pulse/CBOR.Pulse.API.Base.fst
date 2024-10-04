module CBOR.Pulse.API.Base
include CBOR.Spec.API.Type
open Pulse.Lib.Pervasives
module T = CBOR.Spec.API.Type
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util

let cbor_major_type (c: cbor) : Tot T.major_type_t =
  match unpack c with
  | CSimple _ -> cbor_major_type_simple_value
  | CInt64 ty _
  | CString ty _ -> ty
  | CArray _ -> cbor_major_type_array
  | CMap _ -> cbor_major_type_map
  | CTagged _ _ -> cbor_major_type_tagged

inline_for_extraction
let equal
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
    (fun res -> vmatch p1 x1 v1 ** vmatch p2 x2 v2 ** pure (res == (Ghost.reveal v1 = Ghost.reveal v2)))

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
let read_uint64_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt FStar.UInt64.t
    (vmatch p x y ** pure (CInt64? (unpack y)))
    (fun res -> vmatch p x y ** pure (match unpack y with
    | CInt64 _ v -> res == v
    | _ -> False
    ))

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
      S.pts_to res #p' v' **
      Trade.trade
        (S.pts_to res #p' v')
        (vmatch p x y) **
      pure (match unpack y with
      | CString _ v -> v == v'
      | _ -> False
      )
    )

inline_for_extraction
let get_array_length_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (x: t) ->
  (#p: perm) ->
  (#y: Ghost.erased cbor) ->
  stt FStar.UInt64.t
    (vmatch p x y ** pure (CArray? (unpack y)))
    (fun res -> vmatch p x y ** pure (match unpack y with
      | CArray v -> FStar.UInt64.v res == List.Tot.length v
      | _ -> False
      )
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

module R = Pulse.Lib.Reference

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
