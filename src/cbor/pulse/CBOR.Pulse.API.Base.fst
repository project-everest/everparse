module CBOR.Pulse.API.Base
open CBOR.Spec.API.Type
open Pulse.Lib.Pervasives
module T = CBOR.Spec.API.Type
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
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
    (fun res -> vmatch p1 x1 v1 ** vmatch p2 x2 v2 ** pure (res == (Ghost.reveal v1 = Ghost.reveal v2)))

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

let get_array_item_post
  (i: FStar.UInt64.t)
  (y: cbor)
  (y' : cbor)
: Tot prop
= match unpack y with
      | CArray v -> U64.v i < List.Tot.length v /\
        List.Tot.nth v (U64.v i) == Some y'
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
    (vmatch p x y ** pure (match unpack y with
    | CArray v -> U64.v i < List.Tot.length v
    | _ -> False
    ))
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
let mk_int64_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (ty: major_type_uint64_or_neg_int64) ->
  (v: U64.t) ->
  stt t
    (emp)
    (fun res -> vmatch 1.0R res (pack (CInt64 ty v)))

inline_for_extraction
let mk_string_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (ty: major_type_byte_string_or_text_string) ->
  (s: S.slice U8.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt t
    (pts_to s #p v ** pure (FStar.UInt.fits (Seq.length v) 64))
    (fun res -> exists* p' v' .
      vmatch p' res (pack (CString ty v')) **
      Trade.trade
        (vmatch p' res (pack (CString ty v')))
        (pts_to s #p v) **
      pure (v' == Ghost.reveal v)
    )

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
    (fun res -> exists* p' .
      vmatch p' res (pack (CTagged tag v')) **
      Trade.trade
        (vmatch p' res (pack (CTagged tag v')))
        (R.pts_to r #pr v ** vmatch pv v v')
    )

inline_for_extraction
let mk_array_t
  (#t: Type)
  (vmatch: perm -> t -> cbor -> slprop)
= (a: A.array t) ->
  (len: U64.t) ->
  (#pa: perm) ->
  (#va: Ghost.erased (Seq.seq t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list cbor)) ->
  stt t
    (A.pts_to a #pa va **
      PM.seq_list_match va vv (vmatch pv) **
      pure (U64.v len == Seq.length va)
    )
    (fun res -> exists* p' v' .
      vmatch p' res (pack (CArray v')) **
      Trade.trade
        (vmatch p' res (pack (CArray v')))
        (A.pts_to a #pa va **
          PM.seq_list_match va vv (vmatch pv)
        ) **
        pure (v' == Ghost.reveal vv)
    )

inline_for_extraction
let mk_map_t
  (#t1 #t2: Type)
  (vmatch1: perm -> t1 -> cbor -> slprop)
  (vmatch2: perm -> t2 -> (cbor & cbor) -> slprop)
= (a: A.array t2) ->
  (len: U64.t) ->
  (#va: Ghost.erased (Seq.seq t2)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list (cbor & cbor))) ->
  stt t1
    (A.pts_to a va **
      PM.seq_list_match va vv (vmatch2 pv) **
      pure (U64.v len == Seq.length va /\
        List.Tot.no_repeats_p (List.Tot.map fst vv)
      )
    )
    (fun res -> exists* p' (v': cbor_map {FStar.UInt.fits (cbor_map_length v') 64}) va' .
      vmatch1 p' res (pack (CMap v')) **
      Trade.trade
        (vmatch1 p' res (pack (CMap v')))
        (A.pts_to a va' ** // this function potentially sorts the input array, so we lose the link to the initial array contents
          PM.seq_list_match va vv (vmatch2 pv) // but we keep the permissions on each element
        ) **
        pure (
          (forall x . List.Tot.assoc x vv == cbor_map_get v' x) /\
          cbor_map_length v' == Seq.length va
        )
    )
