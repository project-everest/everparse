module CBOR.Pulse
include CBOR.Spec.Constants
include CBOR.Pulse.Extern
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

module Cbor = CBOR.Spec
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module I16 = FStar.Int16
module SM = Pulse.Lib.SeqMatch

val byte_array_compare
  (sz: SZ.t)
  (a1: A.larray U8.t (SZ.v sz))
  (a2: A.larray U8.t (SZ.v sz))
  (#p1: perm)
  (#p2: perm)
  (#va1: Ghost.erased (Seq.seq U8.t))
  (#va2: Ghost.erased (Seq.seq U8.t))
: stt I16.t
    (A.pts_to a1 #p1 va1 ** A.pts_to a2 #p2 va2)
    (fun res ->
        A.pts_to a1 #p1 va1 ** A.pts_to a2 #p2 va2 **
        pure (I16.v res == Cbor.bytes_lex_compare va1 va2)
    )

val cbor_compare
  (a1: cbor)
  (a2: cbor)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased Cbor.raw_data_item)
  (#v2: Ghost.erased Cbor.raw_data_item)
: stt I16.t
    (raw_data_item_match p1 a1 v1 ** raw_data_item_match p2 a2 v2)
    (fun res -> raw_data_item_match p1 a1 v1 ** raw_data_item_match p2 a2 v2 ** pure (
      ((I16.v res <: int) == Cbor.cbor_compare v1 v2)
    ))

val cbor_is_equal
  (a1: cbor)
  (a2: cbor)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased Cbor.raw_data_item)
  (#v2: Ghost.erased Cbor.raw_data_item)
: stt bool
    (raw_data_item_match p1 a1 v1 ** raw_data_item_match p2 a2 v2)
    (fun res -> raw_data_item_match p1 a1 v1 ** raw_data_item_match p2 a2 v2 ** pure (
      (res == true <==> v1 == v2)
    ))

[@@no_auto_projectors]
noeq
type cbor_map_get_t =
| Found of cbor
| NotFound

let rec list_ghost_assoc
  (#key: Type)
  (#value: Type)
  (k: key)
  (m: list (key & value))
: GTot (option value)
  (decreases m)
= match m with
  | [] -> None
  | (k', v') :: m' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then Some v'
    else list_ghost_assoc k m'

let cbor_map_get_post_not_found
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor)
: Tot vprop
= raw_data_item_match p map vmap ** pure (
    Cbor.Map? vmap /\
    list_ghost_assoc vkey (Cbor.Map?.v vmap) == None
  )

let cbor_map_get_post_found
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor)
  (value: cbor)
: Tot vprop
= exists* vvalue.
    raw_data_item_match p value vvalue **
    (raw_data_item_match p value vvalue @==> raw_data_item_match p map vmap) **
    pure (
      Cbor.Map? vmap /\
      list_ghost_assoc vkey (Cbor.Map?.v vmap) == Some vvalue
  )

let cbor_map_get_post
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
: Tot vprop
= match res with
  | NotFound -> cbor_map_get_post_not_found p vkey vmap map
  | Found value -> cbor_map_get_post_found p vkey vmap map value

let cbor_map_get_invariant
  (pmap: perm)
  (vkey: Ghost.erased Cbor.raw_data_item)
  (vmap: Ghost.erased Cbor.raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
  (i: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
= match res with
  | Found value -> cbor_map_get_post_found pmap vkey vmap map value ** pure (
      Cbor.Map? vmap /\
      Some? (list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap))
    )
  | NotFound ->
    cbor_map_iterator_match pmap i l **
    (cbor_map_iterator_match pmap i l @==> raw_data_item_match pmap map vmap) **
    pure (
        Cbor.Map? vmap /\
        list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap) ==
          list_ghost_assoc (Ghost.reveal vkey) l
    )

val cbor_map_get
  (key: cbor)
  (map: cbor)
  (#pkey: perm)
  (#pmap: perm)
  (#vkey: Ghost.erased Cbor.raw_data_item)
  (#vmap: Ghost.erased Cbor.raw_data_item)
: stt cbor_map_get_t
    (raw_data_item_match pkey key vkey ** raw_data_item_match pmap map vmap ** pure (
      Cbor.Map? vmap
    ))
    (fun res -> raw_data_item_match pkey key vkey ** cbor_map_get_post pmap vkey vmap map res ** pure (
      Cbor.Map? vmap /\
      Found? res == Some? (list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap))
    ))

val cbor_map_sort
    (a: A.array cbor_map_entry)
    (len: SZ.t)
    (#c: Ghost.erased (Seq.seq cbor_map_entry))
    (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
: stt bool (
    A.pts_to a c **
    SM.seq_list_match c l (raw_data_item_map_entry_match 1.0R) **
    pure (SZ.v len == A.length a \/ SZ.v len == Seq.length c \/ SZ.v len == List.Tot.length l)
  ) (fun res ->
    exists* c' l' .
    A.pts_to a c' **
    SM.seq_list_match c' l' (raw_data_item_map_entry_match 1.0R) **
    pure (
        Cbor.cbor_map_sort l == (res, l')
    )
  )
