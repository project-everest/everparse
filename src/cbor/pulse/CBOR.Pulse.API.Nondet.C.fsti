module CBOR.Pulse.API.Nondet.C
include CBOR.Pulse.API.Nondet.Type
open CBOR.Spec.Constants
open CBOR.Pulse.API.Base
open Pulse.Lib.Pervasives

module Spec = CBOR.Spec.API.Format
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Trade = Pulse.Lib.Trade.Util
module SM = Pulse.Lib.SeqMatch.Util
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64
module L = FStar.List.Tot

val cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop

inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_nondet_reset_perm (_: unit) : reset_perm_t #_ cbor_nondet_match

val cbor_nondet_share
  (_: unit)
: CBOR.Pulse.API.Base.share_t u#0 u#0 #_ #_ cbor_nondet_match

val cbor_nondet_gather
  (_: unit)
: CBOR.Pulse.API.Base.gather_t u#0 u#0 #_ #_ cbor_nondet_match

val cbor_nondet_parse (_: unit) : cbor_nondet_parse_from_arrayptr_t #cbor_nondet_t cbor_nondet_match

val cbor_nondet_match_with_size
  (size: nat)
  (p: perm)
  (c: cbor_nondet_t)
  (v: Spec.cbor)
: Tot slprop

val cbor_nondet_match_with_size_intro (_: unit) : ghost_get_size_t #_ cbor_nondet_match cbor_nondet_match_with_size

val cbor_nondet_size (_: unit) : get_size_t #_ cbor_nondet_match_with_size

val cbor_nondet_serialize
  (_: unit)
: cbor_nondet_serialize_to_arrayptr_t #cbor_nondet_t cbor_nondet_match_with_size

(* Destructors *)

val cbor_nondet_major_type (_: unit) : get_major_type_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_simple_value (_: unit) : read_simple_value_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_simple (_: unit) : elim_simple_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_uint64 (_: unit) : read_uint64_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_int64 (_: unit) : read_int64_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_int64 (_: unit) : elim_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_string (_: unit) : get_string_as_arrayptr_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_byte_string (_: unit) : get_string_as_arrayptr_safe_gen_t u#0 (Some cbor_major_type_byte_string) #_ cbor_nondet_match

val cbor_nondet_get_text_string (_: unit) : get_string_as_arrayptr_safe_gen_t u#0 (Some cbor_major_type_text_string) #_ cbor_nondet_match

val cbor_nondet_get_tagged (_: unit) : get_tagged_safe_t #_ cbor_nondet_match

val cbor_nondet_get_array_length (_: unit) : get_array_length_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_array_iterator_match: perm -> cbor_nondet_array_iterator_t -> list Spec.cbor -> slprop

val cbor_nondet_array_iterator_start (_: unit) : array_iterator_start_safe_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_length (_: unit) : array_iterator_length_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_next (_: unit) : array_iterator_next_safe_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_truncate (_: unit) : array_iterator_truncate_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_get_array_item (_: unit) : get_array_item_safe_t #_ cbor_nondet_match

(* Structural array builder operations.

   These build CBOR arrays by O(1) structural composition (no element copy or
   re-encoding), on top of fully-owned arrays. [cbor_nondet_array_owned x l]
   means [x] is a fully-owned (permission 1.0R, canonical length encoding) CBOR
   array whose elements are [l]. Such arrays can be combined with
   [cbor_nondet_array_append] and turned back into a normal CBOR object with
   [cbor_nondet_array_finalize].

   No heap allocation: the application provides the (fixed number of) scratch
   references the operations need. *)

val cbor_nondet_array_owned (x: cbor_nondet_t) (l: list Spec.cbor) : slprop

val cbor_nondet_array_empty (_: unit)
: stt cbor_nondet_t
    emp
    (fun res -> cbor_nondet_array_owned res [])

val cbor_nondet_array_singleton
  (x: cbor_nondet_t) (ry: R.ref cbor_nondet_t)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbor_nondet_t)
: stt cbor_nondet_t
    (cbor_nondet_match pm x v ** R.pts_to ry w0)
    (fun res ->
      cbor_nondet_array_owned res [Ghost.reveal v] **
      Trade.trade
        (cbor_nondet_array_owned res [Ghost.reveal v])
        (cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w)))

val cbor_nondet_array_append
  (x1 x2: cbor_nondet_t)
  (r_before r_after: R.ref cbor_nondet_array_append_cell_t)
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased cbor_nondet_array_append_cell_t)
: stt (option cbor_nondet_t)
    (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
     R.pts_to r_before vb0 ** R.pts_to r_after va0)
    (fun res ->
      match res with
      | None ->
        cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)
      | Some r ->
        cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)) **
        Trade.trade
          (cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
          (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
           (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))

val cbor_nondet_array_finalize
  (x: cbor_nondet_t)
  (#l: Ghost.erased (l': list Spec.cbor { FStar.UInt.fits (L.length l') U64.n }))
: stt unit
    (cbor_nondet_array_owned x l)
    (fun _ ->
      cbor_nondet_match 1.0R x (Spec.pack (Spec.CArray (Ghost.reveal l))) **
      Trade.trade
        (cbor_nondet_match 1.0R x (Spec.pack (Spec.CArray (Ghost.reveal l))))
        (cbor_nondet_array_owned x l))

(* The length of an owned array fits in a u64; lets callers discharge the
   refinement of [cbor_nondet_array_finalize] after a chain of [cbor_nondet_array_append]s. *)
val cbor_nondet_array_owned_length_fits
  (x: cbor_nondet_t) (#l: Ghost.erased (list Spec.cbor))
: stt_ghost unit emp_inames
    (cbor_nondet_array_owned x l)
    (fun _ -> cbor_nondet_array_owned x l **
      pure (FStar.UInt.fits (L.length (Ghost.reveal l)) U64.n))

val cbor_nondet_get_map_length (_: unit) : get_map_length_safe_t u#0 #_ cbor_nondet_match

val cbor_nondet_map_iterator_match: perm -> cbor_nondet_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_nondet_map_iterator_start (_: unit) : map_iterator_start_safe_t #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_is_empty (_: unit) : map_iterator_is_empty_t u#0 #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_match: perm -> cbor_nondet_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_nondet_map_entry_key (_: unit) : map_entry_key_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_entry_value (_: unit) : map_entry_value_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_iterator_next (_: unit) : map_iterator_next_safe_t #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_share
  (_: unit)
: share_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match

val cbor_nondet_map_entry_gather
  (_: unit)
: gather_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match

(* Equality *)

val cbor_nondet_equal
  (x1: cbor_nondet_t)
  (#p1: perm)
  (#v1: Ghost.erased Spec.cbor)
  (x2: cbor_nondet_t)
  (#p2: perm)
  (#v2: Ghost.erased Spec.cbor)
: stt bool
(requires
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2
)
(ensures fun res ->
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2 **
  pure (res == true <==> Ghost.reveal v1 == Ghost.reveal v2)
)

val cbor_nondet_map_get (_: unit)
: map_get_by_ref_safe_t #_ cbor_nondet_match

(* Constructors *)

val cbor_nondet_mk_simple_value (_: unit) : mk_simple_safe_t #_ cbor_nondet_match

val cbor_nondet_mk_uint64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match cbor_major_type_uint64

val cbor_nondet_mk_neg_int64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match cbor_major_type_neg_int64

val cbor_nondet_mk_int64 (_: unit) : mk_signed_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_mk_byte_string (_: unit) : mk_string_from_arrayptr_t #_ cbor_nondet_match cbor_major_type_byte_string

val cbor_nondet_mk_text_string (_: unit) : mk_string_from_arrayptr_t #_ cbor_nondet_match cbor_major_type_text_string

val cbor_nondet_mk_tagged (_: unit) : mk_tagged_safe_t #_ cbor_nondet_match

val cbor_nondet_mk_array (_: unit) : mk_array_from_arrayptr_t #_ cbor_nondet_match

val cbor_nondet_mk_map_entry (_: unit) : mk_map_entry_t #_ #_ cbor_nondet_match cbor_nondet_map_entry_match

val cbor_nondet_mk_map (_: unit)
: mk_map_from_arrayptr_safe_t #cbor_nondet_t #cbor_nondet_map_entry_t cbor_nondet_match cbor_nondet_map_entry_match

type cbor_nondet_map_get_multiple_entry_t = cbor_map_get_multiple_entry_t cbor_nondet_t

val cbor_nondet_map_get_multiple (_: unit) : cbor_map_get_multiple_as_arrayptr_t #_ cbor_nondet_match cbor_nondet_map_get_multiple_entry_t
