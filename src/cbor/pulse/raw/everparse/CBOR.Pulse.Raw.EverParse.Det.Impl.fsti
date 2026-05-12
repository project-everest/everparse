module CBOR.Pulse.Raw.EverParse.Det.Impl
#lang-pulse

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Base
open CBOR.Pulse.API.Det.Type

module Spec = CBOR.Spec.API.Format
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Trade = Pulse.Lib.Trade.Util

val cbor_det_match: perm -> cbor_det_t -> Spec.cbor -> slprop

val cbor_det_share (_: unit) : share_t cbor_det_match
val cbor_det_gather (_: unit) : gather_t cbor_det_match

val cbor_det_size
  (x: cbor_det_t)
  (bound: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
: stt SZ.t
    (cbor_det_match pm x y)
    (fun res -> cbor_det_match pm x y ** pure (cbor_det_size_post bound y res))

val cbor_det_equal (_: unit) : equal_t cbor_det_match

val cbor_det_major_type (_: unit) : get_major_type_t cbor_det_match

val cbor_det_get_tagged_payload (_: unit) : get_tagged_payload_t cbor_det_match

(* String reader returning an arrayptr *)
inline_for_extraction noextract [@@noextract_to "krml"]
let det_get_string_t =
  (x: cbor_det_t) ->
  (#p: perm) ->
  (#y: Ghost.erased Spec.cbor) ->
  stt (AP.ptr U8.t)
    (cbor_det_match p x y ** pure (Spec.CString? (Spec.unpack y)))
    (fun res -> exists* p' v' .
      pts_to res #p' v' **
      Trade.trade
        (pts_to res #p' v')
        (cbor_det_match p x y) **
      pure (get_string_post y v')
    )

val cbor_det_get_string (_: unit) : det_get_string_t

val cbor_det_mk_simple_value (_: unit) : mk_simple_t cbor_det_match
val cbor_det_mk_int64 (_: unit) : mk_int64_t cbor_det_match

(* Top-level serializer (arrayptr-based) *)
fn cbor_det_serialize
  (c: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
  requires
    (exists* va . cbor_det_match pm c y ** pts_to output va ** pure (SZ.v output_len == Seq.length va /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
  returns res: SZ.t
  ensures
    (exists* vb . cbor_det_match pm c y ** pts_to output vb ** pure (
        SZ.v output_len == Seq.length vb /\
        cbor_det_serialize_fits_postcond y res vb
      ))

fn cbor_det_serialize_safe
  (c: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#pm: perm)
  requires
    (cbor_det_match pm c y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
  returns res: SZ.t
  ensures
    (exists* v' . cbor_det_match pm c y ** pts_to output v' ** pure (
        SZ.v output_len == Seq.length v' /\
        cbor_det_serialize_postcond_c y v v' res
      ))

(* UTF8 validator over a raw arrayptr *)
inline_for_extraction noextract [@@noextract_to "krml"]
let det_impl_utf8_correct_from_array_t =
  (s: AP.ptr U8.t) ->
  (len: SZ.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (pts_to s #p v ** pure (SZ.v len == Seq.length v))
    (fun res -> pts_to s #p v ** pure (res == CBOR.Spec.API.UTF8.correct v))

val cbor_det_impl_utf8_correct_from_array (_: unit) : det_impl_utf8_correct_from_array_t

(* Field readers *)
val cbor_det_read_simple_value (_: unit) : read_simple_value_t cbor_det_match
val cbor_det_read_uint64 (_: unit) : read_uint64_t cbor_det_match
val cbor_det_get_string_length (_: unit) : get_string_length_t cbor_det_match
val cbor_det_get_tagged_tag (_: unit) : get_tagged_tag_t cbor_det_match
val cbor_det_get_array_length (_: unit) : get_array_length_t cbor_det_match
val cbor_det_get_map_length (_: unit) : get_map_length_t cbor_det_match

(* Elim functions *)
val cbor_det_elim_simple (_: unit) : elim_simple_t cbor_det_match
val cbor_det_elim_int64 (_: unit) : elim_int64_t cbor_det_match

(* Reset perm *)
val cbor_det_reset_perm (_: unit) : reset_perm_t u#0 u#0 cbor_det_match

(* Constructors *)
val cbor_det_mk_tagged (_: unit) : mk_tagged_t cbor_det_match
val cbor_det_mk_string (_: unit) : mk_string_t cbor_det_match

(* ======== Map entries ======== *)

val cbor_det_map_entry_match: perm -> CBOR.Pulse.API.Det.Type.cbor_det_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_det_map_entry_share (_: unit) : share_t cbor_det_map_entry_match
val cbor_det_map_entry_gather (_: unit) : gather_t cbor_det_map_entry_match

val cbor_det_map_entry_key (_: unit) : map_entry_key_t cbor_det_map_entry_match cbor_det_match
val cbor_det_map_entry_value (_: unit) : map_entry_value_t cbor_det_map_entry_match cbor_det_match

val cbor_det_mk_map_entry (_: unit) : mk_map_entry_t cbor_det_match cbor_det_map_entry_match

(* ======== Array iterator ======== *)

val cbor_det_array_iterator_match: perm -> CBOR.Pulse.API.Det.Type.cbor_det_array_iterator_t -> list Spec.cbor -> slprop

val cbor_det_array_iterator_share (_: unit) : share_t cbor_det_array_iterator_match
val cbor_det_array_iterator_gather (_: unit) : gather_t cbor_det_array_iterator_match
val cbor_det_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t cbor_det_array_iterator_match
val cbor_det_array_iterator_start (_: unit) : array_iterator_start_t cbor_det_match cbor_det_array_iterator_match
val cbor_det_array_iterator_length (_: unit) : array_iterator_length_t cbor_det_array_iterator_match
val cbor_det_array_iterator_next (_: unit) : array_iterator_next_t cbor_det_match cbor_det_array_iterator_match


(* ======== Validation (rescued from legacy) ======== *)

val cbor_det_validate (_: unit) : cbor_det_validate_t

val cbor_det_parse_valid (_: unit) : cbor_det_parse_valid_t cbor_det_match

val cbor_det_array_iterator_truncate (_: unit) : array_iterator_truncate_t cbor_det_array_iterator_match

val cbor_det_serialize_tag (_: unit) : cbor_det_serialize_tag_t
val cbor_det_serialize_string (_: unit) : cbor_det_serialize_string_t
val cbor_det_serialize_array (_: unit) : cbor_det_serialize_array_t
val cbor_det_serialize_map (_: unit) : cbor_det_serialize_map_t


(* ====================================================================
   Status of original task spec items, as of latest commits in this branch
   ====================================================================

   ✓ DONE (verified clean, zero admits, only project-wide assume SZ.fits_u64):

     1.  cbor_det_validate          via Det.Validate (rescued from legacy)
     2.  cbor_det_parse_valid       via Read.cbor_raw_read + zero-copy adapter
     3.  4 raw fragment serializers in Det.Serialize
         + 4 of 5 API-level wrappers here:
             cbor_det_serialize_tag, _string, _array, _map.
         (cbor_det_serialize_map_insert is the one fragment NOT done; see below.)
     4.  cbor_det_map_entry_match + share + gather
     5.  cbor_det_mk_map_entry
     8.  Array iterator FULL: match / share / gather / is_empty / start /
         length / next / truncate.
     11. cbor_det_map_entry_key, _value.

   TODO:

     3 (rest). cbor_det_serialize_map_insert
        Needs an EverParse-side `cbor_raw_map_insert` primitive that is
        currently only in raw/old/CBOR.Pulse.Raw.Insert.fst (~213 lines).
        Once that's factored over to the new EverParse.Det.Serialize stack,
        the API wrapper here is ~5 lines (mk_det_raw_cbor_map_raw_snoc lemma
        + forward).

     6.  cbor_det_mk_array(_from_array): wrap Make.cbor_mk_array plus
         seq_list_match ↔ mixed_list_match bridge.

     7.  cbor_det_mk_map_gen: ~300 lines of sort+dedup using
         Pulse.Lib.Sort.Merge.Slice + 4 spec-level lemmas (heavy).

     9.  cbor_det_get_array_item: random access into an array iterator.

     10. Full map iterator (match/start/is_empty/length/next/truncate/share/
         gather): mirror of array iterator + a Spec.Raw bridge for
         map_iterator_start_post (cbor_map_get ↔ List.Tot.assoc).

     12. cbor_det_map_get: linear scan over map iterator (small once 10 lands).
*)
