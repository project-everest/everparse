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


(* Item 3 (fragment serialisers): the four raw-side primitives
   `cbor_serialize_{tag,string,array,map}` are landed in
   `CBOR.Pulse.Raw.EverParse.Det.Serialize` (after exposing
   `write_header`/`size_header` from Raw.EverParse.Serialize.fsti).
   The thin API-level wrappers in this module that lift the raw
   postconditions to use `Spec.cbor_det_*` are deferred: bridging
   `Spec.cbor_det_serialize_tag tag == SpecF.serialize_cbor_tag (mk_raw_uint64 tag)`
   across module boundaries even with `friend CBOR.Spec.API.Format`,
   `[SMTPat]`, and `assert_norm` does not propagate through Pulse's
   postcondition check in this F*/Pulse version. Callers can use
   `CBOR.Pulse.Raw.EverParse.Det.Serialize.*` directly. *)

(*
   ======== TODO (deferred to a follow-up session) ========

   The following items from the original task spec are NOT yet implemented in
   this module. They were deferred either because they require porting >300
   lines of legacy proof machinery (sort/dedup, fragment serializers, det
   validation) or because they need additional EverParse-side primitives that
   have not been ported from the legacy `raw/everparse/old/` modules.

   1.  cbor_det_validate            : cbor_det_validate_t
       Needs the EverParse-side `impl_pred_t` instances for
       `raw_data_item_ints_optimal_elem` and
       `raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order`
       (the legacy `cbor_raw_ints_optimal` / `cbor_raw_sorted` from
       `raw/everparse/old/CBOR.Pulse.Raw.Format.Parse.fst` lines 268-470).
       Currently neither is exposed from the new EverParse stack.

   2.  cbor_det_parse_valid         : cbor_det_parse_valid_t cbor_det_match
       Wraps a parser similar to legacy `Parse.cbor_parse`. Needs (1) and
       a `cbor_read` analog at the EverParse layer (constructs a
       `CBOR_Case_*` with `Base (Serialized ...)` payload from a slice).

   3.  cbor_det_serialize_tag, cbor_det_serialize_string,
       cbor_det_serialize_array, cbor_det_serialize_map_insert,
       cbor_det_serialize_map     — fragment serializers.
       Needs new exposed serializers (`cbor_serialize_tag`,
       `cbor_serialize_string`, `cbor_serialize_array`, `cbor_serialize_map`,
       `cbor_raw_map_insert`) factored out of the new `Raw.EverParse.Serialize`
       (currently only top-level `cbor_serialize` and `cbor_size` are exposed).

   6.  cbor_det_mk_array            : mk_array_t cbor_det_match
       Needs a slice -> mixed_list adapter on top of Make.cbor_mk_array, plus
       a seq_list_match <-> mixed_list_match bridge for cbor_det_match.

   7.  cbor_det_mk_map_gen          : mk_map_gen_t cbor_det_match cbor_det_map_entry_match
       Heavy port (~300 lines) of legacy sort + dedup logic from
       `raw/old/CBOR.Pulse.API.Det.Common.fst` lines 668-971; uses
       `Pulse.Lib.Sort.Merge.Slice` plus 4 spec-level lemmas.

   8 (partial). Array iterator: `_match`, `_share`, `_gather`, `_is_empty`
       are LANDED. Still TODO:
        * `_length` (needs SZ.fits proof for `len_before + len_after`,
           which requires propagating fits_u64 invariant through
           `cbor_det_array_iterator_match`)
        * `_start`  (`cbor_raw_get_array` + `iterator_start`; blocked on
           `mk_det_raw_cbor_array_eq` lemma — the obvious port from
           `CBOR.Spec.API.Format.cbor_det_serialize_array_length_gt_list`'s
           internal proof regressed `cbor_det_mk_int64`'s rewrite, likely
           via SMT-context interaction with `assert_norm` of
           `raw_data_item_ints_optimal == holds_on_raw_data_item …`)
        * `_next`   (`iterator_next`; needs the same bridge)
        * `_truncate`

   9.  cbor_det_get_array_item      : get_array_item_t cbor_det_match
       Iterator-based (or direct nlist random-access) lookup. Depends on (8).

   10. Map iterator                 : symmetric to (8). Same blockers.

   12. cbor_det_map_get             : map_get_by_ref_t cbor_det_match
       Linear search using `cbor_det_equal` over the map iterator.
       Depends on (10).
*)
