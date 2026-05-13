module CBOR.Pulse.API.Det.C
#lang-pulse

(* Implementation of the CBOR.Pulse.API.Det.C interface using the new
   EverParse-based stack (CBOR.Pulse.Raw.EverParse.Det.Impl).

   This file delegates most operations to Det.Impl, with thin
   ArrayPtr ↔ Slice conversion wrappers where the API exposes
   ArrayPtr but Det.Impl works on Slice. *)

module Impl = CBOR.Pulse.Raw.EverParse.Det.Impl
module SU = Pulse.Lib.Slice.Util

(* ======== Match relation and basic ops ======== *)

[@@pulse_unfold]
let cbor_det_match = Impl.cbor_det_match

let cbor_det_reset_perm = Impl.cbor_det_reset_perm

let cbor_det_share = Impl.cbor_det_share

let cbor_det_gather = Impl.cbor_det_gather

(* ======== Validate, parse, size, serialize ======== *)

fn cbor_det_validate
  (input: AP.ptr U8.t)
  (input_len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v ** pure (SZ.v input_len == Seq.length v))
returns res: SZ.t
ensures
    (pts_to input #pm v ** pure (
      cbor_det_validate_post v res
    ))
{
  let s = SU.arrayptr_to_slice_intro_trade input input_len;
  let res = Impl.cbor_det_validate () s;
  Trade.elim _ (pts_to input #pm v);
  res
}

module ID = FStar.IndefiniteDescription

let cbor_det_validate_success_elim
  (len: SZ.t)
  (v: Seq.seq U8.t)
: Pure (Ghost.erased (Spec.cbor & Seq.seq U8.t))
    (requires exists v1 v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1))
    (ensures fun (v1, v2) ->
      Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)
    )
= let v1 = ID.indefinite_description_tot _ (fun v1 -> exists v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)) in
  let v2 = ID.indefinite_description_tot _ (fun v2 -> Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)) in
  (Ghost.reveal v1, Ghost.reveal v2)

fn cbor_det_parse
  (input: AP.ptr U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v ** pure (
      exists v1 v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)
    ))
returns res: cbor_det_t
ensures
    (exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade (cbor_det_match 1.0R res v') (pts_to input #pm v) ** pure (
        SZ.v len <= Seq.length v /\
        Seq.slice v 0 (SZ.v len) == Spec.cbor_det_serialize v'
    ))
{
  let v1v2 = cbor_det_validate_success_elim len v;
  assert (pure (Seq.equal (Seq.slice v 0 (SZ.v len)) (Spec.cbor_det_serialize (fst v1v2))));
  let gr : Ghost.erased (AP.ptr U8.t) = AP.ghost_split input len;
  intro
    (Trade.trade
      (pts_to input #pm (Seq.slice v 0 (SZ.v len)))
      (pts_to input #pm v)
    )
    #(pts_to (Ghost.reveal gr) #pm (Seq.slice v (SZ.v len) (Seq.length v)))
    fn _
  {
    Seq.lemma_split v (SZ.v len);
    AP.join input gr
  };
  Seq.append_empty_r (Spec.cbor_det_serialize (fst v1v2));
  let s = SU.arrayptr_to_slice_intro_trade input len;
  Trade.trans _ _ (pts_to input #pm v);
  S.pts_to_len s;
  let res = Impl.cbor_det_parse_valid () s;
  Trade.trans _ _ (pts_to input #pm v);
  res
}

let cbor_det_size = Impl.cbor_det_size

#restart-solver
fn cbor_det_serialize
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
norewrite
requires
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
returns res: SZ.t
ensures
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      SZ.v output_len == Seq.length v /\
      cbor_det_serialize_fits_postcond y res v
    ))
{
  Impl.cbor_det_serialize x output output_len
}

#restart-solver
fn cbor_det_serialize_safe
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#pm: perm)
norewrite
requires
    (cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
returns res: SZ.t
ensures
    (exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      SZ.v output_len == Seq.length v' /\
      cbor_det_serialize_postcond_c y v v' res
    ))
{
  Impl.cbor_det_serialize_safe x output output_len
}

(* ======== UTF8 ======== *)

fn cbor_det_impl_utf8_correct_from_array (_: unit) : cbor_det_impl_utf8_correct_from_array_t
=
  (s: _)
  (len: _)
  (#p: _)
  (#v: _)
{
  let sl = S.arrayptr_to_slice_intro s len;
  S.pts_to_len sl;
  let res = CBOR.Pulse.API.UTF8.impl_utf8_correct sl;
  S.arrayptr_to_slice_elim sl;
  res
}

(* ======== Constructors ======== *)

let cbor_det_mk_simple_value = Impl.cbor_det_mk_simple_value
let cbor_det_mk_int64 = Impl.cbor_det_mk_int64
let cbor_det_mk_tagged = Impl.cbor_det_mk_tagged

let cbor_det_mk_byte_string_from_arrayptr (_: unit) =
  mk_string_from_arrayptr (Impl.cbor_det_mk_string ()) cbor_major_type_byte_string

let cbor_det_mk_text_string_from_arrayptr (_: unit) =
  mk_string_from_arrayptr (Impl.cbor_det_mk_string ()) cbor_major_type_text_string

(* `cbor_det_mk_array_from_array`: needs `Impl.cbor_det_mk_array`, which is not yet
   exposed. Admitted as TODO for now. *)
let cbor_det_mk_array_from_array () : mk_array_from_array_t cbor_det_match
  = admit ()

[@@pulse_unfold]
let cbor_det_map_entry_match = Impl.cbor_det_map_entry_match

let cbor_det_mk_map_entry = Impl.cbor_det_mk_map_entry

(* TODO: cbor_det_mk_map_from_array and cbor_det_mk_map_from_array_safe
   need item 7 (mk_map_gen — sort+dedup over a slice) which is not yet
   ported to the EverParse stack. Once Impl.cbor_det_mk_map_gen is provided,
   the wrappers below become one-liners (mk_map_from_array, etc.).
   For now they are admitted as TODO. *)

let cbor_det_mk_map_from_array : mk_map_from_array_t cbor_det_match cbor_det_map_entry_match
  = admit ()

let cbor_det_mk_map_from_array_safe () : mk_map_from_array_safe_t cbor_det_match cbor_det_map_entry_match
  = admit ()

(* ======== Destructors ======== *)

let cbor_det_equal = Impl.cbor_det_equal

let cbor_det_major_type = Impl.cbor_det_major_type

let cbor_det_read_simple_value = Impl.cbor_det_read_simple_value

let cbor_det_elim_simple = Impl.cbor_det_elim_simple

let cbor_det_read_uint64 = Impl.cbor_det_read_uint64

let cbor_det_elim_int64 = Impl.cbor_det_elim_int64

let cbor_det_get_string_length = Impl.cbor_det_get_string_length

let cbor_det_get_tagged_tag = Impl.cbor_det_get_tagged_tag

let cbor_det_get_tagged_payload = Impl.cbor_det_get_tagged_payload

let cbor_det_get_string = Impl.cbor_det_get_string

let cbor_det_get_array_length = Impl.cbor_det_get_array_length

[@@pulse_unfold]
let cbor_det_array_iterator_match = Impl.cbor_det_array_iterator_match

let cbor_det_array_iterator_start = Impl.cbor_det_array_iterator_start
let cbor_det_array_iterator_is_empty = Impl.cbor_det_array_iterator_is_empty
let cbor_det_array_iterator_length = Impl.cbor_det_array_iterator_length
let cbor_det_array_iterator_next = Impl.cbor_det_array_iterator_next
let cbor_det_array_iterator_truncate = Impl.cbor_det_array_iterator_truncate
let cbor_det_array_iterator_share = Impl.cbor_det_array_iterator_share
let cbor_det_array_iterator_gather = Impl.cbor_det_array_iterator_gather

(* TODO: cbor_det_get_array_item — item 9 (random access into array iterator).
   Could be implemented by iterating up to the index, but no helper exists yet. *)
let cbor_det_get_array_item () : get_array_item_t cbor_det_match
  = admit ()

let cbor_det_get_map_length = Impl.cbor_det_get_map_length

(* TODO: full map iterator family — item 10. The array iterator analogue
   from Det.Impl can be mirrored once Access.cbor_raw_get_map is wired in
   here. Marked admits as TODO for now. *)
let cbor_det_map_iterator_match = Impl.cbor_det_map_iterator_match

let cbor_det_map_iterator_start () : map_iterator_start_t cbor_det_match cbor_det_map_iterator_match
  = admit ()

let cbor_det_map_iterator_is_empty = Impl.cbor_det_map_iterator_is_empty

let cbor_det_map_iterator_next () : map_iterator_next_t cbor_det_map_entry_match cbor_det_map_iterator_match
  = admit ()

let cbor_det_map_iterator_share = Impl.cbor_det_map_iterator_share

let cbor_det_map_iterator_gather = Impl.cbor_det_map_iterator_gather

let cbor_det_map_entry_key = Impl.cbor_det_map_entry_key
let cbor_det_map_entry_value = Impl.cbor_det_map_entry_value
let cbor_det_map_entry_share = Impl.cbor_det_map_entry_share
let cbor_det_map_entry_gather = Impl.cbor_det_map_entry_gather

(* TODO: cbor_det_map_get — item 12 (linear scan over map iterator). *)
let cbor_det_map_get () : map_get_by_ref_t cbor_det_match
  = admit ()

(* ======== Serializer wrappers (slice → ArrayPtr) ======== *)

fn cbor_det_serialize_tag_to_array (_: unit)
: cbor_det_serialize_tag_to_array_t
=
  (tag: _)
  (out: _)
  (out_len: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_tag () tag sout;
  S.arrayptr_to_slice_elim sout;
  res
}

fn cbor_det_serialize_array_to_array (_: unit)
: cbor_det_serialize_array_to_array_t
=
  (len: _)
  (out: _)
  (out_len: _)
  (l: _)
  (off: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_array () len sout l off;
  S.pts_to_len sout;
  S.arrayptr_to_slice_elim sout;
  res
}

fn cbor_det_serialize_string_to_array (_: unit)
: cbor_det_serialize_string_to_array_t
=
  (ty: _)
  (off: _)
  (out: _)
  (out_len: _)
  (#v: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_string () ty off sout;
  S.pts_to_len sout;
  S.arrayptr_to_slice_elim sout;
  res
}

fn cbor_det_serialize_map_insert_to_array (_: unit)
: cbor_det_serialize_map_insert_to_array_t
=
  (out: _)
  (out_len: _)
  (m: _)
  (off2: _)
  (key: _)
  (off3: _)
  (value: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_map_insert () sout m off2 key off3 value;
  S.pts_to_len sout;
  S.arrayptr_to_slice_elim sout;
  res
}

fn cbor_det_serialize_map_to_array (_: unit)
: cbor_det_serialize_map_to_array_t
=
  (len: _)
  (out: _)
  (out_len: _)
  (l: _)
  (off: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = Impl.cbor_det_serialize_map () len sout l off;
  S.pts_to_len sout;
  S.arrayptr_to_slice_elim sout;
  res
}
