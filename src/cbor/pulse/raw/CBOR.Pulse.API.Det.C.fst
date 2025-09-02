module CBOR.Pulse.API.Det.C
#lang-pulse

(* NOTE: this .fst file does not need anything from the Raw namespace,
but it has been moved here to be hidden from verified clients. *)

[@@pulse_unfold]
let cbor_det_match = CBOR.Pulse.API.Det.Common.cbor_det_match

let cbor_det_reset_perm = CBOR.Pulse.API.Det.Common.cbor_det_reset_perm

let cbor_det_share = CBOR.Pulse.API.Det.Common.cbor_det_share

let cbor_det_gather = CBOR.Pulse.API.Det.Common.cbor_det_gather

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
  let res = CBOR.Pulse.API.Det.Common.cbor_det_validate () s;
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
= let v1 = FStar.IndefiniteDescription.indefinite_description_tot _ (fun v1 -> exists v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)) in
  let v2 = FStar.IndefiniteDescription.indefinite_description_tot _ (fun v2 -> Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)) in
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
  let res = CBOR.Pulse.API.Det.Common.cbor_det_parse_valid () s;
  Trade.trans _ _ (pts_to input #pm v);
  res
}

let cbor_det_size = CBOR.Pulse.API.Det.Common.cbor_det_size

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
  let ou = S.arrayptr_to_slice_intro output output_len;
  S.pts_to_len ou;
  let res = CBOR.Pulse.API.Det.Common.cbor_det_serialize x ou;
  S.pts_to_len ou;
  assert (pure (SZ.v res == Seq.length (Spec.cbor_det_serialize y)));
  S.arrayptr_to_slice_elim ou;
  res
}

let seq_slice_append
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (ensures
    Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) `Seq.equal` s1 /\
    Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2) `Seq.equal` s2
  )
= ()

fn cbor_det_serialize_safe
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#pm: perm)
requires
    (cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
returns res: SZ.t
ensures
    (exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      SZ.v output_len == Seq.length v' /\
      cbor_det_serialize_postcond_c y v v' res
    ))
{
  Spec.cbor_det_serialize_parse y;
  let sz = cbor_det_size x output_len;
  if (sz = 0sz) {
    0sz
  } else {
    Seq.lemma_split v (SZ.v sz);
    Classical.forall_intro (seq_slice_append (Spec.cbor_det_serialize y));
    let _ = AP.split output sz;
    let res = cbor_det_serialize x output sz;
    with v' . assert (AP.pts_to output v');
    assert (pure (Seq.equal v' (Spec.cbor_det_serialize y)));
    AP.join output _;
    res
  }
}

fn cbor_det_impl_utf8_correct_from_array (_: unit) : cbor_det_impl_utf8_correct_from_array_t
=
  (s: _)
  (len: _)
  (#p: _)
  (#v: _)
{
  let sl = S.arrayptr_to_slice_intro s len;
  S.pts_to_len sl;
  let res = CBOR.Pulse.Raw.UTF8.impl_utf8_correct sl;
  S.arrayptr_to_slice_elim sl;
  res
}

let cbor_det_mk_simple_value = CBOR.Pulse.API.Det.Common.cbor_det_mk_simple_value
let cbor_det_mk_int64 = CBOR.Pulse.API.Det.Common.cbor_det_mk_int64
let cbor_det_mk_tagged = CBOR.Pulse.API.Det.Common.cbor_det_mk_tagged

let cbor_det_mk_string_from_arrayptr (_: unit) =
  mk_string_from_arrayptr (CBOR.Pulse.API.Det.Common.cbor_det_mk_string ())

let cbor_det_mk_array_from_array (_: unit) =
  mk_array_from_array (CBOR.Pulse.API.Det.Common.cbor_det_mk_array ())

[@@pulse_unfold]
let cbor_det_map_entry_match = CBOR.Pulse.API.Det.Common.cbor_det_map_entry_match

let cbor_det_mk_map_entry = CBOR.Pulse.API.Det.Common.cbor_det_mk_map_entry

let cbor_det_mk_map_from_array : mk_map_from_array_t cbor_det_match cbor_det_map_entry_match =
  mk_map_from_array (CBOR.Pulse.API.Base.mk_map_from_ref (CBOR.Pulse.API.Det.Type.dummy_cbor_det_t ()) (CBOR.Pulse.API.Det.Common.cbor_det_mk_map_gen ()))

ghost fn map_gen_post_to_array
  (#t1 #t2: Type0)
  (vmatch1: perm -> t1 -> Spec.cbor -> slprop)
  (vmatch2: perm -> t2 -> (Spec.cbor & Spec.cbor) -> slprop)
  (a: A.array t2)
  (s: S.slice t2)
  (va: (Seq.seq t2))
  (pv: perm)
  (vv: (list (Spec.cbor & Spec.cbor)))
  (vdest0: t1)
  (bres: bool)
  (res: option t1)
  (vdest: t1)
requires
  mk_map_gen_post vmatch1 vmatch2 s va pv vv res **  
  S.is_from_array a s **
  pure (mk_map_gen_by_ref_postcond vdest0 res vdest bres /\
    mk_map_gen_by_ref_postcond vdest0 res vdest bres
  )
ensures
  mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest bres
{
  match res {
    None -> {
      unfold (mk_map_gen_post vmatch1 vmatch2 s va pv vv None);
      S.to_array s;
      fold (mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest false);
    }
    Some vres -> {
      unfold (mk_map_gen_post vmatch1 vmatch2 s va pv vv (Some vres));
      with w va' . assert (Trade.trade (vmatch1 1.0R vres w) (pts_to s va' ** PM.seq_list_match va vv (vmatch2 pv)));
      intro
        (Trade.trade
          (S.pts_to s va')
          (A.pts_to a va')
        )
        #(S.is_from_array a s)
        fn _
      {
        S.to_array s;
      };
      Trade.trans_concl_l _ _ _ _;
      rewrite each vres as vdest;
      fold (mk_map_from_array_safe_post vmatch1 vmatch2 a va pv vv vdest true);
    }
  }
}

fn cbor_det_mk_map_from_array_safe () :
  mk_map_from_array_safe_t #_ #_ cbor_det_match cbor_det_map_entry_match
=
  (a: _)
  (len: _)
  (dest: _)
  (#va: _)
  (#pv: _)
  (#vv: _)
{
  with vdest0 . assert (pts_to dest vdest0);
  let _ : squash (SZ.fits_u64) = assume SZ.fits_u64;  
  let s = S.from_array a (SZ.uint64_to_sizet len);
  S.pts_to_len s;
  PM.seq_list_match_length (cbor_det_map_entry_match pv) va vv;
  let bres = CBOR.Pulse.API.Det.Common.cbor_det_mk_map_gen () s dest;
  with res . assert (mk_map_gen_post cbor_det_match cbor_det_map_entry_match s va pv vv res);
  with vdest . assert (pts_to dest vdest);
  map_gen_post_to_array _ _ a s va pv vv vdest0 bres res vdest;
  bres
}

let cbor_det_equal = CBOR.Pulse.API.Det.Common.cbor_det_equal

let cbor_det_major_type = CBOR.Pulse.API.Det.Common.cbor_det_major_type

let cbor_det_read_simple_value = CBOR.Pulse.API.Det.Common.cbor_det_read_simple_value

let cbor_det_elim_simple = CBOR.Pulse.API.Det.Common.cbor_det_elim_simple

let cbor_det_read_uint64 = CBOR.Pulse.API.Det.Common.cbor_det_read_uint64

let cbor_det_elim_int64 = CBOR.Pulse.API.Det.Common.cbor_det_elim_int64

let cbor_det_get_string_length = CBOR.Pulse.API.Det.Common.cbor_det_get_string_length

let cbor_det_get_tagged_tag = CBOR.Pulse.API.Det.Common.cbor_det_get_tagged_tag

let cbor_det_get_tagged_payload = CBOR.Pulse.API.Det.Common.cbor_det_get_tagged_payload

fn cbor_det_get_string
  (_: unit)
: cbor_det_get_string_t
=
  (x: _)
  (#p: _)
  (#y: _)
{
  let sl = CBOR.Pulse.API.Det.Common.cbor_det_get_string () x;
  let res = SU.slice_to_arrayptr_intro_trade sl;
  Trade.trans _ _ (cbor_det_match p x y);
  res
}

let cbor_det_get_array_length = CBOR.Pulse.API.Det.Common.cbor_det_get_array_length

[@@pulse_unfold]
let cbor_det_array_iterator_match = CBOR.Pulse.API.Det.Common.cbor_det_array_iterator_match

let cbor_det_array_iterator_start = CBOR.Pulse.API.Det.Common.cbor_det_array_iterator_start

let cbor_det_array_iterator_is_empty = CBOR.Pulse.API.Det.Common.cbor_det_array_iterator_is_empty

let cbor_det_array_iterator_length = CBOR.Pulse.API.Det.Common.cbor_det_array_iterator_length

let cbor_det_array_iterator_next = CBOR.Pulse.API.Det.Common.cbor_det_array_iterator_next

let cbor_det_array_iterator_truncate = CBOR.Pulse.API.Det.Common.cbor_det_array_iterator_truncate

let cbor_det_array_iterator_share = CBOR.Pulse.API.Det.Common.cbor_det_array_iterator_share

let cbor_det_array_iterator_gather = CBOR.Pulse.API.Det.Common.cbor_det_array_iterator_gather

let cbor_det_get_array_item = CBOR.Pulse.API.Det.Common.cbor_det_get_array_item

let cbor_det_get_map_length = CBOR.Pulse.API.Det.Common.cbor_det_get_map_length

[@@pulse_unfold]
let cbor_det_map_iterator_match = CBOR.Pulse.API.Det.Common.cbor_det_map_iterator_match

let cbor_det_map_iterator_start = CBOR.Pulse.API.Det.Common.cbor_det_map_iterator_start

let cbor_det_map_iterator_is_empty = CBOR.Pulse.API.Det.Common.cbor_det_map_iterator_is_empty

let cbor_det_map_iterator_next = CBOR.Pulse.API.Det.Common.cbor_det_map_iterator_next

let cbor_det_map_iterator_share = CBOR.Pulse.API.Det.Common.cbor_det_map_iterator_share

let cbor_det_map_iterator_gather = CBOR.Pulse.API.Det.Common.cbor_det_map_iterator_gather

let cbor_det_map_entry_key = CBOR.Pulse.API.Det.Common.cbor_det_map_entry_key

let cbor_det_map_entry_value = CBOR.Pulse.API.Det.Common.cbor_det_map_entry_value

let cbor_det_map_entry_share = CBOR.Pulse.API.Det.Common.cbor_det_map_entry_share

let cbor_det_map_entry_gather = CBOR.Pulse.API.Det.Common.cbor_det_map_entry_gather

fn cbor_det_map_get
  (_: unit)
: map_get_by_ref_t #_ cbor_det_match
=
  (x: _)
  (k: _)
  (dest: _)
  (#px: _)
  (#vx: _)
  (#pk: _)
  (#vk: _)
  (#vdest0: _)
{
  CBOR.Pulse.API.Det.Common.cbor_det_map_get () x k dest
}

fn cbor_det_serialize_tag_to_array (_: unit)
: cbor_det_serialize_tag_to_array_t
=
  (tag: _)
  (out: _)
  (out_len: _)
{
  let sout = S.arrayptr_to_slice_intro out out_len;
  S.pts_to_len sout;
  let res = CBOR.Pulse.API.Det.Common.cbor_det_serialize_tag () tag sout;
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
  let res = CBOR.Pulse.API.Det.Common.cbor_det_serialize_array () len sout l off;
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
  let res = CBOR.Pulse.API.Det.Common.cbor_det_serialize_string () ty off sout;
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
  let res = CBOR.Pulse.API.Det.Common.cbor_det_serialize_map_insert () sout m off2 key off3 value;
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
  let res = CBOR.Pulse.API.Det.Common.cbor_det_serialize_map () len sout l off;
  S.pts_to_len sout;
  S.arrayptr_to_slice_elim sout;
  res
}
