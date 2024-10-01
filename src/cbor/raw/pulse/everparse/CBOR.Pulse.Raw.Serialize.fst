module CBOR.Pulse.Raw.Serialize
open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.Serialized.Base
friend CBOR.Spec.Raw.Order
open CBOR.Spec.Raw.Format
open CBOR.Pulse.Raw.Format
open LowParse.Spec.Base
open LowParse.Pulse.Base

open CBOR.Pulse.Raw.Match
module LP = LowParse.Pulse.Combinators
module LPI = LowParse.Pulse.Int

inline_for_extraction
let write_initial_byte_t' : l2r_leaf_writer serialize_initial_byte_t =
  l2r_leaf_writer_ext
    (LP.l2r_leaf_write_synth'
      (LowParse.Pulse.BitSum.l2r_write_bitsum'
        mk_synth_initial_byte
        (LPI.l2r_leaf_write_u8 ())
      )
      synth_initial_byte
      synth_initial_byte_recip
    )
    _

inline_for_extraction
let write_long_argument_8_simple_value
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
  (sq2: squash ((b.major_type = cbor_major_type_simple_value) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
          l2r_leaf_writer_ext
            (LP.l2r_leaf_write_synth'
              (LP.l2r_leaf_write_filter
                (LPI.l2r_leaf_write_u8 ())
                simple_value_long_argument_wf
              )
              (LongArgumentSimpleValue #b ())
              (LongArgumentSimpleValue?.v)
            )
            (serialize_long_argument b)

(* etc. *)

assume val write_header : l2r_leaf_writer serialize_header

module SZ = FStar.SizeT
module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice

let nlist_match_array
  (#t': Type0)
  (#t: Type)
  (vmatch: (t' -> t -> slprop))
  (n: nat)
  (p: perm)
  (a: A.array t')
  (l: LowParse.Spec.VCList.nlist n t)
: Tot slprop
= exists* c .
    A.pts_to a #p c **
    PM.seq_list_match c l vmatch

assume val l2r_write_nlist_as_array
  (#t': Type0)
  (#t: Type)
  (vmatch: (t' -> t -> slprop))
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: l2r_writer vmatch s { k.parser_kind_subkind == Some LP.ParserStrong })
  (n: SZ.t)
  (p: perm)
: l2r_writer (nlist_match_array vmatch (SZ.v n) p) (LowParse.Spec.VCList.serialize_nlist (SZ.v n) s)

assume val ser_body_for_array
  (f: (p: perm) -> LP.l2r_writer (cbor_match p) serialize_raw_data_item)
  (p: perm)
  (c: cbor_raw { CBOR_Case_Array? c })
  (r: Ghost.erased raw_data_item)
: LP.l2r_writer_for (cbor_match p) serialize_raw_data_item c r

```pulse
fn cbor_raw_get_header
  (p: perm)
  (xl: cbor_raw)
  (xh: erased raw_data_item)
requires
      (cbor_match p xl xh)
returns res: header
ensures
          cbor_match p xl xh **
          pure (res == get_raw_data_item_header xh)
{
  cbor_match_cases xl;
  if (CBOR_Case_Int? xl) {
      let ty = cbor_match_int_elim_type xl;
      let v = cbor_match_int_elim_value xl;
      raw_uint64_as_argument ty v
  }
  else if (CBOR_Case_String? xl) {
    let ty = cbor_match_string_elim_type xl;
    let len = cbor_match_string_elim_length xl;
    raw_uint64_as_argument ty len
  }
  else if (CBOR_Case_Tagged? xl || CBOR_Case_Serialized_Tagged? xl) {
    let tag = cbor_match_tagged_get_tag xl;
    raw_uint64_as_argument cbor_major_type_tagged tag
  }
  else if (CBOR_Case_Array? xl || CBOR_Case_Serialized_Array? xl) {
    let len = cbor_match_array_get_length xl;
    raw_uint64_as_argument cbor_major_type_array len
  }
  else if (CBOR_Case_Map? xl || CBOR_Case_Serialized_Map? xl) {
    let len = cbor_match_map_get_length xl;
    raw_uint64_as_argument cbor_major_type_map len
  }
  else {
    let v = cbor_match_simple_elim xl;
    simple_value_as_argument v
  }
}
```

let synth_raw_data_item_recip_synth_raw_data_item
  (x: _)
: Lemma
  (synth_raw_data_item_recip (synth_raw_data_item x) == x)
= assert (synth_raw_data_item (synth_raw_data_item_recip (synth_raw_data_item x)) == synth_raw_data_item x)

inline_for_extraction
```pulse
fn cbor_raw_get_header'
  (p: perm)
  (xl: cbor_raw)
  (xh: erased (dtuple2 header content))
requires
      (LP.vmatch_synth (cbor_match p) synth_raw_data_item xl (reveal xh))
returns res: header
ensures
          LP.vmatch_synth (cbor_match p) synth_raw_data_item xl (reveal xh) **
          pure (res == dfst (reveal xh))
{
  synth_raw_data_item_recip_synth_raw_data_item xh;
  unfold (LP.vmatch_synth (cbor_match p) synth_raw_data_item xl (reveal xh));
  let res = cbor_raw_get_header p xl _;
  fold (LP.vmatch_synth (cbor_match p) synth_raw_data_item xl (reveal xh));
  res
}
```

inline_for_extraction
```pulse
fn ser_payload
  (f: ((p: perm) -> l2r_writer (cbor_match p) serialize_raw_data_item))
  (p: perm)
  (xh1: header)
: l2r_writer #cbor_raw #(content xh1)
        (LP.vmatch_dep_proj2
            (LP.vmatch_synth
                (cbor_match p)
                synth_raw_data_item
            )
            xh1
        )
        #(parse_content_kind)
        #(parse_content parse_raw_data_item xh1)
        (serialize_content xh1)
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  admit ()
}
```

inline_for_extraction
let ser_body
  (f: (p: perm) -> LP.l2r_writer (cbor_match p) serialize_raw_data_item)
  (p: perm)
: LP.l2r_writer (cbor_match p) serialize_raw_data_item
= LP.l2r_writer_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (LP.l2r_write_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (LP.l2r_write_dtuple2_recip_explicit_header
        write_header
        (cbor_raw_get_header' p)
        ()
        (ser_payload f p)
      )
    )
    (Classical.forall_intro parse_raw_data_item_eq; serialize_raw_data_item)

let ser_pre
  (p: perm)
  (x': cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
: Tot slprop
=
    (S.pts_to out v ** cbor_match p x' x ** pure (
      SZ.v offset + Seq.length (bare_serialize serialize_raw_data_item x) <= Seq.length v
    ))

let ser_post
  (p: perm)
  (x': cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
  (res: SZ.t)
: Tot slprop
=
  exists* v' .
      S.pts_to out v' ** cbor_match p x' x ** pure (
      let bs = bare_serialize serialize_raw_data_item x in
      SZ.v res == SZ.v offset + Seq.length bs /\
      SZ.v res <= Seq.length v /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
      Seq.slice v' (SZ.v offset) (SZ.v res) `Seq.equal` bs
  )

inline_for_extraction
```pulse
fn ser_fold
  (f: (p: perm) -> (x': cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre p x' x out offset v) (fun res -> ser_post p x' x out offset v res))
  (p: perm)
: LP.l2r_writer #cbor_raw #raw_data_item (cbor_match p) #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item
=
  (x': cbor_raw) (#x: raw_data_item) (out: S.slice LP.byte) (offset: SZ.t) (#v: Ghost.erased LP.bytes)
{
  fold (ser_pre p x' x out offset v);
  let res = f p x' x out offset v;
  unfold (ser_post p x' x out offset v res);
  res
}
```

inline_for_extraction
```pulse
fn ser_unfold
  (f: (p: perm) -> LP.l2r_writer (cbor_match p) serialize_raw_data_item)
  (p: perm)
  (x': cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre p x' x out offset v)
returns res: SZ.t
ensures
  (ser_post p x' x out offset v res)
{
  unfold (ser_pre p x' x out offset v);
  let res = f p x' out offset;
  fold (ser_post p x' x out offset v res);
  res
}
```

inline_for_extraction
```pulse
fn ser_body'
  (f: (p: perm) -> (x': cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre p x' x out offset v) (fun res -> ser_post p x' x out offset v res))
  (p: perm)
  (x': cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre p x' x out offset v)
returns res: SZ.t
ensures
  ser_post p x' x out offset v res
{
  ser_unfold (ser_fold f) p x' x out offset v;
}
```

inline_for_extraction
```pulse
fn rec ser'
  (p: perm)
  (x': cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre p x' x out offset v)
returns res: SZ.t
ensures
  ser_post p x' x out offset v res
{
  ser_body' ser' p x' x out offset v
}
```

let ser (p: perm) : l2r_writer (cbor_match p) serialize_raw_data_item = ser_fold ser' p
