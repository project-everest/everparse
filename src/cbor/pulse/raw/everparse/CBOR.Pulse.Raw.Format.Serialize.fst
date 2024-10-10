module CBOR.Pulse.Raw.Format.Serialize
open Pulse.Lib.Pervasives
open CBOR.Pulse.Raw.EverParse.Serialized.Base
friend CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Format
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

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_8_not_simple_value
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
  (sq2: squash ((b.major_type = cbor_major_type_simple_value) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (LP.l2r_leaf_write_synth'
                  (LPI.l2r_leaf_write_u8 ())
                  (LongArgumentU8 #b ())
                  (LongArgumentU8?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_8
  (b: initial_byte)
  (sq1: squash ((b.additional_info = additional_info_long_argument_8_bits) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
    (serialize_long_argument b)
    (b.major_type = cbor_major_type_simple_value)
    (write_long_argument_8_simple_value b sq1)
    (write_long_argument_8_not_simple_value b sq1)

(* etc. *)

assume val write_header : l2r_leaf_writer serialize_header

module SZ = FStar.SizeT
module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array

let cbor_match_with_perm
  (x: with_perm cbor_raw)
  (y: raw_data_item)
: Tot slprop
= cbor_match x.p x.v y

module Trade = Pulse.Lib.Trade.Util

```pulse
ghost
fn cbor_match_with_perm_lens
  (p: perm)
: vmatch_lens #_ #_ #_ (cbor_match p) cbor_match_with_perm
=
  (x: cbor_raw)
  (y: raw_data_item)
{
  let res : with_perm cbor_raw = {
    v = x;
    p = p;
  };
  Trade.rewrite_with_trade
    (cbor_match p x y)
    (cbor_match_with_perm res y);
  res
}
```

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

```pulse
fn cbor_raw_with_perm_get_header
  (xl: with_perm cbor_raw)
  (xh: erased raw_data_item)
requires
      (cbor_match_with_perm xl xh)
returns res: header
ensures
          cbor_match_with_perm xl xh **
          pure (res == get_raw_data_item_header xh)
{
  unfold (cbor_match_with_perm xl xh);
  let res = cbor_raw_get_header xl.p xl.v xh;
  fold (cbor_match_with_perm xl xh);
  res
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
  (xl: with_perm cbor_raw)
  (xh: erased (dtuple2 header content))
requires
      (LP.vmatch_synth (cbor_match_with_perm) synth_raw_data_item xl (reveal xh))
returns res: header
ensures
          LP.vmatch_synth (cbor_match_with_perm) synth_raw_data_item xl (reveal xh) **
          pure (res == dfst (reveal xh))
{
  synth_raw_data_item_recip_synth_raw_data_item xh;
  unfold (LP.vmatch_synth (cbor_match_with_perm) synth_raw_data_item xl (reveal xh));
  let res = cbor_raw_with_perm_get_header xl _;
  fold (LP.vmatch_synth (cbor_match_with_perm) synth_raw_data_item xl (reveal xh));
  res
}
```

let match_cbor_payload
  (xh1: header)
=
        (LP.vmatch_dep_proj2
            (LP.vmatch_synth
                (cbor_match_with_perm)
                synth_raw_data_item
            )
            xh1
        )

module U64 = FStar.UInt64

```pulse
ghost
fn ser_payload_string_lens_aux
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
  (xl: with_perm cbor_raw)
  (xh: content xh1)
requires
  (vmatch_ext
      (Seq.Properties.lseq byte
                  (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))))
      (match_cbor_payload xh1) xl xh
  )
returns xh': Ghost.erased raw_data_item
ensures
  (cbor_match_with_perm xl xh' **
    Trade.trade
      (cbor_match_with_perm xl xh')
      (vmatch_ext
        (Seq.Properties.lseq byte
          (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
            (get_header_long_argument xh1))))
        (match_cbor_payload xh1) xl xh
      ) **
      pure (synth_raw_data_item_recip xh' == (| xh1, xh |))
  )
{
  admit ()
}
```

```pulse
ghost
fn pts_to_seqbytes_intro
  (n: nat)
  (p: perm)
  (s: S.slice byte)
  (v: bytes)
  (res: with_perm (S.slice byte))
requires
  S.pts_to s #p v ** pure (Seq.length v == n /\ res.v == s /\ res.p == p)
returns v': Ghost.erased (Seq.lseq byte n)
ensures
  LowParse.Pulse.SeqBytes.pts_to_seqbytes n res v' **
  Trade.trade
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes n res v')
    (S.pts_to s #p v) **
  pure (v == Ghost.reveal v')
{
  let v' : Seq.lseq byte n = v;
  fold (LowParse.Pulse.SeqBytes.pts_to_seqbytes n res v');
  ghost fn aux (_: unit)
    requires emp ** LowParse.Pulse.SeqBytes.pts_to_seqbytes n res v'
    ensures S.pts_to s #p v
  {
    unfold (LowParse.Pulse.SeqBytes.pts_to_seqbytes n res v')
  };
  Trade.intro _ _ _ aux;
  v'
}
```

inline_for_extraction
```pulse
fn ser_payload_string_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
: 
vmatch_lens #_ #_ #_
  (vmatch_ext
      (Seq.Properties.lseq byte
                  (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))))
      (match_cbor_payload xh1))
  (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
  )
= (x1': _)
  (x: _)
{
  let xh' = ser_payload_string_lens_aux xh1 sq x1' x;
  Trade.rewrite_with_trade
    (cbor_match_with_perm x1' xh')
    (cbor_match x1'.p x1'.v xh');
  Trade.trans
    (cbor_match x1'.p x1'.v xh')
    _ _;
  let s = cbor_match_string_elim_payload x1'.v;
  Trade.trans _ (cbor_match _ x1'.v xh') _;
  S.pts_to_len s;
  with p' . assert (S.pts_to s #p' x);
  let res : with_perm (S.slice byte) = {
    v = s;
    p = p';
  };
  let x' = pts_to_seqbytes_intro
    (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1)))
    _
    s
    x
    res;
  Trade.trans
    (LowParse.Pulse.SeqBytes.pts_to_seqbytes
              (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                      (get_header_long_argument xh1)))
      res x')
    _ _;
  res
}
```

inline_for_extraction
let ser_payload_string
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_string_lens xh1 sq)
      (LowParse.Pulse.SeqBytes.l2r_write_lseq_bytes_copy
        (U64.v (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
      )
    )
    (serialize_content xh1)

inline_for_extraction
let cbor_with_perm_case_array
  (c: with_perm cbor_raw)
: Tot bool
= CBOR_Case_Array? c.v

inline_for_extraction
let cbor_with_perm_case_array_get
  (c: with_perm cbor_raw)
: Tot (option (with_perm (A.array cbor_raw)))
= match c.v with
  | CBOR_Case_Array a -> Some { v = a.cbor_array_ptr; p = perm_mul c.p a.cbor_array_array_perm }
  | _ -> None

let cbor_with_perm_case_array_match_elem
  (c: with_perm cbor_raw)
: (x: cbor_raw) ->
  (y: raw_data_item) ->
  Tot slprop
= cbor_match
    (perm_mul c.p (match c.v with CBOR_Case_Array a -> a.cbor_array_payload_perm | _ -> 1.0R (* dummy *) ))

inline_for_extraction
let ser_payload_array_array_elem
  (f: l2r_writer cbor_match_with_perm serialize_raw_data_item)
  (a: with_perm cbor_raw)
: l2r_writer (cbor_with_perm_case_array_match_elem a) serialize_raw_data_item
= l2r_writer_lens
    (cbor_match_with_perm_lens _)
    f

#restart-solver
```pulse
ghost
fn ser_payload_array_array_lens_aux
  (f64: squash SZ.fits_u64)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_array))
  (xl: with_perm cbor_raw)
  (xh: LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))) raw_data_item)
requires
  (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array)
      xl xh
  )
ensures
  LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_array_get
    cbor_with_perm_case_array_match_elem
    (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1))))
    xl xh **
  Trade.trade
    (LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh)
      (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1))))
                  raw_data_item)
                  (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array)
                  xl xh
      )
{
  unfold       (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1))))
                  raw_data_item)
                  (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array)
                  xl xh
      );
  with xh2 . assert 
    (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array xl xh2);
  unfold (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array xl xh2);
  let xh0' : raw_data_item' = (| xh1, xh2 |);
  let xh0 = synth_raw_data_item xh0';
  let a = CBOR_Case_Array?.v xl.v;
  cbor_match_eq_array xl.p a xh0;
  rewrite (match_cbor_payload xh1 xl xh2) as (cbor_match_array a xl.p xh0 cbor_match);
  unfold (cbor_match_array a xl.p xh0 cbor_match);
  let ar = Some?.v (cbor_with_perm_case_array_get xl);
    LowParse.Pulse.VCList.nlist_match_array_intro cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh
      ar _
    ;
  ghost fn aux (_: unit)
  requires emp **
    LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh
  ensures
    (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array)
      xl xh
    )
  {
    unfold (    LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh
    );
    fold (cbor_match_array a xl.p xh0 cbor_match);
    rewrite (cbor_match_array a xl.p xh0 cbor_match) as (match_cbor_payload xh1 xl xh2);
    fold (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array xl xh2);
    fold (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1))))
                  raw_data_item)
                  (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array)
                  xl xh
      );
  };
  Trade.intro _ _ _ aux
}
```

inline_for_extraction
```pulse
fn ser_payload_array_array_lens
  (f64: squash SZ.fits_u64)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_array))
:
vmatch_lens #_ #_ #_
  (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array))
  (LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))))
=
  (x1': _)
  (x: _)
{
  ser_payload_array_array_lens_aux f64 xh1 sq x1' x;
  x1'
}
```

inline_for_extraction
let ser_payload_array_array
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_array_array_lens f64 xh1 sq)
      (LowParse.Pulse.VCList.l2r_write_nlist_as_array
        cbor_with_perm_case_array_get
        cbor_with_perm_case_array_match_elem
        serialize_raw_data_item
        (ser_payload_array_array_elem f)
        (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
      )
    )
    (serialize_content xh1)

assume val ser_payload_array_not_array
  (f64: squash SZ.fits_u64)
//  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
:
l2r_writer (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_array))
  (serialize_content xh1)

inline_for_extraction
let ser_payload_array
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_array
    (ser_payload_array_array f64 f xh1 sq)
    (ser_payload_array_not_array f64 (* f *) xh1 sq)

assume val ser_payload_not_string_not_array
  (f64: squash SZ.fits_u64)
//  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)

inline_for_extraction
let ser_payload_not_string
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array)
    (ser_payload_array f64 f xh1)
    (ser_payload_not_string_not_array f64 (* f *) xh1 sq)

inline_for_extraction
let ser_payload
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)
    (ser_payload_string xh1)
    (ser_payload_not_string f64 f xh1)

inline_for_extraction
let ser_body
  (f64: squash SZ.fits_u64)
  (f: LP.l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
: LP.l2r_writer (cbor_match_with_perm) serialize_raw_data_item
= LP.l2r_writer_ext #_ #_ #_ #_ #_ #serialize_raw_data_item_aux
    (LP.l2r_write_synth_recip
      _
      synth_raw_data_item
      synth_raw_data_item_recip
      (LP.l2r_write_dtuple2_recip_explicit_header
        write_header
        (cbor_raw_get_header')
        ()
        (ser_payload f64 f)
      )
    )
    (Classical.forall_intro parse_raw_data_item_eq; serialize_raw_data_item)

let ser_pre
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
: Tot slprop
=
    (S.pts_to out v ** cbor_match_with_perm x' x ** pure (
      SZ.v offset + Seq.length (bare_serialize serialize_raw_data_item x) <= Seq.length v
    ))

let ser_post
  (x': with_perm cbor_raw)
  (x: raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
  (res: SZ.t)
: Tot slprop
=
  exists* v' .
      S.pts_to out v' ** cbor_match_with_perm x' x ** pure (
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
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre x' x out offset v) (fun res -> ser_post x' x out offset v res))
: LP.l2r_writer #_ #raw_data_item (cbor_match_with_perm) #parse_raw_data_item_kind #parse_raw_data_item serialize_raw_data_item
=
  (x': with_perm cbor_raw) (#x: raw_data_item) (out: S.slice LP.byte) (offset: SZ.t) (#v: Ghost.erased LP.bytes)
{
  fold (ser_pre x' x out offset v);
  let res = f x' x out offset v;
  unfold (ser_post x' x out offset v res);
  res
}
```

inline_for_extraction
```pulse
fn ser_unfold
  (f: LP.l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre x' x out offset v)
returns res: SZ.t
ensures
  (ser_post x' x out offset v res)
{
  unfold (ser_pre x' x out offset v);
  let res = f x' out offset;
  fold (ser_post x' x out offset v res);
  res
}
```

inline_for_extraction
```pulse
fn ser_body'
  (f64: squash SZ.fits_u64)
  (f: (x': with_perm cbor_raw) -> (x: Ghost.erased raw_data_item) -> (out: S.slice LP.byte) -> (offset: SZ.t) -> (v: Ghost.erased LP.bytes) -> stt SZ.t (ser_pre x' x out offset v) (fun res -> ser_post x' x out offset v res))
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre x' x out offset v)
returns res: SZ.t
ensures
  ser_post x' x out offset v res
{
  ser_unfold (ser_body f64 (ser_fold f)) x' x out offset v;
}
```

```pulse
fn rec ser'
  (f64: squash SZ.fits_u64)
  (x': with_perm cbor_raw)
  (x: Ghost.erased raw_data_item)
  (out: S.slice LP.byte)
  (offset: SZ.t)
  (v: Ghost.erased LP.bytes)
requires
  (ser_pre x' x out offset v)
returns res: SZ.t
ensures
  ser_post x' x out offset v res
{
  ser_body' f64 (ser' f64) x' x out offset v
}
```

let ser (f64: squash SZ.fits_u64) (p: perm) : l2r_writer (cbor_match p) serialize_raw_data_item =
  l2r_writer_lens
    (cbor_match_with_perm_lens p)
    (ser_fold (ser' f64))

```pulse
fn cbor_serialize
  (x: cbor_raw)
  (output: S.slice U8.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
requires
    (exists* v . cbor_match pm x y ** S.pts_to output v ** pure (Seq.length (serialize_cbor y) <= SZ.v (S.len output)))
returns res: SZ.t
ensures exists* v . cbor_match pm x y ** S.pts_to output v ** pure (
      let s = serialize_cbor y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))
    )
{
  let sq : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len output;
  let res = ser sq _ x output 0sz;
  with v . assert (S.pts_to output v);
  Seq.lemma_split v (SZ.v res);
  res
}
```
