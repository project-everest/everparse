module CBOR.Pulse.Raw.Format.Serialize
open Pulse.Lib.Pervasives
friend CBOR.Spec.Raw.Format
friend CBOR.Pulse.Raw.Format.Match
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.Base
open LowParse.Pulse.Base

open CBOR.Pulse.Raw.Match
module LP = LowParse.Pulse.Combinators
module LPI = LowParse.Pulse.Int

inline_for_extraction
let write_initial_byte' : l2r_leaf_writer serialize_initial_byte_t =
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
noextract [@@noextract_to "krml"]
let write_initial_byte : l2r_leaf_writer serialize_initial_byte =
  LP.l2r_leaf_write_filter
    write_initial_byte'
    initial_byte_wf

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

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_16
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_16_bits) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (LP.l2r_leaf_write_synth'
                  (LPI.l2r_leaf_write_u16 ())
                  (LongArgumentU16 #b ())
                  (LongArgumentU16?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_32
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_32_bits) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (LP.l2r_leaf_write_synth'
                  (LPI.l2r_leaf_write_u32 ())
                  (LongArgumentU32 #b ())
                  (LongArgumentU32?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_64
  (b: initial_byte)
  (sq: squash ((b.additional_info = additional_info_long_argument_64_bits) == true))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (LP.l2r_leaf_write_synth'
                  (LPI.l2r_leaf_write_u64 ())
                  (LongArgumentU64 #b ())
                  (LongArgumentU64?.v)
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_other
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
  (sq64: squash ((b.additional_info = additional_info_long_argument_64_bits) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
=
              l2r_leaf_writer_ext
                (LP.l2r_leaf_write_synth'
                  LP.l2r_leaf_write_empty
                  (LongArgumentOther #b b.additional_info ())
                  LongArgumentOther?.v
                )
                (serialize_long_argument b)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_not_8_16_32
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
  (sq32: squash ((b.additional_info = additional_info_long_argument_32_bits) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_64_bits)
    (write_long_argument_64 b)
    (write_long_argument_other b sq8 sq16 sq32)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_not_8_16
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
  (sq16: squash ((b.additional_info = additional_info_long_argument_16_bits) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_32_bits)
    (write_long_argument_32 b)
    (write_long_argument_not_8_16_32 b sq8 sq16)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument_not_8
  (b: initial_byte)
  (sq8: squash ((b.additional_info = additional_info_long_argument_8_bits) == false))
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
    (serialize_long_argument b)
    (b.additional_info = additional_info_long_argument_16_bits)
    (write_long_argument_16 b)
    (write_long_argument_not_8_16 b sq8)

inline_for_extraction
noextract [@@noextract_to "krml"]
let write_long_argument
  (b: initial_byte)
: Tot (l2r_leaf_writer (serialize_long_argument b))
= l2r_leaf_writer_ifthenelse
      (serialize_long_argument b)
      (b.additional_info = additional_info_long_argument_8_bits)
      (write_long_argument_8 b)
      (write_long_argument_not_8 b)

let write_header : l2r_leaf_writer serialize_header =
  l2r_leaf_writer_ext
    (LP.l2r_leaf_write_dtuple2
      write_initial_byte
      ()
      write_long_argument
    )
    _

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
fn match_cbor_payload_elim_trade
  (xh1: header)
  (xl: with_perm cbor_raw)
  (xh: content xh1)
requires
  match_cbor_payload xh1 xl xh
returns xh': Ghost.erased raw_data_item
ensures
  (cbor_match_with_perm xl xh' **
    Trade.trade
      (cbor_match_with_perm xl xh')
      (match_cbor_payload xh1 xl xh) **
      pure (synth_raw_data_item_recip xh' == (| xh1, xh |))
  )
{
  Trade.rewrite_with_trade
    (match_cbor_payload xh1 xl xh)
    (cbor_match_with_perm xl (synth_raw_data_item (| xh1, xh |)));
  synth_raw_data_item_recip_synth_raw_data_item (| xh1, xh |);
  synth_raw_data_item (| xh1, xh |)
}
```

```pulse
ghost
fn ser_payload_string_lens_aux
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string))
  (xl: with_perm cbor_raw)
  (xh: Seq.Properties.lseq byte
                  (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))))
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
  let _ = vmatch_ext_elim_trade 
      (Seq.Properties.lseq byte
                  (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))))
      (match_cbor_payload xh1) xl xh;
  let xh' = match_cbor_payload_elim_trade xh1 xl _;
  Trade.trans (cbor_match_with_perm xl xh') _ _;
  xh'
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
  with p' . assert (pts_to s #p' (Ghost.reveal x <: Seq.seq U8.t));
  let res : with_perm (S.slice byte) = {
    v = s;
    p = p';
  };
  let x' = LowParse.Pulse.SeqBytes.pts_to_seqbytes_intro
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
  let xh2 = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          raw_data_item) (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_array) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) _ _ _;
  Trade.trans (match_cbor_payload xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 _ _;
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match _ _ _) _ _;
  cbor_match_cases _;
  let a = CBOR_Case_Array?.v xl.v;
  cbor_match_eq_array xl.p a xh0;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_array a xl.p xh0 cbor_match);
  Trade.trans (cbor_match_array a xl.p xh0 cbor_match) _ _;
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
    cbor_match_array a xl.p xh0 cbor_match
  {
    unfold (    LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_array_get
      cbor_with_perm_case_array_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh
    );
    fold (cbor_match_array a xl.p xh0 cbor_match);
  };
  Trade.intro _ _ _ aux;
  Trade.trans _ (cbor_match_array a xl.p xh0 cbor_match) _;
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

```pulse
ghost
fn cbor_serialized_array_pts_to_serialized_with_perm_trade
  (xs: cbor_serialized)
  (p: perm)
  (xh0: raw_data_item { Array? xh0 })
  (n: nat { n == U64.v (Array?.len xh0).value })
  (res: with_perm (S.slice byte))
requires
  cbor_match_serialized_array xs p xh0 ** pure (
    res.v == xs.cbor_serialized_payload /\
    res.p == p `perm_mul` xs.cbor_serialized_perm
  )
ensures
  pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0) **
  Trade.trade
    (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0) )
    (cbor_match_serialized_array xs p xh0)
{
  unfold (cbor_match_serialized_array xs p xh0);
  unfold (cbor_match_serialized_payload_array xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Array?.v xh0));
  with n' (r': LowParse.Spec.VCList.nlist n' raw_data_item) . assert
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' serialize_raw_data_item) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) r');
  rewrite (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' serialize_raw_data_item) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) r')
    as (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0));
  ghost fn aux (_: unit)
  requires
    emp ** pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0)
  ensures
    cbor_match_serialized_array xs p xh0
  { 
    rewrite (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) res (Array?.v xh0))
      as (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n serialize_raw_data_item) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) (Array?.v xh0));
    fold (cbor_match_serialized_payload_array xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Array?.v xh0));
    fold (cbor_match_serialized_array xs p xh0);
  };
  Trade.intro _ _ _ aux
}
```

inline_for_extraction
```pulse
fn ser_payload_array_not_array_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
: vmatch_lens #_ #_ #_ (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_array)))
  (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          serialize_raw_data_item))
= (xl: _)
  (v: _)
{
  let _ = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          raw_data_item)
      (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_array)) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) (pnot cbor_with_perm_case_array) _ _;
  Trade.trans (match_cbor_payload xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl _;
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match xl.p xl.v xh0) _ _;
  cbor_match_cases xl.v;
  let xs = CBOR_Case_Serialized_Array?.v xl.v;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_serialized_array xs xl.p xh0);
  Trade.trans (cbor_match_serialized_array xs xl.p xh0) _ _;
  let res : with_perm (S.slice byte) = {
    v = xs.cbor_serialized_payload;
    p = xl.p `perm_mul` xs.cbor_serialized_perm;
  };
  cbor_serialized_array_pts_to_serialized_with_perm_trade xs xl.p xh0
    (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
    res;
  Trade.trans _ (cbor_match_serialized_array xs xl.p xh0) _;
  res
}
```

inline_for_extraction
let ser_payload_array_not_array
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_array))
:
l2r_writer (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_array))
  (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_array_not_array_lens xh1 sq)
      (l2r_write_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) serialize_raw_data_item
      ))
    )
    _

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
    (ser_payload_array_not_array xh1 sq)

inline_for_extraction
let cbor_with_perm_case_map
  (c: with_perm cbor_raw)
: Tot bool
= CBOR_Case_Map? c.v

inline_for_extraction
let cbor_with_perm_case_map_get
  (c: with_perm cbor_raw)
: Tot (option (with_perm (A.array cbor_map_entry)))
= match c.v with
  | CBOR_Case_Map a -> Some { v = a.cbor_map_ptr; p = perm_mul c.p a.cbor_map_array_perm }
  | _ -> None

let cbor_with_perm_case_map_match_elem_perm
  (c: with_perm cbor_raw)
: Tot perm
= (perm_mul c.p (match c.v with CBOR_Case_Map a -> a.cbor_map_payload_perm | _ -> 1.0R (* dummy *) ))

let cbor_with_perm_case_map_match_elem
  (c: with_perm cbor_raw)
: (x: cbor_map_entry) ->
  (y: (raw_data_item & raw_data_item)) ->
  Tot slprop
= cbor_match_map_entry (cbor_with_perm_case_map_match_elem_perm c)

inline_for_extraction
```pulse
fn ser_payload_map_map_elem_fst
  (a: with_perm cbor_raw)
  (xl: cbor_map_entry)
  (xh: erased (raw_data_item & raw_data_item))
requires
  (cbor_with_perm_case_map_match_elem a xl xh)
returns xl1: (with_perm cbor_raw)
ensures
      (
          cbor_match_with_perm xl1 (fst xh) **
          trade (cbor_match_with_perm xl1 (fst xh)) (cbor_with_perm_case_map_match_elem a xl xh))
{
  let xl1 : with_perm cbor_raw = {
    v = xl.cbor_map_entry_key;
    p = cbor_with_perm_case_map_match_elem_perm a;
  };
  Trade.rewrite_with_trade
    (cbor_with_perm_case_map_match_elem a xl xh)
    (cbor_match_with_perm xl1 (fst xh) **
      cbor_match (cbor_with_perm_case_map_match_elem_perm a) xl.cbor_map_entry_value (snd xh)
    );
  Trade.elim_hyp_r _ _ _;
  xl1
}
```

inline_for_extraction
```pulse
fn ser_payload_map_map_elem_snd
  (a: with_perm cbor_raw)
  (xl: cbor_map_entry)
  (xh: erased (raw_data_item & raw_data_item))
requires
  (cbor_with_perm_case_map_match_elem a xl xh)
returns xl1: (with_perm cbor_raw)
ensures
      (
          cbor_match_with_perm xl1 (snd xh) **
          trade (cbor_match_with_perm xl1 (snd xh)) (cbor_with_perm_case_map_match_elem a xl xh))
{
  let xl2 : with_perm cbor_raw = {
    v = xl.cbor_map_entry_value;
    p = cbor_with_perm_case_map_match_elem_perm a;
  };
  Trade.rewrite_with_trade
    (cbor_with_perm_case_map_match_elem a xl xh)
    (cbor_match (cbor_with_perm_case_map_match_elem_perm a) xl.cbor_map_entry_key (fst xh) **
      cbor_match_with_perm xl2 (snd xh)
    );
  Trade.elim_hyp_l _ _ _;
  xl2
}
```

inline_for_extraction
let ser_payload_map_map_elem
  (f: l2r_writer cbor_match_with_perm serialize_raw_data_item)
  (a: with_perm cbor_raw)
: l2r_writer (cbor_with_perm_case_map_match_elem a) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
= LP.l2r_write_nondep_then
    f
    ()
    f
    _
    (ser_payload_map_map_elem_fst a)
    (ser_payload_map_map_elem_snd a)

#restart-solver
```pulse
ghost
fn ser_payload_map_map_lens_aux
  (f64: squash SZ.fits_u64)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_map))
  (xl: with_perm cbor_raw)
  (xh: LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1)))) (raw_data_item & raw_data_item))
requires
  (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map)
      xl xh
  )
ensures
  LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_map_get
    cbor_with_perm_case_map_match_elem
    (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1))))
    xl xh **
  Trade.trade
    (LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh)
      (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                                              xh1)
                                              (get_header_long_argument xh1))))
                  (raw_data_item & raw_data_item))
                  (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map)
                  xl xh
      )
{
  let xh2 = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          (raw_data_item & raw_data_item)) (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) _ _ _;
  Trade.trans (match_cbor_payload xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 _ _;
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match _ _ _) _ _;
  cbor_match_cases _;
  let a = CBOR_Case_Map?.v xl.v;
  cbor_match_eq_map0 xl.p a xh0;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_map0 a xl.p xh0 cbor_match);
  Trade.trans (cbor_match_map0 a xl.p xh0 cbor_match) _ _;
  cbor_match_map0_map_trade a xl.p xh0;
  Trade.trans (cbor_match_map xl.p a xh0) _ _;
  unfold (cbor_match_map xl.p a xh0);
  let ar = Some?.v (cbor_with_perm_case_map_get xl);
  LowParse.Pulse.VCList.nlist_match_array_intro cbor_with_perm_case_map_get
    cbor_with_perm_case_map_match_elem
    (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
      (get_header_long_argument xh1))))
    xl xh
    ar _
  ;
  ghost fn aux (_: unit)
  requires emp **
    LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh
  ensures
    cbor_match_map xl.p a xh0
  {
    unfold (    LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
        (get_header_long_argument xh1))))
      xl xh
    );
    fold (cbor_match_map xl.p a xh0);
  };
  Trade.intro _ _ _ aux;
  Trade.trans _ (cbor_match_map xl.p a xh0) _;
}
```

inline_for_extraction
```pulse
fn ser_payload_map_map_lens
  (f64: squash SZ.fits_u64)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in
    b.major_type = cbor_major_type_map))
:
vmatch_lens #_ #_ #_
  (vmatch_ext (LowParse.Spec.VCList.nlist (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte
                          xh1)
                      (get_header_long_argument xh1))))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map))
  (LowParse.Pulse.VCList.nlist_match_array cbor_with_perm_case_map_get
      cbor_with_perm_case_map_match_elem
      (SZ.v (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1)
                  (get_header_long_argument xh1)))))
=
  (x1': _)
  (x: _)
{
  ser_payload_map_map_lens_aux f64 xh1 sq x1' x;
  x1'
}
```

inline_for_extraction
let ser_payload_map_map
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (vmatch_with_cond (match_cbor_payload xh1) cbor_with_perm_case_map) (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_map_map_lens f64 xh1 sq)
      (LowParse.Pulse.VCList.l2r_write_nlist_as_array
        cbor_with_perm_case_map_get
        cbor_with_perm_case_map_match_elem
        (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
        (ser_payload_map_map_elem f)
        (SZ.uint64_to_sizet (argument_as_uint64 (get_header_initial_byte xh1) (get_header_long_argument xh1)))
      )
    )
    (serialize_content xh1)

```pulse
ghost
fn cbor_serialized_map_pts_to_serialized_with_perm_trade
  (xs: cbor_serialized)
  (p: perm)
  (xh0: raw_data_item { Map? xh0 })
  (n: nat { n == U64.v (Map?.len xh0).value })
  (res: with_perm (S.slice byte))
requires
  cbor_match_serialized_map xs p xh0 ** pure (
    res.v == xs.cbor_serialized_payload /\
    res.p == p `perm_mul` xs.cbor_serialized_perm
  )
ensures
  pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0) **
  Trade.trade
    (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0) )
    (cbor_match_serialized_map xs p xh0)
{
  unfold (cbor_match_serialized_map xs p xh0);
  unfold (cbor_match_serialized_payload_map xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Map?.v xh0));
  with n' (r': LowParse.Spec.VCList.nlist n' (raw_data_item & raw_data_item)) . assert
    (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) r');
  rewrite (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n' (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) r')
    as (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0));
  ghost fn aux (_: unit)
  requires
    emp ** pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0)
  ensures
    cbor_match_serialized_map xs p xh0
  { 
    rewrite (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) res (Map?.v xh0))
      as (pts_to_serialized (LowParse.Spec.VCList.serialize_nlist n (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)) xs.cbor_serialized_payload #(p `perm_mul` xs.cbor_serialized_perm) (Map?.v xh0));
    fold (cbor_match_serialized_payload_map xs.cbor_serialized_payload (p `perm_mul` xs.cbor_serialized_perm) (Map?.v xh0));
    fold (cbor_match_serialized_map xs p xh0);
  };
  Trade.intro _ _ _ aux
}
```

inline_for_extraction
```pulse
fn ser_payload_map_not_map_lens
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: vmatch_lens #_ #_ #_ (vmatch_ext (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_map)))
  (pts_to_serialized_with_perm (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)))
= (xl: _)
  (v: _)
{
  let _ = vmatch_ext_elim_trade (LowParse.Spec.VCList.nlist (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
          (raw_data_item & raw_data_item))
      (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_map)) _ _;
  vmatch_with_cond_elim_trade (match_cbor_payload xh1) (pnot cbor_with_perm_case_map) _ _;
  Trade.trans (match_cbor_payload xh1 _ _) _ _;
  let xh0 = match_cbor_payload_elim_trade xh1 xl _;
  Trade.trans (cbor_match_with_perm xl xh0) _ _;
  Trade.rewrite_with_trade
    (cbor_match_with_perm xl xh0)
    (cbor_match xl.p xl.v xh0);
  Trade.trans (cbor_match xl.p xl.v xh0) _ _;
  cbor_match_cases xl.v;
  let xs = CBOR_Case_Serialized_Map?.v xl.v;
  Trade.rewrite_with_trade
    (cbor_match xl.p xl.v xh0)
    (cbor_match_serialized_map xs xl.p xh0);
  Trade.trans (cbor_match_serialized_map xs xl.p xh0) _ _;
  let res : with_perm (S.slice byte) = {
    v = xs.cbor_serialized_payload;
    p = xl.p `perm_mul` xs.cbor_serialized_perm;
  };
  cbor_serialized_map_pts_to_serialized_with_perm_trade xs xl.p xh0
    (U64.v (argument_as_uint64 (get_header_initial_byte
                      xh1)
                  (get_header_long_argument xh1)))
    res;
  Trade.trans _ (cbor_match_serialized_map xs xl.p xh0) _;
  res
}
```

inline_for_extraction
let ser_payload_map_not_map
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
:
l2r_writer (vmatch_with_cond (match_cbor_payload xh1) (pnot cbor_with_perm_case_map))
  (serialize_content xh1)
= l2r_writer_ext_gen
    (l2r_writer_lens
      (ser_payload_map_not_map_lens xh1 sq)
      (l2r_write_copy (LowParse.Spec.VCList.serialize_nlist (U64.v (argument_as_uint64 (get_header_initial_byte xh1)
                          (get_header_long_argument xh1))) (LP.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item)
      ))
    )
    _

inline_for_extraction
let ser_payload_map
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse_low
    _ _
    cbor_with_perm_case_map
    (ser_payload_map_map f64 f xh1 sq)
    (ser_payload_map_not_map xh1 sq)

assume val ser_payload_tagged
  (xh1: header)
  (sq: squash (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)

inline_for_extraction
let ser_payload_scalar
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
  (sq_not_tagged: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_tagged == false))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ext_gen
    (LP.l2r_write_empty _)
    _

inline_for_extraction
let ser_payload_not_string_not_array_not_map
  (f64: squash SZ.fits_u64)
//  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq_not_string: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (sq_not_array: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
  (sq_not_map: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_map == false))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_tagged)
    (ser_payload_tagged xh1)
    (ser_payload_scalar xh1 () () ())

inline_for_extraction
let ser_payload_not_string_not_array
  (f64: squash SZ.fits_u64)
  (f: l2r_writer (cbor_match_with_perm) serialize_raw_data_item)
  (xh1: header)
  (sq: squash (not (let b = get_header_initial_byte xh1 in b.major_type = 
cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string)))
  (_: squash ((get_header_initial_byte xh1).major_type = cbor_major_type_array == false))
: l2r_writer (match_cbor_payload xh1) (serialize_content xh1)
= l2r_writer_ifthenelse _ _
    (let b = get_header_initial_byte xh1 in b.major_type = cbor_major_type_map)
    (ser_payload_map f64 f xh1)
    (ser_payload_not_string_not_array_not_map f64 xh1 () ())

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
    (ser_payload_not_string_not_array f64 f xh1 sq)

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
    (pts_to out v ** cbor_match_with_perm x' x ** pure (
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
      pts_to out v' ** cbor_match_with_perm x' x ** pure (
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
    (exists* v . cbor_match pm x y ** pts_to output v ** pure (Seq.length (serialize_cbor y) <= SZ.v (S.len output)))
returns res: SZ.t
ensures exists* v . cbor_match pm x y ** pts_to output v ** pure (
      let s = serialize_cbor y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))
    )
{
  let sq : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len output;
  let res = ser sq _ x output 0sz;
  with v . assert (pts_to output v);
  Seq.lemma_split v (SZ.v res);
  res
}
```
