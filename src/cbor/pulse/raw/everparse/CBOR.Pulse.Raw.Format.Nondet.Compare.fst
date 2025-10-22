module CBOR.Pulse.Raw.Format.Nondet.Compare
#lang-pulse
friend CBOR.Pulse.Raw.Format.Match

module EP = CBOR.Pulse.Raw.EverParse.Nondet.Basic
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

fn cbor_match_equal_serialized_tagged
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Tagged? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Tagged? r2 })
requires
  (cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (
      valid_raw_data_item r1 /\
      valid_raw_data_item r2
    ) 
  )
returns res: bool
ensures
  (
    cbor_match_serialized_tagged c1 pm1 r1 **
    cbor_match_serialized_tagged c2 pm2 r2 **
    pure (
      res == raw_equiv r1 r2
    )
  )
{
  unfold (cbor_match_serialized_tagged c1 pm1 r1);
  unfold (cbor_match_serialized_tagged c2 pm2 r2);
  unfold (cbor_match_serialized_payload_tagged c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Tagged?.v r1));
  unfold (cbor_match_serialized_payload_tagged c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Tagged?.v r2));
  valid_eq basic_data_model r1;
  valid_eq basic_data_model r2;
  raw_equiv_eq_valid r1 r2;
if ((c1.cbor_serialized_header.value <: FStar.UInt64.t) <> c2.cbor_serialized_header.value) {
  fold (cbor_match_serialized_payload_tagged c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Tagged?.v r2));
  fold (cbor_match_serialized_payload_tagged c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Tagged?.v r1));
  fold (cbor_match_serialized_tagged c1 pm1 r1);
  fold (cbor_match_serialized_tagged c2 pm2 r2);
  false
} else {
  CBOR.Spec.Raw.Nondet.check_equiv_correct basic_data_model None (Tagged?.v r1) (Tagged?.v r2);
  let res = EP.impl_check_equiv_basic None c1.cbor_serialized_payload c2.cbor_serialized_payload;
  fold (cbor_match_serialized_payload_tagged c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Tagged?.v r2));
  fold (cbor_match_serialized_payload_tagged c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Tagged?.v r1));
  fold (cbor_match_serialized_tagged c1 pm1 r1);
  fold (cbor_match_serialized_tagged c2 pm2 r2);
  (res = Some true)
}
}

fn cbor_match_compare_serialized_array
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Array? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Array? r2 })
requires
  (cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (
      valid_raw_data_item r1 /\
      valid_raw_data_item r2
    )
  )
returns res: bool
ensures
  (
    cbor_match_serialized_array c1 pm1 r1 **
    cbor_match_serialized_array c2 pm2 r2 **
    pure (
      res == raw_equiv r1 r2
    )
  )
{
  unfold (cbor_match_serialized_array c1 pm1 r1);
  unfold (cbor_match_serialized_array c2 pm2 r2);
  unfold (cbor_match_serialized_payload_array c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Array?.v r1));
  unfold (cbor_match_serialized_payload_array c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Array?.v r2));
  valid_eq basic_data_model r1;
  valid_eq basic_data_model r2;
  raw_equiv_eq_valid r1 r2;
  Classical.forall_intro_2 (CBOR.Spec.Raw.Nondet.check_equiv_correct basic_data_model None);
  CBOR.Spec.Raw.Nondet.check_equiv_list_map_correct basic_data_model None (Array?.v r1) (Array?.v r2);
  assume (pure (SZ.fits_u64));
  let n1 : SZ.t = (SZ.uint64_to_sizet c1.cbor_serialized_header.value);
  LowParse.Pulse.VCList.pts_to_serialized_nlist_ext _ _ c1.cbor_serialized_payload CBOR.Spec.Raw.EverParse.serialize_raw_data_item (SZ.v n1);
  with p1' r1' . assert (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n1) CBOR.Spec.Raw.EverParse.serialize_raw_data_item) c1.cbor_serialized_payload #p1' r1');
  let n2 : SZ.t = (SZ.uint64_to_sizet c2.cbor_serialized_header.value);
  LowParse.Pulse.VCList.pts_to_serialized_nlist_ext _ _ c2.cbor_serialized_payload CBOR.Spec.Raw.EverParse.serialize_raw_data_item (SZ.v n2);
  with p2' r2' . assert (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n2) CBOR.Spec.Raw.EverParse.serialize_raw_data_item) c2.cbor_serialized_payload #p2' r2');
  let res = EP.impl_check_equiv_list_basic
    None
    n1
    c1.cbor_serialized_payload
    n2
    c2.cbor_serialized_payload
  ;
  Trade.elim (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n2) CBOR.Spec.Raw.EverParse.serialize_raw_data_item) c2.cbor_serialized_payload #p2' _) _;
  Trade.elim (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n1) CBOR.Spec.Raw.EverParse.serialize_raw_data_item) c1.cbor_serialized_payload #p1' _) _;
  fold (cbor_match_serialized_payload_array c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Array?.v r2));
  fold (cbor_match_serialized_payload_array c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Array?.v r1));
  fold (cbor_match_serialized_array c1 pm1 r1);
  fold (cbor_match_serialized_array c2 pm2 r2);
  (res = Some true)
}

fn cbor_match_compare_serialized_map
  (c1 c2: cbor_serialized)
  (#pm1: perm)
  (#r1: Ghost.erased raw_data_item { Map? r1 })
  (#pm2: perm)
  (#r2: Ghost.erased raw_data_item { Map? r2 })
requires
  (cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (
      valid_raw_data_item r1 /\
      valid_raw_data_item r2
    )
  )
returns res: bool
ensures
  (
    cbor_match_serialized_map c1 pm1 r1 **
    cbor_match_serialized_map c2 pm2 r2 **
    pure (
      res == raw_equiv r1 r2
    )
  )
{
  unfold (cbor_match_serialized_map c1 pm1 r1);
  unfold (cbor_match_serialized_map c2 pm2 r2);
  unfold (cbor_match_serialized_payload_map c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Map?.v r1));
  unfold (cbor_match_serialized_payload_map c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Map?.v r2));
  valid_eq basic_data_model r1;
  valid_eq basic_data_model r2;
  raw_equiv_eq_valid r1 r2;
  Classical.forall_intro_2 (CBOR.Spec.Raw.Nondet.check_equiv_correct basic_data_model None);
  CBOR.Spec.Raw.Nondet.list_for_all_with_overflow_setoid_assoc_eq_with_overflow_equiv_correct
    basic_data_model None
    (CBOR.Spec.Raw.Nondet.check_equiv basic_data_model None)
    (CBOR.Spec.Util.list_sum (CBOR.Spec.Util.pair_sum raw_data_item_size raw_data_item_size) (Map?.v r1) + CBOR.Spec.Util.list_sum (CBOR.Spec.Util.pair_sum raw_data_item_size raw_data_item_size) (Map?.v r2))
    (Map?.v r1) (Map?.v r2);
  CBOR.Spec.Raw.Nondet.list_for_all_with_overflow_setoid_assoc_eq_with_overflow_equiv_correct
    basic_data_model None
    (CBOR.Spec.Raw.Nondet.check_equiv basic_data_model None)
    (CBOR.Spec.Util.list_sum (CBOR.Spec.Util.pair_sum raw_data_item_size raw_data_item_size) (Map?.v r1) + CBOR.Spec.Util.list_sum (CBOR.Spec.Util.pair_sum raw_data_item_size raw_data_item_size) (Map?.v r2))
    (Map?.v r2) (Map?.v r1);
  assume (pure (SZ.fits_u64));
  let n1 : SZ.t = (SZ.uint64_to_sizet c1.cbor_serialized_header.value);
  LowParse.Pulse.VCList.pts_to_serialized_nlist_ext _ _ c1.cbor_serialized_payload (LowParse.Spec.Combinators.serialize_nondep_then CBOR.Spec.Raw.EverParse.serialize_raw_data_item CBOR.Spec.Raw.EverParse.serialize_raw_data_item) (SZ.v n1);
  with p1' r1' . assert (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n1) (LowParse.Spec.Combinators.serialize_nondep_then CBOR.Spec.Raw.EverParse.serialize_raw_data_item CBOR.Spec.Raw.EverParse.serialize_raw_data_item)) c1.cbor_serialized_payload #p1' r1');
  let n2 : SZ.t = (SZ.uint64_to_sizet c2.cbor_serialized_header.value);
  LowParse.Pulse.VCList.pts_to_serialized_nlist_ext _ _ c2.cbor_serialized_payload (LowParse.Spec.Combinators.serialize_nondep_then CBOR.Spec.Raw.EverParse.serialize_raw_data_item CBOR.Spec.Raw.EverParse.serialize_raw_data_item) (SZ.v n2);
  with p2' r2' . assert (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n2) (LowParse.Spec.Combinators.serialize_nondep_then CBOR.Spec.Raw.EverParse.serialize_raw_data_item CBOR.Spec.Raw.EverParse.serialize_raw_data_item)) c2.cbor_serialized_payload #p2' r2');
  let res21 = EP.impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_basic
    n2
    c2.cbor_serialized_payload
    n1
    c1.cbor_serialized_payload
  ;
  if (res21 = Some true) {
    let res12 = EP.impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_basic
      n1
      c1.cbor_serialized_payload
      n2
      c2.cbor_serialized_payload
    ;
    Trade.elim (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n2) (LowParse.Spec.Combinators.serialize_nondep_then CBOR.Spec.Raw.EverParse.serialize_raw_data_item CBOR.Spec.Raw.EverParse.serialize_raw_data_item)) c2.cbor_serialized_payload #p2' _) _;
    Trade.elim (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n1) (LowParse.Spec.Combinators.serialize_nondep_then CBOR.Spec.Raw.EverParse.serialize_raw_data_item CBOR.Spec.Raw.EverParse.serialize_raw_data_item)) c1.cbor_serialized_payload #p1' _) _;
    fold (cbor_match_serialized_payload_map c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Map?.v r2));
    fold (cbor_match_serialized_payload_map c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Map?.v r1));
    fold (cbor_match_serialized_map c1 pm1 r1);
    fold (cbor_match_serialized_map c2 pm2 r2);
    (res12 = Some true)
  } else {
    Trade.elim (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n2) (LowParse.Spec.Combinators.serialize_nondep_then CBOR.Spec.Raw.EverParse.serialize_raw_data_item CBOR.Spec.Raw.EverParse.serialize_raw_data_item)) c2.cbor_serialized_payload #p2' _) _;
    Trade.elim (LowParse.Pulse.Base.pts_to_serialized (LowParse.Spec.VCList.serialize_nlist (SZ.v n1) (LowParse.Spec.Combinators.serialize_nondep_then CBOR.Spec.Raw.EverParse.serialize_raw_data_item CBOR.Spec.Raw.EverParse.serialize_raw_data_item)) c1.cbor_serialized_payload #p1' _) _;
    fold (cbor_match_serialized_payload_map c2.cbor_serialized_payload (pm2 `perm_mul` c2.cbor_serialized_perm) (Map?.v r2));
    fold (cbor_match_serialized_payload_map c1.cbor_serialized_payload (pm1 `perm_mul` c1.cbor_serialized_perm) (Map?.v r1));
    fold (cbor_match_serialized_map c1 pm1 r1);
    fold (cbor_match_serialized_map c2 pm2 r2);
    false
  }
}
