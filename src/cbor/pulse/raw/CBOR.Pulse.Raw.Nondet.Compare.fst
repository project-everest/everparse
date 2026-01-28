module CBOR.Pulse.Raw.Nondet.Compare
#lang-pulse
open CBOR.Pulse.Raw.Match
open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Base

module Spec = CBOR.Spec.API.Format
module Raw = CBOR.Pulse.Raw.Match
module SpecRaw = CBOR.Spec.Raw
module Read = CBOR.Pulse.Raw.Read
module U64 = FStar.UInt64
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_equiv_t =
  (x1: Raw.cbor_raw) ->
  (#p1: perm) ->
  (#v1: Ghost.erased SpecRaw.raw_data_item) ->
  (x2: Raw.cbor_raw) ->
  (#p2: perm) ->
  (#v2: Ghost.erased SpecRaw.raw_data_item) ->
  stt bool
  (Raw.cbor_match p1 x1 v1 **
    Raw.cbor_match p2 x2 v2 **
    pure (SpecRaw.valid_raw_data_item v1 /\
      SpecRaw.valid_raw_data_item v2
    )
  )
  (fun res ->
    Raw.cbor_match p1 x1 v1 **
    Raw.cbor_match p2 x2 v2 **
    pure (res == SpecRaw.raw_equiv v1 v2)
  )

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_setoid_assoc_eq
  (cbor_nondet_equiv: cbor_nondet_equiv_t)
  (i1: cbor_map_iterator)
  (#p1: perm)
  (#v1: Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)))
  (x2: cbor_map_entry)
  (#p2: perm)
  (#v2: Ghost.erased (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
requires
  Read.cbor_map_iterator_match p1 i1 v1 **
  cbor_match_map_entry p2 x2 v2 **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst v1) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd v1) /\
    SpecRaw.valid_raw_data_item (fst v2) /\
    SpecRaw.valid_raw_data_item (snd v2)

  )
returns res: bool
ensures
  Read.cbor_map_iterator_match p1 i1 v1 **
  cbor_match_map_entry p2 x2 v2 **
  pure (res == CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1 v2)
{
  Trade.refl (Read.cbor_map_iterator_match p1 i1 v1);
  let mut pi1 = i1;
  let mut pres = (None #bool);
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  while (
    if (Some? !pres) {
      false
    } else {
      let i1 = !pi1;
      not (Read.cbor_map_iterator_is_empty i1)
    }
  ) invariant b . exists* gi1 l1 res . (
    pts_to pi1 gi1 **
    Read.cbor_map_iterator_match p1 gi1 l1 **
    Trade.trade
      (Read.cbor_map_iterator_match p1 gi1 l1)
      (Read.cbor_map_iterator_match p1 i1 v1) **
    pts_to pres res **
    cbor_match_map_entry p2 x2 v2 **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l1) /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd l1) /\
      CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1 v2 == (match res with Some r -> r | _ -> CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv l1 v2)
    ) ** pure (
      b == (Cons? l1 && None? res)
    )
  ) {
    let x1 = Read.cbor_map_iterator_next () pi1;
    Trade.trans _ _ (Read.cbor_map_iterator_match p1 i1 v1);
    with px1 vx1 . assert (Read.cbor_match_map_entry px1 x1 vx1);
    unfold (Read.cbor_match_map_entry px1 x1 vx1);
    unfold (Read.cbor_match_map_entry p2 x2 v2);
    if (cbor_nondet_equiv x2.cbor_map_entry_key x1.cbor_map_entry_key) {
      pres := Some (cbor_nondet_equiv x2.cbor_map_entry_value x1.cbor_map_entry_value);
      fold (Read.cbor_match_map_entry px1 x1 vx1);
      fold (Read.cbor_match_map_entry p2 x2 v2);
      Trade.elim_hyp_l _ _ _
    } else {
      fold (Read.cbor_match_map_entry px1 x1 vx1);
      fold (Read.cbor_match_map_entry p2 x2 v2);
      Trade.elim_hyp_l _ _ _
    }
  };
  Trade.elim _ _;
  CBOR.Pulse.Raw.Util.eq_Some_true !pres
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_list_for_all_setoid_assoc_eq
  (cbor_nondet_equiv: cbor_nondet_equiv_t)
  (i1: cbor_map_iterator)
  (#p1: perm)
  (#v1: Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)))
  (i2: cbor_map_iterator)
  (#p2: perm)
  (#v2: Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)))
requires
  Read.cbor_map_iterator_match p1 i1 v1 **
  Read.cbor_map_iterator_match p2 i2 v2 **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst v1) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd v1) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst v2) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd v2)
  )
returns res: bool
ensures
  Read.cbor_map_iterator_match p1 i1 v1 **
  Read.cbor_map_iterator_match p2 i2 v2 **
  pure (res == List.Tot.for_all (CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1) v2)
{
  let mut pi2 = i2;
  Trade.refl (Read.cbor_map_iterator_match p2 i2 v2);
  let mut pres = true;
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  while (
    if (!pres) {
      let i2 = !pi2;
      not (Read.cbor_map_iterator_is_empty i2)
    } else {
      false
    }
  ) invariant b . exists* gi2 l2 res . (
    Read.cbor_map_iterator_match p1 i1 v1 **
    pts_to pi2 gi2 **
    Read.cbor_map_iterator_match p2 gi2 l2 **
    pts_to pres res **
    Trade.trade
      (Read.cbor_map_iterator_match p2 gi2 l2)
      (Read.cbor_map_iterator_match p2 i2 v2) **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l2) /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd l2) /\
      List.Tot.for_all (CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1) v2 == (res && List.Tot.for_all (CBOR.Spec.Util.setoid_assoc_eq SpecRaw.raw_equiv SpecRaw.raw_equiv v1) l2)
    ) ** pure (
      b == (res && Cons? l2)
    )
  ) {
    let x2 = Read.cbor_map_iterator_next () pi2;
    Trade.trans _ _ (Read.cbor_map_iterator_match p2 i2 v2);
    pres := cbor_nondet_setoid_assoc_eq cbor_nondet_equiv i1 x2;
    Trade.elim_hyp_l _ _ _
  };
  Trade.elim _ _;
  !pres
}

#push-options "--z3rlimit 32 --print_implicits"

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_nondet_equiv_body
  (cbor_nondet_equiv: cbor_nondet_equiv_t)
: cbor_nondet_equiv_t
=
  (x1: _)
  (#p1: perm)
  (#v1: Ghost.erased SpecRaw.raw_data_item)
  (x2: _)
  (#p2: perm)
  (#v2: Ghost.erased SpecRaw.raw_data_item)
{
  cbor_match_cases x1;
  cbor_match_cases x2;
  SpecRaw.valid_eq SpecRaw.basic_data_model v1;
  SpecRaw.valid_eq SpecRaw.basic_data_model v2;
  SpecRaw.raw_equiv_eq_valid v1 v2;
  let mt1 = CBOR.Pulse.Raw.Compare.impl_major_type x1;
  let mt2 = CBOR.Pulse.Raw.Compare.impl_major_type x2;
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  if (mt1 <> mt2) {
    false
  } else if (mt1 = Spec.cbor_major_type_simple_value) {
    let w1 = Raw.cbor_match_simple_elim x1;
    let w2 = Raw.cbor_match_simple_elim x2;
    (w1 = w2)
  } else if (mt1 = Spec.cbor_major_type_uint64 || mt1 = Spec.cbor_major_type_neg_int64) {
    let w1 = Raw.cbor_match_int_elim_value x1;
    let w2 = Raw.cbor_match_int_elim_value x2;
    ((w1.value <: U64.t) = w2.value)
  } else if (mt1 = Spec.cbor_major_type_byte_string || mt1 = Spec.cbor_major_type_text_string) {
    let len1 = Raw.cbor_match_string_elim_length x1;
    let len2 = Raw.cbor_match_string_elim_length x2;
    if ((len1.value <: U64.t) <> len2.value) {
      false
    } else {
      let w1 = Raw.cbor_match_string_elim_payload x1;
      let w2 = Raw.cbor_match_string_elim_payload x2;
      let res = CBOR.Pulse.Raw.Compare.Bytes.lex_compare_bytes w1 w2;
      CBOR.Spec.Raw.Format.bytes_lex_compare_equal (SpecRaw.String?.v v1) (SpecRaw.String?.v v2);
      Trade.elim _ (cbor_match p1 x1 v1);
      Trade.elim _ _;
      (res = 0s)
    }
  } else if (mt1 = Spec.cbor_major_type_tagged) {
    if (match x1, x2 with Raw.CBOR_Case_Serialized_Tagged _, Raw.CBOR_Case_Serialized_Tagged _ -> true | _ -> false) {
      norewrite let Raw.CBOR_Case_Serialized_Tagged cs1 = x1;
      norewrite let Raw.CBOR_Case_Serialized_Tagged cs2 = x2;
      Trade.rewrite_with_trade
        (cbor_match p1 x1 v1)
        (cbor_match_serialized_tagged cs1 p1 v1);
      Trade.rewrite_with_trade
        (cbor_match p2 x2 v2)
        (cbor_match_serialized_tagged cs2 p2 v2);
      let res = CBOR.Pulse.Raw.Format.Nondet.Compare.cbor_match_equal_serialized_tagged cs1 cs2;
      Trade.elim _ (cbor_match p1 x1 v1);
      Trade.elim _ _;
      res
    } else {
      let tag1 = Raw.cbor_match_tagged_get_tag x1;
      let tag2 = Raw.cbor_match_tagged_get_tag x2;
      if ((tag1.value <: U64.t) <> tag2.value) {
        false
      } else {
        let w1 = Read.cbor_match_tagged_get_payload x1;
        let w2 = Read.cbor_match_tagged_get_payload x2;
        let res = cbor_nondet_equiv w1 w2;
        Trade.elim _ (cbor_match p1 x1 v1);
        Trade.elim _ _;
        res
      }
    }
  } else if (mt1 = Spec.cbor_major_type_array) {
    if (match x1, x2 with Raw.CBOR_Case_Serialized_Array _, Raw.CBOR_Case_Serialized_Array _ -> true | _ -> false) {
      norewrite let Raw.CBOR_Case_Serialized_Array cs1 = x1;
      norewrite let Raw.CBOR_Case_Serialized_Array cs2 = x2;
      Trade.rewrite_with_trade
        (cbor_match p1 x1 v1)
        (cbor_match_serialized_array cs1 p1 v1);
      Trade.rewrite_with_trade
        (cbor_match p2 x2 v2)
        (cbor_match_serialized_array cs2 p2 v2);
      let res = CBOR.Pulse.Raw.Format.Nondet.Compare.cbor_match_compare_serialized_array cs1 cs2;
      Trade.elim _ (cbor_match p1 x1 v1);
      Trade.elim _ _;
      res
    } else {
      let len1 = Raw.cbor_match_array_get_length x1;
      let len2 = Raw.cbor_match_array_get_length x2;
      Classical.move_requires (CBOR.Spec.Util.list_for_all2_length SpecRaw.raw_equiv (SpecRaw.Array?.v v1)) (SpecRaw.Array?.v v2);
      if ((len1.value <: U64.t) <> len2.value) {
        false
      } else {
        let i1 = Read.cbor_array_iterator_init () x1;
        let i2 = Read.cbor_array_iterator_init () x2;
        let mut pi1 = i1;
        let mut pi2 = i2;
        let mut pres = true;
        while (
          if (!pres) {
            let i1 = !pi1;
            not (Read.cbor_array_iterator_is_empty i1)
          } else {
            false
          }
        ) invariant b . exists* i1 i2 res l1 l2 pj1 pj2 . (
          pts_to pi1 i1 **
          pts_to pi2 i2 **
          pts_to pres res **
          Read.cbor_array_iterator_match pj1 i1 l1 **
          Read.cbor_array_iterator_match pj2 i2 l2 **
          Trade.trade
            (Read.cbor_array_iterator_match pj1 i1 l1)
            (cbor_match p1 x1 v1) **
          Trade.trade
            (Read.cbor_array_iterator_match pj2 i2 l2)
            (cbor_match p2 x2 v2) **
          pure (
            List.Tot.length l1 == List.Tot.length l2 /\
            List.Tot.for_all SpecRaw.valid_raw_data_item l1 /\
            List.Tot.for_all SpecRaw.valid_raw_data_item l2 /\
            (SpecRaw.raw_equiv v1 v2 == (res && CBOR.Spec.Util.list_for_all2 SpecRaw.raw_equiv l1 l2))
          ) ** pure (
              b == (Cons? l1 && res)
        )) {
          let y1 = Read.cbor_array_iterator_next () pi1;
          Trade.trans _ _ (cbor_match p1 x1 v1);
          let y2 = Read.cbor_array_iterator_next () pi2;
          Trade.trans _ _ (cbor_match p2 x2 v2);
          pres := cbor_nondet_equiv y1 y2;
          Trade.elim_hyp_l _ _ (cbor_match p1 x1 v1);
          Trade.elim_hyp_l _ _ (cbor_match p2 x2 v2);
        };
        Trade.elim _ (cbor_match p1 x1 v1);
        Trade.elim _ _;
        !pres
      }
    }
  } else {
    assert (pure (mt1 == Spec.cbor_major_type_map));
    if (match x1, x2 with Raw.CBOR_Case_Serialized_Map _, Raw.CBOR_Case_Serialized_Map _ -> true | _ -> false) {
      norewrite let Raw.CBOR_Case_Serialized_Map cs1 = x1;
      norewrite let Raw.CBOR_Case_Serialized_Map cs2 = x2;
      Trade.rewrite_with_trade
        (cbor_match p1 x1 v1)
        (cbor_match_serialized_map cs1 p1 v1);
      Trade.rewrite_with_trade
        (cbor_match p2 x2 v2)
        (cbor_match_serialized_map cs2 p2 v2);
      let res = CBOR.Pulse.Raw.Format.Nondet.Compare.cbor_match_compare_serialized_map cs1 cs2;
      Trade.elim _ (cbor_match p1 x1 v1);
      Trade.elim _ _;
      res
    } else {
      let i1 = Read.cbor_map_iterator_init () x1;
      let i2 = Read.cbor_map_iterator_init () x2;
      if (not (cbor_nondet_list_for_all_setoid_assoc_eq cbor_nondet_equiv i2 i1)) {
        Trade.elim _ (cbor_match p1 x1 v1);
        Trade.elim _ _;
        false
      } else {
        let res = cbor_nondet_list_for_all_setoid_assoc_eq cbor_nondet_equiv i1 i2;
        Trade.elim _ (cbor_match p1 x1 v1);
        Trade.elim _ _;
        res
      }
    }
  }
}

#pop-options

fn rec cbor_nondet_equiv
  (x1: _)
  (#p1: perm)
  (#v1: Ghost.erased SpecRaw.raw_data_item)
  (x2: _)
  (#p2: perm)
  (#v2: Ghost.erased SpecRaw.raw_data_item)
requires
  Raw.cbor_match p1 x1 v1 **
  Raw.cbor_match p2 x2 v2 **
  pure (SpecRaw.valid_raw_data_item v1 /\
    SpecRaw.valid_raw_data_item v2
  )
returns res: bool
ensures
  Raw.cbor_match p1 x1 v1 **
  Raw.cbor_match p2 x2 v2 **
  pure (res == SpecRaw.raw_equiv v1 v2)
{
  cbor_nondet_equiv_body cbor_nondet_equiv x1 x2
}

module S = Pulse.Lib.Slice.Util
module SM = Pulse.Lib.SeqMatch.Util

fn cbor_nondet_no_setoid_repeats
  (x: S.slice cbor_map_entry)
  (#px: perm)
  (#s: Ghost.erased (Seq.seq cbor_map_entry))
  (#ps: perm)
  (#l: Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)))
requires
  pts_to x #px s **
  SM.seq_list_match s l (Raw.cbor_match_map_entry ps) **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l)
  )
returns res: bool
ensures
  pts_to x #px s **
  SM.seq_list_match s l (Raw.cbor_match_map_entry ps) **
  pure (res == CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l))
{
  S.pts_to_len x;
  let mut pn1 = 0sz;
  let mut pres = true;
  Trade.refl (SM.seq_list_match s l (Raw.cbor_match_map_entry ps));
  while (
    if (!pres) {
      SM.seq_list_match_length (Raw.cbor_match_map_entry ps) _ _;
      SZ.lt !pn1 (S.len x)
    } else {
      false
    }
  ) invariant b . exists* n1 res s1 l1 . (
    pts_to x #px s **
    pts_to pn1 n1 **
    pts_to pres res **
    SM.seq_list_match s1 l1 (Raw.cbor_match_map_entry ps) **
    Trade.trade
      (SM.seq_list_match s1 l1 (Raw.cbor_match_map_entry ps))
      (SM.seq_list_match s l (Raw.cbor_match_map_entry ps)) **
    pure (
      b == (res && Cons? l1)
    ) ** pure (
      SZ.v n1 <= Seq.length s /\
      Seq.equal s1 (Seq.slice s (SZ.v n1) (Seq.length s)) /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l1) /\
      CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l) == (res && CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l1))
    )
  ) {
    SM.seq_list_match_length (Raw.cbor_match_map_entry ps) _ _;
    let n1 = !pn1;
    let x1 = S.op_Array_Access x n1;
    SM.seq_list_match_cons_elim_trade _ _ (Raw.cbor_match_map_entry ps);
    Trade.trans _ _ (SM.seq_list_match s l (Raw.cbor_match_map_entry ps));
    with gx1 y1 . assert Raw.cbor_match_map_entry ps gx1 y1;
    rewrite each gx1 as x1;
    let n2 : SZ.t = SZ.add n1 1sz;
    pn1 := n2;
    let mut pn2 = n2;
    with s1' l1' . assert (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps));
    Trade.refl (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps));
    while (
      if (!pres) {
        SM.seq_list_match_length (Raw.cbor_match_map_entry ps) _ _;
        SZ.lt !pn2 (S.len x)
      } else {
        false
      }
    ) invariant b . exists* n2 res s2 l2 . (
      pts_to x #px s **
      Raw.cbor_match_map_entry ps x1 y1 **
      pts_to pn2 n2 **
      pts_to pres res **
      SM.seq_list_match s2 l2 (Raw.cbor_match_map_entry ps) **
      Trade.trade
        (SM.seq_list_match s2 l2 (Raw.cbor_match_map_entry ps))
        (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps)) **
      pure (
        b == (res && Cons? l2)
      ) ** pure (
        SZ.v n2 <= Seq.length s /\
        Seq.equal s2 (Seq.slice s (SZ.v n2) (Seq.length s)) /\
        List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l2) /\
        CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l) == (res && (not (List.Tot.existsb (SpecRaw.raw_equiv (fst y1)) (List.Tot.map fst l2))) && CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l1'))
      )
    ) {
      SM.seq_list_match_length (Raw.cbor_match_map_entry ps) _ _;
      let n2 = !pn2;
      let x2 = S.op_Array_Access x n2;
      SM.seq_list_match_cons_elim_trade _ _ (Raw.cbor_match_map_entry ps);
      with gx2 y2 . assert (Raw.cbor_match_map_entry ps x1 y1 ** Raw.cbor_match_map_entry ps gx2 y2);
      rewrite each gx2 as x2;
      unfold (Raw.cbor_match_map_entry ps x1 y1);
      unfold (Raw.cbor_match_map_entry ps x2 y2);
      pres := not (cbor_nondet_equiv x1.cbor_map_entry_key x2.cbor_map_entry_key);
      fold (Raw.cbor_match_map_entry ps x1 y1);
      fold (Raw.cbor_match_map_entry ps x2 y2);
      Trade.elim_hyp_l (Raw.cbor_match_map_entry ps x2 y2) _ _;
      Trade.trans _ _ (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps));
      pn2 := SZ.add n2 1sz;
    };
    Trade.elim_hyp_l _ _ _;
    Trade.elim _ (SM.seq_list_match s1' l1' (Raw.cbor_match_map_entry ps));
    ()
  };
  Trade.elim _ _;
  !pres
}
