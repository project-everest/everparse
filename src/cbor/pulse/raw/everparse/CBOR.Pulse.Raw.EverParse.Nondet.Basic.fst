module CBOR.Pulse.Raw.EverParse.Nondet.Basic
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Gen
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Format
open LowParse.Spec.VCList
open LowParse.Pulse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
fn impl_basic_data_model (_: unit): impl_equiv_hd_t basic_data_model =
  (n1: Ghost.erased nat)
  (l1: S.slice byte)
  (n2: Ghost.erased nat)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist n1 raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist n2 raw_data_item))
{
  false
}

// FIXME: fold definition of impl_check_equiv_map_hd_t
fn rec impl_check_equiv_map_hd_basic
  (map_bound: option SZ.t)
  (n1: Ghost.erased nat)
  (l1: S.slice byte)
  (n2: Ghost.erased nat)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist n1 raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist n2 raw_data_item))
  requires
    (pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0
      )
    )
  returns res: option bool
  ensures
    (
pts_to_serialized (serialize_nlist n1 serialize_raw_data_item) l1 #p1 gl1 **
      pts_to_serialized (serialize_nlist n2 serialize_raw_data_item) l2 #p2 gl2 **
      pure (
        n1 > 0 /\ n2 > 0 /\
        res == (check_equiv_map basic_data_model (option_sz_v map_bound)) (List.Tot.hd gl1) (List.Tot.hd gl2)
      )
    )
{
  impl_check_equiv_map_hd_body (impl_basic_data_model ()) (impl_check_equiv_map_hd_basic) map_bound n1 l1 n2 l2
}

let impl_check_equiv_list_basic
  (map_bound: option SZ.t)
: impl_check_equiv_list_t (check_equiv_map basic_data_model (option_sz_v map_bound))
= impl_check_equiv_list_map impl_check_equiv_map_hd_basic map_bound

let impl_check_equiv_basic
  (map_bound: option SZ.t)
: impl_equiv_t #_ (check_equiv basic_data_model (option_sz_v map_bound))
= impl_check_equiv map_bound (impl_check_equiv_list_basic map_bound)

let impl_check_valid_basic
  (map_bound: option SZ.t)
  (strict_bound_check: bool)
: impl_fun_with_invariant_t #_
    (check_valid basic_data_model (option_sz_v map_bound) strict_bound_check)
    emp
= impl_check_valid map_bound (impl_check_equiv_basic map_bound) strict_bound_check
