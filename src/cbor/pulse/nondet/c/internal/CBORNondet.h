

#ifndef internal_CBORNondet_H
#define internal_CBORNondet_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "krmllib.h"

#include "CBORNondetType.h"
#include <everparse/CBORNondet.h>

bool
CBOR_Pulse_Raw_EverParse_Format_validate_raw_data_item_nlist_bounded(
  size_t map_length_bound,
  size_t d,
  size_t n,
  CBOR_Pulse_Raw_Slice_byte_slice input,
  size_t *poffset
);

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t
FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_tags;

bool CBOR_Pulse_Raw_Format_Serialize_siz__d(cbor_raw x_, size_t *out);

size_t
CBOR_Pulse_Raw_Format_Serialize_ser__d(
  cbor_raw x_,
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t offset
);

typedef struct FStar_Pervasives_Native_option__bool_s
{
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  bool v;
}
FStar_Pervasives_Native_option__bool;

typedef struct FStar_Pervasives_Native_option__size_t_s
{
  FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  size_t v;
}
FStar_Pervasives_Native_option__size_t;

bool
CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_aux(
  size_t bound,
  CBOR_Pulse_Raw_Slice_byte_slice *pl,
  size_t n1
);

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(
  FStar_Pervasives_Native_option__size_t map_bound,
  CBOR_Pulse_Raw_Slice_byte_slice l1,
  CBOR_Pulse_Raw_Slice_byte_slice l2
);

bool CBOR_Pulse_Raw_Nondet_Compare_cbor_nondet_equiv_with_depth(cbor_raw x1, cbor_raw x2);

typedef struct CBOR_Spec_Raw_Hash_sip_s
{
  uint64_t v0;
  uint64_t v1;
  uint64_t v2;
  uint64_t v3;
  uint64_t nw;
}
CBOR_Spec_Raw_Hash_sip;

CBOR_Spec_Raw_Hash_sip
CBOR_Pulse_Raw_EverParse_DupCheck_hash_items(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  uint64_t k0,
  uint64_t k1,
  CBOR_Spec_Raw_Hash_sip st0,
  size_t o0,
  size_t c0,
  size_t *pout
);

typedef struct Pulse_Lib_Slice_slice__size_t_s
{
  size_t *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__size_t;

int16_t
CBOR_Pulse_Raw_EverParse_DupCheck_cmp_one(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  Pulse_Lib_Slice_slice__size_t sc,
  size_t x,
  size_t y
);

typedef struct Pulse_Lib_Slice_slice__uint64_t_s
{
  uint64_t *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__uint64_t;

bool
CBOR_Pulse_Raw_EverParse_DupCheck_check_items(
  CBOR_Pulse_Raw_Slice_byte_slice b,
  Pulse_Lib_Slice_slice__size_t sc,
  uint64_t k0,
  uint64_t k1,
  Pulse_Lib_Slice_slice__uint64_t hv,
  Pulse_Lib_Slice_slice__size_t idx,
  size_t o0,
  size_t c0,
  size_t *pout
);

#if defined(__cplusplus)
}
#endif

#define internal_CBORNondet_H_DEFINED
#endif /* internal_CBORNondet_H */
