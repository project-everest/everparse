

#ifndef internal_CBORNondet_H
#define internal_CBORNondet_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "krmllib.h"

#include "CBORNondetType.h"
#include "../CBORNondet.h"

typedef struct FStar_Pervasives_Native_option__bool_s
{
  FStar_Pervasives_Native_option__bool_tags tag;
  bool v;
}
FStar_Pervasives_Native_option__bool;

typedef struct FStar_Pervasives_Native_option__size_t_s
{
  FStar_Pervasives_Native_option__bool_tags tag;
  size_t v;
}
FStar_Pervasives_Native_option__size_t;

bool
CBOR_Pulse_Raw_EverParse_Nondet_Gen_impl_check_map_depth_aux(
  size_t bound,
  byte_slice *pl,
  size_t n1
);

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_tagged(
  FStar_Pervasives_Native_option__size_t map_bound,
  cbor_raw x1,
  cbor_raw x2
);

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_array(
  FStar_Pervasives_Native_option__size_t map_bound,
  cbor_raw x1,
  cbor_raw x2,
  size_t len
);

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_array_slow(
  FStar_Pervasives_Native_option__size_t map_bound,
  cbor_raw x1,
  cbor_raw x2,
  size_t len
);

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Compare_compare_cbor_raw_basic_fuel_map(
  FStar_Pervasives_Native_option__size_t map_bound,
  cbor_raw x1,
  cbor_raw x2
);

size_t CBOR_Pulse_Raw_EverParse_Serialize_ser_(cbor_raw x_, byte_slice out, size_t offset);

bool CBOR_Pulse_Raw_EverParse_Serialize_siz_(cbor_raw x_, size_t *out);

FStar_Pervasives_Native_option__bool
CBOR_Pulse_Raw_EverParse_Nondet_Basic_impl_check_equiv_map_hd_basic(
  FStar_Pervasives_Native_option__size_t map_bound,
  size_t n1,
  byte_slice l1,
  size_t n2,
  byte_slice l2
);

#if defined(__cplusplus)
}
#endif

#define internal_CBORNondet_H_DEFINED
#endif /* internal_CBORNondet_H */
