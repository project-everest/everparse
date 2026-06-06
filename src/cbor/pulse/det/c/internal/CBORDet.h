

#ifndef internal_CBORDet_H
#define internal_CBORDet_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "krmllib.h"

#include "CBORDetType.h"
#include "../CBORDet.h"

int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_tagged(cbor_raw x1, cbor_raw x2);

int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_array(
  cbor_raw x1,
  cbor_raw x2,
  size_t len
);

int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_map(
  cbor_raw x1,
  cbor_raw x2,
  size_t len
);

size_t CBOR_Pulse_Raw_EverParse_Serialize_ser_(cbor_raw x_, byte_slice out, size_t offset);

bool CBOR_Pulse_Raw_EverParse_Serialize_siz_(cbor_raw x_, size_t *out);

bool
CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a
);

typedef cbor_det_freeable_t_ cbor_det_freeable_t;

void panic____(void);

#if defined(__cplusplus)
}
#endif

#define internal_CBORDet_H_DEFINED
#endif /* internal_CBORDet_H */
