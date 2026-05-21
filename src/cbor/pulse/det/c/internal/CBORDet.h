

#ifndef internal_CBORDet_H
#define internal_CBORDet_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "krmllib.h"

#include "../CBORDet.h"

size_t
CBOR_Pulse_Raw_EverParse_Serialize_ser_(
  cbor_raw x_,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t offset
);

bool CBOR_Pulse_Raw_EverParse_Serialize_siz_(cbor_raw x_, size_t *out);

int16_t CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel(cbor_raw x1, cbor_raw x2);

bool
CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a
);

typedef cbor_raw cbor_det_t;

typedef cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw cbor_det_map_entry_t;

typedef LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_array_iterator_t;

typedef LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_map_iterator_t;

typedef cbor_det_freeable_t_ cbor_det_freeable_t;

void panic____(void);

#if defined(__cplusplus)
}
#endif

#define internal_CBORDet_H_DEFINED
#endif /* internal_CBORDet_H */
