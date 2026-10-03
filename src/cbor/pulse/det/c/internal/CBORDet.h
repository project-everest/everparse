

#ifndef internal_CBORDet_H
#define internal_CBORDet_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "krmllib.h"

#include "CBORDetType.h"
#include "../CBORDet.h"

cbor_freeable cbor_copy0_with_depth(cbor_raw x);

void cbor_free_(cbor_freeable0 x);

int16_t CBOR_Pulse_Raw_Compare_cbor_compare_with_depth(cbor_raw x1, cbor_raw x2);

bool CBOR_Pulse_Raw_Format_Serialize_siz__d(cbor_raw x_, size_t *out);

size_t
CBOR_Pulse_Raw_Format_Serialize_ser__d(
  cbor_raw x_,
  CBOR_Pulse_Raw_Slice_byte_slice out,
  size_t offset
);

bool
CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a
);

#if defined(__cplusplus)
}
#endif

#define internal_CBORDet_H_DEFINED
#endif /* internal_CBORDet_H */
