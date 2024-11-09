

#ifndef __internal_CBORDet_H
#define __internal_CBORDet_H

#include "krmllib.h"

#include "../CBORDet.h"

size_t
CBOR_Pulse_Raw_Format_Serialize_ser_(
  cbor_raw x_,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t offset
);

bool CBOR_Pulse_Raw_Format_Serialize_siz_(cbor_raw x_, size_t *out);

int16_t CBOR_Pulse_Raw_Compare_impl_cbor_compare(cbor_raw x1, cbor_raw x2);

bool cbor_raw_sort_aux(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a);


#define __internal_CBORDet_H_DEFINED
#endif
