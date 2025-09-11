

#ifndef internal_CBORDet_H
#define internal_CBORDet_H

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

bool
CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a
);

void cbor_free_(cbor_freeable0 x);

cbor_freeable cbor_copy0(cbor_raw x);

typedef cbor_raw cbor_det_t;

typedef cbor_map_entry cbor_det_map_entry_t;

typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_t;

typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
cbor_det_map_iterator_t;

typedef cbor_freeable cbor_det_freeable_t;


#define internal_CBORDet_H_DEFINED
#endif /* internal_CBORDet_H */
