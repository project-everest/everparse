

#ifndef __internal_CBORDet_H
#define __internal_CBORDet_H

#include "krmllib.h"

#include "../CBORDet.h"

typedef struct Pulse_Lib_MutableSlice_slice__uint8_t_s
{
  uint8_t *elt;
  size_t len;
}
Pulse_Lib_MutableSlice_slice__uint8_t;

size_t
CBOR_Pulse_Raw_Format_Serialize_ser_(
  cbor_raw x_,
  Pulse_Lib_MutableSlice_slice__uint8_t out,
  size_t offset
);

bool CBOR_Pulse_Raw_Format_Serialize_siz_(cbor_raw x_, size_t *out);

int16_t CBOR_Pulse_Raw_Compare_impl_cbor_compare(cbor_raw x1, cbor_raw x2);

void cbor_free_(cbor_freeable0 x);

cbor_freeable cbor_copy0(cbor_raw x);

typedef struct Pulse_Lib_MutableSlice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  cbor_map_entry *elt;
  size_t len;
}
Pulse_Lib_MutableSlice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry;

bool cbor_raw_sort_aux(Pulse_Lib_MutableSlice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a);


#define __internal_CBORDet_H_DEFINED
#endif
