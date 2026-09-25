

#ifndef COSE_EverCrypt_H
#define COSE_EverCrypt_H

#include "krmllib.h"

#include "COSE_Format.h"
#include "CBORDetType.h"

COSE_Format_evercddl_int COSE_EverCrypt_mk_int(int32_t i);

void
COSE_EverCrypt_create_sig(
  uint8_t *privkey,
  COSE_Format_empty_or_serialized_map phdr,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t payload,
  uint8_t *sigbuf
);

typedef FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
COSE_EverCrypt_dummy_map_type;

FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
COSE_EverCrypt_dummy_map_val(void);

COSE_Format_empty_or_serialized_map
COSE_EverCrypt_mk_phdrs(
  int32_t alg,
  FStar_Pervasives_Native_tuple2__COSE_Format_evercddl_label_CBOR_Pulse_API_Det_Type_cbor_det_t
  *rest
);

Pulse_Lib_Slice_slice__uint8_t
COSE_EverCrypt_sign1(
  uint8_t *privkey,
  COSE_Format_header_map uhdr,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t payload,
  Pulse_Lib_Slice_slice__uint8_t outbuf
);

Pulse_Lib_Slice_slice__uint8_t
COSE_EverCrypt_sign1_simple(
  uint8_t *privkey,
  Pulse_Lib_Slice_slice__uint8_t payload,
  Pulse_Lib_Slice_slice__uint8_t outbuf
);

bool
COSE_EverCrypt_verify_sig(
  uint8_t *pubkey,
  COSE_Format_empty_or_serialized_map phdr,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t payload,
  uint8_t *sigbuf
);

FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
COSE_EverCrypt_verify1(
  uint8_t *pubkey,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t msg
);

FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice__uint8_t
COSE_EverCrypt_verify1_simple(uint8_t *pubkey, Pulse_Lib_Slice_slice__uint8_t msg);


#define COSE_EverCrypt_H_DEFINED
#endif /* COSE_EverCrypt_H */
