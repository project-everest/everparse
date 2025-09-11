

#ifndef COSE_EverCrypt_H
#define COSE_EverCrypt_H

#include "krmllib.h"

#include "COSE_Format.h"
#include "CBORDetAbstract.h"

COSE_Format_evercddl_int COSE_EverCrypt_mk_int(int32_t i);

typedef void *COSE_EverCrypt_ser_to;

typedef void *COSE_EverCrypt_to_be_signed_spec;

void
COSE_EverCrypt_create_sig(
  uint8_t *privkey,
  COSE_Format_empty_or_serialized_map phdr,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t payload,
  uint8_t *sigbuf
);

K___COSE_Format_label_COSE_Format_values COSE_EverCrypt_dummy_map_val(void);

COSE_Format_empty_or_serialized_map
COSE_EverCrypt_mk_phdrs(int32_t alg, K___COSE_Format_label_COSE_Format_values *rest);

typedef void *COSE_EverCrypt_sign1_spec;

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

typedef void *COSE_EverCrypt_parses_from;

typedef void *COSE_EverCrypt_good_signature;

typedef struct FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t_s
{
  FStar_Pervasives_Native_option__size_t_tags tag;
  Pulse_Lib_Slice_slice__uint8_t v;
}
FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t;

FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t
COSE_EverCrypt_verify1(
  uint8_t *pubkey,
  Pulse_Lib_Slice_slice__uint8_t aad,
  Pulse_Lib_Slice_slice__uint8_t msg
);

FStar_Pervasives_Native_option__Pulse_Lib_Slice_slice_uint8_t
COSE_EverCrypt_verify1_simple(uint8_t *pubkey, Pulse_Lib_Slice_slice__uint8_t msg);


#define COSE_EverCrypt_H_DEFINED
#endif /* COSE_EverCrypt_H */
