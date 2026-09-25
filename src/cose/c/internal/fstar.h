

#ifndef internal_fstar_H
#define internal_fstar_H

#include "krmllib.h"

#include "CBORDetType.h"

extern bool cbor_det_impl_utf8_correct_from_array(uint8_t *x0, size_t x1);

extern bool
cbor_det_serialize_map_insert_to_array(uint8_t *x0, size_t x1, size_t x2, size_t x3);

extern bool EverCrypt_Ed25519_verify(uint8_t *x0, uint32_t x1, uint8_t *x2, uint8_t *x3);


#define internal_fstar_H_DEFINED
#endif /* internal_fstar_H */
