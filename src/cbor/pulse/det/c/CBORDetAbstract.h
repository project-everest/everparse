/*
  This handwritten file is meant for verified clients to hide the
  definition of types marked CAbstractType in CBOR.Pulse.API.Det.Type
 */

#ifndef __CBORDet_H
#define __CBORDet_H

#include <stdint.h>
#include "CBORDetSize.h"

typedef struct cbor_det_t_s {
  union {
    uint64_t dummy64[__sizeof_cbor_det_t / sizeof(uint64_t)];
    void * dummypvoid[__sizeof_cbor_det_t / sizeof(uint8_t *)];
    size_t dummysize[__sizeof_cbor_det_t / sizeof(size_t)];
  };
} cbor_det_t;

typedef struct cbor_det_map_entry_t_s {
  cbor_det_t dummy[__sizeof_cbor_det_map_entry_t / sizeof(cbor_det_t)];
} cbor_det_map_entry_t;

typedef struct cbor_det_array_iterator_t_s {
  union {
    uint8_t dummyu8[__sizeof_cbor_det_array_iterator_t / sizeof(uint8_t)];
    void * dummypvoid[__sizeof_cbor_det_array_iterator_t / sizeof(void *)];
    size_t * dummysize[__sizeof_cbor_det_array_iterator_t / sizeof(size_t)];
  };
} cbor_det_array_iterator_t;

typedef struct cbor_det_map_iterator_t_s {
  union {
    uint8_t dummyu8[__sizeof_cbor_det_map_iterator_t / sizeof(uint8_t)];
    void * dummypvoid[__sizeof_cbor_det_map_iterator_t / sizeof(void *)];
    size_t * dummysize[__sizeof_cbor_det_map_iterator_t / sizeof(size_t)];
  };
} cbor_det_map_iterator_t;

#include "CBORDetSizeCheck.h"

#define __CBORDet_H_DEFINED
#endif
