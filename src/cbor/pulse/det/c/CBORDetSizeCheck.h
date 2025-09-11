/* This handwritten file is intended to check that the size and
   alignment of types tagged as CAbstractType in
   CBOR.Pulse.Det.API.Type and manually defined in CBORDetAbstract.h
   for use by verified clients is consistent with those extracted in
   CBORDet.h
 */

#ifndef __CBORDetSizeCheck_H
#define __CBORDetSizeCheck_H

#include "CBORDetSize.h"
#include <assert.h>

static_assert(sizeof(cbor_det_t) == __sizeof_cbor_det_t, "cbor_det_t size failed");
static_assert(alignof(cbor_det_t) == __alignof_cbor_det_t, "cbor_det_t align failed");

static_assert(sizeof(cbor_det_map_entry_t) == __sizeof_cbor_det_map_entry_t, "cbor_det_map_entry_t size failed");
static_assert(alignof(cbor_det_map_entry_t) == __alignof_cbor_det_map_entry_t, "cbor_det_map_entry_t align failed");

static_assert(sizeof(cbor_det_array_iterator_t) == __sizeof_cbor_det_array_iterator_t, "cbor_det_array_iterator_t size failed");
static_assert(alignof(cbor_det_array_iterator_t) == __alignof_cbor_det_array_iterator_t, "cbor_det_array_iterator_t align failed");

static_assert(sizeof(cbor_det_map_iterator_t) == __sizeof_cbor_det_map_iterator_t, "cbor_det_map_iterator_t size failed");
static_assert(alignof(cbor_det_map_iterator_t) == __alignof_cbor_det_map_iterator_t, "cbor_det_map_iterator_t align failed");

#define __CBORDetSizeCheck_H_DEFINED
#endif
