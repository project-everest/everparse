/* This handwritten file is intended to compute the size and alignment
   of types tagged as CAbstractType in CBOR.Pulse.Det.API.Type and
   extracted in CBORDet.h, while hiding the actually extracted type
   definitions for use by verified clients, in part because they use
   monomorphized types such as Pulse slices, which would be extracted
   by Karamel twice.
 */

#ifndef __CBORDetSize_H
#define __CBORDetSize_H

#include <stdint.h>
#include <stddef.h>
#include <stdalign.h>

#define __CBORDetSize_MIN(A, B) (((A) < (B)) ? (A) : (B))
#define __CBORDetSize_MAX(A, B) (((A) > (B)) ? (A) : (B))

#define __sizeof_CBOR_Spec_Raw_Base_raw_uint64 (2 * sizeof(uint64_t))
#define __alignof_CBOR_Spec_Raw_Base_raw_uint64 (alignof(uint64_t))

#define __sizeof_Pulse_Lib_Slice_slice (2 * __CBORDetSize_MAX(sizeof(void *), sizeof(size_t)))
#define __alignof_Pulse_Lib_Slice_slice (__CBORDetSize_MAX(alignof(void *), alignof(size_t)))

#define __sizeof_cbor_string (2 * __sizeof_Pulse_Lib_Slice_slice)
#define __alignof_cbor_string (__alignof_Pulse_Lib_Slice_slice)

#define __sizeof_cbor_serialized (2 * __CBORDetSize_MAX(__sizeof_CBOR_Spec_Raw_Base_raw_uint64, __sizeof_Pulse_Lib_Slice_slice))
#define __alignof_cbor_serialized (__CBORDetSize_MAX(__alignof_CBOR_Spec_Raw_Base_raw_uint64, __alignof_Pulse_Lib_Slice_slice)))

#define __sizeof_cbor_tagged (2 * __CBORDetSize_MAX(__sizeof_CBOR_Spec_Raw_Base_raw_uint64, sizeof(void *)))
#define __alignof_cbor_tagged (__CBORDetSize_MAX(__alignof_CBOR_Spec_Raw_Base_raw_uint64))

#define __sizeof_cbor_array (2 * __CBORDetSize_MAX(sizeof(uint8_t), __sizeof_Pulse_Lib_Slice_slice))
#define __alignof_cbor_array (__CBORDetSize_MAX(alignof(uint8_t), __alignof_Pulse_Lib_Slice_slice)))

#define __sizeof_cbor_map (__sizeof_cbor_array)
#define __alignof_cbor_map (__alignof_cbor_array)

#define __sizeof_cbor_int (2 * sizeof(uint64_t))
#define __alignof_cbor_int (alignof(uint64_t))

#define __alignof_cbor_det_t (__CBORDetSize_MAX(alignof(uint64_t), __CBORDetSize_MAX(alignof(size_t), alignof(void *))))
#define __sizeof_cbor_det_t (__alignof_cbor_det_t + __CBORDetSize_MAX(__sizeof_cbor_int, __CBORDetSize_MAX(__sizeof_cbor_string, __CBORDetSize_MAX(__sizeof_cbor_tagged, __CBORDetSize_MAX(__sizeof_cbor_map, __sizeof_cbor_serialized)))))

#define __sizeof_cbor_det_map_entry_t (2 * __sizeof_cbor_det_t)
#define __alignof_cbor_det_map_entry_t __alignof_cbor_det_t

#define __sizeof_cbor_det_array_iterator_t (__CBORDetSize_MAX(sizeof(uint8_t), __alignof_Pulse_Lib_Slice_slice) + __sizeof_Pulse_Lib_Slice_slice + sizeof(uint64_t))
#define __alignof_cbor_det_array_iterator_t (__CBORDetSize_MAX(alignof(uint8_t), __alignof_Pulse_Lib_Slice_slice))

#define __sizeof_cbor_det_map_iterator_t __sizeof_cbor_det_array_iterator_t
#define __alignof_cbor_det_map_iterator_t __alignof_cbor_det_array_iterator_t

#define __CBORDetSize_H_DEFINED
#endif
