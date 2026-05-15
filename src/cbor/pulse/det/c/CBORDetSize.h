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

/* Pulse_Lib_Slice_slice = struct { T *elt; size_t len; } */
#define __sizeof_Pulse_Lib_Slice_slice (sizeof(void *) + sizeof(size_t))
#define __alignof_Pulse_Lib_Slice_slice (__CBORDetSize_MAX(alignof(void *), alignof(size_t)))

/* cbor_string = struct { uint8 type; uint8 size; Pulse_Lib_Slice_slice ptr; } */
#define __sizeof_cbor_string (__alignof_Pulse_Lib_Slice_slice + __sizeof_Pulse_Lib_Slice_slice)
#define __alignof_cbor_string (__alignof_Pulse_Lib_Slice_slice)

/* cbor_tagged = struct { raw_uint64 tag; cbor_raw *ptr; } */
#define __sizeof_cbor_tagged (__sizeof_CBOR_Spec_Raw_Base_raw_uint64 + sizeof(void *))
#define __alignof_cbor_tagged (__CBORDetSize_MAX(__alignof_CBOR_Spec_Raw_Base_raw_uint64, alignof(void *)))

/* cbor_tagged_serialized = struct { raw_uint64 tag; Pulse_Lib_Slice_slice ptr; } */
#define __sizeof_cbor_tagged_serialized (__sizeof_CBOR_Spec_Raw_Base_raw_uint64 + __sizeof_Pulse_Lib_Slice_slice)
#define __alignof_cbor_tagged_serialized (__CBORDetSize_MAX(__alignof_CBOR_Spec_Raw_Base_raw_uint64, __alignof_Pulse_Lib_Slice_slice))

/* base_mixed_list = struct { uint8 tag; union { void *Singleton;
       Pulse_Lib_Slice_slice Slice; struct { size_t count;
       Pulse_Lib_Slice_slice payload; } Serialized; }; }
   The Serialized case dominates: size_t + Pulse_Lib_Slice_slice */
#define __sizeof_base_mixed_list_union (sizeof(size_t) + __sizeof_Pulse_Lib_Slice_slice)
#define __alignof_base_mixed_list_union (__CBORDetSize_MAX(alignof(size_t), __alignof_Pulse_Lib_Slice_slice))
#define __alignof_base_mixed_list __alignof_base_mixed_list_union
/* tag (1) padded up to alignof(union), then the union itself */
#define __sizeof_base_mixed_list (__alignof_base_mixed_list + __sizeof_base_mixed_list_union)

/* mixed_list = struct { uint8 tag; union { base_mixed_list Base;
       struct { size_t cb, ca, ob; mixed_list *before; size_t oa;
       mixed_list *after; } Append; }; }
   The Append case is 4 size_t + 2 pointers. */
#define __sizeof_mixed_list_case_Append (4 * sizeof(size_t) + 2 * sizeof(void *))
#define __alignof_mixed_list_case_Append (__CBORDetSize_MAX(alignof(size_t), alignof(void *)))

#define __sizeof_mixed_list_union (__CBORDetSize_MAX(__sizeof_base_mixed_list, __sizeof_mixed_list_case_Append))
#define __alignof_mixed_list_union (__CBORDetSize_MAX(__alignof_base_mixed_list, __alignof_mixed_list_case_Append))

#define __alignof_mixed_list __alignof_mixed_list_union
#define __sizeof_mixed_list (__alignof_mixed_list + __sizeof_mixed_list_union)

/* cbor_array = struct { uint8 length_size; mixed_list ptr; }
   cbor_map  has the same shape (only the map_entry vs cbor_raw inner type
   changes, but those are pointer/slice based and yield the same size). */
#define __alignof_cbor_array __alignof_mixed_list
#define __sizeof_cbor_array (__alignof_cbor_array + __sizeof_mixed_list)

#define __sizeof_cbor_map (__sizeof_cbor_array)
#define __alignof_cbor_map (__alignof_cbor_array)

/* cbor_int = struct { uint8 type; uint8 size; uint64 value; } */
#define __sizeof_cbor_int (2 * sizeof(uint64_t))
#define __alignof_cbor_int (alignof(uint64_t))

/* cbor_raw = struct { uint8 tag; union { cbor_int Int; uint8 Simple;
       cbor_string String; cbor_tagged Tagged;
       cbor_tagged_serialized Tagged_Serialized; cbor_array Array;
       cbor_map Map; }; } */
#define __sizeof_cbor_raw_union \
  (__CBORDetSize_MAX(__sizeof_cbor_int, \
   __CBORDetSize_MAX(sizeof(uint8_t), \
   __CBORDetSize_MAX(__sizeof_cbor_string, \
   __CBORDetSize_MAX(__sizeof_cbor_tagged, \
   __CBORDetSize_MAX(__sizeof_cbor_tagged_serialized, \
   __CBORDetSize_MAX(__sizeof_cbor_array, __sizeof_cbor_map))))))) 

#define __alignof_cbor_raw_union \
  (__CBORDetSize_MAX(__alignof_cbor_int, \
   __CBORDetSize_MAX(alignof(uint8_t), \
   __CBORDetSize_MAX(__alignof_cbor_string, \
   __CBORDetSize_MAX(__alignof_cbor_tagged, \
   __CBORDetSize_MAX(__alignof_cbor_tagged_serialized, \
   __CBORDetSize_MAX(__alignof_cbor_array, __alignof_cbor_map)))))))

#define __alignof_cbor_det_t (__alignof_cbor_raw_union)
#define __sizeof_cbor_det_t (__alignof_cbor_det_t + __sizeof_cbor_raw_union)

#define __sizeof_cbor_det_map_entry_t (2 * __sizeof_cbor_det_t)
#define __alignof_cbor_det_map_entry_t (__alignof_cbor_det_t)

/* iterator = struct { base_mixed_list before; mixed_list after; } */
#define __sizeof_cbor_det_array_iterator_t (__sizeof_base_mixed_list + __sizeof_mixed_list)
#define __alignof_cbor_det_array_iterator_t (__CBORDetSize_MAX(__alignof_base_mixed_list, __alignof_mixed_list))

#define __sizeof_cbor_det_map_iterator_t (__sizeof_cbor_det_array_iterator_t)
#define __alignof_cbor_det_map_iterator_t (__alignof_cbor_det_array_iterator_t)

#define __CBORDetSize_H_DEFINED
#endif
