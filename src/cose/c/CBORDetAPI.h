

#ifndef CBORDetAPI_H
#define CBORDetAPI_H

#include "krmllib.h"

#include "CBORDetAbstract.h"

#define CBOR_MAJOR_TYPE_SIMPLE_VALUE (7U)

#define CBOR_MAJOR_TYPE_UINT64 (0U)

#define CBOR_MAJOR_TYPE_NEG_INT64 (1U)

#define CBOR_MAJOR_TYPE_BYTE_STRING (2U)

#define CBOR_MAJOR_TYPE_TEXT_STRING (3U)

#define CBOR_MAJOR_TYPE_ARRAY (4U)

#define CBOR_MAJOR_TYPE_MAP (5U)

#define CBOR_MAJOR_TYPE_TAGGED (6U)

#define MIN_SIMPLE_VALUE_LONG_ARGUMENT (32U)

#define MAX_SIMPLE_VALUE_ADDITIONAL_INFO (23U)

typedef struct cbor_det_t_s cbor_det_t;

typedef struct cbor_det_map_entry_t_s cbor_det_map_entry_t;

typedef struct cbor_det_array_iterator_t_s cbor_det_array_iterator_t;

typedef struct cbor_det_map_iterator_t_s cbor_det_map_iterator_t;

extern cbor_det_t dummy_cbor_det_t(void);

extern cbor_det_t cbor_det_reset_perm(cbor_det_t x0);

extern size_t cbor_det_validate(uint8_t *input, size_t input_len);

extern cbor_det_t cbor_det_parse(uint8_t *input, size_t len);

extern size_t cbor_det_size(cbor_det_t x, size_t bound);

extern size_t cbor_det_serialize(cbor_det_t x, uint8_t *output, size_t output_len);

extern size_t cbor_det_serialize_safe(cbor_det_t x, uint8_t *output, size_t output_len);

extern bool cbor_det_impl_utf8_correct_from_array(uint8_t *x0, size_t x1);

extern cbor_det_t cbor_det_mk_simple_value(uint8_t x0);

extern cbor_det_t cbor_det_mk_int64(uint8_t x0, uint64_t x1);

extern cbor_det_t cbor_det_mk_tagged(uint64_t x0, cbor_det_t *x1);

extern cbor_det_t cbor_det_mk_string_from_arrayptr(uint8_t x0, uint8_t *x1, uint64_t x2);

extern cbor_det_t cbor_det_mk_array_from_array(cbor_det_t *x0, uint64_t x1);

extern cbor_det_map_entry_t cbor_det_mk_map_entry(cbor_det_t x0, cbor_det_t x1);

extern cbor_det_t cbor_det_mk_map_from_array(cbor_det_map_entry_t *uu___, uint64_t x0);

extern bool
cbor_det_mk_map_from_array_safe(cbor_det_map_entry_t *x0, uint64_t x1, cbor_det_t *x2);

extern bool cbor_det_equal(cbor_det_t x0, cbor_det_t x1);

extern uint8_t cbor_det_major_type(cbor_det_t x0);

extern uint8_t cbor_det_read_simple_value(cbor_det_t x0);

extern uint64_t cbor_det_read_uint64(cbor_det_t x0);

extern uint64_t cbor_det_get_string_length(cbor_det_t x0);

extern uint64_t cbor_det_get_tagged_tag(cbor_det_t x0);

extern cbor_det_t cbor_det_get_tagged_payload(cbor_det_t x0);

extern uint8_t *cbor_det_get_string(cbor_det_t x0);

extern uint64_t cbor_det_get_array_length(cbor_det_t x0);

extern cbor_det_array_iterator_t cbor_det_array_iterator_start(cbor_det_t x0);

extern bool cbor_det_array_iterator_is_empty(cbor_det_array_iterator_t x0);

extern uint64_t cbor_det_array_iterator_length(cbor_det_array_iterator_t x0);

extern cbor_det_t cbor_det_array_iterator_next(cbor_det_array_iterator_t *x0);

extern cbor_det_array_iterator_t
cbor_det_array_iterator_truncate(cbor_det_array_iterator_t x0, uint64_t x1);

extern cbor_det_t cbor_det_get_array_item(cbor_det_t x0, uint64_t x1);

extern uint64_t cbor_det_get_map_length(cbor_det_t x0);

extern cbor_det_map_iterator_t cbor_det_map_iterator_start(cbor_det_t x0);

extern bool cbor_det_map_iterator_is_empty(cbor_det_map_iterator_t x0);

extern cbor_det_map_entry_t cbor_det_map_iterator_next(cbor_det_map_iterator_t *x0);

extern cbor_det_t cbor_det_map_entry_key(cbor_det_map_entry_t x0);

extern cbor_det_t cbor_det_map_entry_value(cbor_det_map_entry_t x0);

extern bool cbor_det_map_get(cbor_det_t x0, cbor_det_t x1, cbor_det_t *x2);

extern size_t cbor_det_serialize_tag_to_array(uint64_t x0, uint8_t *x1, size_t x2);

extern size_t
cbor_det_serialize_array_to_array(uint64_t x0, uint8_t *x1, size_t x2, size_t x3);

extern size_t
cbor_det_serialize_string_to_array(uint8_t x0, uint64_t x1, uint8_t *x2, size_t x3);

extern bool
cbor_det_serialize_map_insert_to_array(uint8_t *x0, size_t x1, size_t x2, size_t x3);

extern size_t cbor_det_serialize_map_to_array(uint64_t x0, uint8_t *x1, size_t x2, size_t x3);


#define CBORDetAPI_H_DEFINED
#endif /* CBORDetAPI_H */
