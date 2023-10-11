#include <stdlib.h>
#include <malloc.h>
#include <stdint.h>
#include "CBOR.h"

struct cbor;

struct cbor_string {
  uint64_t cbor_string_byte_length;
  uint8_t *cbor_string_payload;
};

struct cbor_tagged {
  uint64_t cbor_tagged_tag;
  struct cbor *cbor_tagged_payload;
};

struct cbor_array {
  uint64_t cbor_array_count;
  struct cbor *cbor_array_payload;
};

struct cbor_pair;

struct cbor_map {
  uint64_t cbor_map_entry_count;
  struct cbor_pair *cbor_map_payload;
};

struct cbor_serialized {
  size_t cbor_serialized_byte_size;
  uint8_t *cbor_serialized_payload;
};

union cbor_case {
  uint64_t cbor_case_uint64;
  uint64_t cbor_case_neg_int64;
  struct cbor_string cbor_case_byte_string;
  struct cbor_string cbor_case_text_string;
  struct cbor_tagged cbor_case_tagged;
  struct cbor_array cbor_case_array;
  struct cbor_map cbor_case_map;
  uint8_t cbor_case_simple_value;
  struct cbor_serialized cbor_case_serialized;
};

#define CBOR_TYPE_SERIALIZED ((uint8_t)255)

struct cbor {
  uint8_t cbor_type;
  union cbor_case cbor_payload;
};

struct cbor_pair {
  struct cbor cbor_pair_key;
  struct cbor cbor_pair_value;
};

uint8_t cbor_get_type (struct cbor *elt) {
  uint8_t ty = elt->cbor_type;
  if (ty == CBOR_TYPE_SERIALIZED)
    return CBOR_SteelST_Raw_read_major_type(elt->cbor_payload.cbor_case_serialized.cbor_serialized_payload);
  else
    return ty;
}

uint64_t cbor_read_int64 (struct cbor *elt) {
  switch (elt->cbor_type) {
  case CBOR_TYPE_SERIALIZED:
    return CBOR_SteelST_Raw_read_int64(elt->cbor_payload.cbor_case_serialized.cbor_serialized_payload);
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_UINT64:
    return elt->cbor_payload.cbor_case_uint64;
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_NEG_INT64:
    return elt->cbor_payload.cbor_case_neg_int64;
  default:
    return 0; // this shouldn't happen
  }
}

void preload_cbor_with_size (uint8_t *src, size_t src_size, struct cbor *dst) {
  dst->cbor_type = CBOR_TYPE_SERIALIZED;
  dst->cbor_payload.cbor_case_serialized.cbor_serialized_byte_size = src_size;
  dst->cbor_payload.cbor_case_serialized.cbor_serialized_payload = src;
}

bool validate_cbor (uint8_t *input, size_t len, struct cbor* elt) {
  uint32_t error = 0;
  CBOR_SteelST_Raw_validate_raw_data_item(input, len, &error);
  bool res = error != 0;
  if (res)
    preload_cbor_with_size (input, len, elt);
  return res;
}

void preload_cbor (uint8_t **src, struct cbor *dst) {
  size_t src_size = CBOR_SteelST_Raw_jump_raw_data_item(*src);
  preload_cbor_with_size(*src, src_size, dst);
  *src += src_size;
}

void load_cbor (struct cbor* elt) {
  if (elt->cbor_type != CBOR_TYPE_SERIALIZED)
    return;
  uint8_t *payload = elt->cbor_payload.cbor_case_serialized.cbor_serialized_payload;
  uint8_t typ = CBOR_SteelST_Raw_read_major_type(payload);
  switch (typ) {
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_UINT64:
    {
      elt->cbor_type = typ;
      elt->cbor_payload.cbor_case_uint64 = CBOR_SteelST_Raw_read_int64(payload);
      return;
    }
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_NEG_INT64:
    {
      elt->cbor_type = typ;
      elt->cbor_payload.cbor_case_neg_int64 = CBOR_SteelST_Raw_read_int64(payload);
      return;
    }
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_BYTE_STRING:
    {
      elt->cbor_type = typ;
      elt->cbor_payload.cbor_case_byte_string.cbor_string_byte_length = CBOR_SteelST_Raw_read_argument_as_uint64(payload);
      elt->cbor_payload.cbor_case_byte_string.cbor_string_payload = CBOR_SteelST_Raw_focus_string(payload);
      return;
    }
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_TEXT_STRING:
    {
      elt->cbor_type = typ;
      elt->cbor_payload.cbor_case_text_string.cbor_string_byte_length = CBOR_SteelST_Raw_read_argument_as_uint64(payload);
      elt->cbor_payload.cbor_case_text_string.cbor_string_payload = CBOR_SteelST_Raw_focus_string(payload);
      return;
    }
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_ARRAY:
    {
      uint64_t count = CBOR_SteelST_Raw_read_argument_as_uint64(payload);
      struct cbor *array = calloc(count, sizeof(struct cbor));
      if (array == NULL)
        return;
      elt->cbor_type = typ;
      elt->cbor_payload.cbor_case_array.cbor_array_count = count;
      elt->cbor_payload.cbor_case_array.cbor_array_payload = array;
      payload += CBOR_SteelST_Raw_jump_header(payload);
      for (uint64_t i = 0; i < count; ++i) {
        preload_cbor(&payload, array);
        ++array;
      }
      return;
    }
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_MAP:
    {
      uint64_t count = CBOR_SteelST_Raw_read_argument_as_uint64(payload);
      struct cbor_pair *map = calloc(count, sizeof(struct cbor_pair));
      if (map == NULL)
        return;
      elt->cbor_type = typ;
      elt->cbor_payload.cbor_case_map.cbor_map_entry_count = count;
      elt->cbor_payload.cbor_case_map.cbor_map_payload = map;
      payload += CBOR_SteelST_Raw_jump_header(payload);
      for (uint64_t i = 0; i < count; ++i) {
        preload_cbor(&payload, &(map->cbor_pair_key));
        preload_cbor(&payload, &(map->cbor_pair_value));
        ++map;
      }
      return;
    }
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_TAGGED:
    {
      struct cbor *elt = malloc(sizeof(struct cbor));
      if (elt == NULL)
        return;
      uint64_t tag = CBOR_SteelST_Raw_read_argument_as_uint64(payload);
      elt->cbor_type = typ;
      elt->cbor_payload.cbor_case_tagged.cbor_tagged_tag = tag;
      elt->cbor_payload.cbor_case_tagged.cbor_tagged_payload = elt;
      payload += CBOR_SteelST_Raw_jump_header(payload);
      preload_cbor(&payload, elt);
      return;
    }
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_SIMPLE_VALUE:
    {
      elt->cbor_type = typ;
      elt->cbor_payload.cbor_case_simple_value = CBOR_SteelST_Raw_read_simple_value(payload);
      return;
    }
  }
}

/* Warning: this function may exhaust the stack */
void full_load_cbor (struct cbor* elt) {
  load_cbor(elt);
  switch (elt->cbor_type) {
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_ARRAY:
    {
      uint64_t count = elt->cbor_payload.cbor_case_array.cbor_array_count;
      struct cbor* child = elt->cbor_payload.cbor_case_array.cbor_array_payload;
      for (uint64_t i = 0; i < count; ++i) {
        full_load_cbor(child);
        ++child;
      }
      return;
    }
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_MAP:
    {
      uint64_t count = elt->cbor_payload.cbor_case_map.cbor_map_entry_count;
      struct cbor_pair* entry = elt->cbor_payload.cbor_case_map.cbor_map_payload;
      for (uint64_t i = 0; i < count; ++i) {
        full_load_cbor(&(entry->cbor_pair_key));
        full_load_cbor(&(entry->cbor_pair_value));
        ++entry;
      }
      return;
    }
  case CBOR_SPEC_CONSTANTS_MAJOR_TYPE_TAGGED:
    {
      full_load_cbor(elt->cbor_payload.cbor_case_tagged.cbor_tagged_payload);
      return;
    }
  }
}
