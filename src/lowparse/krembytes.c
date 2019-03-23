#include <kremlib.h>
#include <kremlin/internal/compat.h>

typedef uint8_t FStar_Bytes_byte;

#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      KRML_HOST_EPRINTF("malloc failed at %s:%d", __FILE__, __LINE__);           \
      KRML_HOST_EXIT(253);                                                     \
    }                                                                          \
  } while (0)

inline FStar_Bytes_bytes FStar_Bytes_copy(FStar_Bytes_bytes b1) {
  return b1;
}

inline krml_checked_int_t FStar_Bytes_length(FStar_Bytes_bytes b) {
  return b.length;
}

FStar_Bytes_bytes FStar_Bytes_empty_bytes = { .length = 0,
                                                     .data = NULL };

inline FStar_Bytes_byte
FStar_Bytes_get(FStar_Bytes_bytes b, uint32_t i) {
  return (FStar_Bytes_byte)b.data[i];
}

inline FStar_Bytes_bytes
FStar_Bytes_create(uint32_t length, FStar_Bytes_byte initial) {
  char *data = KRML_HOST_MALLOC(length);
  CHECK(data);
  memset(data, initial, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

inline FStar_Bytes_bytes
FStar_Bytes_append(FStar_Bytes_bytes b1, FStar_Bytes_bytes b2) {
  // Overflow check
  uint32_t length = Prims_op_Addition(b1.length, b2.length);
  char *data = KRML_HOST_MALLOC(length);
  CHECK(data);
  if (b1.length > 0)
    memcpy(data, b1.data, b1.length);
  if (b2.length > 0)
    memcpy(data + b1.length, b2.data, b2.length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

inline FStar_Bytes_bytes
FStar_Bytes_slice(FStar_Bytes_bytes b1, uint32_t s, uint32_t e) {
  if (s == e)
    return FStar_Bytes_empty_bytes;
  if (s > e) {
    KRML_HOST_EPRINTF("!! s > e in FStar_Bytes_slice\n");
    KRML_HOST_EXIT(254);
  }

  uint32_t length = e - s;
  char *data = KRML_HOST_MALLOC(length);
  CHECK(data);
  memcpy(data, b1.data + s, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

inline FStar_UInt32_t FStar_Bytes_len(FStar_Bytes_bytes b1) {
  return b1.length;
}

#undef CHECK
