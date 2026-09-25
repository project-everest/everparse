/* Under --pulse, as under the Low* backend, a copy buffer is an opaque
   EVERPARSE_COPY_BUFFER_T handle, and the client defines both its
   representation and the projections the generated code uses to reach the
   underlying input stream. The only difference from Low* is that a Pulse
   input stream also carries a read position, hence the extra
   EverParseStreamPos hook and the extra field below. */

void SpecializeABCEverParseError(char *StructName, char *FieldName, char *Reason) {
    printf("Validation failed in SpecializeABC, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

/* The copy buffer is an opaque handle, exactly as in the Low* backend: the
   client picks its representation and provides the projections below. */
typedef struct {
  uint8_t *cb_base;
  size_t cb_len;
  size_t cb_pos;
} copy_buffer_t;

#define CB(x) (*((copy_buffer_t *) (x)))

uint8_t * EverParseStreamOf(EVERPARSE_COPY_BUFFER_T x) {
    return CB(x).cb_base;
}

size_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T x) {
    return CB(x).cb_len;
}
/* No Low* counterpart: a Pulse input stream carries its read position, so the
   client also has to provide the cell holding it. */
size_t * EverParseStreamPos(EVERPARSE_COPY_BUFFER_T x) {
    return &CB(x).cb_pos;
}


uint64_t UlongToPtr(uint32_t ptr) {
    return (uint64_t) ptr;
}


BOOLEAN ProbeAndCopyLenAux(
    uint64_t bytes_to_read,
    uint64_t read_offset,
    uint64_t write_offset,
    uint8_t *src,
    uint64_t src_len,
    EVERPARSE_COPY_BUFFER_T dst
  )
  {
    printf("ProbeAndCopyLenAux: bytes_to_read=%lu, read_offset=%lu, write_offset=%lu, src_len=%lu, copy_buffer_len=%lu\n",
        bytes_to_read, read_offset, write_offset, src_len, ((uint64_t) CB(dst).cb_len));
    if (read_offset + bytes_to_read > src_len)
    {
      printf("ProbeAndCopy failed: src_len=%lu, read_offset=%lu, bytes_to_read=%lu\n",
          src_len, read_offset, bytes_to_read);
      return false;
    }
    if (write_offset + bytes_to_read > ((uint64_t) CB(dst).cb_len))
    {
      printf("ProbeAndCopy failed: ((uint64_t) CB(dst).cb_len)=%lu, write_offset=%lu, bytes_to_read=%lu\n", 
           ((uint64_t) CB(dst).cb_len), write_offset, bytes_to_read);
      return false;
    }
    memcpy(CB(dst).cb_base + write_offset, src + read_offset, bytes_to_read);
    printf("ProbeAndCopyLenAux succeeded\n");
    return true;
  }
  
BOOLEAN WriteU64(uint64_t src, uint64_t write_offset, EVERPARSE_COPY_BUFFER_T dst)
{
    if (write_offset + sizeof(uint64_t) > ((uint64_t) CB(dst).cb_len))
    {
        printf("WriteU64 failed\n");
        return false;
    }
    memcpy(CB(dst).cb_base + write_offset, &src, sizeof(uint64_t));
    return true;
}
