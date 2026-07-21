typedef enum _copy_buffer_type { 
    COPY_BUFFER_A = 0,
    COPY_BUFFER_B = 1
} copy_buffer_type;


typedef struct {
    uint8_t *buf;
    uint64_t len;
    copy_buffer_type type;
} copy_buffer_t;
  
void SpecializeABCEverParseError(char *StructName, char *FieldName, char *Reason) {
    printf("Validation failed in SpecializeABC, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

uint8_t * EverParseStreamOf(EVERPARSE_COPY_BUFFER_T x) {
    return ((copy_buffer_t *) x)->buf;
}

uint64_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T x) {
    return ((copy_buffer_t *) x)->len;
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
    copy_buffer_t *p = dst;
    printf("ProbeAndCopyLenAux: bytes_to_read=%lu, read_offset=%lu, write_offset=%lu, src_len=%lu, copy_buffer_len=%lu\n",
        bytes_to_read, read_offset, write_offset, src_len, p->len);
    if (read_offset + bytes_to_read > src_len)
    {
      printf("ProbeAndCopy failed: src_len=%lu, read_offset=%lu, bytes_to_read=%lu\n",
          src_len, read_offset, bytes_to_read);
      return false;
    }
    if (write_offset + bytes_to_read > p->len)
    {
      printf("ProbeAndCopy failed: p->len=%lu, write_offset=%lu, bytes_to_read=%lu\n", 
           p->len, write_offset, bytes_to_read);
      return false;
    }
    memcpy(p->buf + write_offset, src + read_offset, bytes_to_read);
    printf("ProbeAndCopyLenAux succeeded\n");
    return true;
  }
  
BOOLEAN WriteU64(uint64_t src, uint64_t write_offset, EVERPARSE_COPY_BUFFER_T dst)
{
    copy_buffer_t *p = dst;
    if (write_offset + sizeof(uint64_t) > p->len)
    {
        printf("WriteU64 failed\n");
        return false;
    }
    memcpy(p->buf + write_offset, &src, sizeof(uint64_t));
    return true;
}
