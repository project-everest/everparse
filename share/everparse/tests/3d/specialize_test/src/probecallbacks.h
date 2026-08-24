/* Under --pulse a copy buffer is a pointer to an EVERPARSE_COPY_BUFFER_DESCR,
   the buffer backend's input buffer: a base pointer, a length and a position
   cell. The client allocates the descriptor and hands over its address, so a
   callback can also repoint the buffer, as in-place probing does in Low*. */

void SpecializeABCEverParseError(char *StructName, char *FieldName, char *Reason) {
    printf("Validation failed in SpecializeABC, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

uint8_t * EverParseStreamOf(EVERPARSE_COPY_BUFFER_T x) {
    return x->cb_base;
}

uint64_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T x) {
    return (uint64_t) x->cb_len;
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
        bytes_to_read, read_offset, write_offset, src_len, ((uint64_t) dst->cb_len));
    if (read_offset + bytes_to_read > src_len)
    {
      printf("ProbeAndCopy failed: src_len=%lu, read_offset=%lu, bytes_to_read=%lu\n",
          src_len, read_offset, bytes_to_read);
      return false;
    }
    if (write_offset + bytes_to_read > ((uint64_t) dst->cb_len))
    {
      printf("ProbeAndCopy failed: ((uint64_t) dst->cb_len)=%lu, write_offset=%lu, bytes_to_read=%lu\n", 
           ((uint64_t) dst->cb_len), write_offset, bytes_to_read);
      return false;
    }
    memcpy(dst->cb_base + write_offset, src + read_offset, bytes_to_read);
    printf("ProbeAndCopyLenAux succeeded\n");
    return true;
  }
  
BOOLEAN WriteU64(uint64_t src, uint64_t write_offset, EVERPARSE_COPY_BUFFER_T dst)
{
    if (write_offset + sizeof(uint64_t) > ((uint64_t) dst->cb_len))
    {
        printf("WriteU64 failed\n");
        return false;
    }
    memcpy(dst->cb_base + write_offset, &src, sizeof(uint64_t));
    return true;
}
