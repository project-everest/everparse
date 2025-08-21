// client.c
#include <glib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <thrift/c_glib/protocol/thrift_compact_protocol.h>
#include <thrift/c_glib/transport/thrift_memory_buffer.h>
// If you prefer binary protocol, include thrift_binary_protocol.h instead.

#include "parquet_types.h"

static gboolean read_footer_region(const char* path, guchar** out_buf, gsize* out_len,
                                   GError** error) {
  gboolean ok = FALSE;
  FILE* fp = fopen(path, "rb");
  if (!fp) {
    g_set_error(error, g_quark_from_string("io"), 1, "open failed: %s", path);
    return FALSE;
  }

  if (fseek(fp, 0, SEEK_END) != 0) {
    g_set_error(error, g_quark_from_string("io"), 2, "fseek end failed");
    goto done;
  }
  long fsize = ftell(fp);
  if (fsize < 8) {
    g_set_error(error, g_quark_from_string("io"), 3, "file too small");
    goto done;
  }

  if (fseek(fp, -8, SEEK_END) != 0) {
    g_set_error(error, g_quark_from_string("io"), 4, "fseek footer trailer failed");
    goto done;
  }

  uint32_t footer_len_le = 0;
  char magic[4];
  if (fread(&footer_len_le, 1, 4, fp) != 4 || fread(magic, 1, 4, fp) != 4) {
    g_set_error(error, g_quark_from_string("io"), 5, "read trailer failed");
    goto done;
  }
  if (memcmp(magic, "PAR1", 4) != 0) {
    g_set_error(error, g_quark_from_string("format"), 6, "bad magic");
    goto done;
  }

  uint32_t footer_len =
      footer_len_le;  // file is little-endian; host little-endian is most common.
  if ((long)footer_len > fsize - 8) {
    g_set_error(error, g_quark_from_string("format"), 7, "footer_len out of range");
    goto done;
  }

  long footer_off = fsize - 8 - (long)footer_len;
  if (fseek(fp, footer_off, SEEK_SET) != 0) {
    g_set_error(error, g_quark_from_string("io"), 8, "seek footer failed");
    goto done;
  }

  guchar* buf = g_malloc(footer_len);
  if (fread(buf, 1, footer_len, fp) != footer_len) {
    g_set_error(error, g_quark_from_string("io"), 9, "read footer failed");
    g_free(buf);
    goto done;
  }

  *out_buf = buf;
  *out_len = footer_len;
  ok = TRUE;

done:
  fclose(fp);
  return ok;
}

int main(int argc, char** argv) {
  if (argc != 2) {
    fprintf(stderr, "Usage: %s <file.parquet>\n", argv[0]);
    return 2;
  }

  GError* error = NULL;
  guchar* footer = NULL;
  gsize footer_len = 0;

  if (!read_footer_region(argv[1], &footer, &footer_len, &error)) {
    fprintf(stderr, "Error: %s\n", error->message);
    g_clear_error(&error);
    return 1;
  }

  // Wrap the footer bytes in a Thrift memory buffer transport
  ThriftTransport* transport = THRIFT_TRANSPORT(g_object_new(
      THRIFT_TYPE_MEMORY_BUFFER, "buf", footer,  // pointer is *not* copied; keep it alive
      "len", footer_len,                         // readable length
      NULL));

  // Use Compact protocol (Parquet metadata is written with Thrift CompactProtocol)
  ThriftProtocol* protocol = THRIFT_PROTOCOL(
      g_object_new(THRIFT_TYPE_COMPACT_PROTOCOL, "transport", transport, NULL));

  // Create your generated object and read it
  FileMetaData* meta = g_object_new(TYPE_FILE_META_DATA, NULL);
  if (thrift_struct_read(THRIFT_STRUCT(meta), protocol, &error) < 0) {
    fprintf(stderr, "Thrift read error: %s\n", error ? error->message : "unknown");
    g_clear_error(&error);
    g_object_unref(meta);
    g_object_unref(protocol);
    g_object_unref(transport);
    g_free(footer);
    return 1;
  }

  // Use the fields
  printf("version = %d\n", meta->version);
  printf("num_rows = %lld\n", (long long)meta->num_rows);

  // Example: iterate schema (GPtrArray of SchemaElement*)
  if (meta->schema) {
    printf("schema size = %u\n", meta->schema->len);
    // SchemaElement *se = g_ptr_array_index(meta->schema, 0); // then inspect se->...
    // (from its generated header)
  }

  // Example: optional fields check
  if (meta->__isset_created_by && meta->created_by) {
    printf("created_by = %s\n", meta->created_by);
  }

  // Cleanup
  g_object_unref(meta);
  g_object_unref(protocol);
  g_object_unref(transport);
  g_free(footer);
  return 0;
}
