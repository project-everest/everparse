/* Runs a Custard-extracted ASN.1 DER validator over files.
   Input (stdin): one file path per line.
   Output (stdout), one line per file: "<ok> <offset> <size> <path>", where
   <ok> is 1 iff the validator succeeded and <offset> is the number of bytes
   it consumed.
   Compile with -DHEADER='"M.h"' -DVALIDATE=M_validate_f. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include HEADER

int main(void) {
  static char path[4096];
  while (fgets(path, sizeof path, stdin)) {
    size_t len = strlen(path);
    if (len > 0 && path[len - 1] == '\n') path[--len] = 0;
    if (len == 0) continue;
    FILE *f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "cannot open %s\n", path); return 2; }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *buf = malloc(sz > 0 ? (size_t)sz : 1);
    if (!buf || fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
      fprintf(stderr, "cannot read %s\n", path);
      return 2;
    }
    fclose(f);
    Pulse_Lib_Slice_slice__uint8 s = { buf, (size_t)sz };
    size_t off = 0;
    bool ok = VALIDATE(s, &off);
    printf("%d %zu %ld %s\n", ok ? 1 : 0, ok ? off : (size_t)0, sz, path);
    free(buf);
  }
  return 0;
}
