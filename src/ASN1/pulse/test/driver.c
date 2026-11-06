/* Runs a Custard-extracted ASN.1 DER validator over test vectors.
   Input (stdin), one vector per line: "A <hex> [comment]" (expect accept)
   or "R <hex> [comment]" (expect reject); <hex> has no spaces.  A vector is accepted iff the validator
   succeeds and consumes the whole input.
   Compile with -DHEADER='"M.h"' -DVALIDATE=M_validate_f. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include HEADER

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

int main(void) {
  static char line[1 << 16];
  static uint8_t buf[1 << 15];
  unsigned total = 0, failed = 0;
  while (fgets(line, sizeof line, stdin)) {
    char expect = line[0];
    if (expect != 'A' && expect != 'R') continue;
    size_t n = 0;
    int hi = -1;
    char *p = line + 1;
    while (*p == ' ') p++;
    for (; *p && *p != ' ' && *p != '\n'; p++) {
      int v = hexval((unsigned char)*p);
      if (v < 0) break;
      if (hi < 0) hi = v;
      else { buf[n++] = (uint8_t)(hi << 4 | v); hi = -1; }
    }
    Pulse_Lib_Slice_slice__uint8 s = { buf, n };
    size_t off = 0;
    bool ok = VALIDATE(s, &off) && off == n;
    total++;
    if (ok != (expect == 'A')) {
      failed++;
      printf("MISMATCH (expected %s):%s", expect == 'A' ? "accept" : "reject", line + 1);
    }
  }
  printf("%u vectors, %u mismatches\n", total, failed);
  return failed ? 1 : 0;
}
