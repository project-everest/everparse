#ifndef HARNESS_H
#define HARNESS_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "EverParse.h"

#define HX_MAXLEN 128
#define HX_NARGS 8

/* A copy buffer, as the client is expected to supply it. The Pulse backend
   additionally needs a position cell (EverParseStreamPos); the Low* backend
   has no such notion. Defining one struct covering both lets the very same
   driver source compile against either backend. */
typedef struct {
  uint8_t *buf;
  size_t len;
  size_t pos;
  int slot;
} hx_cb_t;

typedef BOOLEAN (*hx_call_t)(const uint64_t *args, uint8_t *buf, uint32_t len,
                             char *desc);

typedef struct {
  const char *name;
  hx_call_t call;
  int nargs;
} hx_entry_t;

extern const hx_entry_t hx_entries[];
extern const int hx_nentries;

/* One test case: the scalar arguments plus the input buffer. */
typedef struct {
  uint64_t args[HX_NARGS];
  uint32_t len;
  uint8_t buf[HX_MAXLEN];
} hx_case_t;

void hx_init(void);
void hx_reset(void);
void hx_error(const char *t, const char *f, const char *r);
const char *hx_errors(void);
const char *hx_u64(uint64_t v);
const char *hx_off(const uint8_t *p, const uint8_t *base, uint32_t len);
void hx_cb_init(hx_cb_t *cb, int slot);
const char *hx_cb_show(const hx_cb_t *cb);

#endif
