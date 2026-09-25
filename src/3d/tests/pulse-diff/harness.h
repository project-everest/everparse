#ifndef HARNESS_H
#define HARNESS_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "EverParse.h"

/* Large enough to hold the longest solver-derived seed in seeds.inc; the
   witness generator emits fixed 256-byte inputs. */
#define HX_MAXLEN 256
#define HX_NARGS 8

/* Size of the per-case description that driver.c's generated call_* functions
   fill in. It has to cover every argument, out-parameter and copy buffer an
   entrypoint can report; the copy buffers dominate, at 2*CB_LEN hex characters
   each, so this must be kept comfortably above CB_SLOTS * 2 * CB_LEN. */
#define HX_DESCSZ 8192

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
  /* The integer literals of this entrypoint's .3d specification, used as a
     mutation dictionary. Magic numbers and enum tags are not reachable by
     chance, so without this several entrypoints never validated once and so
     produced no cross-backend evidence at all. */
  const uint64_t *dict;
  int ndict;
} hx_entry_t;

extern const hx_entry_t hx_entries[];
extern const int hx_nentries;

/* One test case: the scalar arguments plus the input buffer. */
typedef struct {
  uint64_t args[HX_NARGS];
  uint32_t len;
  uint8_t buf[HX_MAXLEN];
} hx_case_t;

/* An input a solver proved some entrypoint accepts. See gen_seeds.py. */
typedef struct {
  const char *entry;
  uint32_t len;
  const uint8_t *buf;
} hx_seed_t;

void hx_init(void);
void hx_reset(void);
void hx_error(const char *t, const char *f, const char *r);
const char *hx_errors(void);
const char *hx_u64(uint64_t v);
const char *hx_off(const uint8_t *p, const uint8_t *base, uint32_t len);
void hx_cb_init(hx_cb_t *cb, int slot);
const char *hx_cb_show(const hx_cb_t *cb);

/* Renders an out-parameter whose type is defined by the test itself (an
   output type, or an external typedef such as iter's OUT_T). We cannot
   interpret those, but both backends see the same declaration, so comparing
   the raw bytes is exactly the right check. */
const char *hx_bytes(const void *p, size_t n);

#endif
