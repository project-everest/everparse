#ifndef PULSE_LOWSTAR_DIFF_OBSERVE_H
#define PULSE_LOWSTAR_DIFF_OBSERVE_H

#include <inttypes.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static FILE *df_trace;
static const char *df_case, *df_function;
static unsigned df_errors;
static struct {
  const char *name;
  uintptr_t start;
  size_t length;
} df_regions[64];
static unsigned df_region_count;

static void df_string(const char *s) {
  fputc('"', df_trace);
  if (s) {
    for (; *s; ++s) {
      unsigned char c = (unsigned char)*s;
      if (c == '"' || c == '\\') fprintf(df_trace, "\\%c", c);
      else if (c < 32 || c >= 127) fprintf(df_trace, "\\u%04x", c);
      else fputc(c, df_trace);
    }
  }
  fputc('"', df_trace);
}

static void df_key(const char *field) {
  fputs("@@{\"case\":", df_trace); df_string(df_case);
  fputs(",\"function\":", df_trace); df_string(df_function);
  fputs(",\"field\":", df_trace); df_string(field);
  fputs(",\"value\":", df_trace);
}

static void df_u64(const char *field, uint64_t value) {
  df_key(field); fprintf(df_trace, "%" PRIu64 "}\n", value);
}

static void df_text(const char *field, const char *value) {
  df_key(field);
  if (value) df_string(value); else fputs("null", df_trace);
  fputs("}\n", df_trace);
}

static void df_region(const char *name, const void *base, size_t length) {
  if (!base || df_region_count == 64) {
    fprintf(stderr, "invalid differential pointer region: %s\n", name);
    exit(2);
  }
  df_regions[df_region_count].name = name;
  df_regions[df_region_count].start = (uintptr_t)base;
  df_regions[df_region_count++].length = length;
}

static void df_pointer(const char *field, const void *pointer) {
  if (!pointer) { df_text(field, NULL); return; }
  uintptr_t address = (uintptr_t)pointer;
  for (unsigned i = 0; i < df_region_count; ++i) {
    uintptr_t start = df_regions[i].start;
    if (address >= start && address - start <= df_regions[i].length) {
      char value[256];
      snprintf(value, sizeof(value), "%s+%" PRIuPTR,
               df_regions[i].name, address - start);
      df_text(field, value);
      return;
    }
  }
  df_text(field, "<unregistered-pointer>");
}

static void df_begin(const char *name, const char *function) {
  if (!df_trace) {
    const char *path = getenv("DIFF_TRACE");
    if (!path || !(df_trace = fopen(path, "w"))) {
      perror("DIFF_TRACE"); exit(2);
    }
  }
  df_case = name; df_function = function; df_errors = 0; df_region_count = 0;
  fprintf(stderr, "@@CASE %s %s\n", name, function);
}

static void df_end(uint64_t result, int packed) {
  df_u64("return", result);
  if (packed) {
    df_u64("return.kind", result >> 60);
    df_u64("return.position", result & UINT64_C(0x0fffffffffffffff));
  }
  df_u64("error.count", df_errors);
  fflush(df_trace);
}

static void df_error_strings(const char *type, const char *field, const char *reason) {
  char key[80];
  snprintf(key, sizeof(key), "error.%u.type", df_errors); df_text(key, type);
  snprintf(key, sizeof(key), "error.%u.field", df_errors); df_text(key, field);
  snprintf(key, sizeof(key), "error.%u.reason", df_errors); df_text(key, reason);
}

static void df_error(const char *type, const char *field, const char *reason,
                     uint64_t code, uint8_t *context, EVERPARSE_INPUT_BUFFER input,
                     uint64_t position) {
  char key[80];
  df_error_strings(type, field, reason);
  snprintf(key, sizeof(key), "error.%u.kind", df_errors); df_u64(key, code);
  snprintf(key, sizeof(key), "error.%u.position", df_errors); df_u64(key, position);
  snprintf(key, sizeof(key), "error.%u.context", df_errors); df_pointer(key, context);
#ifdef DF_EXTERN
  snprintf(key, sizeof(key), "error.%u.input", df_errors); df_pointer(key, input.base);
  snprintf(key, sizeof(key), "error.%u.has_length", df_errors); df_u64(key, input.has_length);
  if (input.has_length) {
    snprintf(key, sizeof(key), "error.%u.length", df_errors); df_u64(key, input.length);
  }
#else
  snprintf(key, sizeof(key), "error.%u.input", df_errors); df_pointer(key, input);
#endif
  ++df_errors;
}

#endif
