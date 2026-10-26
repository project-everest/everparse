#ifndef EVERPARSE_TEST_STATIC_HOOKS_H
#define EVERPARSE_TEST_STATIC_HOOKS_H

#include <stddef.h>
#include "EverParseEndianness.h"

#ifdef __cplusplus
extern "C" {
#endif

#ifdef LOWSTAR
static inline BOOLEAN EverParseHas(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base, uint64_t n)
{
  (void)extra; (void)base; (void)n;
  return (BOOLEAN)255;
}

static inline void EverParseSkip(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base, uint64_t n)
{
  (void)extra; (void)base; (void)n;
}

static inline uint64_t EverParseEmpty(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base)
{
  (void)extra; (void)base;
  return 0;
}

static inline uint8_t *EverParseRead(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base, uint64_t n, uint8_t *dst)
{
  (void)extra; (void)base; (void)n;
  return dst;
}

static inline uint8_t *EverParsePeep(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base, uint64_t n)
{
  (void)extra; (void)base; (void)n;
  return NULL;
}
#else
static inline BOOLEAN EverParseStreamHas(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base, size_t n)
{
  (void)extra; (void)base; (void)n;
  return (BOOLEAN)255;
}

static inline BOOLEAN EverParseStreamHasAt(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base, size_t off, size_t n)
{
  (void)extra; (void)base; (void)off; (void)n;
  return (BOOLEAN)255;
}

static inline uint64_t EverParseStreamGetPosition(EVERPARSE_INPUT_STREAM_BASE base)
{
  (void)base;
  return 0;
}

static inline void EverParseStreamReadBytes(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base, size_t n, uint8_t *dst)
{
  (void)extra; (void)base; (void)n; (void)dst;
}

static inline void EverParseStreamSkip(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base, size_t n)
{
  (void)extra; (void)base; (void)n;
}

static inline size_t EverParseStreamEmpty(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base)
{
  (void)extra; (void)base;
  return 0;
}

static inline BOOLEAN EverParseFieldPtrAfterImpl(EVERPARSE_EXTRA_T extra, uint64_t size, uint8_t **out, EVERPARSE_INPUT_STREAM_BASE base)
{
  (void)extra; (void)size; (void)out; (void)base;
  return (BOOLEAN)255;
}
#endif

#ifdef __cplusplus
}
#endif
#endif
