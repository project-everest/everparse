#ifndef __AA_ExternalTypedefs_H
#define __AA_ExternalTypedefs_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <stdint.h>

typedef struct _OPAIR {
  uint32_t fst;
  uint32_t snd;
} OPAIR;

typedef struct _OTRIPLE {
  uint32_t fst;
  uint32_t snd;
  uint32_t thd;
} OTRIPLE;

#if defined(__cplusplus)
}
#endif

#define __AA_ExternalTypedefs_H_DEFINED
#endif
