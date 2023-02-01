#ifndef __AA_ExternalTypedefs_H
#define __AA_ExternalTypedefs_H

#if defined(__cplusplus)
extern "C" {
#endif

typedef struct _Opair {
  uint32_t fst;
  uint32_t snd;
} Opair;

typedef struct _Otriple {
  uint32_t fst;
  uint32_t snd;
  uint32_t thd;
} Otriple;

#if defined(__cplusplus)
}
#endif

#define __AA_ExternalTypedefs_H_DEFINED
#endif
