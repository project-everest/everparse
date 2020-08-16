#ifndef C_ASSERT
#define C_ASSERT(e) typedef char __C_ASSERT__[(e)?1:-1]
#endif
typedef struct _S {
  uint8_t f1[10];
  uint8_t f2[20];
} S;
