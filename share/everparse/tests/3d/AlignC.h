#include <stdint.h>

#ifndef C_ASSERT
#define C_ASSERT(e) typedef char __C_ASSERT__[(e)?1:-1]
#endif

typedef struct _A
{
   uint8_t  a1;
   uint16_t a2; //1 byte of padding
} A;

typedef struct _B
{
   uint8_t  b1;
   A        b2; //1 byte of padding, since T is aligned at 2
} B;


typedef struct _C
{
   uint8_t  c1;
   B        c2; //1 byte of padding, since T is aligned at 2
   uint8_t  c3; //1 byte of end padding; since B is 2-aligned
} C;

typedef struct _D
{
   uint8_t  d1;
   C        d2; //1 byte of padding
   uint32_t d3; //offset 12, ok ... no padding
   uint8_t  d4; //3 bytes of end padding
} D;

typedef union _E
{
  A e1;
  uint32_t e2;
} E;

typedef struct _F
{
  uint8_t f1;
  E f2;
} F;

typedef struct _USE_T
{
   uint64_t pt;
   uint16_t other;
} USE_T;
