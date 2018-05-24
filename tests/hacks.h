#include "kremlib.h"
#ifndef __Hacks_H
#define __Hacks_H

#include "Prims.h"
#include "FStar.h"
#include "kremlin/prims_int.h"
#include "kremlin/prims_string.h"

typedef struct
{
  uint8_t fst;
  uint8_t snd;
}
__uint8_t_pair;
//K___uint8_t_uint8_t;

typedef struct
{
  FStar_Bytes_bytes fst;
  FStar_Bytes_bytes snd;
}
__FStar_bytes_pair;
//K___FStar_Bytes_bytes_FStar_Bytes_bytes;

typedef uint8_t // enum { FStar_Pervasives_Native_None, FStar_Pervasives_Native_Some }
FStar_Pervasives_Native_option__Prims_string_tags;

typedef struct FStar_Pervasives_Native_option__Prims_string_s
{
  FStar_Pervasives_Native_option__Prims_string_tags tag;
  Prims_string v;
}
FStar_Pervasives_Native_option__Prims_string;

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1
#define K___uint8_t_uint8_t __uint8_t_pair
#define K___FStar_Bytes_bytes_FStar_Bytes_bytes __FStar_bytes_pair
#include "kremlin/fstar_bytes.h"
#undef K___FStar_Bytes_bytes_FStar_Bytes_bytes
#undef K___uint8_t_uint8_t
#undef FStar_Pervasives_Native_Some
#undef FStar_Pervasives_Native_None

#define __Hacks_H_DEFINED
#endif

