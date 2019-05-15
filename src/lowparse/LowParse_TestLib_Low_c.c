#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/types.h"
#include "LowParse_TestLib_Aux.h"

typedef struct K___uint8_t__int32_t_s
{
  uint8_t *fst;
  int32_t snd;
}
K___uint8_t__int32_t;

K___uint8_t__int32_t LowParse_TestLib_Low_load_file_buffer_aux(const char * x0)
{
    K___uint8_t__int32_t ret;
    LowParse_TestLib_Aux_load_file(x0, (uint8_t**)&ret.fst, &ret.snd);
    return ret;
}

K___uint8_t__int32_t LowParse_TestLib_Low_load_file_buffer(Prims_string x0)
{
    return LowParse_TestLib_Low_load_file_buffer_aux(x0);
}

K___uint8_t__int32_t LowParse_TestLib_Low_load_file_buffer_c(C_String_t x0)
{
    return LowParse_TestLib_Low_load_file_buffer_aux(x0);
}

bool LowParse_TestLib_Low_beqb (uint8_t * b1, uint8_t * b2, uint32_t len) {
  return memcmp(b1, b2, len) == 0;
}
