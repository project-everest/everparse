#include "EverParseEndianness.h"
#include "Boolean.h"

#include <assert.h>

#ifdef __cplusplus
static_assert(sizeof(BOOLEAN) == sizeof(uint8_t), "BOOLEAN must remain byte-valued");
#else
_Static_assert(sizeof(BOOLEAN) == sizeof(uint8_t), "BOOLEAN must remain byte-valued");
#endif

int main(void)
{
  for (unsigned int value = 0; value <= UINT8_MAX; ++value)
  {
    BOOLEAN byte = (BOOLEAN)value;
    bool logical = EverParse3d_CAbi_Boolean_to_bool(byte);
    assert(logical == (value != 0));
    assert(EverParse3d_CAbi_Boolean_of_bool(logical) == (value != 0 ? 1 : 0));
  }
  return 0;
}
