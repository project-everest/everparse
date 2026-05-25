

#include "internal/CBORNondetType.h"

bool uu___is_CBOR_Case_Array(cbor_raw projectee)
{
  if (projectee.tag == CBOR_Case_Array)
    return true;
  else
    return false;
}

