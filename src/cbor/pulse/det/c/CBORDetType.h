/* Compatibility shim.  karamel split the CBOR types into a separate header;
   Custard emits a single translation unit, so all of them are declared in
   CBORDet.h.  Kept so that the karamel-based consumers which pass
   -add-include '"CBORDetType.h"' keep building unchanged. */
#ifndef __DET_TYPE_SHIM_H
#define __DET_TYPE_SHIM_H
#include "CBORDet.h"
#endif
