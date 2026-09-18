/* Compatibility shim.  karamel split the CBOR types into a separate header;
   Custard emits a single translation unit, so all of them are declared in
   CBORNondet.h.  Kept so that the karamel-based consumers which pass
   -add-include '"CBORNondetType.h"' keep building unchanged. */
#ifndef __NONDET_TYPE_SHIM_H
#define __NONDET_TYPE_SHIM_H
#include "CBORNondet.h"
#endif
