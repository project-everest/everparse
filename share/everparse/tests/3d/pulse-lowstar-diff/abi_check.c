/* Compile-only check that the public `EVERPARSE_ERROR_HANDLER` typedef is
   present, and correct, in *both* backends' generated headers.

   The Low*-compatible API uses the packed-result callback from
   EverParse3d.Lowstar.ErrorHandler.Buffer; the native Pulse API uses the
   byte-status callback from EverParse3d.Actions.ErrorHandler.Buffer.

   Custard runtime header generation exports the error-handler typedef
   specialized to each API and input stream; see src/3d/krml/header.Makefile.
   This file checks that the typedef is present and matches: it names it and
   passes a value of that type to a generated validator, so any drift is a
   compile error.

   The validator signatures deliberately differ between the backends (that
   part of the ABI change is intentional), but `<M>Validate<T>` takes the
   error handler as its second argument in both, and the trailing
   length/position arguments accept `0` either way, so one translation unit
   can be compiled against both. It is never run. */

#include "Bitfields0.h"
#include "BoolSwitchWrapper.h"

#ifdef HX_API_LOWSTAR
typedef BOOLEAN API_BOOL;
#else
typedef bool API_BOOL;
#endif

/* Scalar Bool differs by API; wrapper results remain BOOLEAN in both.
   A function-pointer assignment rejects otherwise implicit conversions. */
BOOLEAN (*EverParseAbiCheckBool)(API_BOOL, uint8_t *, uint32_t) = BoolSwitchCheckT;

extern EVERPARSE_ERROR_HANDLER EverParseAbiCheckHandler;

int EverParseAbiCheck(void);

int EverParseAbiCheck(void) {
  return Bitfields0ValidateT(NULL, EverParseAbiCheckHandler, NULL, 0, 0) != 0;
}
