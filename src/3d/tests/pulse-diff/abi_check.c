/* Compile-only check that the public `EVERPARSE_ERROR_HANDLER` typedef is
   present, and correct, in *both* backends' generated headers.

   The Low* backend gets the typedef from KaRaMeL: `error_handler` is a
   monomorphic F* type abbreviation there (the input stream type is fixed when
   the Low* prelude is built, once per `--input_stream` binding), so
   `-no-inline-type-abbrev EverParse3d.Actions.Common.error_handler` preserves
   it and `-fmicrosoft` uppercases it.

   Under `--pulse` the abbreviation is parameterized by the input stream types
   (the Pulse prelude is built once and instantiated through a typeclass) and
   KaRaMeL has no parameterized typedefs, so it is inlined at every use site
   and the generated prototypes spell the function-pointer type out in full.
   The typedef is recovered by instantiating the abbreviation at each
   backend's stream types in EverParse3d.Actions.ErrorHandler.<Backend>; see
   lib/everparse/3d/krml/header.Makefile. This file checks that the typedef
   really is present and really does match: it names the typedef and then
   passes a value of that type to a generated validator, so any drift is a
   compile error.

   The validator signatures deliberately differ between the backends (that
   part of the ABI change is intentional), but `<M>Validate<T>` takes the
   error handler as its second argument in both, and the trailing
   length/position arguments accept `0` either way, so one translation unit
   can be compiled against both. It is never run. */

#include "Bitfields0.h"

extern EVERPARSE_ERROR_HANDLER EverParseAbiCheckHandler;

int EverParseAbiCheck(void);

int EverParseAbiCheck(void) {
  return Bitfields0ValidateT(NULL, EverParseAbiCheckHandler, NULL, 0, 0) != 0;
}
