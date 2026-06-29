/* Handwritten header providing the EVERPARSE_ERROR_HANDLER_MACRO that
   the generated C code is expected to call when validation fails
   under --use_error_handler_macro.

   The signature must match EverParse3d's `error_handler` type:

     typename_s : const char *
     fieldname  : const char *
     reason     : const char *
     error_code : uint64_t
     ctxt       : uint8_t *
     input      : uint8_t *  (input buffer pointer)
     pos        : uint64_t

   For this test we simply print a one-line diagnostic.  Real users
   would route this into their application's error reporting. */

#ifndef MY_ERROR_HANDLER_MACRO_H
#define MY_ERROR_HANDLER_MACRO_H

#include <stdio.h>
#include <stdint.h>

#define EVERPARSE_ERROR_HANDLER_MACRO(                                  \
    typename_s, fieldname, reason, error_code, ctxt, input, pos)        \
  do {                                                                  \
    (void) (ctxt);                                                      \
    (void) (input);                                                     \
    fprintf(stderr,                                                     \
            "[macro error handler] %s.%s: %s (code %llu, pos %llu)\n",  \
            (typename_s), (fieldname), (reason),                        \
            (unsigned long long) (error_code),                          \
            (unsigned long long) (pos));                                \
  } while (0)

#endif
