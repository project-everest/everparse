#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#if !defined(KRML_MAYBE_UNUSED_VAR)
# define KRML_MAYBE_UNUSED_VAR(x) ((void) (x))
#endif

/* For "bare" targets that do not have a C stdlib, the user might want to use
 * [-add-early-include '"mydefinitions.h"'] and override these. */
#ifndef KRML_HOST_PRINTF
#  define KRML_HOST_PRINTF printf
#endif

#ifndef KRML_HOST_EXIT
#  define KRML_HOST_EXIT exit
#endif

#ifndef KRML_HOST_MALLOC
#  define KRML_HOST_MALLOC malloc
#endif

/* In expression position, use the comma-operator and a malloc to return an
 * expression of the right size. KaRaMeL passes t as the parameter to the macro.
 */
#if !defined(KRML_EABORT)
# define KRML_EABORT(t, msg)                                                    \
  (KRML_HOST_PRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__, msg),  \
   KRML_HOST_EXIT(255), *((t *)KRML_HOST_MALLOC(sizeof(t))))
#endif
