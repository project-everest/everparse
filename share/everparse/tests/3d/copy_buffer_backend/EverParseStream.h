#ifndef __CBB_TEST_EVERPARSESTREAM
#define __CBB_TEST_EVERPARSESTREAM

#include <stddef.h>
#include <stdint.h>

/* This test never compiles or links a program: it only drives the frontend,
   F* and KaRaMeL, so the client stream needs no implementation. All that is
   required is the two type names the generated headers mention. The `extern`
   and `static` tests next door cover the primitives themselves. */

typedef struct cbb_stream_s *EVERPARSE_INPUT_STREAM_BASE;
typedef void *EVERPARSE_EXTRA_T;

#endif
