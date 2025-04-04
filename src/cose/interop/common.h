#ifndef COMMON_H
#define COMMON_H

#include "COSE_Format.h"
#include <openssl/evp.h>
#include <openssl/err.h>
#include <fcntl.h>

void openssl_error_msg(const char *msg);

#define check(cond) { if (!(cond)) { fprintf(stderr, "failed: %s\n", #cond); abort(); } }
#define openssl_check(cond) { if (!(cond)) { openssl_error_msg(#cond); abort(); } }

typedef Pulse_Lib_Slice_slice__uint8_t bstr;

bstr mk_sig_structure(
    COSE_Format_evercddl_empty_or_serialized_map_pretty protected_headers,
    bstr aad, bstr payload);

#define COSE_ALGORITHM_EDDSA (-8)

void write_to_file(const char *fn, const uint8_t *content, size_t content_len);

bstr read_from_file(const char *fn);

#endif