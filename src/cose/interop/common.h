#ifndef COMMON_H
#define COMMON_H

#include "COSE_Format.h"
#include "COSE_OpenSSL.h"
#include <openssl/evp.h>
#include <openssl/err.h>
#include <fcntl.h>

#define check(cond) { if (!(cond)) { fprintf(stderr, "failed: %s\n", #cond); abort(); } }
#define openssl_check(cond) { if (!(cond)) { COSE_OpenSSL_openssl_error_msg(#cond); abort(); } }

EVP_PKEY *parse_ed25519_private_key(bstr cose_key);
EVP_PKEY *parse_ed25519_public_key(bstr cose_key);

#define COSE_ALGORITHM_EDDSA (-8)

void write_to_file(const char *fn, const uint8_t *content, size_t content_len);

bstr read_from_file(const char *fn);

#endif
