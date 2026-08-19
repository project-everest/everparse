#ifndef COSE_OPENSSL_H
#define COSE_OPENSSL_H

#include "COSE_Format.h"
#include <openssl/evp.h>
#include <openssl/err.h>

void COSE_OpenSSL_openssl_error_msg(const char *msg);

typedef Pulse_Lib_Slice_slice__uint8_t bstr;

bstr COSE_OpenSSL_sign_eddsa(EVP_PKEY *signing_key, const bstr tbs);
bool COSE_OpenSSL_validate(EVP_PKEY *signing_key, bstr tbs, bstr sig);

COSE_Format_header_map COSE_OpenSSL_empty_sig_headers();

bstr COSE_OpenSSL_sign1(EVP_PKEY *signing_key,
        COSE_Format_header_map protected_headers,
        COSE_Format_header_map unprotected_headers,
        bstr aad, bstr payload);

bstr COSE_OpenSSL_verify1(EVP_PKEY *signing_key, bstr aad, bstr msg);

#endif // COSE_OPENSSL_H
