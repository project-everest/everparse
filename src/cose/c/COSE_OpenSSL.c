#include "COSE_OpenSSL.h"

void COSE_OpenSSL_openssl_error_msg(const char *msg) {
    char buf[256] = "unknown error";
    unsigned long err = ERR_get_error();
    if (err) ERR_error_string_n(err, buf, sizeof(buf) - 1);
    fprintf(stderr, "openssl failed: %s (%s)\n", msg, buf);
}

#define check(cond) { if (!(cond)) { fprintf(stderr, "failed: %s\n", #cond); abort(); } }
#define openssl_check(cond) { if (!(cond)) { COSE_OpenSSL_openssl_error_msg(#cond); abort(); } }

const COSE_Format_evercddl_int_tags signature1 = 1;

static
bstr mk_sig_structure(COSE_Format_empty_or_serialized_map protected_headers,
        bstr aad, bstr payload) {
    COSE_Format_sig_structure c = {
        .context = signature1,
        .body_protected = protected_headers,
        ._x0 = {
            .tag = COSE_Format_Inr,
            .case_Inr = {
                .fst = aad,
                .snd = payload,
            },
        },
    };
    
    bstr out;
    out.len = 1024; // TODO
    check(out.elt = malloc(out.len));

    check(out.len = COSE_Format_serialize_sig_structure(c, out));

    return out;
}

COSE_Format_header_map COSE_OpenSSL_empty_sig_headers() {
    return (COSE_Format_header_map) {
        .intkey1 = { .tag = FStar_Pervasives_Native_None },
        .intkey2 = { .tag = FStar_Pervasives_Native_None },
        .intkey3 = { .tag = FStar_Pervasives_Native_None },
        .intkey4 = { .tag = FStar_Pervasives_Native_None },
        ._x0 = {
            .tag = COSE_Format_Inr,
            .case_Inr = {
                .tag = COSE_Format_Inr,
                .case_Inr = {
                    .fst = { .tag = FStar_Pervasives_Native_None },
                    .snd = { .tag = FStar_Pervasives_Native_None },
                },
            }
        },
        ._x1 = {
            .tag = COSE_Format_Inl,
            .case_Inl = {
                .elt = (K___COSE_Format_label_COSE_Format_values[]) {},
                .len = 0,
            },
        },
    };
}

bstr COSE_OpenSSL_sign_eddsa(EVP_PKEY *signing_key, const bstr tbs) {
    EVP_MD_CTX *sign_context = EVP_MD_CTX_new();
    openssl_check(sign_context);

    openssl_check(EVP_DigestSignInit(sign_context, NULL, NULL, NULL, signing_key) == 1);

    bstr sig;
    openssl_check(EVP_DigestSign(sign_context, NULL, &sig.len, tbs.elt, tbs.len) == 1);
    openssl_check(sig.elt = OPENSSL_malloc(sig.len));

    openssl_check(EVP_DigestSign(sign_context, sig.elt, &sig.len, tbs.elt, tbs.len) == 1);

    EVP_MD_CTX_free(sign_context);
    return sig;
}

bstr COSE_OpenSSL_sign1(EVP_PKEY *signing_key,
        COSE_Format_header_map protected_headers,
        COSE_Format_header_map unprotected_headers,
        bstr aad, bstr payload) {
    protected_headers.intkey1 = (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_COSE_Format_tstr) {
        .tag = FStar_Pervasives_Native_Some,
        .v = {
            .tag = COSE_Format_Inl,
            .case_Inl = { // I just hope this is -8 (COSE_ALGORITHM_EDDSA)
                .tag = COSE_Format_Mkevercddl_int1,
                .case_Mkevercddl_int1 = 7,
            }
        },
    };
    COSE_Format_empty_or_serialized_map protected_headers_ = {
        .tag = COSE_Format_Mkempty_or_serialized_map0,
        .case_Mkempty_or_serialized_map0 = protected_headers,
    };

    bstr sig_structure = mk_sig_structure(protected_headers_, aad, payload);
    bstr sig = COSE_OpenSSL_sign_eddsa(signing_key, sig_structure);
    free(sig_structure.elt);

    COSE_Format_cose_sign1 c = {
        .protected = protected_headers_,
        .unprotected = unprotected_headers,
        .payload = { .tag = COSE_Format_Inl, .case_Inl = payload },
        .signature = sig,
    };

    bstr out;
    out.len = 1024; // TODO
    check(out.elt = malloc(out.len));
    check(out.len = COSE_Format_serialize_cose_sign1_tagged(c, out));

    OPENSSL_free(sig.elt);

    return out;
}

bool COSE_OpenSSL_validate(EVP_PKEY *signing_key, bstr tbs, bstr sig) {
    EVP_MD_CTX *sign_context = EVP_MD_CTX_new();
    openssl_check(sign_context);

    openssl_check(EVP_DigestVerifyInit(sign_context, NULL, NULL, NULL, signing_key) == 1);

    int verify_result = EVP_DigestVerify(sign_context, sig.elt, sig.len, tbs.elt, tbs.len);
    openssl_check(verify_result == 0 || verify_result == 1);

    EVP_MD_CTX_free(sign_context);

    return verify_result == 1;
}

bstr COSE_OpenSSL_verify1(EVP_PKEY *signing_key, bstr aad, bstr msg) {
    FStar_Pervasives_Native_option___COSE_Format_cose_sign1_tagged___Pulse_Lib_Slice_slice_uint8_t_ parsed_msg =
        COSE_Format_validate_and_parse_cose_sign1_tagged(msg);
    check(parsed_msg.tag);

    check(parsed_msg.v.fst.payload.tag == COSE_Format_Inl); // detached payload not supported
    bstr payload = parsed_msg.v.fst.payload.case_Inl;

    bstr sig = parsed_msg.v.fst.signature;
    
    COSE_Format_empty_or_serialized_map protected_headers =
        parsed_msg.v.fst.protected;
    // TODO check algorithm
  
    bstr sig_structure = mk_sig_structure(protected_headers, aad, payload);

    check(COSE_OpenSSL_validate(signing_key, sig_structure, sig));

    free(sig_structure.elt);

    return payload;
}
