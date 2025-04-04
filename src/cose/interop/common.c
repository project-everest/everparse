#include "common.h"

void openssl_error_msg(const char *msg) {
    char buf[256] = "unknown error";
    unsigned long err = ERR_get_error();
    if (err) ERR_error_string_n(err, buf, sizeof(buf) - 1);
    fprintf(stderr, "openssl failed: %s (%s)\n", msg, buf);
}

#define check(cond) { if (!(cond)) { fprintf(stderr, "failed: %s\n", #cond); abort(); } }
#define openssl_check(cond) { if (!(cond)) { openssl_error_msg(#cond); abort(); } }

typedef Pulse_Lib_Slice_slice__uint8_t bstr;

const COSE_Format_evercddl_int_tags signature1 = 1;

bstr mk_sig_structure(COSE_Format_evercddl_empty_or_serialized_map_pretty protected_headers,
        bstr aad, bstr payload) {
    bstr empty = { .elt = (uint8_t[]) {}, .len = 0 };

    COSE_Format_evercddl_Sig_structure_pretty c = {
        .x0 = signature1,
        .x1 = protected_headers,
        .x2 = {
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

    check(out.len = COSE_Format_serialize_Sig_structure(c, out));

    return out;
}

COSE_Format_evercddl_header_map_pretty empty_sig_headers() {
    return (COSE_Format_evercddl_header_map_pretty) {
        .x0 = { .tag = FStar_Pervasives_Native_None },
        .x1 = { .tag = FStar_Pervasives_Native_None },
        .x2 = { .tag = FStar_Pervasives_Native_None },
        .x3 = { .tag = FStar_Pervasives_Native_None },
        .x4 = {
            .tag = COSE_Format_Inr,
            .case_Inr = {
                .tag = COSE_Format_Inr,
                .case_Inr = {
                    .fst = { .tag = FStar_Pervasives_Native_None },
                    .snd = { .tag = FStar_Pervasives_Native_None },
                },
            }
        },
        .x5 = {
            .tag = COSE_Format_Inl,
            .case_Inl = {
                .elt = (K___COSE_Format_aux_env27_type_2_pretty_COSE_Format_aux_env27_type_4_pretty[]) {},
                .len = 0,
            },
        },
    };
}

bstr sign_eddsa(EVP_PKEY *signing_key, const bstr tbs) {
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

bstr sign1(EVP_PKEY *signing_key,
        COSE_Format_evercddl_header_map_pretty protected_headers,
        COSE_Format_evercddl_header_map_pretty unprotected_headers,
        bstr aad, bstr payload) {
    protected_headers.x0 = (FStar_Pervasives_Native_option__FStar_Pervasives_either_COSE_Format_evercddl_int_pretty_COSE_Format_evercddl_tstr_pretty) {
        .tag = FStar_Pervasives_Native_Some,
        .v = {
            .tag = COSE_Format_Inl,
            .case_Inl = { // I just hope this is -8 (COSE_ALGORITHM_EDDSA)
                .tag = COSE_Format_Mkevercddl_int_pretty1,
                .case_Mkevercddl_int_pretty1 = 7,
            }
        },
    };
    COSE_Format_evercddl_empty_or_serialized_map_pretty protected_headers_ = {
        .tag = COSE_Format_Mkevercddl_empty_or_serialized_map_pretty0,
        .case_Mkevercddl_empty_or_serialized_map_pretty0 = protected_headers,
    };

    bstr sig_structure = mk_sig_structure(protected_headers_, aad, payload);
    bstr sig = sign_eddsa(signing_key, sig_structure);
    free(sig_structure.elt);

    COSE_Format_evercddl_COSE_Sign1_pretty c = {
        .x0 = protected_headers_,
        .x1 = unprotected_headers,
        .x2 = { .tag = COSE_Format_Inl, .case_Inl = payload },
        .x3 = sig,
    };

    bstr out;
    out.len = 1024; // TODO
    check(out.elt = malloc(out.len));
    check(out.len = COSE_Format_serialize_COSE_Sign1_Tagged(c, out));

    OPENSSL_free(sig.elt);

    return out;
}

bool validate(EVP_PKEY *signing_key, bstr tbs, bstr sig) {
    EVP_MD_CTX *sign_context = EVP_MD_CTX_new();
    openssl_check(sign_context);

    openssl_check(EVP_DigestVerifyInit(sign_context, NULL, NULL, NULL, signing_key) == 1);

    int verify_result = EVP_DigestVerify(sign_context, sig.elt, sig.len, tbs.elt, tbs.len);
    openssl_check(verify_result == 0 || verify_result == 1);

    EVP_MD_CTX_free(sign_context);

    return verify_result == 1;
}

bstr verify1(EVP_PKEY *signing_key, bstr aad, bstr msg) {
    FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Sign1_Tagged_pretty___Pulse_Lib_Slice_slice_uint8_t_ parsed_msg =
        COSE_Format_validate_and_parse_COSE_Sign1_Tagged(msg);
    check(parsed_msg.tag);

    check(parsed_msg.v.fst.x2.tag == COSE_Format_Inl); // detached payload not supported
    bstr payload = parsed_msg.v.fst.x2.case_Inl;

    bstr sig = parsed_msg.v.fst.x3;
    
    COSE_Format_evercddl_empty_or_serialized_map_pretty protected_headers =
        parsed_msg.v.fst.x0;
    // TODO check algorithm
  
    bstr sig_structure = mk_sig_structure(protected_headers, aad, payload);

    check(validate(signing_key, sig_structure, sig));

    free(sig_structure.elt);

    return payload;
}

EVP_PKEY *parse_ed25519_private_key(bstr cose_key) {
    FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_OKP_pretty___Pulse_Lib_Slice_slice_uint8_t_
        parsed_key = COSE_Format_validate_and_parse_COSE_Key_OKP(cose_key);
    check(parsed_key.tag);
    check(parsed_key.v.fst.x1.tag == COSE_Format_Inl);
    check(parsed_key.v.fst.x1.case_Inl.tag == COSE_Format_Mkevercddl_int_pretty0);
    check(parsed_key.v.fst.x1.case_Inl.case_Mkevercddl_int_pretty0 == 6);
    check(parsed_key.v.fst.x3.tag);
    check(parsed_key.v.fst.x3.v.len == 32);
    EVP_PKEY *pkey;
    openssl_check(pkey = EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519, NULL, parsed_key.v.fst.x3.v.elt, parsed_key.v.fst.x3.v.len));
    return pkey;
}

EVP_PKEY *parse_ed25519_public_key(bstr cose_key) {
    FStar_Pervasives_Native_option___COSE_Format_evercddl_COSE_Key_OKP_pretty___Pulse_Lib_Slice_slice_uint8_t_
        parsed_key = COSE_Format_validate_and_parse_COSE_Key_OKP(cose_key);
    check(parsed_key.tag);
    check(parsed_key.v.fst.x1.tag == COSE_Format_Inl);
    check(parsed_key.v.fst.x1.case_Inl.tag == COSE_Format_Mkevercddl_int_pretty0);
    check(parsed_key.v.fst.x1.case_Inl.case_Mkevercddl_int_pretty0 == 6);
    check(parsed_key.v.fst.x2.tag);
    check(parsed_key.v.fst.x2.v.len == 32);
    EVP_PKEY *pkey;
    openssl_check(pkey = EVP_PKEY_new_raw_public_key(EVP_PKEY_ED25519, NULL, parsed_key.v.fst.x2.v.elt, parsed_key.v.fst.x2.v.len));
    return pkey;
}

void write_to_file(const char *fn, const uint8_t *content, size_t content_len) {
    FILE *f; check(f = fopen(fn, "w"));
    check(fwrite(content, content_len, 1, f) == 1);
    check(fclose(f) == 0);
}

bstr read_from_file(const char *fn) {
    FILE *f; check(f = fopen(fn, "r"));
    check(fseek(f, 0, SEEK_END) == 0);
    long size = ftell(f);
    check(fseek(f, 0, SEEK_SET) == 0);
    bstr out = { .len = size };
    check(out.elt = malloc(size));
    check(fread(out.elt, size, 1, f) == 1);
    check(fclose(f) == 0);
    return out;
}