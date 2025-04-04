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