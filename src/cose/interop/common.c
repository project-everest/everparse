#include "common.h"

EVP_PKEY *parse_ed25519_private_key(bstr cose_key) {
    FStar_Pervasives_Native_option___COSE_Format_cose_key_okp___Pulse_Lib_Slice_slice_uint8_t_
        parsed_key = COSE_Format_validate_and_parse_cose_key_okp(cose_key);
    check(parsed_key.tag);
    check(parsed_key.v.fst.intkeyneg1.tag == COSE_Format_Inl);
    check(parsed_key.v.fst.intkeyneg1.case_Inl.tag == COSE_Format_Mkevercddl_int0);
    check(parsed_key.v.fst.intkeyneg1.case_Inl.case_Mkevercddl_int0 == 6);
    check(parsed_key.v.fst.intkeyneg4.tag);
    check(parsed_key.v.fst.intkeyneg4.v.len == 32);
    EVP_PKEY *pkey;
    openssl_check(pkey = EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519, NULL, parsed_key.v.fst.intkeyneg4.v.elt, parsed_key.v.fst.intkeyneg4.v.len));
    return pkey;
}

EVP_PKEY *parse_ed25519_public_key(bstr cose_key) {
    FStar_Pervasives_Native_option___COSE_Format_cose_key_okp___Pulse_Lib_Slice_slice_uint8_t_
        parsed_key = COSE_Format_validate_and_parse_cose_key_okp(cose_key);
    check(parsed_key.tag);
    check(parsed_key.v.fst.intkeyneg1.tag == COSE_Format_Inl);
    check(parsed_key.v.fst.intkeyneg1.case_Inl.tag == COSE_Format_Mkevercddl_int0);
    check(parsed_key.v.fst.intkeyneg1.case_Inl.case_Mkevercddl_int0 == 6);
    check(parsed_key.v.fst.intkeyneg2.tag);
    check(parsed_key.v.fst.intkeyneg2.v.len == 32);
    EVP_PKEY *pkey;
    openssl_check(pkey = EVP_PKEY_new_raw_public_key(EVP_PKEY_ED25519, NULL, parsed_key.v.fst.intkeyneg2.v.elt, parsed_key.v.fst.intkeyneg2.v.len));
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
