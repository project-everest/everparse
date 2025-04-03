#include "COSE_Format.h"
#include <openssl/evp.h>
#include <openssl/err.h>
#include <fcntl.h>

void openssl_error_msg(const char *msg) {
    char buf[256] = "unknown error";
    unsigned long err = ERR_get_error();
    if (err) ERR_error_string_n(err, buf, sizeof(buf) - 1);
    fprintf(stderr, "openssl failed: %s (%s)\n", msg, buf);
}

#define check(cond) { if (!(cond)) { fprintf(stderr, "failed: %s\n", #cond); abort(); } }
#define openssl_check(cond) { if (!(cond)) { openssl_error_msg(#cond); abort(); } }

typedef Pulse_Lib_Slice_slice__uint8_t bstr;

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

const int COSE_ALGORITHM_EDDSA = -8;

bstr sign1(EVP_PKEY *signing_key, bstr aad, bstr payload) {
    COSE_Format_evercddl_empty_or_serialized_map_pretty protected_headers = {
        .tag = COSE_Format_Mkevercddl_empty_or_serialized_map_pretty0,
        .case_Mkevercddl_empty_or_serialized_map_pretty0 = {
            .x0 = {
                .tag = FStar_Pervasives_Native_Some,
                .v = { // I just hope this is -8 (COSE_ALGORITHM_EDDSA)
                    .tag = COSE_Format_Inl,
                    .case_Inl = {
                        .tag = COSE_Format_Mkevercddl_int_pretty1,
                        .case_Mkevercddl_int_pretty1 = 7,
                    }
                },
            },
            .x1 = { .tag = FStar_Pervasives_Native_None },
            .x2 = { .tag = FStar_Pervasives_Native_None },
            .x3 = { .tag = FStar_Pervasives_Native_None },
            .x4 = { .tag = FStar_Pervasives_Native_None },
            .x5 = { .tag = FStar_Pervasives_Native_None },
        },
    };

    bstr sig_structure = mk_sig_structure(protected_headers, aad, payload);
    bstr sig = sign_eddsa(signing_key, sig_structure);
    free(sig_structure.elt);

    // here would the content-type and key id go if we had them
    COSE_Format_evercddl_header_map_pretty unprotected_headers = {
        .x0 = { .tag = FStar_Pervasives_Native_None },
        .x1 = { .tag = FStar_Pervasives_Native_None },
        .x2 = { .tag = FStar_Pervasives_Native_None },
        .x3 = { .tag = FStar_Pervasives_Native_None },
        .x4 = { .tag = FStar_Pervasives_Native_None },
        .x5 = { .tag = FStar_Pervasives_Native_None },
    };

    COSE_Format_evercddl_COSE_Sign1_pretty c = {
        .x0 = protected_headers,
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

// ed25519 private key from the t_cose test suite
const uint8_t ed25519_private_key[] = {
  0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70,
  0x04, 0x22, 0x04, 0x20, 0x5f, 0xe3, 0x9b, 0x74, 0x55, 0xa0, 0x73, 0xd1,
  0x38, 0xc2, 0xe7, 0xd4, 0xe5, 0x06, 0x30, 0x52, 0x9f, 0xce, 0x7d, 0xdc,
  0xe8, 0x22, 0x80, 0x2a, 0x68, 0x5d, 0xa8, 0x99, 0x16, 0x5d, 0x44, 0x58
};

bstr test_sign() {
    char payload_str[] = "payload";
    bstr payload = { .elt = payload_str, .len = sizeof(payload_str) - 1 };
    bstr aad = { .elt = (uint8_t[]) {}, .len = 0 };
    const uint8_t *key_data = ed25519_private_key;
    EVP_PKEY *signing_key = d2i_PrivateKey(EVP_PKEY_ED25519, NULL, &key_data, sizeof(ed25519_private_key));
    openssl_check(signing_key);
    return sign1(signing_key, aad, payload);
}

void write_to_file(const char *fn, const uint8_t *content, size_t content_len) {
    FILE *f = fopen(fn, "w");
    fwrite(content, content_len, 1, f);
    fclose(f);
}

int main() {
    bstr result = test_sign();

    char msg_fn[] = "message.cbor";
    printf("writing message to %s\n", msg_fn);
    write_to_file(msg_fn, result.elt, result.len);

    char key_fn[] = "message.key";
    printf("writing ed25519 private key to %s (DER format)\n", key_fn);
    write_to_file(key_fn, ed25519_private_key,  sizeof(ed25519_private_key));
}