#include "common.c"
#include <openssl/pem.h>

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

bstr test_verify(bstr msg, bstr key_data) {
    bstr aad = { .elt = (uint8_t[]) {}, .len = 0 };
    BIO *bio = BIO_new_mem_buf(key_data.elt, key_data.len);
    EVP_PKEY *signing_key = PEM_read_bio_PUBKEY(bio, NULL, NULL, NULL);
    openssl_check(signing_key);
    BIO_free(bio);
    bstr out = verify1(signing_key, aad, msg);
    EVP_PKEY_free(signing_key);
    return out;
}

int main(int argc, const char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: verifytest message.pubkey message.cbor");
        exit(1);
    }

    bstr key_data = read_from_file(argv[1]);
    bstr msg = read_from_file(argv[2]);

    bstr payload = test_verify(msg, key_data);

    fprintf(stderr, "writing payload to stdout\n");
    check(fwrite(payload.elt, payload.len, 1, stdout) == 1);

    free(key_data.elt);
    free(msg.elt);
}