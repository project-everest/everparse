#include "common.h"

bstr test_sign(bstr payload, bstr key_data) {
    bstr aad = { .elt = (uint8_t[]) {}, .len = 0 };
    EVP_PKEY *signing_key = parse_ed25519_private_key(key_data);
    bstr out = COSE_OpenSSL_sign1(signing_key, COSE_OpenSSL_empty_sig_headers(), COSE_OpenSSL_empty_sig_headers(), aad, payload);
    EVP_PKEY_free(signing_key);
    return out;
}

int main(int argc, const char **argv) {
    if (argc != 4) {
        fprintf(stderr, "usage: signtest message.data message.privkey message.cbor\n");
        exit(1);
    }

    bstr payload = read_from_file(argv[1]);
    bstr key_data = read_from_file(argv[2]);

    bstr result = test_sign(payload, key_data);

    const char *msg_fn = argv[3];
    printf("writing message to %s\n", msg_fn);
    write_to_file(msg_fn, result.elt, result.len);

    free(payload.elt);
    free(key_data.elt);
    free(result.elt);
}
