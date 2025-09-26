#include "common.h"

bstr test_verify(bstr msg, bstr key_data) {
    bstr aad = { .elt = (uint8_t[]) {}, .len = 0 };
    EVP_PKEY *signing_key = parse_ed25519_public_key(key_data);
    bstr out = COSE_OpenSSL_verify1(signing_key, aad, msg);
    EVP_PKEY_free(signing_key);
    return out;
}

int main(int argc, const char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: verifytest message.pubkey message.cbor\n");
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
