#include "common.h"

bstr test_verify(bstr msg, bstr key_data) {
    uint8_t *signing_key = parse_ed25519_public_key(key_data);
    FStar_Pervasives_Native_option__slice_uint8 verified_payload =
        COSE_EverCrypt_verify1_simple(signing_key, msg);
    check(verified_payload.tag == FSTAR_PERVASIVES_NATIVE_SOME__SLICE_UINT8);
    return verified_payload.val.Some;
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
