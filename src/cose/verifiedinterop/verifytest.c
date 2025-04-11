#include "common.h"
#include "CommonPulse.h"

bstr test_verify(bstr msg, bstr key_data) {
    uint8_t *signing_key = parse_ed25519_public_key(key_data);
    check(verify1_simple(signing_key, msg));
    return (bstr) { .len = 0, .elt = NULL }; // FIXME
}

int main(int argc, const char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: verifytest message.pubkey message.cbor\n");
        exit(1);
    }

    bstr key_data = read_from_file(argv[1]);
    bstr msg = read_from_file(argv[2]);

    bstr payload = test_verify(msg, key_data);

    // FIXME
    // fprintf(stderr, "writing payload to stdout\n");
    // check(fwrite(payload.elt, payload.len, 1, stdout) == 1);

    free(key_data.elt);
    free(msg.elt);
}