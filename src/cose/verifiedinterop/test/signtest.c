#include "common.h"
#include "COSE_EverCrypt.h"

bstr test_sign(bstr payload, bstr key_data) {
    uint8_t *signing_key = parse_ed25519_private_key(key_data);
    bstr outbuf = { .len = 1024 };
    check(outbuf.elt = malloc(outbuf.len));
    outbuf = COSE_EverCrypt_sign1_simple(signing_key, payload, outbuf);
    return outbuf;
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
