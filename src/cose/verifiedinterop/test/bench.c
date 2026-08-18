#include "common.h"
#include "COSE_EverCrypt.h"
#include <time.h>

extern void
EverCrypt_Ed25519_sign(
  uint8_t *signature,
  uint8_t *private_key,
  uint32_t msg_len,
  uint8_t *msg
);

extern bool
EverCrypt_Ed25519_verify(
  uint8_t *public_key,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *signature
);


void report_bench_time(const char *func, unsigned nruns, struct timespec *start, struct timespec *end) {
    double d_ns =
        (end->tv_sec - start->tv_sec) * 1.0e9 +
        (((double) end->tv_nsec) - start->tv_nsec);
    printf("%s: %.3f us/iter\n", func, (d_ns / 1.0e3) / nruns);
}

#define xp1(x) x x
#define xp2(x) xp1(x x)
#define xp3(x) xp2(x x)
#define xp4(x) xp3(x x)
#define xp5(x) xp4(x x)
#define xp6(x) xp5(x x)
#define xp7(x) xp6(x x)

unsigned char payload_str[] = xp7("payload");
bstr payload = { .len = sizeof(payload_str) - 1, .elt = payload_str };

void bench_sign(uint8_t *privkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    bstr outbuf = { .len = 1024 };
    check(outbuf.elt = malloc(outbuf.len));

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        COSE_EverCrypt_sign1_simple(privkey, payload, outbuf);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    report_bench_time("sign1", nruns, &start, &finish);
}

void bench_verify(uint8_t *privkey, uint8_t *pubkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    bstr outbuf = { .len = 1024 };
    check(outbuf.elt = malloc(outbuf.len));
    bstr signed_msg = COSE_EverCrypt_sign1_simple(privkey, payload, outbuf);
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        check(COSE_EverCrypt_verify1_simple(pubkey, signed_msg).tag);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);
    free(outbuf.elt);

    report_bench_time("verify1", nruns, &start, &finish);
}

void bench_ed25519_sign(uint8_t *privkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    COSE_Format_sig_structure sig_struct = {
        .context = 1,
        .body_protected = COSE_EverCrypt_mk_phdrs(-8, NULL),
        ._x0 = {
            .tag = COSE_Format_Inr,
            .case_Inr = {
                .fst = { .len = 0, .elt = (uint8_t[]) {} },
                .snd = payload,
            },
        },
    };
    bstr msg = { .len = 1024 };
    check(msg.elt = malloc(msg.len));
    COSE_Format_serialize_sig_structure(sig_struct, msg);

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        uint8_t sig[64];
        EverCrypt_Ed25519_sign(sig, privkey, msg.len, msg.elt);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    free(msg.elt);
    report_bench_time("ed25519_sign", nruns, &start, &finish);
}

void bench_ed25519_verify(uint8_t *privkey, uint8_t *pubkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    COSE_Format_sig_structure sig_struct = {
        .context = 1,
        .body_protected = COSE_EverCrypt_mk_phdrs(-8, NULL),
        ._x0 = {
            .tag = COSE_Format_Inr,
            .case_Inr = {
                .fst = { .len = 0, .elt = (uint8_t[]) {} },
                .snd = payload,
            },
        },
    };
    bstr msg = { .len = 1024 };
    check(msg.elt = malloc(msg.len));
    COSE_Format_serialize_sig_structure(sig_struct, msg);
    uint8_t sig[64];
    EverCrypt_Ed25519_sign(sig, privkey, msg.len, msg.elt);

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        EverCrypt_Ed25519_verify(pubkey, msg.len, msg.elt, sig);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    free(msg.elt);
    report_bench_time("ed25519_verify", nruns, &start, &finish);
}

int main() {
    bstr privkey_data = read_from_file("message.privkey");
    uint8_t *privkey = parse_ed25519_private_key(privkey_data);

    bstr pubkey_data = read_from_file("message.pubkey");
    uint8_t *pubkey = parse_ed25519_public_key(pubkey_data);

    bench_sign(privkey);
    bench_verify(privkey, pubkey);
    bench_ed25519_sign(privkey);
    bench_ed25519_verify(privkey, pubkey);

    free(privkey_data.elt);
    free(pubkey_data.elt);
}
