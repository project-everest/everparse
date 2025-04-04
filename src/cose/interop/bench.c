#include "common.h"
#include <time.h>
// #include <sys/time.h>

EVP_PKEY *create_key_pair() {
    EVP_PKEY *pkey;
    EVP_PKEY_CTX *pctx; openssl_check(pctx = EVP_PKEY_CTX_new_id(EVP_PKEY_ED25519, NULL));
    openssl_check(EVP_PKEY_keygen_init(pctx) == 1);
    openssl_check(EVP_PKEY_keygen(pctx, &pkey) == 1);
    EVP_PKEY_CTX_free(pctx);
    return pkey;
}

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

char payload_str[] = xp7("payload");
bstr payload = { .len = sizeof(payload_str) - 1, .elt = payload_str };

bstr aad = { .len = 0, .elt = (uint8_t[]) {} };

void bench_sign(EVP_PKEY *pkey) {
    unsigned nruns = 10000;
    struct timespec start, finish;

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        bstr signed_msg = sign1(pkey, empty_sig_headers(), empty_sig_headers(), aad, payload);
        free(signed_msg.elt);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    report_bench_time("sign1", nruns, &start, &finish);
}

void bench_verify(EVP_PKEY *pkey) {
    unsigned nruns = 10000;
    struct timespec start, finish;

    bstr signed_msg = sign1(pkey, empty_sig_headers(), empty_sig_headers(), aad, payload);
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        verify1(pkey, aad, signed_msg);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);
    free(signed_msg.elt);

    report_bench_time("verify1", nruns, &start, &finish);
}

void bench_parse(EVP_PKEY *pkey) {
    unsigned nruns = 10000;
    struct timespec start, finish;

    bstr signed_msg = sign1(pkey, empty_sig_headers(), empty_sig_headers(), aad, payload);
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        COSE_Format_validate_and_parse_COSE_Sign1_Tagged(signed_msg);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);
    free(signed_msg.elt);

    report_bench_time("parse", nruns, &start, &finish);
}

void bench_serialize(EVP_PKEY *pkey) {
    unsigned nruns = 10000;
    struct timespec start, finish;

    bstr out = { .len = 1024 };
    out.elt = malloc(out.len);

    bstr signed_msg = sign1(pkey, empty_sig_headers(), empty_sig_headers(), aad, payload);
    COSE_Format_evercddl_COSE_Sign1_pretty c =
        COSE_Format_validate_and_parse_COSE_Sign1_Tagged(signed_msg).v.fst;

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        COSE_Format_serialize_COSE_Sign1_Tagged(c, out);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    free(signed_msg.elt);
    free(out.elt);

    report_bench_time("serialize", nruns, &start, &finish);
}

void bench_serialize_sig_struct(EVP_PKEY *pkey) {
    unsigned nruns = 10000;
    struct timespec start, finish;

    bstr out = { .len = 1024 };
    out.elt = malloc(out.len);

    bstr signed_msg = sign1(pkey, empty_sig_headers(), empty_sig_headers(), aad, payload);
    COSE_Format_evercddl_COSE_Sign1_pretty c =
        COSE_Format_validate_and_parse_COSE_Sign1_Tagged(signed_msg).v.fst;
    COSE_Format_evercddl_Sig_structure_pretty sig_struct = {
        .x0 = 1,
        .x1 = c.x0,
        .x2 = {
            .tag = COSE_Format_Inr,
            .case_Inr = {
                .fst = aad,
                .snd = payload,
            },
        },
    };

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        COSE_Format_serialize_Sig_structure(sig_struct, out);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    free(signed_msg.elt);
    free(out.elt);

    report_bench_time("serialize_sig_struct", nruns, &start, &finish);
}


int main() {
    EVP_PKEY *pkey = create_key_pair();
    bench_sign(pkey);
    bench_verify(pkey);
    bench_parse(pkey);
    bench_serialize(pkey);
    bench_serialize_sig_struct(pkey);
    EVP_PKEY_free(pkey);
}