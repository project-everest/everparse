#include "common.h"
#include <time.h>

EVP_PKEY *create_key_pair() {
    EVP_PKEY *pkey = NULL;
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

unsigned char payload_str[] = xp7("payload");
bstr payload = { .len = sizeof(payload_str) - 1, .elt = payload_str };

bstr aad = { .len = 0, .elt = (uint8_t[]) {} };

void bench_sign(EVP_PKEY *pkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        bstr signed_msg = COSE_OpenSSL_sign1(pkey, COSE_OpenSSL_empty_sig_headers(), COSE_OpenSSL_empty_sig_headers(), aad, payload);
        free(signed_msg.elt);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    report_bench_time("sign1", nruns, &start, &finish);
}

void bench_verify(EVP_PKEY *pkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    bstr signed_msg = COSE_OpenSSL_sign1(pkey, COSE_OpenSSL_empty_sig_headers(), COSE_OpenSSL_empty_sig_headers(), aad, payload);
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        COSE_OpenSSL_verify1(pkey, aad, signed_msg);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);
    free(signed_msg.elt);

    report_bench_time("verify1", nruns, &start, &finish);
}

void bench_parse(EVP_PKEY *pkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    bstr signed_msg = COSE_OpenSSL_sign1(pkey, COSE_OpenSSL_empty_sig_headers(), COSE_OpenSSL_empty_sig_headers(), aad, payload);
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        COSE_Format_validate_and_parse_cose_sign1_tagged(signed_msg);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);
    free(signed_msg.elt);

    report_bench_time("parse", nruns, &start, &finish);
}

void bench_serialize(EVP_PKEY *pkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    bstr out = { .len = 1024 };
    out.elt = malloc(out.len);

    bstr signed_msg = COSE_OpenSSL_sign1(pkey, COSE_OpenSSL_empty_sig_headers(), COSE_OpenSSL_empty_sig_headers(), aad, payload);
    COSE_Format_cose_sign1 c =
        COSE_Format_validate_and_parse_cose_sign1_tagged(signed_msg).v.fst;

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        COSE_Format_serialize_cose_sign1_tagged(c, out);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    free(signed_msg.elt);
    free(out.elt);

    report_bench_time("serialize", nruns, &start, &finish);
}

void bench_serialize_sig_struct(EVP_PKEY *pkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    bstr out = { .len = 1024 };
    out.elt = malloc(out.len);

    bstr signed_msg = COSE_OpenSSL_sign1(pkey, COSE_OpenSSL_empty_sig_headers(), COSE_OpenSSL_empty_sig_headers(), aad, payload);
    COSE_Format_cose_sign1 c =
        COSE_Format_validate_and_parse_cose_sign1_tagged(signed_msg).v.fst;
    COSE_Format_sig_structure sig_struct = {
        .context = 1,
        .body_protected = c.protected0,
        ._x0 = {
            .tag = COSE_Format_Inr,
            .case_Inr = {
                .fst = aad,
                .snd = payload,
            },
        },
    };

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        COSE_Format_serialize_sig_structure(sig_struct, out);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    free(signed_msg.elt);
    free(out.elt);

    report_bench_time("serialize_sig_struct", nruns, &start, &finish);
}

void bench_ed25519_sign(EVP_PKEY *pkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    COSE_Format_sig_structure sig_struct = {
        .context = 1,
        .body_protected = {},
        ._x0 = {
            .tag = COSE_Format_Inr,
            .case_Inr = {
                .fst = { .len = 0, .elt = (uint8_t[]) {} },
                .snd = payload,
            },
        },
    };
    bstr tbs = { .len = 1024 };
    check(tbs.elt = malloc(tbs.len));
    COSE_Format_serialize_sig_structure(sig_struct, tbs);

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        bstr sig = COSE_OpenSSL_sign_eddsa(pkey, tbs);
        free(sig.elt);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    free(tbs.elt);
    report_bench_time("ed25519_sign", nruns, &start, &finish);
}

void bench_ed25519_verify(EVP_PKEY *pkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;

    COSE_Format_sig_structure sig_struct = {
        .context = 1,
        .body_protected = {},
        ._x0 = {
            .tag = COSE_Format_Inr,
            .case_Inr = {
                .fst = { .len = 0, .elt = (uint8_t[]) {} },
                .snd = payload,
            },
        },
    };
    bstr tbs = { .len = 1024 };
    check(tbs.elt = malloc(tbs.len));
    COSE_Format_serialize_sig_structure(sig_struct, tbs);
    bstr sig = COSE_OpenSSL_sign_eddsa(pkey, tbs);

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        COSE_OpenSSL_validate(pkey, tbs, sig);
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    free(tbs.elt);
    free(sig.elt);
    report_bench_time("ed25519_verify", nruns, &start, &finish);
}

int main() {
    EVP_PKEY *pkey = create_key_pair();
    bench_sign(pkey);
    bench_verify(pkey);
    bench_parse(pkey);
    bench_serialize(pkey);
    bench_serialize_sig_struct(pkey);
    bench_ed25519_sign(pkey);
    bench_ed25519_verify(pkey);
    EVP_PKEY_free(pkey);
}
