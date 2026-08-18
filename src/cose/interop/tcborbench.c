#include <time.h>
#include <openssl/evp.h>
#include <openssl/err.h>
#include <fcntl.h>
#include <t_cose/t_cose_sign1_sign.h>
#include <t_cose/t_cose_sign1_verify.h>

void openssl_error_msg(const char *msg) {
    char buf[256] = "unknown error";
    unsigned long err = ERR_get_error();
    if (err) ERR_error_string_n(err, buf, sizeof(buf) - 1);
    fprintf(stderr, "openssl failed: %s (%s)\n", msg, buf);
}

#define check(cond) { if (!(cond)) { fprintf(stderr, "failed: %s\n", #cond); abort(); } }
#define openssl_check(cond) { if (!(cond)) { openssl_error_msg(#cond); abort(); } }
#define tcose_check(result) { int _res = (result); if (_res != T_COSE_SUCCESS) { fprintf(stderr, "tcose failed: %s (%i)\n", #result, _res); abort(); } }

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

unsigned char payload_str[] = xp7("payload");
struct q_useful_buf_c payload = { .len = sizeof(payload_str) - 1, .ptr = payload_str };

// bstr aad = { .len = 0, .elt = (uint8_t[]) {} };

void bench_sign(EVP_PKEY *pkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;
        
    struct t_cose_sign1_sign_ctx context;
    t_cose_sign1_sign_init(&context, 0, T_COSE_ALGORITHM_EDDSA);
    t_cose_sign1_set_signing_key(&context,
        (struct t_cose_key) { .crypto_lib = T_COSE_CRYPTO_LIB_OPENSSL, { .key_ptr = pkey } },
        NULL_Q_USEFUL_BUF_C);

    struct q_useful_buf auxbuf = { .len = 2000 };
    check(auxbuf.ptr = malloc(auxbuf.len));
    t_cose_sign1_sign_set_auxiliary_buffer(&context, auxbuf);

    struct q_useful_buf outbuf = { .len = 2000 };
    check(outbuf.ptr = malloc(outbuf.len));

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        struct q_useful_buf_c msg;
        tcose_check(t_cose_sign1_sign(&context, payload, outbuf, &msg));
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    report_bench_time("sign1", nruns, &start, &finish);
}

void bench_verify(EVP_PKEY *pkey) {
    unsigned nruns = 100000;
    struct timespec start, finish;
    
    struct t_cose_sign1_sign_ctx sign_ctx;
    t_cose_sign1_sign_init(&sign_ctx, 0, T_COSE_ALGORITHM_EDDSA);
    t_cose_sign1_set_signing_key(&sign_ctx,
        (struct t_cose_key) { .crypto_lib = T_COSE_CRYPTO_LIB_OPENSSL, { .key_ptr = pkey } },
        NULL_Q_USEFUL_BUF_C);

    struct q_useful_buf auxbuf = { .len = 2000 };
    check(auxbuf.ptr = malloc(auxbuf.len));
    t_cose_sign1_sign_set_auxiliary_buffer(&sign_ctx, auxbuf);

    struct q_useful_buf outbuf = { .len = 2000 };
    check(outbuf.ptr = malloc(outbuf.len));

    struct q_useful_buf_c signed_msg;
    tcose_check(t_cose_sign1_sign(&sign_ctx, payload, outbuf, &signed_msg));
    
    struct t_cose_sign1_verify_ctx verify_ctx;
    t_cose_sign1_verify_init(&verify_ctx, 0);
    // t_cose_sign1_verify_init(&verify_ctx, T_COSE_ALGORITHM_EDDSA);
    t_cose_sign1_set_verification_key(&verify_ctx,
        (struct t_cose_key) { .crypto_lib = T_COSE_CRYPTO_LIB_OPENSSL, { .key_ptr = pkey } });
    t_cose_sign1_verify_set_auxiliary_buffer(&verify_ctx, auxbuf);

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (unsigned i = 0; i < nruns; i++) {
        struct q_useful_buf_c parsed_payload;
        struct t_cose_parameters phdrs;
        tcose_check(t_cose_sign1_verify(&verify_ctx, signed_msg, &parsed_payload, NULL));
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);

    report_bench_time("verify1", nruns, &start, &finish);
}

// void bench_parse(EVP_PKEY *pkey) {
//     unsigned nruns = 100000;
//     struct timespec start, finish;

//     bstr signed_msg = sign1(pkey, empty_sig_headers(), empty_sig_headers(), aad, payload);
//     clock_gettime(CLOCK_MONOTONIC, &start);
//     for (unsigned i = 0; i < nruns; i++) {
//         COSE_Format_validate_and_parse_COSE_Sign1_Tagged(signed_msg);
//     }
//     clock_gettime(CLOCK_MONOTONIC, &finish);
//     free(signed_msg.elt);

//     report_bench_time("parse", nruns, &start, &finish);
// }

// void bench_serialize(EVP_PKEY *pkey) {
//     unsigned nruns = 100000;
//     struct timespec start, finish;

//     bstr out = { .len = 1024 };
//     out.elt = malloc(out.len);

//     bstr signed_msg = sign1(pkey, empty_sig_headers(), empty_sig_headers(), aad, payload);
//     COSE_Format_evercddl_COSE_Sign1_pretty c =
//         COSE_Format_validate_and_parse_COSE_Sign1_Tagged(signed_msg).v.fst;

//     clock_gettime(CLOCK_MONOTONIC, &start);
//     for (unsigned i = 0; i < nruns; i++) {
//         COSE_Format_serialize_COSE_Sign1_Tagged(c, out);
//     }
//     clock_gettime(CLOCK_MONOTONIC, &finish);

//     free(signed_msg.elt);
//     free(out.elt);

//     report_bench_time("serialize", nruns, &start, &finish);
// }

// void bench_serialize_sig_struct(EVP_PKEY *pkey) {
//     unsigned nruns = 100000;
//     struct timespec start, finish;

//     bstr out = { .len = 1024 };
//     out.elt = malloc(out.len);

//     bstr signed_msg = sign1(pkey, empty_sig_headers(), empty_sig_headers(), aad, payload);
//     COSE_Format_evercddl_COSE_Sign1_pretty c =
//         COSE_Format_validate_and_parse_COSE_Sign1_Tagged(signed_msg).v.fst;
//     COSE_Format_evercddl_Sig_structure_pretty sig_struct = {
//         .context = 1,
//         .body_protected = c.protected,
//         ._x0 = {
//             .tag = COSE_Format_Inr,
//             .case_Inr = {
//                 .fst = aad,
//                 .snd = payload,
//             },
//         },
//     };

//     clock_gettime(CLOCK_MONOTONIC, &start);
//     for (unsigned i = 0; i < nruns; i++) {
//         COSE_Format_serialize_Sig_structure(sig_struct, out);
//     }
//     clock_gettime(CLOCK_MONOTONIC, &finish);

//     free(signed_msg.elt);
//     free(out.elt);

//     report_bench_time("serialize_sig_struct", nruns, &start, &finish);
// }

// void bench_ed25519_sign(EVP_PKEY *pkey) {
//     unsigned nruns = 100000;
//     struct timespec start, finish;

//     COSE_Format_evercddl_Sig_structure_pretty sig_struct = {
//         .context = 1,
//         .body_protected = {},
//         ._x0 = {
//             .tag = COSE_Format_Inr,
//             .case_Inr = {
//                 .fst = { .len = 0, .elt = (uint8_t[]) {} },
//                 .snd = payload,
//             },
//         },
//     };
//     bstr tbs = { .len = 1024 };
//     check(tbs.elt = malloc(tbs.len));
//     COSE_Format_serialize_Sig_structure(sig_struct, tbs);

//     clock_gettime(CLOCK_MONOTONIC, &start);
//     for (unsigned i = 0; i < nruns; i++) {
//         bstr sig = sign_eddsa(pkey, tbs);
//         free(sig.elt);
//     }
//     clock_gettime(CLOCK_MONOTONIC, &finish);

//     free(tbs.elt);
//     report_bench_time("ed25519_sign", nruns, &start, &finish);
// }

// void bench_ed25519_verify(EVP_PKEY *pkey) {
//     unsigned nruns = 100000;
//     struct timespec start, finish;

//     COSE_Format_evercddl_Sig_structure_pretty sig_struct = {
//         .context = 1,
//         .body_protected = {},
//         ._x0 = {
//             .tag = COSE_Format_Inr,
//             .case_Inr = {
//                 .fst = { .len = 0, .elt = (uint8_t[]) {} },
//                 .snd = payload,
//             },
//         },
//     };
//     bstr tbs = { .len = 1024 };
//     check(tbs.elt = malloc(tbs.len));
//     COSE_Format_serialize_Sig_structure(sig_struct, tbs);
//     bstr sig = sign_eddsa(pkey, tbs);

//     clock_gettime(CLOCK_MONOTONIC, &start);
//     for (unsigned i = 0; i < nruns; i++) {
//         validate(pkey, tbs, sig);
//     }
//     clock_gettime(CLOCK_MONOTONIC, &finish);

//     free(tbs.elt);
//     free(sig.elt);
//     report_bench_time("ed25519_verify", nruns, &start, &finish);
// }

int main() {
    EVP_PKEY *pkey = create_key_pair();
    bench_sign(pkey);
    bench_verify(pkey);
    // bench_parse(pkey);
    // bench_serialize(pkey);
    // bench_serialize_sig_struct(pkey);
    // bench_ed25519_sign(pkey);
    // bench_ed25519_verify(pkey);
    EVP_PKEY_free(pkey);
}