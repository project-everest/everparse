#include "COSE_OpenSSL.h"

void COSE_OpenSSL_openssl_error_msg(const char *msg) {
    char buf[256] = "unknown error";
    unsigned long err = ERR_get_error();
    if (err) ERR_error_string_n(err, buf, sizeof(buf) - 1);
    fprintf(stderr, "openssl failed: %s (%s)\n", msg, buf);
}

#define check(cond) { if (!(cond)) { fprintf(stderr, "failed: %s\n", #cond); abort(); } }
#define openssl_check(cond) { if (!(cond)) { COSE_OpenSSL_openssl_error_msg(#cond); abort(); } }

// "Signature1": Custard models this CDDL constant as `either unit unit`,
// where karamel emits a plain enum tag.
// Both arms carry unit, so Custard collapses this to a bare enum.
static const FStar_Pervasives_either__unit_unit signature1 =
    FSTAR_PERVASIVES_INR__UNIT_UNIT;

static
bstr mk_sig_structure(COSE_Format_empty_or_serialized_map protected_headers,
        bstr aad, bstr payload) {
    COSE_Format_sig_structure c = {
        .context = signature1,
        .body_protected = protected_headers,
        ._x0 = {
            .tag = FSTAR_PERVASIVES_INR__TUPLE2_EMPTY_OR_SERIALIZED_MAP_TUPLE2_BSTR_BSTR_,
            .val.FStar_Pervasives_Inr__tuple2_empty_or_serialized_map_tuple2_bstr_bstr_.v = {
                ._1 = aad,
                ._2 = payload,
            },
        },
    };
    
    bstr out;
    out.len = 1024; // TODO
    check(out.elt = malloc(out.len));

    check(out.len = COSE_Format_serialize_sig_structure(c, out));

    return out;
}

COSE_Format_header_map COSE_OpenSSL_empty_sig_headers() {
    return (COSE_Format_header_map) {
        .intkey1 = { .tag = FSTAR_PERVASIVES_NATIVE_NONE__EITHER_EVERCDDL_INT_TSTR },
        .intkey2 = { .tag = FSTAR_PERVASIVES_NATIVE_NONE__EITHER_SLICE_AUX_ENV34_TYPE_1_ARRAY_ITERATOR_T_C },
        .intkey3 = { .tag = FSTAR_PERVASIVES_NATIVE_NONE__EITHER_TSTR_EVERCDDL_INT },
        .intkey4 = { .tag = FSTAR_PERVASIVES_NATIVE_NONE__BSTR },
        ._x0 = {
            .tag = FSTAR_PERVASIVES_INR__TUPLE2_BSTR_OPTION_EVERPARSENOMATCH_EITHER_TUPLE,
            .val.FStar_Pervasives_Inr__tuple2_bstr_option_everparsenomatch_either_tuple.v = {
                .tag = FSTAR_PERVASIVES_INR__TUPLE2_BSTR_OPTION_EVERPARSENOMATCH_TUPLE2_OPTIO,
                .val.FStar_Pervasives_Inr__tuple2_bstr_option_everparsenomatch_tuple2_optio.v = {
                    ._1 = FSTAR_PERVASIVES_NATIVE_NONE__EVERPARSENOMATCH,
                    ._2 = FSTAR_PERVASIVES_NATIVE_NONE__EVERPARSENOMATCH,
                },
            }
        },
        ._x1 = {
            .tag = FSTAR_PERVASIVES_INL__SLICE_TUPLE2_EVERCDDL_LABEL_VALUES_MAP_ITERATOR_,
            .val.FStar_Pervasives_Inl__slice_tuple2_evercddl_label_values_map_iterator_.v = {
                .elt = (FStar_Pervasives_Native_tuple2__evercddl_label_values[]) {},
                .len = 0,
            },
        },
    };
}

bstr COSE_OpenSSL_sign_eddsa(EVP_PKEY *signing_key, const bstr tbs) {
    EVP_MD_CTX *sign_context = EVP_MD_CTX_new();
    openssl_check(sign_context);

    openssl_check(EVP_DigestSignInit(sign_context, NULL, NULL, NULL, signing_key) == 1);

    bstr sig;
    openssl_check(EVP_DigestSign(sign_context, NULL, &sig.len, tbs.elt, tbs.len) == 1);
    openssl_check(sig.elt = OPENSSL_malloc(sig.len));

    openssl_check(EVP_DigestSign(sign_context, sig.elt, &sig.len, tbs.elt, tbs.len) == 1);

    EVP_MD_CTX_free(sign_context);
    return sig;
}

bstr COSE_OpenSSL_sign1(EVP_PKEY *signing_key,
        COSE_Format_header_map protected_headers,
        COSE_Format_header_map unprotected_headers,
        bstr aad, bstr payload) {
    protected_headers.intkey1 = (FStar_Pervasives_Native_option__either_evercddl_int_tstr) {
        .tag = FSTAR_PERVASIVES_NATIVE_SOME__EITHER_EVERCDDL_INT_TSTR,
        .val.FStar_Pervasives_Native_Some__either_evercddl_int_tstr.v = {
            .tag = FSTAR_PERVASIVES_INL__EVERCDDL_INT_TSTR,
            .val.FStar_Pervasives_Inl__evercddl_int_tstr.v = { // -8 (COSE_ALGORITHM_EDDSA)
                .tag = COSE_FORMAT_MKEVERCDDL_INT1,
                .val.COSE_Format_Mkevercddl_int1._x0 = 7,
            }
        },
    };
    COSE_Format_empty_or_serialized_map protected_headers_ = {
        .tag = COSE_FORMAT_MKEMPTY_OR_SERIALIZED_MAP0,
        .val.COSE_Format_Mkempty_or_serialized_map0._x0 = protected_headers,
    };

    bstr sig_structure = mk_sig_structure(protected_headers_, aad, payload);
    bstr sig = COSE_OpenSSL_sign_eddsa(signing_key, sig_structure);
    free(sig_structure.elt);

    COSE_Format_cose_sign1 c = {
        .protected = protected_headers_,
        .unprotected = unprotected_headers,
        .payload = { .tag = FSTAR_PERVASIVES_INL__BSTR_NIL,
                     .val.FStar_Pervasives_Inl__bstr_nil.v = payload },
        .signature = sig,
    };

    bstr out;
    out.len = 1024; // TODO
    check(out.elt = malloc(out.len));
    check(out.len = COSE_Format_serialize_cose_sign1_tagged(c, out));

    OPENSSL_free(sig.elt);

    return out;
}

bool COSE_OpenSSL_validate(EVP_PKEY *signing_key, bstr tbs, bstr sig) {
    EVP_MD_CTX *sign_context = EVP_MD_CTX_new();
    openssl_check(sign_context);

    openssl_check(EVP_DigestVerifyInit(sign_context, NULL, NULL, NULL, signing_key) == 1);

    int verify_result = EVP_DigestVerify(sign_context, sig.elt, sig.len, tbs.elt, tbs.len);
    openssl_check(verify_result == 0 || verify_result == 1);

    EVP_MD_CTX_free(sign_context);

    return verify_result == 1;
}

bstr COSE_OpenSSL_verify1(EVP_PKEY *signing_key, bstr aad, bstr msg) {
    FStar_Pervasives_Native_option__tuple2_cose_sign1_tagged_slice_uint8 parsed_msg =
        COSE_Format_validate_and_parse_cose_sign1_tagged(msg);
    check(parsed_msg.tag == FSTAR_PERVASIVES_NATIVE_SOME__TUPLE2_COSE_SIGN1_TAGGED_SLICE_UINT8);
    COSE_Format_cose_sign1 parsed =
        parsed_msg.val.FStar_Pervasives_Native_Some__tuple2_cose_sign1_tagged_slice_uint8.v._1;

    check(parsed.payload.tag == FSTAR_PERVASIVES_INL__BSTR_NIL); // detached payload not supported
    bstr payload = parsed.payload.val.FStar_Pervasives_Inl__bstr_nil.v;

    bstr sig = parsed.signature;

    COSE_Format_empty_or_serialized_map protected_headers = parsed.protected;
    // TODO check algorithm
  
    bstr sig_structure = mk_sig_structure(protected_headers, aad, payload);

    check(COSE_OpenSSL_validate(signing_key, sig_structure, sig));

    free(sig_structure.elt);

    return payload;
}
