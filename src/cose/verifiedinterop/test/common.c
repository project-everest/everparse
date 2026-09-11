#include "common.h"

/* Abort.abort is an assume val realized by libc's abort.  karamel got the
   unqualified C name from -no-prefix Abort; Custard's --custard_c_no_prefix
   does not cover assume vals, so the realization is provided here. */
void Abort_abort(void) { abort(); }

#define check(cond) { if (!(cond)) { fprintf(stderr, "failed: %s\n", #cond); abort(); } }

typedef Pulse_Lib_Slice_slice__uint8 bstr;

uint8_t *parse_ed25519_private_key(bstr cose_key) {
    FStar_Pervasives_Native_option__tuple2_cose_key_okp_slice_uint8
        parsed_key = COSE_Format_validate_and_parse_cose_key_okp(cose_key);
    check(parsed_key.tag == FSTAR_PERVASIVES_NATIVE_SOME__TUPLE2_COSE_KEY_OKP_SLICE_UINT8);
    COSE_Format_cose_key_okp key =
        parsed_key.val.FStar_Pervasives_Native_Some__tuple2_cose_key_okp_slice_uint8.v._1;
    check(key.intkeyneg1.tag == FSTAR_PERVASIVES_INL__EVERCDDL_INT_TSTR);
    COSE_Format_evercddl_int label = key.intkeyneg1.val.FStar_Pervasives_Inl__evercddl_int_tstr.v;
    check(label.tag == COSE_FORMAT_MKEVERCDDL_INT0);
    check(label.val.COSE_Format_Mkevercddl_int0._x0 == 6);
    check(key.intkeyneg4.tag == FSTAR_PERVASIVES_NATIVE_SOME__BSTR);
    bstr k4 = key.intkeyneg4.val.FStar_Pervasives_Native_Some__bstr.v;
    check(k4.len == 32);
    return k4.elt;
}

uint8_t *parse_ed25519_public_key(bstr cose_key) {
    FStar_Pervasives_Native_option__tuple2_cose_key_okp_slice_uint8
        parsed_key = COSE_Format_validate_and_parse_cose_key_okp(cose_key);
    check(parsed_key.tag == FSTAR_PERVASIVES_NATIVE_SOME__TUPLE2_COSE_KEY_OKP_SLICE_UINT8);
    COSE_Format_cose_key_okp key =
        parsed_key.val.FStar_Pervasives_Native_Some__tuple2_cose_key_okp_slice_uint8.v._1;
    check(key.intkeyneg1.tag == FSTAR_PERVASIVES_INL__EVERCDDL_INT_TSTR);
    COSE_Format_evercddl_int label = key.intkeyneg1.val.FStar_Pervasives_Inl__evercddl_int_tstr.v;
    check(label.tag == COSE_FORMAT_MKEVERCDDL_INT0);
    check(label.val.COSE_Format_Mkevercddl_int0._x0 == 6);
    check(key.intkeyneg2.tag == FSTAR_PERVASIVES_NATIVE_SOME__BSTR);
    bstr k2 = key.intkeyneg2.val.FStar_Pervasives_Native_Some__bstr.v;
    check(k2.len == 32);
    return k2.elt;
}

void write_to_file(const char *fn, const uint8_t *content, size_t content_len) {
    FILE *f; check(f = fopen(fn, "w"));
    check(fwrite(content, content_len, 1, f) == 1);
    check(fclose(f) == 0);
}

bstr read_from_file(const char *fn) {
    FILE *f; check(f = fopen(fn, "r"));
    check(fseek(f, 0, SEEK_END) == 0);
    long size = ftell(f);
    check(fseek(f, 0, SEEK_SET) == 0);
    bstr out = { .len = size };
    check(out.elt = malloc(size));
    check(fread(out.elt, size, 1, f) == 1);
    check(fclose(f) == 0);
    return out;
}
