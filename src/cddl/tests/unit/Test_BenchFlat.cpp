#include <stdio.h>
#include "qcbor/qcbor_encode.h"
#include "qcbor/qcbor_spiffy_decode.h"
#include "tinycbor/src/cbor.h"

// Prevent clashes between QCBOR and our header :-)
#undef CBOR_MAJOR_TYPE_BYTE_STRING
#undef CBOR_MAJOR_TYPE_TEXT_STRING
#undef CBOR_MAJOR_TYPE_ARRAY
#undef CBOR_MAJOR_TYPE_MAP

#include "timing.h"

extern "C" {
#include "BenchFlat.h"
#include "CBORDetAPI.h"
}

#define EXPECTED_SIZE 97
#define LAPS 100000 /* how many times the lookup pass is repeated */

uint64_t bigrand() {
    uint64_t r = rand ();
    r = r * RAND_MAX + rand ();
    r = r * RAND_MAX + rand ();
    r = r * RAND_MAX + rand ();
    return r ; // % 100000000;
}

void bench_evercddl () {
    uint8_t *buf = (uint8_t *) malloc(EXPECTED_SIZE);
    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = EXPECTED_SIZE
    };

    BenchFlat_record_s r;

    r.f1 = bigrand();
    r.f2 = bigrand();
    r.f3 = bigrand();
    r.f4 = bigrand();
    r.f5 = bigrand();
    r.f6 = bigrand();
    r.f7 = bigrand();
    r.f8 = bigrand();

    float f;
    TIME_void(({
        for (int i = 0; i < LAPS; i++) {
            size_t rc = BenchFlat_serialize_record(r, slice);
            assert (rc == EXPECTED_SIZE);
        }
    }), &f);

    printf(" >>> EVERCDDL SERIALIZATION OF RECORD TAKES: %f us\n", f * 1e6 / LAPS);

    FStar_Pervasives_Native_option___BenchFlat_record___Pulse_Lib_Slice_slice_uint8_t_
      rc;
    TIME_void(({
        for (int i = 0; i < LAPS; i++) {
            rc = BenchFlat_validate_and_parse_record(slice);
            assert (rc.tag == FStar_Pervasives_Native_Some);
            // size_t rc = BenchFlat_serialize_record(r, slice);
            // assert (rc == 97);
        }
    }), &f);

    BenchFlat_record_s r2;
 
    r2 = rc.v.fst;

    printf(" >>> EVERCDDL PARSING OF RECORD TAKES: %f us\n", f * 1e6 / LAPS);
    assert (r.f1 == r2.f1);
    assert (r.f2 == r2.f2);
    assert (r.f3 == r2.f3);
    assert (r.f4 == r2.f4);
    assert (r.f5 == r2.f5);
    assert (r.f6 == r2.f6);
    assert (r.f7 == r2.f7);
    assert (r.f8 == r2.f8);
}

UsefulBufC qcbor_encode(UsefulBuf buf, BenchFlat_record_s r) {
    QCBOREncodeContext ctx;
    QCBOREncode_Init(&ctx, buf);
    QCBOREncode_OpenMap(&ctx);
    QCBOREncode_AddUInt64ToMapSZ(&ctx, "f1", r.f1);
    QCBOREncode_AddUInt64ToMapSZ(&ctx, "f2", r.f2);
    QCBOREncode_AddUInt64ToMapSZ(&ctx, "f3", r.f3);
    QCBOREncode_AddUInt64ToMapSZ(&ctx, "f4", r.f4);
    QCBOREncode_AddUInt64ToMapSZ(&ctx, "f5", r.f5);
    QCBOREncode_AddUInt64ToMapSZ(&ctx, "f6", r.f6);
    QCBOREncode_AddUInt64ToMapSZ(&ctx, "f7", r.f7);
    QCBOREncode_AddUInt64ToMapSZ(&ctx, "f8", r.f8);
    QCBOREncode_CloseMap(&ctx);
    UsefulBufC EncodedCBOR;
    QCBORError uErr;
    uErr = QCBOREncode_Finish(&ctx, &EncodedCBOR);
    if (uErr != QCBOR_SUCCESS) {
        printf(" encode failed, error %d: %s\n",
               uErr, qcbor_err_to_str(uErr));
        return NULLUsefulBufC;
    } else {
        return EncodedCBOR;
    }
}

// bool qcbor_decode(UsefulBufC buf, BenchFlat_record_s *res) {
//     QCBORError rc;
//     QCBORDecodeContext ctx;
//     QCBORDecode_Init(&ctx, buf, QCBOR_DECODE_MODE_NORMAL);
//     QCBORDecode_EnterMap(&ctx, NULL);
//     while ((rc = QCBORDecode_GetNext(&ctx, NULL)) != QCBOR_ERR_NO_MORE_ITEMS) {
//         printf("G1\n");
//         uint64_t key;
//         QCBORDecode_GetUInt64(&ctx, &key);
//         printf("G2\n");
//         switch (key) {
//             case 1:
//                 QCBORDecode_GetUInt64(&ctx, &res->f1);
//                 break;
//             case 2:
//                 QCBORDecode_GetUInt64(&ctx, &res->f2);
//                 break;
//             case 3:
//                 QCBORDecode_GetUInt64(&ctx, &res->f3);
//                 break;
//             case 4:
//                 QCBORDecode_GetUInt64(&ctx, &res->f4);
//                 break;
//             case 5:
//                 QCBORDecode_GetUInt64(&ctx, &res->f5);
//                 break;
//             case 6:
//                 QCBORDecode_GetUInt64(&ctx, &res->f6);
//                 break;
//             case 7:
//                 QCBORDecode_GetUInt64(&ctx, &res->f7);
//                 break;
//             case 8:
//                 QCBORDecode_GetUInt64(&ctx, &res->f8);
//                 break;
//         }
//     }
//     rc = QCBORDecode_GetError(&ctx);
//     if (rc != QCBOR_SUCCESS) {
//         printf("QCBOR error %d\n", rc);
//         return false;
//     }
//     QCBORDecode_ExitMap(&ctx);
//     rc = QCBORDecode_Finish(&ctx);
//     if (rc != QCBOR_SUCCESS) {
//         printf("QCBOR error %d\n", rc);
//         return false;
//     }
//     return true;
// }


bool qcbor_decode_spiffy(UsefulBufC buf, BenchFlat_record_s *res) {
    QCBORError rc;
    QCBORDecodeContext ctx;
    QCBORDecode_Init(&ctx, buf, QCBOR_DECODE_MODE_NORMAL);
    QCBORDecode_EnterMap(&ctx, NULL);
    QCBORDecode_GetUInt64InMapSZ(&ctx, "f1", &res->f1);
    QCBORDecode_GetUInt64InMapSZ(&ctx, "f2", &res->f2);
    QCBORDecode_GetUInt64InMapSZ(&ctx, "f3", &res->f3);
    QCBORDecode_GetUInt64InMapSZ(&ctx, "f4", &res->f4);
    QCBORDecode_GetUInt64InMapSZ(&ctx, "f5", &res->f5);
    QCBORDecode_GetUInt64InMapSZ(&ctx, "f6", &res->f6);
    QCBORDecode_GetUInt64InMapSZ(&ctx, "f7", &res->f7);
    QCBORDecode_GetUInt64InMapSZ(&ctx, "f8", &res->f8);
    rc = QCBORDecode_GetError(&ctx);
    if (rc != QCBOR_SUCCESS) {
        printf("QCBOR error %d\n", rc);
        return false;
    }
    QCBORDecode_ExitMap(&ctx);
    rc = QCBORDecode_Finish(&ctx);
    if (rc != QCBOR_SUCCESS) {
        printf("QCBOR error %d\n", rc);
        return false;
    }
    return true;
}

void bench_qcbor () {
    float f;

    /* reuse evercddl struct, why not. */
    uint8_t *buf = (uint8_t *) malloc(EXPECTED_SIZE);
    BenchFlat_record_s r, r2;
    r.f1 = bigrand();
    r.f2 = bigrand();
    r.f3 = bigrand();
    r.f4 = bigrand();
    r.f5 = bigrand();
    r.f6 = bigrand();
    r.f7 = bigrand();
    r.f8 = bigrand();

    UsefulBuf Buffer = { buf, EXPECTED_SIZE };
    UsefulBufC Encoded;

    UsefulBufC enc;
    TIME_void(
    ({
        for (int i = 0; i < LAPS; i++) {
            enc = qcbor_encode(Buffer, r);
            // assert (enc.len == EXPECTED_SIZE);
        }
    }), &f);
    printf(" >>> QCBOR SERIALIZATION OF RECORD TAKES: %f us\n", f * 1e6 / LAPS);

    for (int j = 0 ; j < enc.len ; j++) {
        printf("%02x ", ((uint8_t *) enc.ptr)[j]);
    }
    printf("\n");

    // TIME_void(
    // ({
    //     for (int i = 0; i < LAPS; i++) {
    //         bool rc = qcbor_decode(enc, &r2);
    //     }
    // }), &f);
    // printf(" >>> QCBOR (NORMAL) PARSING OF RECORD TAKES: %f us\n", f * 1e6 / LAPS);
    // assert (r.f1 == r2.f1);
    // assert (r.f2 == r2.f2);
    // assert (r.f3 == r2.f3);
    // assert (r.f4 == r2.f4);
    // assert (r.f5 == r2.f5);
    // assert (r.f6 == r2.f6);
    // assert (r.f7 == r2.f7);
    // assert (r.f8 == r2.f8);

    TIME_void(
    ({
        for (int i = 0; i < LAPS; i++) {
            bool rc = qcbor_decode_spiffy(enc, &r2);
        }
    }), &f);
    printf(" >>> QCBOR (SPIFFY) PARSING OF RECORD TAKES: %f us\n", f * 1e6 / LAPS);
    assert (r.f1 == r2.f1);
    assert (r.f2 == r2.f2);
    assert (r.f3 == r2.f3);
    assert (r.f4 == r2.f4);
    assert (r.f5 == r2.f5);
    assert (r.f6 == r2.f6);
    assert (r.f7 == r2.f7);
    assert (r.f8 == r2.f8);
}

size_t tinycbor_encode(uint8_t *buf, size_t len, BenchFlat_record_s r) {
    CborEncoder enc;
    cbor_encoder_init(&enc, buf, len, 0);
    cbor_encoder_create_map(&enc, &enc, 8);
    cbor_encode_text_stringz(&enc, "f1"); cbor_encode_uint(&enc, r.f1);
    cbor_encode_text_stringz(&enc, "f2"); cbor_encode_uint(&enc, r.f2);
    cbor_encode_text_stringz(&enc, "f3"); cbor_encode_uint(&enc, r.f3);
    cbor_encode_text_stringz(&enc, "f4"); cbor_encode_uint(&enc, r.f4);
    cbor_encode_text_stringz(&enc, "f5"); cbor_encode_uint(&enc, r.f5);
    cbor_encode_text_stringz(&enc, "f6"); cbor_encode_uint(&enc, r.f6);
    cbor_encode_text_stringz(&enc, "f7"); cbor_encode_uint(&enc, r.f7);
    cbor_encode_text_stringz(&enc, "f8"); cbor_encode_uint(&enc, r.f8);
    cbor_encoder_close_container(&enc, &enc);
    size_t len2 = cbor_encoder_get_buffer_size(&enc, buf);
    if (len2 != len) {
        printf("TINYCBOR ERROR: %zu != %zu\n", len2, len);
        return 0;
    }
    return len2;
}

bool tinycbor_decode(uint8_t *buf, size_t len, BenchFlat_record_s *r) {
    CborParser p;
    CborValue vmap, v;
    cbor_parser_init(buf, len, 0, &p, &vmap);
    cbor_value_map_find_value(&vmap, "f1", &v); cbor_value_get_uint64(&v, &r->f1);
    cbor_value_map_find_value(&vmap, "f2", &v); cbor_value_get_uint64(&v, &r->f2);
    cbor_value_map_find_value(&vmap, "f3", &v); cbor_value_get_uint64(&v, &r->f3);
    cbor_value_map_find_value(&vmap, "f4", &v); cbor_value_get_uint64(&v, &r->f4);
    cbor_value_map_find_value(&vmap, "f5", &v); cbor_value_get_uint64(&v, &r->f5);
    cbor_value_map_find_value(&vmap, "f6", &v); cbor_value_get_uint64(&v, &r->f6);
    cbor_value_map_find_value(&vmap, "f7", &v); cbor_value_get_uint64(&v, &r->f7);
    cbor_value_map_find_value(&vmap, "f8", &v); cbor_value_get_uint64(&v, &r->f8);

    return true;
}

void bench_tinycbor () {
    float f;

    /* reuse evercddl struct, why not. */
    uint8_t *buf = (uint8_t *) malloc(EXPECTED_SIZE);
    BenchFlat_record_s r, r2;
    r.f1 = bigrand();
    r.f2 = bigrand();
    r.f3 = bigrand();
    r.f4 = bigrand();
    r.f5 = bigrand();
    r.f6 = bigrand();
    r.f7 = bigrand();
    r.f8 = bigrand();

    size_t len;
    TIME_void(
    ({
        for (int i = 0; i < LAPS; i++) {
            len = tinycbor_encode(buf, EXPECTED_SIZE, r);
            assert (len == EXPECTED_SIZE);
        }
    }), &f);
    printf(" >>> TINYCBOR SERIALIZATION OF RECORD TAKES: %f us\n", f * 1e6 / LAPS);

    for (int j = 0 ; j < len ; j++) {
        printf("%02x ", buf[j]);
    }
    printf("\n");

    TIME_void(
    ({
        for (int i = 0; i < LAPS; i++) {
            bool rc = tinycbor_decode(buf, len, &r2);
        }
    }), &f);
    printf(" >>> TINYCBOR PARSING OF RECORD TAKES: %f us\n", f * 1e6 / LAPS);
    assert (r.f1 == r2.f1);
    assert (r.f2 == r2.f2);
    assert (r.f3 == r2.f3);
    assert (r.f4 == r2.f4);
    assert (r.f5 == r2.f5);
    assert (r.f6 == r2.f6);
    assert (r.f7 == r2.f7);
    assert (r.f8 == r2.f8);
}


int main()
{
    printf("This test benchmarks serializing and parsing a flat structure\n"
           "using EverCDDL, TinyCBOR, and QCBOR.\n");

    bench_evercddl ();
    bench_qcbor ();
    bench_tinycbor ();

    return 0;
}
