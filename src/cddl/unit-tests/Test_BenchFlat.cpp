#include <stdio.h>
#include "qcbor/qcbor_encode.h"
#include "qcbor/qcbor_spiffy_decode.h"

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
#define LAPS 10000 /* how many times the lookup pass is repeated */

uint64_t bigrand() {
    uint64_t r = rand ();
    r = r * RAND_MAX + rand ();
    r = r * RAND_MAX + rand ();
    r = r * RAND_MAX + rand ();
    return r ; // % 100000000;
}

// bool qcbor_lookup1(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
//   assert (val);
//     QCBORError rc;
//     QCBORDecodeContext ctx;
//     QCBORItem item;
//     QCBORDecode_Init(&ctx, (UsefulBufC){buf, len}, QCBOR_DECODE_MODE_NORMAL);
//     QCBORDecode_EnterMap(&ctx, NULL);
//     QCBORDecode_GetUInt64InMapN(&ctx, key, val);
//     rc = QCBORDecode_GetError(&ctx);
//     if (rc == QCBOR_SUCCESS) {
//         QCBORDecode_ExitMap(&ctx);
//         return true;
//     }

//     return false;
// }

// bool evercbor_lookup1(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
//   cbor_det_t m = cbor_det_parse(buf, len);
//   cbor_det_t k = cbor_det_mk_int64(0, key);
//   cbor_det_t cval;
//   bool rc = cbor_det_map_get(m, k, &cval);

//   if (rc) {
//     *val = cbor_det_read_uint64(cval);
//   }

//   return rc;
// }


// bool qcbor_lookup1_no_short(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
//     QCBORError rc;
//     QCBORDecodeContext ctx;
//     QCBORItem item;
//     QCBORDecode_Init(&ctx, (UsefulBufC){buf, len}, QCBOR_DECODE_MODE_NORMAL);
//     QCBORDecode_EnterMap(&ctx, NULL);
//     while ((rc = QCBORDecode_GetNext(&ctx, &item)) != QCBOR_ERR_NO_MORE_ITEMS) {
//         uint64_t key2;
//         QCBORDecode_GetUInt64(&ctx, &key2);
//         if (key2 == key) {
//             if (val) {
//                 QCBORDecode_GetUInt64(&ctx, val);
//             }
//             QCBORDecode_ExitMap(&ctx);
//             return true;
//         }
//     }
//     return false;
// }

// bool tinycbor_lookup1(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
//     return false;
// }

// bool tinycbor_lookup1_no_short(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
//     return false;
// }

void bench_evercddl () {
    uint8_t *buf = (uint8_t *) malloc(EXPECTED_SIZE);
    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = EXPECTED_SIZE
    };

    BenchFlat_evercddl_record_pretty_s r;

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

    FStar_Pervasives_Native_option___BenchFlat_evercddl_record_pretty___Pulse_Lib_Slice_slice_uint8_t_
      rc;
    TIME_void(({
        for (int i = 0; i < LAPS; i++) {
            rc = BenchFlat_validate_and_parse_record(slice);
            assert (rc.tag == FStar_Pervasives_Native_Some);
            // size_t rc = BenchFlat_serialize_record(r, slice);
            // assert (rc == 97);
        }
    }), &f);

    BenchFlat_evercddl_record_pretty_s r2;
 
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

UsefulBufC qcbor_encode(UsefulBuf buf, BenchFlat_evercddl_record_pretty_s r) {
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

// bool qcbor_decode(UsefulBufC buf, BenchFlat_evercddl_record_pretty_s *res) {
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


bool qcbor_decode_spiffy(UsefulBufC buf, BenchFlat_evercddl_record_pretty_s *res) {
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
    uint8_t *buf = (uint8_t *) malloc(2 * EXPECTED_SIZE);
    BenchFlat_evercddl_record_pretty_s r, r2;
    r.f1 = bigrand();
    r.f2 = bigrand();
    r.f3 = bigrand();
    r.f4 = bigrand();
    r.f5 = bigrand();
    r.f6 = bigrand();
    r.f7 = bigrand();
    r.f8 = bigrand();

    UsefulBuf Buffer = { buf, 2 * EXPECTED_SIZE };
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

int main()
{
    printf("Testing\n");

    bench_evercddl ();
    bench_qcbor ();

    printf("DONE\n");

    return 0;
}
