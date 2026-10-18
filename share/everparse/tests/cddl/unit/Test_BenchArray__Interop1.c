#include <stdio.h>
#include "timing.h"
#include "qcbor/qcbor_decode.h"
#include "qcbor/qcbor_spiffy_decode.h"
#include <assert.h>

// :-)
#undef CBOR_MAJOR_TYPE_BYTE_STRING
#undef CBOR_MAJOR_TYPE_TEXT_STRING
#undef CBOR_MAJOR_TYPE_ARRAY
#undef CBOR_MAJOR_TYPE_MAP

#include "BenchArray.h"
#include "BenchArray_common.h"

QCBORError ValidSpiffy(UsefulBufC Encoded)
{
    QCBORError         uErr;
    QCBORDecodeContext DecodeCtx;

    /* Let QCBORDecode internal error tracking do its work. */
    QCBORDecode_Init(&DecodeCtx, Encoded, QCBOR_DECODE_MODE_NORMAL);
    QCBORDecode_EnterArray(&DecodeCtx, NULL);
    for (int i = 0; i < N; i++) {
        QCBORDecode_EnterArray(&DecodeCtx, NULL);
        for (int j = 0; j < N; j++) {
            int64_t t;
            QCBORDecode_GetInt64(&DecodeCtx, &t);
            // assert (t == 0);
        }
        QCBORDecode_ExitArray(&DecodeCtx);
    }
    QCBORDecode_ExitArray(&DecodeCtx);

    /* Catch further decoding error here */
    uErr = QCBORDecode_Finish(&DecodeCtx);

    return uErr;
}

QCBORError DecodeSpiffy(UsefulBufC Encoded, uint64_t *sum)
{
    QCBORError         uErr;
    QCBORDecodeContext DecodeCtx;

    *sum = 0;

    /* Let QCBORDecode internal error tracking do its work. */
    QCBORDecode_Init(&DecodeCtx, Encoded, QCBOR_DECODE_MODE_NORMAL);
    QCBORDecode_EnterArray(&DecodeCtx, NULL);
    for (int i = 0; i < N; i++) {
        QCBORDecode_EnterArray(&DecodeCtx, NULL);
        for (int j = 0; j < N; j++) {
            int64_t t;
            QCBORDecode_GetInt64(&DecodeCtx, &t);
            *sum += t;
            // assert (t == 0);
        }
        QCBORDecode_ExitArray(&DecodeCtx);
    }
    QCBORDecode_ExitArray(&DecodeCtx);

    /* Catch further decoding error here */
    uErr = QCBORDecode_Finish(&DecodeCtx);

    return uErr;
}

int valid_qcbor(uint8_t *buf, size_t len)
{
    UsefulBufC bb = { buf, len };
    QCBORError uErr = ValidSpiffy(bb);
    if (uErr != QCBOR_SUCCESS) {
        printf("QCBOR error %d\n", uErr);
        return 1;
    }
    printf("QCBOR parsed %zu bytes\n", len);
    return 0;
}

int parse_qcbor(uint8_t *buf, size_t len, uint64_t *sum)
{
    UsefulBufC bb = { buf, len };
    QCBORError uErr = DecodeSpiffy(bb, sum);
    if (uErr != QCBOR_SUCCESS) {
        printf("QCBOR error %d\n", uErr);
        return 1;
    }
    printf("QCBOR parsed %zu bytes\n", len);
    return 0;
}


int main()
{
    size_t len = BSIZE;
    char *buf = malloc(len);
    float f, f0, f2;
    assert(buf);

    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = len
    };

    printf("This test serializes the array with EverCDDL and parses it back with QCBOR.\n");

    BenchArray_arr m = TIME(build(), &f0);
    printf(" >>> Time to build the array in memory: %fs\n", f0);

    size_t size = TIME(BenchArray_serialize_arr(m, slice), &f);
    if (size == 0) {
        printf("Serialization failed\n");
        return 1;
    }
    printf ("Serialized %zu bytes\n", size);
    for (int i = 0; i < 20 && i < size; i++) {
        printf("%02x ", slice.elt[i]);
    }
    printf("... \n");

    printf(" >>> SERIALIZATION BANDWIDTH: %f MB/s\n", size / f / 1e6);
    printf(" >>> SERIALIZATION BANDWIDTH (COMBINED): %f MB/s\n", size / (f + f0) / 1e6);

    /* Now parse it with QCBOR.
       We go through the array twice, to match the guarantees
       of EverCDLL (if the array is corrupt/invalid, we should not allow
       to parse a single element out of it). */

    int rc = TIME(valid_qcbor(slice.elt, size), &f);
    if (rc != 0) {
        printf("QCBOR Parsing failed\n");
        return 1;
    }

    printf(" >>> QCBOR VALIDATION BANDWIDTH: %f MB/s\n", size / f / 1e6);

    uint64_t sum;

    rc = TIME(parse_qcbor(slice.elt, size, &sum), &f2);
    if (rc != 0) {
        printf("QCBOR Parsing failed\n");
        return 1;
    }

    printf(" >>> QCBOR PARSING BANDWIDTH: %f MB/s\n", size / f2 / 1e6);
    printf(" >>> QCBOR COMBINED BANDWIDTH: %f MB/s\n", size / (f + f2) / 1e6);


    return 0;
}
