#include <stdio.h>
#include "timing.h"
#include "qcbor/qcbor_encode.h"
#include <assert.h>

// Prevent clashes between QCBOR and our header :-)
#undef CBOR_MAJOR_TYPE_BYTE_STRING
#undef CBOR_MAJOR_TYPE_TEXT_STRING
#undef CBOR_MAJOR_TYPE_ARRAY
#undef CBOR_MAJOR_TYPE_MAP

#include "BenchArray.h"
#include "BenchArray_common.h"

typedef struct {
    int len;
    int vals[N][N];
} BigMap;

void Init(BigMap *p)
{
    int i;
    p->len = N;
    for (i = 0; i < N; i++)
         for (int j = 0; j < N; j++)
               p->vals[i][j] = 0;
}

UsefulBufC Encode(const BigMap *p, UsefulBuf Buffer)
{
    QCBOREncodeContext EncodeCtx;
    QCBOREncode_Init(&EncodeCtx, Buffer);

    QCBOREncode_OpenArray(&EncodeCtx);

    for (int i = 0; i < p->len; i++) {
        QCBOREncode_OpenArray(&EncodeCtx);
        for (int j = 0; j < p->len; j++) {
            QCBOREncode_AddInt64(&EncodeCtx, p->vals[i][j]);
            //   QCBORError uErr = QCBOREncode_GetErrorState(&EncodeCtx);
            //   if (uErr != QCBOR_SUCCESS) {
            //       printf("Error %d: %s\n", uErr, qcbor_err_to_str(uErr));
            //       return NULLUsefulBufC;
            //   }
        }
        QCBOREncode_CloseArray(&EncodeCtx);
    }
    QCBOREncode_CloseArray(&EncodeCtx);

    UsefulBufC EncodedCBOR;
    QCBORError uErr;
    uErr = QCBOREncode_Finish(&EncodeCtx, &EncodedCBOR);
    if (uErr != QCBOR_SUCCESS) {
        printf(" encode failed, error %d: %s\n",
               uErr, qcbor_err_to_str(uErr));
        return NULLUsefulBufC;
    } else {
        return EncodedCBOR;
    }
}

int main()
{
    BigMap *init;

    init = malloc(sizeof(BigMap));
    assert(init);

    uint8_t *buf = malloc(100 + 3*N + N * N * sizeof(int));
    fflush(stdout);
    assert(buf);
    UsefulBuf Buffer = { buf, 100 + 3*N + N * N * sizeof(int) };
    assert(Buffer.ptr != NULL);
    // printf("Allocated\n");

    printf("This tests serializes an array with QCBOR and parses it back\n"
           "with EverCDDL.\n");

    UsefulBufC Encoded;

    Init(init);

    /* Encode the engine structure. */
    float f, f2;
    Encoded = TIME(Encode(init, Buffer), &f);
    if (UsefulBuf_IsNULLC(Encoded)) {
        printf("Encode failed\n");
        exit(1);
    }
    assert (Encoded.ptr == buf);
    // printf("Encoded in %zu bytes\n", Encoded.len);

    printf(" >>> QCBOR SERIALIZATION BANDWITH : %f MB/s\n",
           (double)Encoded.len / f / 1e6);
    for (int i = 0; i < 20 && i < Encoded.len; i++) {
        printf("%02x ", ((uint8_t *) Encoded.ptr)[i]);
    }
    printf("\n");

    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = Encoded.len,
    };

    /* Validate it, make sure it parses back. */
    FStar_Pervasives_Native_option___BenchArray_arr___Pulse_Lib_Slice_slice_uint8_t_
      m_opt = TIME(BenchArray_validate_and_parse_arr(slice), &f);
    assert (m_opt.tag == FStar_Pervasives_Native_Some);
    // printf("Original len %zu\n", Encoded.len);
    // printf("%zu bytes were NOT parsed\n", m_opt.v.snd.len);
    assert (m_opt.v.snd.len == 0); /* len is whatever remains */

    BenchArray_arr m =  m_opt.v.fst;
    assert (m.tag == BenchArray_Mkarr1);
    CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_BenchArray_aux_env4_type_1
      it = m.case_Mkarr1;

    printf(" >>> EVERCDDL VALIDATION BANDWIDTH: %f MB/s\n", Encoded.len / f / 1e6);

    bool rc = TIME(parse_evercddl(m), &f2);
    if (!rc) {
        printf("Parse failed\n");
        exit(1);
    }

    printf(" >>> EVERCDDL PARSING BANDWIDTH: %f MB/s\n", Encoded.len / f2 / 1e6);
    printf(" >>> EVERCDDL COMBINED BANDWIDTH: %f MB/s\n", Encoded.len / (f + f2) / 1e6);


    return 0;
}
