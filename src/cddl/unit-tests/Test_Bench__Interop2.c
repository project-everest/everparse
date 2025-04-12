#include <stdio.h>
#include "timing.h"
#include "qcbor/qcbor_encode.h"
#include <assert.h>

// Prevent clashes between QCBOR and our header :-)
#undef CBOR_MAJOR_TYPE_BYTE_STRING
#undef CBOR_MAJOR_TYPE_TEXT_STRING
#undef CBOR_MAJOR_TYPE_ARRAY
#undef CBOR_MAJOR_TYPE_MAP

#include "Bench.h"

#define N 1000
#define BSIZE (30 + 3*N + (N*N)) /* size of buffer */

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
    printf("Entry\n");
    BigMap *init;

    init = malloc(sizeof(BigMap));
    assert(init);

    uint8_t *buf = malloc(100 + 3*N + N * N * sizeof(int));
    printf("Allocated %p\n", buf);
    fflush(stdout);
    assert(buf);
    UsefulBuf Buffer = { buf, 100 + 3*N + N * N * sizeof(int) };
    assert(Buffer.ptr != NULL);
    // printf("Allocated\n");

    UsefulBufC Encoded;

    Init(init);

    /* Encode the engine structure. */
    float f;
    Encoded = TIME(Encode(init, Buffer), &f);
    if (UsefulBuf_IsNULLC(Encoded)) {
        printf("Encode failed\n");
        exit(1);
    }
    assert (Encoded.ptr == buf);
    printf("Encoded in %zu bytes\n", Encoded.len);
    printf(" >>> SERIALIZATION BANDWITH : %f MB/s\n",
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
    FStar_Pervasives_Native_option___Bench_evercddl_map_pretty___Pulse_Lib_Slice_slice_uint8_t_
      m_opt = TIME(Bench_validate_and_parse_map(slice), &f);
    assert (m_opt.tag == FStar_Pervasives_Native_Some);
    printf("Parsed %zu bytes\n", m_opt.v.snd.len);
    printf("Original len %zu\n", Encoded.len);
    assert (m_opt.v.snd.len == 0); /* len is whatever remains */

    Bench_evercddl_map_pretty m =  m_opt.v.fst;
    assert (m.tag == Bench_Mkevercddl_map_pretty1);
    CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_Bench_aux_env4_type_1_pretty
      it = m.case_Mkevercddl_map_pretty1;

    printf(" >>> PARSING BANDWIDTH: %f MB/s\n", Encoded.len / f / 1e6);

    printf("Done\n");

    return 0;
}
