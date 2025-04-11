/* Benchmarking QCBOR similarly to Bench.cddl and Test_Bench.c */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "qcbor/qcbor_encode.h"
#include "qcbor/qcbor_decode.h"
#include "qcbor/qcbor_spiffy_decode.h"
#include "timing.h"

// We encode a length N of array on N length N arrays
#define N 10000

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

QCBORError DecodeSpiffy(UsefulBufC Encoded, BigMap *p)
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
            p->vals[i][j] = t;
        }
        QCBORDecode_ExitArray(&DecodeCtx);
    }
    QCBORDecode_ExitArray(&DecodeCtx);

    /* Catch further decoding error here */
    uErr = QCBORDecode_Finish(&DecodeCtx);

Done:
    return uErr;
}

int main()
{
    printf("Entry\n");
    BigMap *init;
    BigMap *decoded;

    init = malloc(sizeof(BigMap));
    assert(init);
    decoded = malloc(sizeof(BigMap));
    assert(decoded);

    /* For every buffer used by QCBOR a pointer and a length are always
     * carried in a UsefulBuf. This is a secure coding and hygene
     * practice to help make sure code never runs off the end of a
     * buffer.
     *
     * UsefulBuf structures are passed as a stack parameter to make the
     * code prettier. The object code generated isn't much different
     * from passing a pointer parameter and a length parameter.
     *
     * This macro is equivalent to:
     *    uint8_t    __pBufBuffer[300];
     *    UsefulBuf  Buffer = {__pBufBuffer, 300};
     */
    uint8_t *buf = malloc(100 + N * N * sizeof(int));
    printf("Allocated %p\n", buf);
    fflush(stdout);
    assert(buf);
    UsefulBuf Buffer = { buf, 100 + N * N * sizeof(int) };
    assert(Buffer.ptr != NULL);
    // printf("Allocated\n");

    /* The pointer in UsefulBuf is not const and used for representing
     * a buffer to be written to. For UsefulbufC, the pointer is const
     * and is used to represent a buffer that has been written to.
     */
    UsefulBufC Encoded;
    // DecodeErrors        uErr;

    /* Initialize the structure with some values. */
    Init(init);

    /* Encode the engine structure. */
    float f;
    Encoded = TIME(Encode(init, Buffer), &f);
    if (UsefulBuf_IsNULLC(Encoded)) {
        printf(" encode failed\n");
        exit(1);
    }
    printf("Example: Definite Length  Encoded in %zu bytes\n",
           Encoded.len);
    printf(" >>> SERIALIZATION BANDWITH : %f MB/s\n",
           (double)Encoded.len / f / 1e6);
    for (int i = 0; i < 20 && i < Encoded.len; i++) {
        printf("%02x ", ((uint8_t *) Encoded.ptr)[i]);
    }
    printf("\n");

    // /* Decode the CBOR */
    QCBORError uErr = TIME(DecodeSpiffy(Encoded, decoded), &f);
    printf("Example: Spiffy  Decode Result: %d\n", uErr);
    printf(" >>> PARSING BANDWITH : %f MB/s\n",
           (double)Encoded.len / f / 1e6);


    // if(uErr) {
    //    goto Done;
    // }

    // /* Check the results */
    // if(!Compare(&Initial, &Decoded)) {
    //    printf("Example: Spiffy  Decode comparison fail\n");
    // }

    /* Further example of how to calculate the encoded size, then allocate */
    // UsefulBufC EncodedSize;
    // EncodedSize = Encode(&Initial, SizeCalculateUsefulBuf);
    // if(UsefulBuf_IsNULLC(Encoded)) {
    //    printf(" encode size calculation failed\n");
    //    goto Done;
    // }
    // (void)EncodedSize; /* Supress unsed variable warning */
    /* Here malloc could be called to allocate a buffer. Then
     * Encode() can be called a second time to actually
     * encode. (The actual code is not live here to avoid a
     * dependency on malloc()).
     *  UsefulBuf  MallocedBuffer;
     *  MallocedBuffer.len = EncodedSize.len;
     *  MallocedBuffer.ptr = malloc(EncodedSize.len);
     *  Encoded = Encode(&Initial, MallocedBuffer);
     */

    printf("\n");

    return 0;
}
