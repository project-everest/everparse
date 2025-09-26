#include <stdio.h>
#include "timing.h"
#include "tinycbor/src/cbor.h"
#include <assert.h>

extern "C" {
#include "BenchArray.h"
#include "BenchArray_common.h"
}

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

size_t Encode(const BigMap *p, uint8_t* out)
{
    CborEncoder enc, arr;
    cbor_encoder_init(&enc, out, BSIZE, 0);
    cbor_encoder_create_array(&enc, &arr, p->len);
    for (int i = 0; i < p->len; i++) {
        CborEncoder subarr;
        cbor_encoder_create_array(&arr, &subarr, p->len);
        for (int j = 0; j < p->len; j++) {
            cbor_encode_int(&subarr, p->vals[i][j]);
        }
        cbor_encoder_close_container(&arr, &subarr);
    }
    cbor_encoder_close_container(&enc, &arr);
    return cbor_encoder_get_buffer_size(&enc, out);
}

bool Valid(uint8_t* buf, size_t len)
{
    CborParser p;
    CborValue v;

    cbor_parser_init(buf, len, 0, &p, &v);

    CborType type = cbor_value_get_type(&v);
    CborValue arr;

    if (CborNoError != cbor_value_enter_container(&v, &arr)) {
        printf("Failed to enter array\n");
        return false;
    }

    for (int i = 0; i < N; i++) {
        CborValue subarr;
        if (CborNoError != cbor_value_enter_container(&arr, &subarr))
            return false;
        for (int j = 0; j < N; j++) {
            uint64_t t;
            if (CborNoError != cbor_value_get_uint64(&subarr, &t))
                return false;
            cbor_value_advance(&subarr);
        }
        cbor_value_leave_container(&arr, &subarr);
    }

    cbor_value_leave_container(&v, &arr);
    return true;
}

bool Decode(uint8_t* buf, size_t len, uint64_t *sum)
{
    CborParser p;
    CborValue v;

    *sum = 0;

    cbor_parser_init(buf, len, 0, &p, &v);

    CborType type = cbor_value_get_type(&v);
    assert (type == CborArrayType);
    assert (cbor_value_is_array(&v));
    CborValue arr;

    if (CborNoError != cbor_value_enter_container(&v, &arr)) {
        printf("Failed to enter array\n");
        return false;
    }

    for (int i = 0; i < N; i++) {
        CborValue subarr;
        // printf("i %d\n", i);
        if (CborNoError != cbor_value_enter_container(&arr, &subarr))
            return false;
        // printf("entered subarray\n");
        for (int j = 0; j < N; j++) {
            uint64_t t;
            // printf ("i %d j %d\n", i, j);
            if (CborNoError != cbor_value_get_uint64(&subarr, &t))
                return false;
            // printf ("read %d\n", t);
            // assert (t == 0);
            *sum += t;
            cbor_value_advance(&subarr);
        }
        cbor_value_leave_container(&arr, &subarr);
    }

    cbor_value_leave_container(&v, &arr);
    return true;
}

int main()
{
    printf ("This test serializes an array using TinyCBOR, then parses it\n"
            "back both with TinyCBOR and EverCDDL.\n");
    BigMap *init;

    init = (BigMap*)malloc(sizeof(BigMap));
    assert(init);

    uint8_t *buf = (uint8_t*)malloc(100 + 3*N + N * N * sizeof(int));
    fflush(stdout);
    assert(buf);
    // printf("Allocated\n");


    Init(init);

    /* Encode the engine structure. */
    float f;
    size_t len = TIME(Encode(init, buf), &f);
    if (len <= 0) {
        printf("Encode failed\n");
        exit(1);
    }
    printf("Encoded in %zu bytes\n", len);
    printf(" >>> TINYCBOR SERIALIZATION BANDWITH : %f MB/s\n",
           (double)len / f / 1e6);
    for (int i = 0; i < 20 && i < len; i++) {
        printf("%02x ", ((uint8_t *) buf)[i]);
    }
    printf("... \n");

    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = len,
    };

    /* Validate it, make sure it parses back. */
    FStar_Pervasives_Native_option___BenchArray_arr___Pulse_Lib_Slice_slice_uint8_t_
      m_opt = TIME(BenchArray_validate_and_parse_arr(slice), &f);
    assert (m_opt.tag == FStar_Pervasives_Native_Some);
    // printf("Original len %zu\n", len);
    // printf("%zu bytes NOT parsed\n", m_opt.v.snd.len);
    assert (m_opt.v.snd.len == 0); /* len is whatever remains */

    BenchArray_arr m = m_opt.v.fst;

    printf(" >>> VALIDATION BANDWIDTH: %f MB/s\n", len / f / 1e6);

    float f2;
    bool rc = TIME(parse_evercddl(m), &f2);
    if (!rc) {
        printf("Parse failed\n");
        exit(1);
    }
    printf(" >>> EVERCDDL PARSING BANDWIDTH: %f MB/s\n", len / f2 / 1e6);

    printf(" >>> EVERCDDL COMBINED BANDWIDTH: %f MB/s\n", len / (f + f2) / 1e6);

    rc = TIME(Valid(buf, len), &f);
    if (!rc) {
        printf("Validation failed\n");
        exit(1);
    }
    printf(" >>> TINYCBOR VALIDATION BANDWIDTH: %f MB/s\n", len / f / 1e6);

    uint64_t sum;

    rc = TIME(Decode(buf, len, &sum), &f2);
    if (!rc) {
        printf("Decode failed\n");
        exit(1);
    }
    printf(" >>> TINYCBOR PARSING BANDWIDTH: %f MB/s\n", len / f / 1e6);
    printf(" >>> TINYCBOR COMBINED BANDWIDTH: %f MB/s\n", len / (f + f2) / 1e6);

    printf("Done\n");

    return 0;
}
