#include <stdio.h>
#include "qcbor/qcbor_decode.h"
#include "qcbor/qcbor_spiffy_decode.h"
#include "tinycbor/src/cbor.h"
// Prevent clashes between QCBOR and our header :-)
#undef CBOR_MAJOR_TYPE_BYTE_STRING
#undef CBOR_MAJOR_TYPE_TEXT_STRING
#undef CBOR_MAJOR_TYPE_ARRAY
#undef CBOR_MAJOR_TYPE_MAP

#include "timing.h"

extern "C" {
#include "BenchMap.h"
#include "CBORDetAPI.h"

/* See the comment in Test_Basic1.c: the two backends differ in how they name
 * specializations and in the shape they give a tagged union. */
#ifdef EVERPARSE_CUSTARD
#  define SLICE_U8        Pulse_Lib_Slice_slice__uint8
#  define TAG_MKMAP0      BENCHMAP_MKMAP0
#  define TAG_MKMAP1      BENCHMAP_MKMAP1
#  define MK_MAP0(...)    { .tag = TAG_MKMAP0, .val = { .Mkmap0 = __VA_ARGS__ } }
#  define MAP1_IT(m)      ((m).val.Mkmap1)
#  define MAP_ITER_T      CDDL_Pulse_Parse_MapGroup_map_iterator_t__cbor_raw_cbor_map_entry_cbor_raw_iterator_cbor_m
#  define PAIR_UINT       FStar_Pervasives_Native_tuple2__evercddl_uint_evercddl_uint
#  define PAIR_FST        _1
#  define PAIR_SND        _2
#  define OPT_MAP         FStar_Pervasives_Native_option__tuple2_map_slice_uint8
#  define TAG_SOME_MAP    FSTAR_PERVASIVES_NATIVE_SOME__TUPLE2_MAP_SLICE_UINT8
#  define SOME_MAP_V(o)   ((o).val.Some)
#else
#  define SLICE_U8        Pulse_Lib_Slice_slice__uint8_t
#  define TAG_MKMAP0      BenchMap_Mkmap0
#  define TAG_MKMAP1      BenchMap_Mkmap1
#  define MK_MAP0(...)    { .tag = TAG_MKMAP0, .case_Mkmap0 = __VA_ARGS__ }
#  define MAP1_IT(m)      ((m).case_Mkmap1)
#  define MAP_ITER_T      CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_BenchMap_evercddl_uint_BenchMap_evercddl_uint
#  define PAIR_UINT       K___BenchMap_evercddl_uint_BenchMap_evercddl_uint
#  define PAIR_FST        fst
#  define PAIR_SND        snd
#  define OPT_MAP         FStar_Pervasives_Native_option___BenchMap_map___Pulse_Lib_Slice_slice__uint8_t_
#  define TAG_SOME_MAP    FStar_Pervasives_Native_Some
#  define SOME_MAP_V(o)   ((o).v)
#endif
}

#define N 8000 /* number of elements in map */
#define BSIZE (30 + 180 * N) /* size of buffer */
#define K 1000 /* number of keys to look up */
#define LAPS 5 /* how many times the lookup pass is repeated */

uint64_t bigrand() {
    uint64_t r = rand ();
    r = r * RAND_MAX + rand ();
    r = r * RAND_MAX + rand ();
    r = r * RAND_MAX + rand ();
    return r;
}

bool lookup1(BenchMap_map m, uint64_t key, uint64_t *val) {
  assert (val);
  MAP_ITER_T it = MAP1_IT(m);

  while (!BenchMap_is_empty_iterate_map_evercddl_uint_and_evercddl_uint(it)) {
    PAIR_UINT k =
        BenchMap_next_iterate_map_evercddl_uint_and_evercddl_uint(&it);
    // printf("EVERCDDL read key %llu\n", k.PAIR_FST);
    if (k.PAIR_FST == key) {
      if (val) {
          *val = k.PAIR_SND;
      }
      return true;
    }

    if (k.PAIR_FST > key) {
      return false;
    }
  }
  return false;
}

bool lookup1_no_short(BenchMap_map m, uint64_t key, uint64_t *val) {
  assert (val);
  MAP_ITER_T it = MAP1_IT(m);

  while (!BenchMap_is_empty_iterate_map_evercddl_uint_and_evercddl_uint(it)) {
    PAIR_UINT k =
        BenchMap_next_iterate_map_evercddl_uint_and_evercddl_uint(&it);
    if (k.PAIR_FST == key) {
      if (val) {
          *val = k.PAIR_SND;
      }
      return true;
    }
  }
  return false;
}

bool qcbor_lookup1(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
  assert (val);
    QCBORError rc;
    QCBORDecodeContext ctx;
    QCBORItem item;
    QCBORDecode_Init(&ctx, (UsefulBufC){buf, len}, QCBOR_DECODE_MODE_NORMAL);
    QCBORDecode_EnterMap(&ctx, NULL);
    QCBORDecode_GetUInt64InMapN(&ctx, key, val);
    rc = QCBORDecode_GetError(&ctx);
    if (rc == QCBOR_SUCCESS) {
        QCBORDecode_ExitMap(&ctx);
        return true;
    }

    return false;
}

bool evercbor_lookup1(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
  cbor_det_t m = cbor_det_parse(buf, len);
  cbor_det_t k = cbor_det_mk_int64(0, key);
  cbor_det_t cval;
  bool rc = cbor_det_map_get(m, k, &cval);

  if (rc) {
    rc = (cbor_det_major_type(cval) == CBOR_MAJOR_TYPE_UINT64);
    if (rc) {
      *val = cbor_det_read_uint64(cval);
    }
  }

  return rc;
}


bool qcbor_lookup1_no_short(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
    QCBORError rc;
    QCBORDecodeContext ctx;
    QCBORItem item;
    QCBORDecode_Init(&ctx, (UsefulBufC){buf, len}, QCBOR_DECODE_MODE_NORMAL);
    QCBORDecode_EnterMap(&ctx, NULL);
    while ((rc = QCBORDecode_GetNext(&ctx, &item)) != QCBOR_ERR_NO_MORE_ITEMS) {
        uint64_t key2;
        QCBORDecode_GetUInt64(&ctx, &key2);
        if (key2 == key) {
            if (val) {
                QCBORDecode_GetUInt64(&ctx, val);
            }
            QCBORDecode_ExitMap(&ctx);
            return true;
        }
    }
    return false;
}

bool tinycbor_lookup1(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
    CborParser p;
    CborValue v;

    cbor_parser_init(buf, len, 0, &p, &v);

    CborType type = cbor_value_get_type(&v);
    assert (type == CborMapType);
    assert (cbor_value_is_map(&v));
    CborValue map;
    if (CborNoError != cbor_value_enter_container(&v, &map)) {
        printf("Failed to enter map\n");
        return false;
    }

    while (!cbor_value_at_end(&map)) {
        uint64_t key_val, val_val;
        // if (CborNoError != cbor_value_get_map_key(&map, &key_val)) {
        //     printf("Failed to get map key\n");
        //     return false;
        // }
        // if (CborNoError != cbor_value_get_map_value(&map, &val_val)) {
        //     printf("Failed to get map value\n");
        //     return false;
        // }
        cbor_value_get_uint64(&map, &key_val);
        cbor_value_advance(&map);
        cbor_value_get_uint64(&map, &val_val);
        cbor_value_advance(&map);

        // printf("TinyCBOR read key %llu\n", key_val);
        // printf("TinyCBOR read val %llu\n", val_val);

        if (key_val == key) {
            if (val)
                *val = val_val;
            return true;
        } else if (key_val > key) {
            return false;
        }
    }

    // cannot use cbor_value_map_find_value, it only works
    // for text string keys

    return false;
}

bool tinycbor_lookup1_no_short(uint8_t *buf, size_t len, uint64_t key, uint64_t *val) {
    return false;
}

int main()
{
    printf("This test benchmarks lookups in a CBOR map with EverCDDL,\n"
           "EverCBOR (i.e. without the CDDL layer), QCBOR and TinyCBOR.\n"
           "The maps are filled with big random numbers, so most lookups miss.\n");

    size_t len = BSIZE;
    uint8_t *buf = (uint8_t*)malloc(len);
    float f;
    assert(buf);

    SLICE_U8 slice = {
        .elt = (uint8_t *) buf,
        .len = len
    };

    PAIR_UINT *elems =
      (PAIR_UINT*)
      malloc(2 * N * 8);
    for (int i = 0; i < N; i++) {
        elems[i].PAIR_FST = bigrand ();
        elems[i].PAIR_SND = bigrand ();
    }

    BenchMap_map m = MK_MAP0({ .elt = elems, .len = N });

    size_t size = TIME(BenchMap_serialize_map(m, slice), &f);
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

    /* Validate it, make sure it parses back. */
    OPT_MAP m_opt = TIME(BenchMap_validate_and_parse_map(slice), &f);

    printf(" >>> EVERCDDL VALIDATION TOOK %f us\n", f * 1e6);


    assert (m_opt.tag == TAG_SOME_MAP);
    assert (SOME_MAP_V(m_opt).PAIR_SND.len == BSIZE - size); /* len is whatever remains */
    BenchMap_map m2 = SOME_MAP_V(m_opt).PAIR_FST;
    assert (m2.tag == TAG_MKMAP1);

    uint64_t keys[K];
    for (int i = 0; i < K; i++)
        keys[i] = bigrand ();

    int nfound = 0, ncheck;

    /* Lookup via the CDDL iterator API. */
    TIME_void(
    ({
        for (int lap = 0; lap < LAPS; lap++) {
            for (int i = 0; i < K; i++) {
                uint64_t key = keys[i];
                uint64_t val;
                nfound += lookup1(m2, key, &val);
            }
        }
    }), &f);
    printf(" NFOUND = %d\n", nfound);
    printf(" >>> EVERCDDL LOOKUP: %f us\n", f * 1e6/ K / LAPS);

    /* Lookup via the CDDL iterator API, but do not stop when we've reached
    a key greater than the one we're looking for (i.e., we don't take advantage
    of the sorting to make it faster). */
    ncheck = 0;
    TIME_void(
    ({
        for (int lap = 0; lap < LAPS; lap++) {
            for (int i = 0; i < K; i++) {
                uint64_t key = keys[i];
                uint64_t val;
                ncheck += lookup1_no_short(m2, key, &val);
            }
        }
    }), &f);
    assert (ncheck == nfound);

    printf(" >>> EVERCDDL LOOKUP (NO SHORT): %f us\n", f * 1e6 / K / LAPS);

    /* Lookup via the pure CBOR API. This is much faster. */
    ncheck = 0;
    TIME_void(
    ({
        for (int lap = 0; lap < LAPS; lap++) {
            for (int i = 0; i < K; i++) {
                uint64_t key = keys[i];
                uint64_t val;
                ncheck += evercbor_lookup1(buf, len, key, &val);
            }
        }
    }), &f);
    printf (" >>> EVERCBOR LOOKUP: %f us\n", f * 1e6 / K / LAPS);
    assert (ncheck == nfound);

    ncheck = 0;
    TIME_void(
    ({
        for (int lap = 0; lap < LAPS; lap++) {
            for (int i = 0; i < K; i++) {
                uint64_t key = keys[i];
                uint64_t val;
                ncheck += qcbor_lookup1(buf, len, key, &val);
            }
        }
    }), &f);
    printf (" >>> QCBOR LOOKUP: %f us\n", f * 1e6 / K / LAPS);
    assert (ncheck == nfound);

    ncheck = 0;
    TIME_void(
    ({
        for (int lap = 0; lap < LAPS; lap++) {
            for (int i = 0; i < K; i++) {
                uint64_t key = keys[i];
                ncheck += tinycbor_lookup1(buf, len, key, NULL);
            }
        }
    }), &f);
    printf (" >>> TINYCBOR lOOKUP: %f us\n", f * 1e6 / K / LAPS);
    assert (ncheck == nfound);

    // ncheck = 0;
    // TIME_void(
    // ({
    //     for (int lap = 0; lap < LAPS; lap++) {
    //         for (int i = 0; i < K; i++) {
    //             uint64_t key = keys[i];
    //             ncheck += tinycbor_lookup1_no_short(buf, len, key, NULL);
    //         }
    //     }
    // }), &f);
    // printf (" >>> TINYCBOR LOOKUP (NO SHORT): %f us\n", f * 1e6 / K / LAPS);
    // assert (ncheck == nfound);

    return 0;
}
