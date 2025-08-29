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
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_BenchMap_evercddl_uint_BenchMap_evercddl_uint
    it = m.case_Mkmap1;

  while (!BenchMap_is_empty_iterate_map_evercddl_uint_and_evercddl_uint(it)) {
    K___BenchMap_evercddl_uint_BenchMap_evercddl_uint k =
        BenchMap_next_iterate_map_evercddl_uint_and_evercddl_uint(&it);
    // printf("EVERCDDL read key %llu\n", k.fst);
    if (k.fst == key) {
      if (val) {
          *val = k.snd;
      }
      return true;
    }

    if (k.fst > key) {
      return false;
    }
  }
  return false;
}

bool lookup1_no_short(BenchMap_map m, uint64_t key, uint64_t *val) {
  assert (val);
  CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_BenchMap_evercddl_uint_BenchMap_evercddl_uint
  it = m.case_Mkmap1;

  while (!BenchMap_is_empty_iterate_map_evercddl_uint_and_evercddl_uint(it)) {
    K___BenchMap_evercddl_uint_BenchMap_evercddl_uint k =
        BenchMap_next_iterate_map_evercddl_uint_and_evercddl_uint(&it);
    if (k.fst == key) {
      if (val) {
          *val = k.snd;
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

    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = len
    };

    K___BenchMap_evercddl_uint_BenchMap_evercddl_uint *elems =
      (K___BenchMap_evercddl_uint_BenchMap_evercddl_uint*)
      malloc(2 * N * 8);
    for (int i = 0; i < N; i++) {
        elems[i].fst = bigrand ();
        elems[i].snd = bigrand ();
    }

    BenchMap_map m = {
        .tag = BenchMap_Mkmap0,
        .case_Mkmap0 = {
            .elt = elems,
            .len = N,
        }
    };

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
    FStar_Pervasives_Native_option___BenchMap_map___Pulse_Lib_Slice_slice_uint8_t_
      m_opt = TIME(BenchMap_validate_and_parse_map(slice), &f);

    printf(" >>> EVERCDDL VALIDATION TOOK %f us\n", f * 1e6);


    assert (m_opt.tag == FStar_Pervasives_Native_Some);
    assert (m_opt.v.snd.len == BSIZE - size); /* len is whatever remains */
    BenchMap_map m2 = m_opt.v.fst;
    assert (m2.tag == BenchMap_Mkmap1);

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
