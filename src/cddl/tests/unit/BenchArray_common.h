#ifndef __BENCH_ARRAY_COMMON
#define __BENCH_ARRAY_COMMON 1

#define N 10000
#define BSIZE (30 + 3*N + (N*N)) /* size of buffer */

BenchArray_arr build() {
    float f;

    BenchArray_subarr *subarrs =
      (BenchArray_subarr *)
      malloc(N * sizeof subarrs[0]);
    for (int i = 0; i < N; i++) {
        uint64_t *elems = (uint64_t*) malloc(N * sizeof elems[0]);
        for (int i = 0; i < N; i++)
            elems[i] = 0;

        BenchArray_subarr subarr = {
                    .tag = BenchArray_Mksubarr0,
                    .case_Mksubarr0 = {
                                .elt = elems,
                                .len = N,
                                }
        };
        subarrs[i] = subarr;
    }

    BenchArray_arr m = {
                .tag = BenchArray_Mkarr0,
                .case_Mkarr0 = {
                             .elt = subarrs,
                             .len = N,
                             }
    };
    return m;
}


// Read the actual numbers out of a validated array
bool parse_evercddl(BenchArray_arr m)
{
    assert (m.tag == BenchArray_Mkarr1);
    CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_BenchArray_aux_env4_type_1
      it = m.case_Mkarr1;

    for (int i = 0; i < N; i++) {
        BenchArray_subarr subarr = BenchArray_next_iterate_array_aux_env4_type_1(&it);
        assert (subarr.tag == BenchArray_Mksubarr1);
        CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_BenchArray_aux_env3_type_1
          it2 = subarr.case_Mksubarr1;
        for (int j = 0; j < N; j++) {
            BenchArray_evercddl_uint t = BenchArray_next_iterate_array_aux_env3_type_1(&it2);
            assert (t == 0);
        }
    }

    return true;
}
#endif
