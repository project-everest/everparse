#ifndef __BENCH_ARRAY_COMMON
#define __BENCH_ARRAY_COMMON 1

#define N 10000
#define BSIZE (30 + 3*N + (N*N)) /* size of buffer */

BenchArray_map build() {
    float f;

    BenchArray_submap *submaps =
      (BenchArray_submap *)
      malloc(N * sizeof submaps[0]);
    for (int i = 0; i < N; i++) {
        uint64_t *elems = (uint64_t*) malloc(N * sizeof elems[0]);
        for (int i = 0; i < N; i++)
            elems[i] = 0;

        BenchArray_submap submap = {
                    .tag = BenchArray_Mksubmap0,
                    .case_Mksubmap0 = {
                                .elt = elems,
                                .len = N,
                                }
        };
        submaps[i] = submap;
    }

    BenchArray_map m = {
                .tag = BenchArray_Mkmap0,
                .case_Mkmap0 = {
                             .elt = submaps,
                             .len = N,
                             }
    };
    return m;
}


// Read the actual numbers out of a validated array
bool parse_evercddl(BenchArray_map m)
{
    assert (m.tag == BenchArray_Mkmap1);
    CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_BenchArray_aux_env4_type_1
      it = m.case_Mkmap1;

    for (int i = 0; i < N; i++) {
        BenchArray_submap submap = BenchArray_next_iterate_array_aux_env4_type_1(&it);
        assert (submap.tag == BenchArray_Mksubmap1);
        CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_BenchArray_aux_env3_type_1
          it2 = submap.case_Mksubmap1;
        for (int j = 0; j < N; j++) {
            BenchArray_evercddl_uint t = BenchArray_next_iterate_array_aux_env3_type_1(&it2);
            assert (t == 0);
        }
    }

    return true;
}
#endif
