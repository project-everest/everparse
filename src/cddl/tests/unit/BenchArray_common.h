#ifndef __BENCH_ARRAY_COMMON
#define __BENCH_ARRAY_COMMON 1

#define N 10000
#define BSIZE (30 + 3*N + (N*N)) /* size of buffer */

/* See the comment in Test_Basic1.c: the two backends differ in how they name
 * specializations and in the shape they give a tagged union.  karamel names a
 * union member `case_<Ctor>' and makes the payload of a one-argument
 * constructor the member itself; Custard nests every arm under `val', names
 * the member after the specialized constructor, and wraps the payload in a
 * struct whose field is the F* one (here `_x0'). */
#ifdef EVERPARSE_CUSTARD
#  define TAG_MKARR0     BENCHARRAY_MKARR0
#  define TAG_MKARR1     BENCHARRAY_MKARR1
#  define TAG_MKSUBARR0  BENCHARRAY_MKSUBARR0
#  define TAG_MKSUBARR1  BENCHARRAY_MKSUBARR1
#  define MK_ARR0(...)     { .tag = TAG_MKARR0, .val = { .BenchArray_Mkarr0 = { ._x0 = __VA_ARGS__ } } }
#  define MK_SUBARR0(...)  { .tag = TAG_MKSUBARR0, .val = { .BenchArray_Mksubarr0 = { ._x0 = __VA_ARGS__ } } }
#  define ARR1_IT(m)     ((m).val.BenchArray_Mkarr1._x0)
#  define SUBARR1_IT(m)  ((m).val.BenchArray_Mksubarr1._x0)
#  define SLICE_U8       Pulse_Lib_Slice_slice__uint8
#  define OPT_ARR        FStar_Pervasives_Native_option__tuple2_arr_slice_uint8
#  define TAG_SOME_ARR   FSTAR_PERVASIVES_NATIVE_SOME__TUPLE2_ARR_SLICE_UINT8
#  define SOME_ARR_V(o)  ((o).val.FStar_Pervasives_Native_Some__tuple2_arr_slice_uint8.v)
#  define PAIR_FST       _1
#  define PAIR_SND       _2
#  define ARR_ITER_T     CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__cbor_raw_iterator_cbor_raw_aux_env4_type_1
#  define SUBARR_ITER_T  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__cbor_raw_iterator_cbor_raw_aux_env3_type_1
#else
#  define TAG_MKARR0     BenchArray_Mkarr0
#  define TAG_MKARR1     BenchArray_Mkarr1
#  define TAG_MKSUBARR0  BenchArray_Mksubarr0
#  define TAG_MKSUBARR1  BenchArray_Mksubarr1
#  define MK_ARR0(...)     { .tag = TAG_MKARR0, .case_Mkarr0 = __VA_ARGS__ }
#  define MK_SUBARR0(...)  { .tag = TAG_MKSUBARR0, .case_Mksubarr0 = __VA_ARGS__ }
#  define ARR1_IT(m)     ((m).case_Mkarr1)
#  define SUBARR1_IT(m)  ((m).case_Mksubarr1)
#  define SLICE_U8       Pulse_Lib_Slice_slice__uint8_t
#  define OPT_ARR        FStar_Pervasives_Native_option___BenchArray_arr___Pulse_Lib_Slice_slice__uint8_t_
#  define TAG_SOME_ARR   FStar_Pervasives_Native_Some
#  define SOME_ARR_V(o)  ((o).v)
#  define PAIR_FST       fst
#  define PAIR_SND       snd
#  define ARR_ITER_T     CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_BenchArray_aux_env4_type_1
#  define SUBARR_ITER_T  CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_array_iterator_t_BenchArray_aux_env3_type_1
#endif

BenchArray_arr build() {
    float f;

    BenchArray_subarr *subarrs =
      (BenchArray_subarr *)
      malloc(N * sizeof subarrs[0]);
    for (int i = 0; i < N; i++) {
        uint64_t *elems = (uint64_t*) malloc(N * sizeof elems[0]);
        for (int i = 0; i < N; i++)
            elems[i] = 0;

        BenchArray_subarr subarr = MK_SUBARR0({ .elt = elems, .len = N });
        subarrs[i] = subarr;
    }

    BenchArray_arr m = MK_ARR0({ .elt = subarrs, .len = N });
    return m;
}


// Read the actual numbers out of a validated array
bool parse_evercddl(BenchArray_arr m)
{
    assert (m.tag == TAG_MKARR1);
    ARR_ITER_T it = ARR1_IT(m);

    for (int i = 0; i < N; i++) {
        BenchArray_subarr subarr = BenchArray_next_iterate_array_aux_env4_type_1(&it);
        assert (subarr.tag == TAG_MKSUBARR1);
        SUBARR_ITER_T it2 = SUBARR1_IT(subarr);
        for (int j = 0; j < N; j++) {
            BenchArray_evercddl_uint t = BenchArray_next_iterate_array_aux_env3_type_1(&it2);
            assert (t == 0);
        }
    }

    return true;
}
#endif
