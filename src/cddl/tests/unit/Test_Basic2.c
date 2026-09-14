#include <stdio.h>
#include <assert.h>
#include "Basic2.h"

/* See the comment in Test_Basic1.c: the two backends differ in how they name
 * specializations and in the shape they give a tagged union. */
#ifdef EVERPARSE_CUSTARD
#  define SLICE_U8    Pulse_Lib_Slice_slice__uint8
#  define TAG_INL     FSTAR_PERVASIVES_INL__SLICE_AUX_ENV3_TYPE_1_ARRAY_ITERATOR_T_CBOR_RAW_
#  define MK_INL(...) { .tag = TAG_INL, \
     .val = { .FStar_Pervasives_Inl__slice_aux_env3_type_1_array_iterator_t_cbor_raw_ = { .v = __VA_ARGS__ } } }
#  define OPT18       FStar_Pervasives_Native_option__tuple2_map18_slice_uint8
#  define OPT42       FStar_Pervasives_Native_option__tuple2_map42_slice_uint8
#  define TAG_SOME18  FSTAR_PERVASIVES_NATIVE_SOME__TUPLE2_MAP18_SLICE_UINT8
#  define TAG_SOME42  FSTAR_PERVASIVES_NATIVE_SOME__TUPLE2_MAP42_SLICE_UINT8
#  define SOME18_V(o) ((o).val.FStar_Pervasives_Native_Some__tuple2_map18_slice_uint8.v)
#  define SOME42_V(o) ((o).val.FStar_Pervasives_Native_Some__tuple2_map42_slice_uint8.v)
#  define PAIR_FST    _1
#  define PAIR_SND    _2
#else
#  define SLICE_U8    Pulse_Lib_Slice_slice__uint8_t
#  define TAG_INL     FStar_Pervasives_Inl
#  define MK_INL(...) { .tag = TAG_INL, .case_Inl = __VA_ARGS__ }
#  define OPT18       FStar_Pervasives_Native_option___Basic2_map18___Pulse_Lib_Slice_slice__uint8_t_
#  define OPT42       FStar_Pervasives_Native_option___Basic2_map42___Pulse_Lib_Slice_slice__uint8_t_
#  define TAG_SOME18  FStar_Pervasives_Native_Some
#  define TAG_SOME42  FStar_Pervasives_Native_Some
#  define SOME18_V(o) ((o).v)
#  define SOME42_V(o) ((o).v)
#  define PAIR_FST    fst
#  define PAIR_SND    snd
#endif

#define SIZE (1<<20)

int main()
{
    printf("testing\n");

    size_t len = SIZE;
    char *buf = malloc(len);
    assert(buf);

    SLICE_U8 slice = {
        .elt = (uint8_t *) buf,
        .len = len
    };

    uint64_t *other_elems = malloc(2 * sizeof other_elems[0]);
    other_elems[0] = 42;

    Basic2_map18 m = {
        .intkey18 = 1818,
        ._x0 = MK_INL({ .len = 1, .elt = other_elems })
    };

    size_t size = Basic2_serialize_map18(m, slice);
    if (size == 0) {
        printf("Serialization failed\n");
        return 1;
    }

    /* Validate it, make sure it parses back. */
    OPT18 m_opt = Basic2_validate_and_parse_map18(slice);
    assert (m_opt.tag == TAG_SOME18);
    assert (SOME18_V(m_opt).PAIR_FST.intkey18 == m.intkey18);
    assert (SOME18_V(m_opt).PAIR_SND.len == SIZE - size); /* len is whatever remains */

    /* We can also parse it back as a map42. No check is performed here:
    the 18 or 42 are just names, not keys. */
    OPT42 m2_opt = Basic2_validate_and_parse_map42(slice);
    assert (m2_opt.tag == TAG_SOME42);
    assert (SOME42_V(m2_opt).PAIR_FST.intkey42 == 1818);
    assert (SOME42_V(m2_opt).PAIR_SND.len == SIZE - size); /* len is whatever remains */

    printf("ok\n");

    return 0;
}
