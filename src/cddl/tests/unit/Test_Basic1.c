#include <stdio.h>
#include <assert.h>
#include "Basic1.h"

/* The two extraction backends publish this module's types under different
 * names, and tagged unions under a different shape (karamel hoists a
 * one-payload-constructor union's field to top level and names a multi-arm
 * union's member `case_<Ctor>'; Custard nests every arm under `val' and names
 * the member after the specialized constructor).  Collecting the difference
 * here keeps the body of the test identical for both. */
#ifdef EVERPARSE_CUSTARD
#  define SLICE_U8    Pulse_Lib_Slice_slice__uint8
#  define PAIR_UINT    FStar_Pervasives_Native_tuple2__evercddl_uint_evercddl_uint
#  define PAIR_FST     _1
#  define PAIR_SND     _2
#  define EITHER18    FStar_Pervasives_either__slice_tuple2_evercddl_uint_evercddl_uint_map_ite
#  define TAG_INL     FSTAR_PERVASIVES_INL__SLICE_TUPLE2_EVERCDDL_UINT_EVERCDDL_UINT_MAP_ITE
#  define MK_INL(...) { .tag = TAG_INL, \
     .val = { .Inl = __VA_ARGS__ } }
#  define OPT18       FStar_Pervasives_Native_option__tuple2_map18_slice_uint8
#  define OPT42       FStar_Pervasives_Native_option__tuple2_map42_slice_uint8
#  define TAG_SOME18  FSTAR_PERVASIVES_NATIVE_SOME__TUPLE2_MAP18_SLICE_UINT8
#  define TAG_SOME42  FSTAR_PERVASIVES_NATIVE_SOME__TUPLE2_MAP42_SLICE_UINT8
#  define SOME_V(o)   ((o).val.Some)
#else
#  define SLICE_U8    Pulse_Lib_Slice_slice__uint8_t
#  define PAIR_UINT    K___Basic1_evercddl_uint_Basic1_evercddl_uint
#  define PAIR_FST     fst
#  define PAIR_SND     snd
#  define EITHER18    FStar_Pervasives_either__CDDL_Pulse_Types_slice___Basic1_evercddl_uint___Basic1_evercddl_uint__CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_API_Det_Type_cbor_det_t_CBOR_Pulse_API_Det_Type_cbor_det_map_entry_t_CBOR_Pulse_API_Det_Type_cbor_det_map_iterator_t_Basic1_evercddl_uint_Basic1_evercddl_uint
#  define TAG_INL     FStar_Pervasives_Inl
#  define MK_INL(...) { .tag = TAG_INL, .case_Inl = __VA_ARGS__ }
#  define OPT18       FStar_Pervasives_Native_option___Basic1_map18___Pulse_Lib_Slice_slice__uint8_t_
#  define OPT42       FStar_Pervasives_Native_option___Basic1_map42___Pulse_Lib_Slice_slice__uint8_t_
#  define TAG_SOME18  FStar_Pervasives_Native_Some
#  define TAG_SOME42  FStar_Pervasives_Native_Some
#  define SOME_V(o)   ((o).v)
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

    PAIR_UINT *other_elems = malloc(2 * sizeof other_elems[0]);
    other_elems[0].PAIR_FST = 42;
    other_elems[0].PAIR_SND = 4242;

    Basic1_map18 m = {
        .intkey18 = 1818,
        ._x0 = MK_INL({ .len = 1, .elt = other_elems })
    };

    size_t size = Basic1_serialize_map18(m, slice);
    if (size == 0) {
        printf("Serialization failed\n");
        return 1;
    }

    /* Validate it, make sure it parses back. */
    OPT18 m_opt = Basic1_validate_and_parse_map18(slice);
    assert (m_opt.tag == TAG_SOME18);
    assert (SOME_V(m_opt).PAIR_FST.intkey18 == m.intkey18);
    assert (SOME_V(m_opt).PAIR_SND.len == SIZE - size); /* len is whatever remains */

    /* We can also parse it back as a map42, given that we added a pair with key
    42 in the other_elems above. The intkey42 is mapped to 4242 as expected. */
    OPT42 m2_opt = Basic1_validate_and_parse_map42(slice);
    assert (m2_opt.tag == TAG_SOME42);
    assert (SOME_V(m2_opt).PAIR_FST.intkey42 == 4242);
    assert (SOME_V(m2_opt).PAIR_SND.len == SIZE - size); /* len is whatever remains */

    printf("ok\n");

    return 0;
}
