#include <stdio.h>
#include <assert.h>
#include "Basic1.h"

#define SIZE (1<<20)

int main()
{
    printf("testing\n");

    size_t len = SIZE;
    char *buf = malloc(len);
    assert(buf);

    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = len
    };

    FStar_Pervasives_Native_tuple2__uint64_t_uint64_t *other_elems =
      malloc(2 * sizeof other_elems[0]);
    other_elems[0]._1 = 42;
    other_elems[0]._2 = 4242;

    Basic1_map18 m = {
        .intkey18 = 1818,
        ._x0 = {
                .tag = FStar_Pervasives_Inl,
                .case_Inl = {
                             .len = 1,
                             .elt = other_elems,
                             }
                }
    };

    size_t size = Basic1_serialize_map18(m, slice);
    if (size == 0) {
        printf("Serialization failed\n");
        return 1;
    }

    /* Validate it, make sure it parses back. */
    FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Basic1_map18_Pulse_Lib_Slice_slice__uint8_t
      m_opt = Basic1_validate_and_parse_map18(slice);
    assert (m_opt.tag == FStar_Pervasives_Native_Some);
    assert (m_opt.v._1.intkey18 == m.intkey18);
    assert (m_opt.v._2.len == SIZE - size); /* len is whatever remains */

    /* We can also parse it back as a map42, given that we added a pair with key
    42 in the other_elems above. The intkey42 is mapped to 4242 as expected. */
    FStar_Pervasives_Native_option__FStar_Pervasives_Native_tuple2__Basic1_map42_Pulse_Lib_Slice_slice__uint8_t
      m2_opt = Basic1_validate_and_parse_map42(slice);
    assert (m2_opt.tag == FStar_Pervasives_Native_Some);
    assert (m2_opt.v._1.intkey42 == 4242);
    assert (m2_opt.v._2.len == SIZE - size); /* len is whatever remains */

    printf("ok\n");

    return 0;
}
