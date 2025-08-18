#include <stdio.h>
#include "Basic2.h"

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

    uint64_t *other_elems = malloc(2 * sizeof other_elems[0]);
    other_elems[0] = 42;

    Basic2_map18 m = {
        .intkey18 = 1818,
        ._x0 = {
                .tag = FStar_Pervasives_Inl,
                .case_Inl = {
                             .len = 1,
                             .elt = other_elems,
                             }
                }
    };

    size_t size = Basic2_serialize_map18(m, slice);
    if (size == 0) {
        printf("Serialization failed\n");
        return 1;
    }

    /* Validate it, make sure it parses back. */
    FStar_Pervasives_Native_option___Basic2_map18___Pulse_Lib_Slice_slice_uint8_t_
      m_opt = Basic2_validate_and_parse_map18(slice);
    assert (m_opt.tag == FStar_Pervasives_Native_Some);
    assert (m_opt.v.fst.intkey18 == m.intkey18);
    assert (m_opt.v.snd.len == SIZE - size); /* len is whatever remains */

    /* We can also parse it back as a map42. No check is performed here:
    the 18 or 42 are just names, not keys. */
    FStar_Pervasives_Native_option___Basic2_map42___Pulse_Lib_Slice_slice_uint8_t_
      m2_opt = Basic2_validate_and_parse_map42(slice);
    assert (m2_opt.tag == FStar_Pervasives_Native_Some);
    assert (m2_opt.v.fst.intkey42 == 1818);
    assert (m2_opt.v.snd.len == SIZE - size); /* len is whatever remains */

    printf("ok\n");

    return 0;
}
