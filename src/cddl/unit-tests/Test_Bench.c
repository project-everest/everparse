#include <stdio.h>
#include "Bench.h"
#include "timing.h"

#define BSIZE (10 + (1<<28)) /* size of buffer */
#define NELEMS (1<<28) /* more elements for test */

int main()
{
    printf("testing\n");

    size_t len = BSIZE;
    char *buf = malloc(len);
    assert(buf);

    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = len
    };

    uint64_t *other_elems = malloc(NELEMS * sizeof other_elems[0]);
    for (int i = 0; i < NELEMS; i++) {
        other_elems[i] = 0;
    }

    Bench_evercddl_map_pretty m = {
        .intkey42 = 1818,
        ._x0 = {
                .tag = FStar_Pervasives_Inl,
                .case_Inl = {
                             .len = NELEMS,
                             .elt = other_elems,
                             }
                }
    };

    size_t size = TIME(Bench_serialize_map(m, slice), NULL);
    if (size == 0) {
        printf("Serialization failed\n");
        return 1;
    }
    printf ("Serialized %zu bytes\n", size);
    for (int i = 0; i < 20; i++) {
        printf("%02x ", slice.elt[i]);
    }

    /* Validate it, make sure it parses back. */
    FStar_Pervasives_Native_option___Bench_evercddl_map_pretty___Pulse_Lib_Slice_slice_uint8_t_
      m_opt = TIME(Bench_validate_and_parse_map(slice), NULL);
    assert (m_opt.tag == FStar_Pervasives_Native_Some);
    assert (m_opt.v.fst.intkey42 == m.intkey42);
    assert (m_opt.v.snd.len == BSIZE - size); /* len is whatever remains */

    // /* We can also parse it back as a map42. No check is performed here:
    // the 18 or 42 are just names, not keys. */
    // FStar_Pervasives_Native_option___Bench_evercddl_map42_pretty___Pulse_Lib_Slice_slice_uint8_t_
    //   m2_opt = Bench_validate_and_parse_map42(slice);
    // assert (m2_opt.tag == FStar_Pervasives_Native_Some);
    // assert (m2_opt.v.fst.intkey42 == 1818);
    // assert (m2_opt.v.snd.len == BSIZE - size); /* len is whatever remains */

    printf("ok\n");

    return 0;
}
