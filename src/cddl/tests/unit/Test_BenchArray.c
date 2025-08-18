#include <stdio.h>
#include "BenchArray.h"
#include "BenchArray_common.h"
#include "timing.h"

int main()
{
    size_t len = BSIZE;
    char *buf = malloc(len);
    assert(buf);
    printf("testing\n");

    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = len
    };

    float f, f0;

    BenchArray_map m = TIME(build(), &f0);

    size_t size = TIME(BenchArray_serialize_map(m, slice), &f);
    if (size == 0) {
        printf("Serialization failed\n");
        return 1;
    }
    printf ("Serialized %zu bytes\n", size);
    for (int i = 0; i < 20 && i < size; i++) {
        printf("%02x ", slice.elt[i]);
    }
    printf("\n");

    printf(" >>> SERIALIZATION BANDWIDTH: %f MB/s\n", size / f / 1e6);
    printf(" >>> SERIALIZATION BANDWIDTH (COMBINED): %f MB/s\n", size / (f0 + f) / 1e6);

    /* Validate it, make sure it parses back. */
    FStar_Pervasives_Native_option___BenchArray_map___Pulse_Lib_Slice_slice_uint8_t_
      m_opt = TIME(BenchArray_validate_and_parse_map(slice), &f);
    assert (m_opt.tag == FStar_Pervasives_Native_Some);
    //assert (m_opt.v.fst.intkey42 == m.intkey42);
    assert (m_opt.v.snd.len == BSIZE - size); /* len is whatever remains */

    // /* We can also parse it back as a map42. No check is performed here:
    // the 18 or 42 are just names, not keys. */
    // FStar_Pervasives_Native_option___BenchArray_map42___Pulse_Lib_Slice_slice_uint8_t_
    //   m2_opt = BenchArray_validate_and_parse_map42(slice);
    // assert (m2_opt.tag == FStar_Pervasives_Native_Some);
    // assert (m2_opt.v.fst.intkey42 == 1818);
    // assert (m2_opt.v.snd.len == BSIZE - size); /* len is whatever remains */

    printf(" >>> PARSING BANDWIDTH: %f MB/s\n", size / f / 1e6);

    printf("ok\n");

    return 0;
}
