#include <stdio.h>
#include "BenchArray.h"
#include "BenchArray_common.h"
#include "timing.h"

int main()
{
    size_t len = BSIZE;
    char *buf = malloc(len);
    assert(buf);

    Pulse_Lib_Slice_slice__uint8_t slice = {
        .elt = (uint8_t *) buf,
        .len = len
    };

    float f, f0;

    printf("This test is purely EverCDDL.\n");

    BenchArray_arr m = TIME(build(), &f0);
    printf(" >>> Time to build the array in memory: %fs\n", f0);

    size_t size = TIME(BenchArray_serialize_arr(m, slice), &f);
    if (size == 0) {
        printf("Serialization failed\n");
        return 1;
    }
    printf ("Serialized %zu bytes.\n", size);
    for (int i = 0; i < 20 && i < size; i++) {
        printf("%02x ", slice.elt[i]);
    }
    printf("... \n");


    printf(" >>> SERIALIZATION BANDWIDTH: %f MB/s\n", size / f / 1e6);
    printf(" >>> SERIALIZATION BANDWIDTH (COMBINED): %f MB/s\n", size / (f0 + f) / 1e6);

    /* Validate it, make sure it parses back. */
    FStar_Pervasives_Native_option___BenchArray_arr___Pulse_Lib_Slice_slice_uint8_t_
      m_opt = TIME(BenchArray_validate_and_parse_arr(slice), &f);
    assert (m_opt.tag == FStar_Pervasives_Native_Some);
    assert (m_opt.v.snd.len == BSIZE - size); /* len is whatever remains */

    printf(" >>> PARSING BANDWIDTH: %f MB/s\n", size / f / 1e6);

    return 0;
}
