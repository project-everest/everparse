#ifndef __LOWPARSE_TESTLIB_AUX_H
#define __LOWPARSE_TESTLIB_AUX_H

#include <kremlib.h>

#include <stdlib.h>
#include <stdio.h>
#include <errno.h>

void LowParse_TestLib_Aux_load_file(const char * x0, uint8_t** buf, int32_t * len)
{
    FILE *fp = fopen(x0, "rb");
    if (!fp) {
        KRML_HOST_EPRINTF("Failed to open input data file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    if (fseek(fp, 0L, SEEK_END) != 0) {
        KRML_HOST_EPRINTF("Failed to seek to end of file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    long filesize = ftell(fp);
    if (filesize < 0) {
        KRML_HOST_EPRINTF("Failed get length of file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    if (fseek(fp, 0L, SEEK_SET) != 0) {
        KRML_HOST_EPRINTF("Failed to seek to start of file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    char *buffer = (char*)KRML_HOST_MALLOC(filesize);
    if (!buffer) {
        KRML_HOST_EPRINTF("Out of memory reading file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    if (fread(buffer, sizeof(char), filesize, fp) == 0) {
        KRML_HOST_EPRINTF("Error reading file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    fclose(fp);
    *buf = (uint8_t*) buffer;
    *len = (int32_t) filesize;
}


#endif
