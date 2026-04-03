#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

/* LowParseTestLib.Pulse assumed functions */

void LowParseTestLib_Pulse_print_string(const char *s) {
    printf("%s", s);
    fflush(stdout);
}

void LowParseTestLib_Pulse_exit_failure(void) {
    exit(1);
}

/* File loading utility: reads a file into a malloc'd buffer, returns slice-like pair */
typedef struct {
    uint8_t *ptr;
    size_t len;
} LowParseTestLib_Pulse_file_data_t;

LowParseTestLib_Pulse_file_data_t LowParseTestLib_Pulse_load_file(const char *filename) {
    LowParseTestLib_Pulse_file_data_t result = { NULL, 0 };
    FILE *fp = fopen(filename, "rb");
    if (!fp) {
        fprintf(stderr, "Failed to open file '%s': %s\n", filename, strerror(errno));
        exit(1);
    }
    fseek(fp, 0L, SEEK_END);
    long filesize = ftell(fp);
    fseek(fp, 0L, SEEK_SET);
    if (filesize < 0) {
        fprintf(stderr, "Failed to get size of '%s'\n", filename);
        fclose(fp);
        exit(1);
    }
    result.ptr = (uint8_t *)malloc((size_t)filesize);
    if (!result.ptr) {
        fprintf(stderr, "Out of memory reading '%s'\n", filename);
        fclose(fp);
        exit(1);
    }
    if (fread(result.ptr, 1, (size_t)filesize, fp) != (size_t)filesize) {
        fprintf(stderr, "Error reading '%s'\n", filename);
        free(result.ptr);
        fclose(fp);
        exit(1);
    }
    fclose(fp);
    result.len = (size_t)filesize;
    return result;
}
