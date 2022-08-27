#include "Test.h"
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <stdint.h>
#include <unistd.h>

int test_read () {
  char * filename = "input.dat";
  int file = open(filename, O_RDONLY);
  if (file == -1)
    return 2;
  struct stat statbuf;
  if (fstat(file, &statbuf)) {
    close(file);
    return 3;
  }
  off_t len = statbuf.st_size;
  if (len > 2147483647) {
    close(file);
    return 4;
  }
  uint8_t * b = (uint8_t *)
    mmap(NULL, len, PROT_READ, MAP_PRIVATE, file, 0);
  if (b == NULL) {
    close(file);
    return 5;
  }
  full_test_pretty_print(b, len);
  munmap(b, len);
  close(file);
  return 0;
}

#define output_length 9

int test_write () {
  uint8_t dummy_input = 42;
  uint8_t output[output_length] = {0};
  uint32_t output_sz = output_length;
  if (! (extract_test_write4 (output, &output_sz, &dummy_input)))
    return 6;
  if (output_sz)
    return 7;
  char * filename = "output.dat";
  int file = open(filename, O_CREAT | O_WRONLY | O_TRUNC, S_IWUSR | S_IRUSR);
  if (file == -1)
    return 8;
  if (write(file, output, output_length) != output_length)
    return 9;
  close(file);
  return 0;
}

int main (int argc, char* argv[]) {
  int ret = test_write ();
  if (ret)
    return ret;
  return (test_read ());
}
