#include "Test.h"
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <stdint.h>
#include <unistd.h>

int main (int argc, char* argv[]) {
  if (argc < 2)
    return 1;
  char * filename = argv[1];
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
