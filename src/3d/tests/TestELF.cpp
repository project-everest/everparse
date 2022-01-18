#include<stdint.h>
#include<fstream>
#include<iostream>
#include<vector>
#include<sys/stat.h>

#include "ELFWrapper.h"

using namespace std;

void ELFEverParseError (const char *struct_name, const char *field_name, const char *reason)
{
  cout << "Validation failed: " << struct_name << ":" << field_name << ":" << reason
       << endl;
}

int main (int argc, char **argv)
{
  if (argc < 2) {
    cout << "Usage: ./elf-test <name of the ELF file>" << endl;
    exit (1);
  }
  const char *elf_file_name = argv[1];
  ifstream file (argv[1], std::ios::binary | std::ios::ate);
  streamsize sz = file.tellg ();
  file.seekg (0, std::ios::beg);

  vector<char> buf (sz);
  if (file.read (buf.data (), sz)) {
    cout << "file read, sz:" << sz << endl;
    ElfCheckElf(sz, (uint8_t *) buf.data (), sz);
  }
  return 0;
}
