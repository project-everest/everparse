#ifndef COMMON_H
#define COMMON_H

#include "COSE_Format.h"
#include "COSE_EverCrypt.h"
#include <fcntl.h>

#define check(cond) { if (!(cond)) { fprintf(stderr, "failed: %s\n", #cond); abort(); } }

typedef Pulse_Lib_Slice_slice__uint8_t bstr;

uint8_t *parse_ed25519_private_key(bstr cose_key);
uint8_t *parse_ed25519_public_key(bstr cose_key);

void write_to_file(const char *fn, const uint8_t *content, size_t content_len);

bstr read_from_file(const char *fn);

#endif
