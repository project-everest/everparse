

#ifndef internal_COSE_Format_H
#define internal_COSE_Format_H

#include "krmllib.h"

#include "../COSE_Format.h"
#include "CBORDetAbstract.h"

size_t Pulse_Lib_Slice_len__uint8_t(Pulse_Lib_Slice_slice__uint8_t s);

uint8_t *Pulse_Lib_Slice_slice_to_arrayptr_intro__uint8_t(Pulse_Lib_Slice_slice__uint8_t s);

Pulse_Lib_Slice_slice__uint8_t Pulse_Lib_Slice_from_array__uint8_t(uint8_t *a, size_t alen);


#define internal_COSE_Format_H_DEFINED
#endif /* internal_COSE_Format_H */
