/*
   Copyright 2023, 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/


#ifndef __internal_CBOR_H
#define __internal_CBOR_H

#include "krmllib.h"

#include "../CBOR.h"

typedef struct LowParse_SteelST_L2ROutput_t_s
{
  uint8_t **ptr;
  size_t *len;
}
LowParse_SteelST_L2ROutput_t;

size_t cbor_size_comp(cbor c, size_t sz, bool *perr);

uint8_t *cbor_l2r_write(cbor c, LowParse_SteelST_L2ROutput_t out);

cbor read_valid_cbor_from_buffer_with_size_strong(uint8_t *a, size_t alen);

cbor_serialized destr_cbor_serialized(cbor c);

size_t size_comp_for_serialized(cbor c, size_t sz, bool *perr);

uint8_t *l2r_writer_for_serialized(cbor c, LowParse_SteelST_L2ROutput_t out);

cbor_array cbor_destr_array(cbor a);

size_t size_comp_for_string(cbor c, size_t sz, bool *perr);

uint8_t *l2r_write_cbor_string(cbor c, LowParse_SteelST_L2ROutput_t out);

size_t size_comp_for_simple_value(cbor c, size_t sz, bool *perr);

uint8_t *l2r_writer_for_simple_value(cbor c, LowParse_SteelST_L2ROutput_t out);

size_t size_comp_for_int64(cbor c, size_t sz, bool *perr);

uint8_t *l2r_writer_for_int64(cbor c, LowParse_SteelST_L2ROutput_t out);

cbor_map destr_cbor_map(cbor a);


#define __internal_CBOR_H_DEFINED
#endif
