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


#ifndef __CBOR_Pulse_H
#define __CBOR_Pulse_H

#include "krmllib.h"

#include "CBOR.h"

int16_t CBOR_Pulse_byte_array_compare(size_t sz, uint8_t *a1, uint8_t *a2);

int16_t CBOR_Pulse_cbor_compare(cbor a1, cbor a2);

bool CBOR_Pulse_cbor_is_equal(cbor a1, cbor a2);

#define CBOR_Pulse_Found 0
#define CBOR_Pulse_NotFound 1

typedef uint8_t CBOR_Pulse_cbor_map_get_t_tags;

typedef struct CBOR_Pulse_cbor_map_get_t_s
{
  CBOR_Pulse_cbor_map_get_t_tags tag;
  cbor _0;
}
CBOR_Pulse_cbor_map_get_t;

CBOR_Pulse_cbor_map_get_t CBOR_Pulse_cbor_map_get(cbor key, cbor map);

bool CBOR_Pulse_cbor_map_sort(cbor_map_entry *a, size_t len);


#define __CBOR_Pulse_H_DEFINED
#endif
