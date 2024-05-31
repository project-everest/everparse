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


#ifndef __internal_CBOR_Pulse_H
#define __internal_CBOR_Pulse_H

#include "krmllib.h"

#include "../CBOR_Pulse.h"

bool CBOR_Pulse_cbor_map_sort_aux(cbor_map_entry *a, size_t lo, size_t hi);


#define __internal_CBOR_Pulse_H_DEFINED
#endif
