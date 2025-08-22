#pragma once

#include <cstring>
#include "Parquet_Pulse_Toplevel.h"  // the KaRaMeL output (C header)
#include "parquet_types.hpp"         // Thrift C++ generated types (namespace parquet)

namespace shim_parquet_pulse {

// std::string and std::vector are "casted" into raw c pointers, instead of
// copyed into fresh memory
Parquet_Pulse_Toplevel_file_meta_data to_pulse_file_metadata(
    const parquet::FileMetaData& src);

// input: &file[0..file.len() - 8]
// poffset: [0, input.len], or more specifically, it will be file.len() - 8 - footer_len
bool validate_footer(Parquet_Pulse_Toplevel_bytes input, size_t* poffset);

Parquet_Pulse_Toplevel_file_meta_data read_footer(Parquet_Pulse_Toplevel_bytes input);

void free_file_metadata(Parquet_Pulse_Toplevel_file_meta_data& m);

}  // namespace shim_parquet_pulse
