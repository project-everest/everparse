#pragma once

#include <cstring>
#include "Parquet_Pulse_Toplevel.h"  // the KaRaMeL output (C header)
#include "parquet_types.hpp"         // Thrift C++ generated types (namespace parquet)

namespace shim_parquet_pulse {

// std::string and std::vector are "casted" into raw c pointers, instead of
// copyed into fresh memory
Parquet_Pulse_Toplevel_file_meta_data to_pulse_file_metadata(
    const parquet::FileMetaData& src);

void free_file_metadata(Parquet_Pulse_Toplevel_file_meta_data& m);

}  // namespace shim_parquet_pulse
