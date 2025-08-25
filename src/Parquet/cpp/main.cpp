// main.cpp
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "EverParquet.h"  // KaRaMeL C API types
#include "parquet_types.hpp"         // Thrift-generated C++ header
#include "pretty_print.hpp"
#include "shim_parquet_pulse.hpp"  // your shim header

// Thrift libs
#include <thrift/protocol/TCompactProtocol.h>
#include <thrift/transport/TBufferTransports.h>

using apache::thrift::protocol::TCompactProtocolT;
using apache::thrift::transport::TMemoryBuffer;

static constexpr const char MAGIC[4] = {'P', 'A', 'R', '1'};

static uint32_t read_le_u32(const unsigned char* p) {
  // little-endian 32-bit length at file end (footer length)
  return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
         ((uint32_t)p[3] << 24);
}

static bool read_all(const std::string& path, std::vector<uint8_t>& out) {
  std::ifstream f(path, std::ios::binary);
  if (!f) return false;
  f.seekg(0, std::ios::end);
  std::streamoff sz = f.tellg();
  if (sz < 0) return false;
  out.resize(static_cast<size_t>(sz));
  f.seekg(0, std::ios::beg);
  f.read(reinterpret_cast<char*>(out.data()), sz);
  return f.good();
}

static bool check_magic(const uint8_t* p) { return std::memcmp(p, MAGIC, 4) == 0; }

static bool extract_footer_slice(const std::vector<uint8_t>& file,
                                 const uint8_t** footer_data, size_t* footer_size) {
  if (file.size() < 12) return false;

  // Verify header magic at the start
  if (!check_magic(file.data())) return false;

  // Tail: [footer_len (4 LE)] [magic (PAR1)]
  const size_t n = file.size();
  const uint8_t* tail_magic = &file[n - 4];
  if (!check_magic(tail_magic)) return false;

  const uint8_t* len_ptr = &file[n - 8];
  uint32_t foot_len = read_le_u32(len_ptr);

  // Sanity
  if (foot_len > n - 12) return false;

  const size_t foot_start = n - 8 - foot_len;
  *footer_data = &file[foot_start];
  *footer_size = foot_len;
  return true;
}

static parquet::FileMetaData parse_footer_thrift(const uint8_t* footer_data,
                                                 size_t footer_size) {
  // Parquet metadata is Thrift-serialized using Compact Protocol
  auto mem =
      std::make_shared<TMemoryBuffer>(const_cast<uint8_t*>(footer_data), footer_size);
  auto proto = std::make_shared<TCompactProtocolT<TMemoryBuffer>>(mem);

  parquet::FileMetaData meta;
  meta.read(proto.get());
  return meta;
}

bool validate_footer(Parquet_Pulse_Toplevel_bytes input, size_t* poffset) {
  try {
    parse_footer_thrift(input.data + *poffset, input.len - *poffset);
    return true;
  } catch (apache::thrift::protocol::TProtocolException&) {
    return false;
  }
}

// Should only be called after validate_footer returned true.
Parquet_Pulse_Toplevel_file_meta_data read_footer(Parquet_Pulse_Toplevel_bytes footer) {
  parquet::FileMetaData meta = parse_footer_thrift(footer.data, footer.len);

  return shim_parquet_pulse::to_pulse_file_metadata(meta);
}

static void print_summary(const std::string& path, const parquet::FileMetaData& m,
                          const Parquet_Pulse_Toplevel_file_meta_data& pm) {
  pretty::print_file_metadata(path, m);
  // Minimal sanity cross-check against pulse view
  std::cout << "  [pulse] version=" << pm.version << " schema.len=" << pm.schema.len
            << " num_rows=" << pm.num_rows2 << " row_groups.len=" << pm.row_groups.len
            << "\n";
}

int main(int argc, char** argv) {
  if (argc < 2) {
    std::cerr << "Usage: " << argv[0] << " <file.parquet> [more.parquet ...]\n";
    return 64;  // EX_USAGE
  }

  int exit_code = 0;

  for (int i = 1; i < argc; ++i) {
    const std::string path = argv[i];

    try {
      std::vector<uint8_t> file;
      if (!read_all(path, file)) {
        std::cerr << "Error: failed to read file: " << path << "\n";
        exit_code = 1;
        continue;
      }

      const uint8_t* footer = nullptr;
      size_t footer_len = 0;
      if (!extract_footer_slice(file, &footer, &footer_len)) {
        std::cerr << "Error: invalid Parquet file or unsupported layout: " << path
                  << "\n";
        exit_code = 1;
        continue;
      }

      parquet::FileMetaData meta = parse_footer_thrift(footer, footer_len);

      // Convert to KaRaMeL view (small allocations; string views)
      Parquet_Pulse_Toplevel_file_meta_data pulse =
          shim_parquet_pulse::to_pulse_file_metadata(meta);

      // Optional: do something with `pulse` here. For demo, just print a tiny summary.
      print_summary(path, meta, pulse);

      // When done, release only the small arrays we allocated in the shim.
      shim_parquet_pulse::free_file_metadata(pulse);
    } catch (const std::exception& e) {
      std::cerr << "Exception while processing " << path << ": " << e.what() << "\n";
      exit_code = 1;
    } catch (...) {
      std::cerr << "Unknown error while processing " << path << "\n";
      exit_code = 1;
    }
  }

  return exit_code;
}
