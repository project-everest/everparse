// pretty_print.hpp
#pragma once
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include "parquet_types.hpp"

namespace pretty {

// Join helper
template <class T>
static std::string join(const std::vector<T>& v, const char* sep) {
  std::ostringstream oss;
  for (size_t i = 0; i < v.size(); ++i) {
    if (i) oss << sep;
    oss << parquet::to_string(v[i]);
  }
  return oss.str();
}
static std::string join_strings(const std::vector<std::string>& v, const char* sep) {
  std::ostringstream oss;
  for (size_t i = 0; i < v.size(); ++i) {
    if (i) oss << sep;
    oss << v[i];
  }
  return oss.str();
}

// TimeUnit is a Thrift "union" with MILLIS/MICROS/NANOS flags.
static inline std::string pp_time_unit(const parquet::TimeUnit& u) {
  if (u.__isset.MILLIS) return "MILLIS";
  if (u.__isset.MICROS) return "MICROS";
  if (u.__isset.NANOS) return "NANOS";
  return "?";
}

// LogicalType is also a Thrift "union"; only one member is set.
static inline std::string pp_logical_type(const parquet::LogicalType& lt) {
  std::ostringstream os;

  if (lt.__isset.STRING) return "STRING";
  if (lt.__isset.MAP) return "MAP";
  if (lt.__isset.LIST) return "LIST";
  if (lt.__isset.ENUM) return "ENUM";

  if (lt.__isset.DECIMAL) {
    os << "DECIMAL(scale=" << lt.DECIMAL.scale << ", precision=" << lt.DECIMAL.precision
       << ")";
    return os.str();
  }

  if (lt.__isset.DATE) return "DATE";

  if (lt.__isset.TIME) {
    os << "TIME(unit=" << pp_time_unit(lt.TIME.unit)
       << ", adjustedToUTC=" << (lt.TIME.isAdjustedToUTC ? "true" : "false") << ")";
    return os.str();
  }

  if (lt.__isset.TIMESTAMP) {
    os << "TIMESTAMP(unit=" << pp_time_unit(lt.TIMESTAMP.unit)
       << ", adjustedToUTC=" << (lt.TIMESTAMP.isAdjustedToUTC ? "true" : "false") << ")";
    return os.str();
  }

  if (lt.__isset.INTEGER) {
    os << "INTEGER(bitWidth=" << int(lt.INTEGER.bitWidth)
       << ", signed=" << (lt.INTEGER.isSigned ? "true" : "false") << ")";
    return os.str();
  }

  if (lt.__isset.UNKNOWN) return "UNKNOWN";
  if (lt.__isset.JSON) return "JSON";
  if (lt.__isset.BSON) return "BSON";
  if (lt.__isset.UUID) return "UUID";
  if (lt.__isset.FLOAT16) return "FLOAT16";
  if (lt.__isset.VARIANT) return "VARIANT";

  if (lt.__isset.GEOMETRY) {
    // Often carries an optional CRS string
    std::string extra;
    if (lt.GEOMETRY.__isset.crs) {
      extra = lt.GEOMETRY.crs;
    } else if (lt.GEOMETRY.__isset.crs) {
      extra = lt.GEOMETRY.crs;
    }
    return extra.empty() ? "GEOMETRY" : ("GEOMETRY(crs=" + extra + ")");
  }

  if (lt.__isset.GEOGRAPHY) {
    // Common fields seen in parquet.thrift: optional crs and/or algorithm
    std::ostringstream g;
    bool opened = false;
    if (lt.GEOGRAPHY.__isset.crs) {
      g << (opened ? ", " : "(") << "crs=" << lt.GEOGRAPHY.crs;
      opened = true;
    }
    if (lt.GEOGRAPHY.__isset.algorithm) {
      // algorithm is an enum-like union in some schemas; print if stringifiable
      g << (opened ? ", " : "(") << "algorithm";
      opened = true;
    }
    if (opened) g << ")";
    return "GEOGRAPHY" + g.str();
  }

  // If nothing matched, return empty so caller can fall back.
  return std::string();
}

// Rebuild a tree view from the flattened schema (depth-first order)
static void print_schema_tree(const std::vector<parquet::SchemaElement>& schema,
                              std::ostream& os) {
  os << "Schema (" << schema.size() << " elements):\n";

  // Depth can be tracked with a stack of remaining-children counters.
  struct Frame {
    int remaining;
  };
  std::vector<Frame> stack;

  for (size_t i = 0; i < schema.size(); ++i) {
    const auto& se = schema[i];

    // Pop finished frames
    while (!stack.empty() && stack.back().remaining == 0) {
      stack.pop_back();
      if (!stack.empty()) stack.back().remaining--;
    }

    // Indentation
    os << "  ";
    for (size_t d = 0; d < stack.size(); ++d) os << "  ";

    // Name
    os << "• " << se.name;

    // Node kind and details
    bool is_leaf = !se.__isset.num_children;
    if (is_leaf) {
      if (se.__isset.type) os << " : " << parquet::to_string(se.type);
      if (se.__isset.repetition_type)
        os << " [" << parquet::to_string(se.repetition_type) << "]";
      if (se.__isset.logicalType) {
        const std::string lt = pp_logical_type(se.logicalType);
        if (!lt.empty()) os << "  (logical=" << lt << ")";
      } else if (se.__isset.converted_type) {
        os << "  (converted=" << parquet::to_string(se.converted_type) << ")";
      }
    } else {
      // group node
      os << " (group, children=" << se.num_children << ")";
      if (se.__isset.repetition_type)
        os << " [" << parquet::to_string(se.repetition_type) << "]";
      // push frame for this group
      stack.push_back(Frame{se.num_children});
    }
    os << "\n";

    // After printing a leaf, decrement parent remaining
    if (is_leaf && !stack.empty()) {
      stack.back().remaining--;
    }
  }

  // Drain any trailing frames
  while (!stack.empty()) {
    if (stack.back().remaining > 0) break;
    stack.pop_back();
  }
}

// clang-format off
// Join path_in_schema like ["a","b","c"] -> "a.b.c"
static inline std::string join_path(const std::vector<std::string>& path) {
  if (path.empty()) return "";
  std::ostringstream os;
  for (size_t i = 0; i < path.size(); ++i) {
    if (i) os << '.';
    os << path[i];
  }
  return os.str();
}

static inline std::string fmt_optional_i64(bool is_set, int64_t v) {
  return is_set ? std::to_string(v) : "-";
}
static inline std::string fmt_optional_i32(bool is_set, int32_t v) {
  return is_set ? std::to_string(v) : "-";
}

// Center/left align helpers for a quick ASCII table
static inline std::string pad(const std::string& s, size_t w) {
  if (s.size() >= w) return s;
  return s + std::string(w - s.size(), ' ');
}

struct ColChunkRow {
  std::string col;          // path_in_schema (or type name as fallback)
  std::string off_off;      // offset_index_offset
  std::string off_len;      // offset_index_length
  std::string col_off;      // column_index_offset
  std::string col_len;      // column_index_length
};

static inline void print_column_chunk_index_table(
    const std::vector<parquet::ColumnChunk>& chunks,
    std::ostream& os)
{
  // Build rows first so we can compute widths
  std::vector<ColChunkRow> rows;
  rows.reserve(chunks.size());

  for (const auto& cc : chunks) {
    // Column label: prefer meta_data.path_in_schema, else type name
    std::string colname;
    if (cc.__isset.meta_data && !cc.meta_data.path_in_schema.empty()) {
      colname = join_path(cc.meta_data.path_in_schema);
    } else if (cc.__isset.meta_data) {
      colname = parquet::to_string(cc.meta_data.type);
    } else {
      colname = "?";
    }

    ColChunkRow r;
    r.col     = std::move(colname);
    r.off_off = fmt_optional_i64(cc.__isset.offset_index_offset,  cc.offset_index_offset);
    r.off_len = fmt_optional_i32(cc.__isset.offset_index_length, cc.offset_index_length);
    r.col_off = fmt_optional_i64(cc.__isset.column_index_offset, cc.column_index_offset);
    r.col_len = fmt_optional_i32(cc.__isset.column_index_length, cc.column_index_length);
    rows.push_back(std::move(r));
  }

  // Column headings
  const std::string H0 = "column";
  const std::string H1 = "offset_index_offset";
  const std::string H2 = "offset_index_length";
  const std::string H3 = "column_index_offset";
  const std::string H4 = "column_index_length";

  // Compute widths
  size_t w0 = H0.size(), w1 = H1.size(), w2 = H2.size(), w3 = H3.size(), w4 = H4.size();
  for (auto& r : rows) {
    w0 = std::max(w0, r.col.size());
    w1 = std::max(w1, r.off_off.size());
    w2 = std::max(w2, r.off_len.size());
    w3 = std::max(w3, r.col_off.size());
    w4 = std::max(w4, r.col_len.size());
  }

  auto sep = [&]() {
    os << '+' << std::string(w0+2, '-')
       << '+' << std::string(w1+2, '-')
       << '+' << std::string(w2+2, '-')
       << '+' << std::string(w3+2, '-')
       << '+' << std::string(w4+2, '-') << "+\n";
  };

  // Print table
  sep();
  os << "| " << pad(H0, w0) << " "
     << "| " << pad(H1, w1) << " "
     << "| " << pad(H2, w2) << " "
     << "| " << pad(H3, w3) << " "
     << "| " << pad(H4, w4) << " |\n";
  sep();
  for (auto& r : rows) {
    os << "| " << pad(r.col,     w0) << " "
       << "| " << pad(r.off_off, w1) << " "
       << "| " << pad(r.off_len, w2) << " "
       << "| " << pad(r.col_off, w3) << " "
       << "| " << pad(r.col_len, w4) << " |\n";
  }
  sep();
}

// join encodings (vector<Encoding>)
static inline std::string join_encs(const std::vector<parquet::Encoding>& encs) {
  std::ostringstream os;
  for (size_t i = 0; i < encs.size(); ++i) {
    if (i) os << ",";
    os << parquet::to_string(encs[i]);
  }
  return os.str();
}

struct ColMetaRow {
  std::string path;
  std::string type;
  std::string codec;
  std::string values;
  std::string uncomp;
  std::string comp;
  std::string data_off;
  std::string dict_off;
  std::string encs;
};

static void print_column_meta_table(const std::vector<parquet::ColumnChunk>& chunks,
                                    std::ostream& os) {
  std::vector<ColMetaRow> rows;
  rows.reserve(chunks.size());

  for (const auto& cc : chunks) {
    const auto* mdp = cc.__isset.meta_data ? &cc.meta_data : nullptr;
    ColMetaRow r;
    r.path     = mdp ? join_path(mdp->path_in_schema)
                     : (cc.__isset.file_path ? cc.file_path : "(unknown)");
    r.type     = mdp ? parquet::to_string(mdp->type) : "-";
    r.codec    = mdp ? parquet::to_string(mdp->codec) : "-";
    r.values   = mdp ? std::to_string(mdp->num_values) : "-";
    r.uncomp   = mdp ? std::to_string(mdp->total_uncompressed_size) : "-";
    r.comp     = mdp ? std::to_string(mdp->total_compressed_size) : "-";
    r.data_off = mdp ? std::to_string(mdp->data_page_offset) : "-";
    r.dict_off = (mdp && mdp->__isset.dictionary_page_offset)
                   ? std::to_string(mdp->dictionary_page_offset) : "-";
    r.encs     = mdp ? join_encs(mdp->encodings) : "-";
    rows.push_back(std::move(r));
  }

  // headings
  const std::string H0="path", H1="type", H2="codec", H3="values", H4="uncomp",
                    H5="comp", H6="data_off", H7="dict_off", H8="encodings";

  // widths
  size_t w0=H0.size(), w1=H1.size(), w2=H2.size(), w3=H3.size(), w4=H4.size(),
         w5=H5.size(), w6=H6.size(), w7=H7.size(), w8=H8.size();
  for (auto& r : rows) {
    w0 = std::max(w0, r.path.size());
    w1 = std::max(w1, r.type.size());
    w2 = std::max(w2, r.codec.size());
    w3 = std::max(w3, r.values.size());
    w4 = std::max(w4, r.uncomp.size());
    w5 = std::max(w5, r.comp.size());
    w6 = std::max(w6, r.data_off.size());
    w7 = std::max(w7, r.dict_off.size());
    w8 = std::max(w8, r.encs.size());
  }

  auto sep = [&]() {
    os << '+' << std::string(w0+2,'-')
       << '+' << std::string(w1+2,'-')
       << '+' << std::string(w2+2,'-')
       << '+' << std::string(w3+2,'-')
       << '+' << std::string(w4+2,'-')
       << '+' << std::string(w5+2,'-')
       << '+' << std::string(w6+2,'-')
       << '+' << std::string(w7+2,'-')
       << '+' << std::string(w8+2,'-') << "+\n";
  };

  sep();
  os << "| " << std::left << std::setw(w0) << H0 << " "
     << "| " << std::setw(w1) << H1 << " "
     << "| " << std::setw(w2) << H2 << " "
     << "| " << std::setw(w3) << H3 << " "
     << "| " << std::setw(w4) << H4 << " "
     << "| " << std::setw(w5) << H5 << " "
     << "| " << std::setw(w6) << H6 << " "
     << "| " << std::setw(w7) << H7 << " "
     << "| " << std::setw(w8) << H8 << " |\n";
  sep();
  for (auto& r : rows) {
    os << "| " << std::setw(w0) << r.path     << " "
       << "| " << std::setw(w1) << r.type     << " "
       << "| " << std::setw(w2) << r.codec    << " "
       << "| " << std::setw(w3) << r.values   << " "
       << "| " << std::setw(w4) << r.uncomp   << " "
       << "| " << std::setw(w5) << r.comp     << " "
       << "| " << std::setw(w6) << r.data_off << " "
       << "| " << std::setw(w7) << r.dict_off << " "
       << "| " << std::setw(w8) << r.encs     << " |\n";
  }
  sep();
}

static void print_row_group(const parquet::RowGroup& rg, size_t rg_index,
                            std::ostream& os) {
  os << "Row group " << rg_index
     << " — rows: " << rg.num_rows
     << ", total_uncompressed: " << rg.total_byte_size
     << (rg.__isset.total_compressed_size ? (", total_compressed: " + std::to_string(rg.total_compressed_size)) : "")
     << (rg.__isset.file_offset ? (", first_page_offset: " + std::to_string(rg.file_offset)) : "")
     << "\n";

  os << "Column page-index summary:\n";
  print_column_chunk_index_table(rg.columns, os);
  os << "\n";

  os << "Column meta data summary:\n";
  print_column_meta_table(rg.columns, os);
}


// Top-level pretty print
inline void print_file_metadata(const std::string& path,
                                const parquet::FileMetaData& m,
                                std::ostream& os = std::cout) {
  os << "Parquet file: " << path << "\n";
  os << "Version  : " << m.version << "\n";
  os << "Rows     : " << m.num_rows << "\n";
  os << "Schema el: " << m.schema.size() << "\n";
  os << "RowGroups: " << m.row_groups.size() << "\n";
  if (m.__isset.created_by) os << "Created by: " << m.created_by << "\n";
  os << "\n";

  print_schema_tree(m.schema, os);
  os << "\n";

  for (size_t i = 0; i < m.row_groups.size(); ++i) {
    print_row_group(m.row_groups[i], i, os);
    if (i + 1 < m.row_groups.size()) os << "\n";
  }
}

} // namespace pretty
