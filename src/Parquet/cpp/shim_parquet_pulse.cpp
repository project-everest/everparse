#include "shim_parquet_pulse.hpp"
#include <cassert>
#include <cstdlib>
// Thrift libs
#include <thrift/protocol/TCompactProtocol.h>
#include <thrift/transport/TBufferTransports.h>

using namespace parquet;

namespace shim_parquet_pulse {

// ---------- small helpers for Karamel option wrappers ----------

static inline FStar_Pervasives_Native_option__int32_t opt_i32_none() {
  FStar_Pervasives_Native_option__int32_t o;
  o.tag = FStar_Pervasives_Native_None;
  o.v = 0;
  return o;
}
static inline FStar_Pervasives_Native_option__int32_t opt_i32_some(int32_t v) {
  FStar_Pervasives_Native_option__int32_t o;
  o.tag = FStar_Pervasives_Native_Some;
  o.v = v;
  return o;
}
static inline FStar_Pervasives_Native_option__int64_t opt_i64_some(int64_t v) {
  FStar_Pervasives_Native_option__int64_t o;
  o.tag = FStar_Pervasives_Native_Some;
  o.v = v;
  return o;
}
static inline FStar_Pervasives_Native_option__int64_t opt_i64_none() {
  FStar_Pervasives_Native_option__int64_t o;
  o.tag = FStar_Pervasives_Native_None;
  o.v = 0;
  return o;
}
static inline FStar_Pervasives_Native_option__bool opt_bool_none() {
  FStar_Pervasives_Native_option__bool o;
  o.tag = FStar_Pervasives_Native_None;
  o.v = false;
  return o;
}
static inline FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_physical_type
opt_physical_none() {
  FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_physical_type o;
  o.tag = FStar_Pervasives_Native_None;
  o.v = 0;
  return o;
}
static inline FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_physical_type
opt_physical_some(uint8_t v) {
  FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_physical_type o;
  o.tag = FStar_Pervasives_Native_Some;
  o.v = v;
  return o;
}

static inline FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_field_repetition_type
opt_repetition_none() {
  FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_field_repetition_type o;
  o.tag = FStar_Pervasives_Native_None;
  o.v = 0;
  return o;
}
static inline FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_field_repetition_type
opt_repetition_some(uint8_t v) {
  FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_field_repetition_type o;
  o.tag = FStar_Pervasives_Native_Some;
  o.v = v;
  return o;
}

static inline FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_converted_type
opt_converted_none() {
  FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_converted_type o;
  o.tag = FStar_Pervasives_Native_None;
  o.v = 0;
  return o;
}
static inline FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_converted_type
opt_converted_some(uint8_t v) {
  FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_converted_type o;
  o.tag = FStar_Pervasives_Native_Some;
  o.v = v;
  return o;
}

static inline FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_encryption_algorithm
opt_encryption_none() {
  FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_encryption_algorithm o;
  o.tag = FStar_Pervasives_Native_None;
  // o.v is a union; leaving it uninitialized is fine because tag=None
  return o;
}

// logical_type is a nested union on both sides — start with None.
// (Easy to extend later.)
static inline FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_logical_type
opt_logical_none() {
  FStar_Pervasives_Native_option__Parquet_Spec_Toplevel_Types_logical_type o;
  o.tag = FStar_Pervasives_Native_None;
  // o.v is a union; leaving it uninitialized is fine because tag=None
  return o;
}

// String cast (Prims_string is a C string in krmllib)
static inline Prims_string make_string(const std::string& s) { return s.c_str(); }

// ---------- vectors ----------

static Parquet_Pulse_Vec_vec__Prims_string make_vec_strings(
    const std::vector<std::string>& v) {
  Parquet_Pulse_Vec_vec__Prims_string out;
  out.len = v.size();
  out.data = (Prims_string*)std::malloc(sizeof(Prims_string) * out.len);
  if (!out.data) {
    out.len = 0;
    return out;
  }
  for (size_t i = 0; i < out.len; ++i) out.data[i] = make_string(v[i]);
  return out;
}

static Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_column_order
make_vec_column_orders(const std::vector<parquet::ColumnOrder>& v) {
  // KaRaMeL side exposes only TYPE_ORDER tag; map everything to TYPE_ORDER.
  Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_column_order out;
  out.len = v.size();
  out.data = (Parquet_Pulse_Toplevel_column_order*)std::malloc(
      sizeof(Parquet_Pulse_Toplevel_column_order) * out.len);
  if (!out.data) {
    out.len = 0;
    return out;
  }
  for (size_t i = 0; i < out.len; ++i) {
    out.data[i] = Parquet_Spec_Toplevel_Types_TYPE_ORDER;
  }
  return out;
}

// ---------- SchemaElement ----------

static Parquet_Pulse_Toplevel_schema_element to_pulse_schema_element(
    const parquet::SchemaElement& se) {
  Parquet_Pulse_Toplevel_schema_element dst;

  dst.type_ = se.__isset.type ? opt_physical_some(static_cast<uint8_t>(se.type))
                              : opt_physical_none();

  dst.type_length =
      se.__isset.type_length ? opt_i32_some(se.type_length) : opt_i32_none();

  dst.repetition_type =
      se.__isset.repetition_type
          ? opt_repetition_some(static_cast<uint8_t>(se.repetition_type))
          : opt_repetition_none();

  dst.name = make_string(se.name);

  dst.num_children =
      se.__isset.num_children ? opt_i32_some(se.num_children) : opt_i32_none();

  dst.converted_type = se.__isset.converted_type
                           ? opt_converted_some(static_cast<uint8_t>(se.converted_type))
                           : opt_converted_none();

  dst.scale1 = se.__isset.scale ? opt_i32_some(se.scale) : opt_i32_none();
  dst.precision1 = se.__isset.precision ? opt_i32_some(se.precision) : opt_i32_none();
  dst.field_id = se.__isset.field_id ? opt_i32_some(se.field_id) : opt_i32_none();

  // logical_type (TODO: map from parquet::LogicalType ->
  // Parquet_Pulse_Toplevel_logical_type)
  dst.logical_type = opt_logical_none();

  return dst;
}

static Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_schema_element make_vec_schema(
    const std::vector<parquet::SchemaElement>& v) {
  Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_schema_element out;
  out.len = v.size();
  out.data = (Parquet_Pulse_Toplevel_schema_element*)std::malloc(
      sizeof(Parquet_Pulse_Toplevel_schema_element) * out.len);
  if (!out.data) {
    out.len = 0;
    return out;
  }
  for (size_t i = 0; i < out.len; ++i) {
    out.data[i] = to_pulse_schema_element(v[i]);
  }
  return out;
}

// ---------- KeyValue ----------

static FStar_Pervasives_Native_option__Prims_string opt_string_none() {
  FStar_Pervasives_Native_option__Prims_string o;
  o.tag = FStar_Pervasives_Native_None;
  o.v = nullptr;
  return o;
}
static FStar_Pervasives_Native_option__Prims_string opt_string_some(
    const std::string& s) {
  FStar_Pervasives_Native_option__Prims_string o;
  o.tag = FStar_Pervasives_Native_Some;
  o.v = make_string(s);
  return o;
}

static Parquet_Pulse_Toplevel_key_value to_pulse_kv(const parquet::KeyValue& kv) {
  Parquet_Pulse_Toplevel_key_value out;
  out.key = make_string(kv.key);
  out.value = kv.__isset.value ? opt_string_some(kv.value) : opt_string_none();
  return out;
}

static Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_key_value make_vec_key_values(
    const std::vector<parquet::KeyValue>& v) {
  Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_key_value out;
  out.len = v.size();
  out.data = (Parquet_Pulse_Toplevel_key_value*)std::malloc(
      sizeof(Parquet_Pulse_Toplevel_key_value) * out.len);
  if (!out.data) {
    out.len = 0;
    return out;
  }
  for (size_t i = 0; i < out.len; ++i) out.data[i] = to_pulse_kv(v[i]);
  return out;
}

static Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_encoding make_vec_encodings(
    const std::vector<parquet::Encoding>& v) {
  Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_encoding out;
  out.len = v.size();
  out.data = (Parquet_Pulse_Toplevel_encoding*)std::malloc(
      sizeof(Parquet_Pulse_Toplevel_encoding) * out.len);
  if (!out.data) {
    out.len = 0;
    return out;
  }
  for (size_t i = 0; i < out.len; ++i) out.data[i] = static_cast<uint8_t>(v[i]);
  return out;
}

static Parquet_Pulse_Toplevel_page_encoding_stats to_pulse_page_encoding_stats(
    const parquet::PageEncodingStats& s) {
  Parquet_Pulse_Toplevel_page_encoding_stats out;
  out.page_type = static_cast<uint8_t>(s.page_type);
  out.encoding2 = static_cast<uint8_t>(s.encoding);
  out.count = s.count;
  return out;
}
static Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_page_encoding_stats
make_vec_page_encoding_stats(const std::vector<parquet::PageEncodingStats>& v) {
  Parquet_Pulse_Vec_vec__Parquet_Spec_Toplevel_Types_page_encoding_stats out;
  out.len = v.size();
  out.data = (Parquet_Pulse_Toplevel_page_encoding_stats*)std::malloc(
      sizeof(Parquet_Pulse_Toplevel_page_encoding_stats) * out.len);
  if (!out.data) {
    out.len = 0;
    return out;
  }
  for (size_t i = 0; i < out.len; ++i) out.data[i] = to_pulse_page_encoding_stats(v[i]);
  return out;
}

static Parquet_Pulse_Toplevel_column_meta_data to_pulse_column_meta_data(
    const parquet::ColumnMetaData& md) {
  Parquet_Pulse_Toplevel_column_meta_data out;

  out.physical_type = static_cast<uint8_t>(md.type);
  out.encodings = make_vec_encodings(md.encodings);
  out.path_in_schema = make_vec_strings(md.path_in_schema);
  out.codec = static_cast<uint8_t>(md.codec);
  out.num_values2 = md.num_values;
  out.total_uncompressed_size = md.total_uncompressed_size;
  out.total_compressed_size = md.total_compressed_size;

  if (md.__isset.key_value_metadata) {
    out.key_value_metadata.tag = FStar_Pervasives_Native_Some;
    out.key_value_metadata.v = make_vec_key_values(md.key_value_metadata);
  } else {
    out.key_value_metadata.tag = FStar_Pervasives_Native_None;
  }

  out.data_page_offset = md.data_page_offset;
  out.index_page_offset =
      md.__isset.index_page_offset ? opt_i64_some(md.index_page_offset) : opt_i64_none();
  out.dictionary_page_offset = md.__isset.dictionary_page_offset
                                   ? opt_i64_some(md.dictionary_page_offset)
                                   : opt_i64_none();

  // statistics - none for now
  out.statistics2.tag = FStar_Pervasives_Native_None;

  if (md.__isset.encoding_stats) {
    out.encoding_stats.tag = FStar_Pervasives_Native_Some;
    out.encoding_stats.v = make_vec_page_encoding_stats(md.encoding_stats);
  } else {
    out.encoding_stats.tag = FStar_Pervasives_Native_None;
  }

  out.bloom_filter_offset = md.__isset.bloom_filter_offset
                                ? opt_i64_some(md.bloom_filter_offset)
                                : opt_i64_none();

  out.bloom_filter_length = md.__isset.bloom_filter_length
                                ? opt_i32_some(md.bloom_filter_length)
                                : opt_i32_none();

  // size_statistics / geospatial_statistics — none for now
  out.size_statistics.tag = FStar_Pervasives_Native_None;
  out.geospatial_statistics.tag = FStar_Pervasives_Native_None;

  return out;
}

static Parquet_Pulse_Toplevel_column_chunk to_pulse_column_chunk(
    const parquet::ColumnChunk& cc) {
  Parquet_Pulse_Toplevel_column_chunk out;

  if (cc.__isset.file_path) {
    out.file_path.tag = FStar_Pervasives_Native_Some;
    out.file_path.v = make_string(cc.file_path);
  } else {
    out.file_path.tag = FStar_Pervasives_Native_None;
    out.file_path.v = nullptr;
  }

  out.file_offset = cc.file_offset;

  if (cc.__isset.meta_data) {
    out.meta_data.tag = FStar_Pervasives_Native_Some;
    out.meta_data.v = to_pulse_column_meta_data(cc.meta_data);
  } else {
    out.meta_data.tag = FStar_Pervasives_Native_None;
  }

  out.offset_index_offset = cc.__isset.offset_index_offset
                                ? opt_i64_some(cc.offset_index_offset)
                                : opt_i64_none();
  out.offset_index_length = cc.__isset.offset_index_length
                                ? opt_i32_some(cc.offset_index_length)
                                : opt_i32_none();
  out.column_index_offset = cc.__isset.column_index_offset
                                ? opt_i64_some(cc.column_index_offset)
                                : opt_i64_none();
  out.column_index_length = cc.__isset.column_index_length
                                ? opt_i32_some(cc.column_index_length)
                                : opt_i32_none();

  out.crypto_metadata.tag = FStar_Pervasives_Native_None;
  if (cc.__isset.encrypted_column_metadata) {
    out.encrypted_column_metadata.tag = FStar_Pervasives_Native_Some;
    out.encrypted_column_metadata.v = make_string(cc.encrypted_column_metadata);
  } else {
    out.encrypted_column_metadata.tag = FStar_Pervasives_Native_None;
    out.encrypted_column_metadata.v = nullptr;
  }

  return out;
}

static Parquet_Pulse_Vec_vec__Parquet_Pulse_Toplevel_column_chunk make_vec_column_chunks(
    const std::vector<parquet::ColumnChunk>& v) {
  Parquet_Pulse_Vec_vec__Parquet_Pulse_Toplevel_column_chunk out;
  out.len = v.size();
  out.data = (Parquet_Pulse_Toplevel_column_chunk*)std::malloc(
      sizeof(Parquet_Pulse_Toplevel_column_chunk) * out.len);
  if (!out.data) {
    out.len = 0;
    return out;
  }
  for (size_t i = 0; i < out.len; ++i) out.data[i] = to_pulse_column_chunk(v[i]);
  return out;
}

// ---------- RowGroup ----------

static Parquet_Pulse_Toplevel_row_group to_pulse_row_group(const parquet::RowGroup& rg) {
  Parquet_Pulse_Toplevel_row_group out;
  out.columns = make_vec_column_chunks(rg.columns);

  out.total_byte_size = rg.total_byte_size;
  out.num_rows1 = rg.num_rows;

  out.sorting_columns.tag = FStar_Pervasives_Native_None;
  out.file_offset1 = opt_i64_some(rg.file_offset);
  out.total_compressed_size1 = opt_i64_some(rg.total_compressed_size);
  FStar_Pervasives_Native_option__int16_t ord;
  ord.tag =
      rg.__isset.ordinal ? FStar_Pervasives_Native_Some : FStar_Pervasives_Native_None;
  ord.v = rg.ordinal;
  out.ordinal = ord;

  return out;
}

static Parquet_Pulse_Vec_vec__Parquet_Pulse_Toplevel_row_group make_vec_row_groups(
    const std::vector<parquet::RowGroup>& v) {
  Parquet_Pulse_Vec_vec__Parquet_Pulse_Toplevel_row_group out;
  out.len = v.size();
  out.data = (Parquet_Pulse_Toplevel_row_group*)std::malloc(
      sizeof(Parquet_Pulse_Toplevel_row_group) * out.len);
  if (!out.data) {
    out.len = 0;
    return out;
  }
  for (size_t i = 0; i < out.len; ++i) out.data[i] = to_pulse_row_group(v[i]);
  return out;
}

// ---------- top-level FileMetaData ----------

Parquet_Pulse_Toplevel_file_meta_data to_pulse_file_metadata(
    const parquet::FileMetaData& src) {
  Parquet_Pulse_Toplevel_file_meta_data dst;

  dst.version = src.version;
  dst.schema = make_vec_schema(src.schema);
  dst.num_rows2 = src.num_rows;

  dst.row_groups = make_vec_row_groups(src.row_groups);

  if (src.__isset.key_value_metadata) {
    dst.key_value_metadata1.tag = FStar_Pervasives_Native_Some;
    dst.key_value_metadata1.v = make_vec_key_values(src.key_value_metadata);
  } else {
    dst.key_value_metadata1.tag = FStar_Pervasives_Native_None;
  }

  if (src.__isset.created_by) {
    dst.created_by.tag = FStar_Pervasives_Native_Some;
    dst.created_by.v = make_string(src.created_by);
  } else {
    dst.created_by.tag = FStar_Pervasives_Native_None;
    dst.created_by.v = nullptr;
  }

  if (src.__isset.column_orders) {
    dst.column_orders.tag = FStar_Pervasives_Native_Some;
    dst.column_orders.v = make_vec_column_orders(src.column_orders);
  } else {
    dst.column_orders.tag = FStar_Pervasives_Native_None;
  }

  dst.encryption_algorithm = opt_encryption_none();

  if (src.__isset.footer_signing_key_metadata) {
    dst.footer_signing_key_metadata.tag = FStar_Pervasives_Native_Some;
    dst.footer_signing_key_metadata.v = make_string(src.footer_signing_key_metadata);
  } else {
    dst.footer_signing_key_metadata.tag = FStar_Pervasives_Native_None;
    dst.footer_signing_key_metadata.v = nullptr;
  }

  return dst;
}

// ---------- OffsetIndex ----------

Parquet_Pulse_Toplevel_page_location to_pulse_page_location(
    const parquet::PageLocation& src) {
  Parquet_Pulse_Toplevel_page_location dst;
  dst.offset = src.offset;
  dst.compressed_page_size1 = src.compressed_page_size;
  dst.first_row_index = src.first_row_index;
  return dst;
}

Parquet_Pulse_Toplevel_offset_index to_pulse_offset_index(
    const parquet::OffsetIndex& src) {
  Parquet_Pulse_Toplevel_offset_index dst;
  dst.page_locations.len = src.page_locations.size();
  dst.page_locations.data = (Parquet_Pulse_Toplevel_page_location*)std::malloc(
      sizeof(Parquet_Pulse_Toplevel_page_location) * dst.page_locations.len);
  if (!dst.page_locations.data) {
    dst.page_locations.len = 0;
    return dst;
  }
  for (size_t i = 0; i < dst.page_locations.len; ++i) {
    dst.page_locations.data[i] = to_pulse_page_location(src.page_locations[i]);
  }
  return dst;
}

// ---------- PageHeader ----------

Parquet_Pulse_Toplevel_data_page_header to_pulse_data_page_header(
    const parquet::DataPageHeader& src) {
  Parquet_Pulse_Toplevel_data_page_header dst;
  dst.num_values = src.num_values;
  dst.encoding_ = static_cast<uint8_t>(src.encoding);
  dst.definition_level_encoding = static_cast<uint8_t>(src.definition_level_encoding);
  dst.repetition_level_encoding = static_cast<uint8_t>(src.repetition_level_encoding);
  // statistics - none for now
  dst.statistics.tag = FStar_Pervasives_Native_None;
  return dst;
}

Parquet_Pulse_Toplevel_dictionary_page_header to_pulse_dictionary_page_header(
    const parquet::DictionaryPageHeader& src) {
  Parquet_Pulse_Toplevel_dictionary_page_header dst;
  dst.num_values1 = src.num_values;
  dst.encoding = static_cast<uint8_t>(src.encoding);
  dst.is_sorted.tag =
      src.__isset.is_sorted ? FStar_Pervasives_Native_Some : FStar_Pervasives_Native_None;
  dst.is_sorted.v = src.is_sorted;
  return dst;
}

Parquet_Pulse_Toplevel_data_page_header_v2 to_pulse_data_page_header_v2(
    const parquet::DataPageHeaderV2& src) {
  Parquet_Pulse_Toplevel_data_page_header_v2 dst;
  dst.num_values1 = src.num_values;
  dst.num_nulls = src.num_nulls;
  dst.num_rows = src.num_rows;
  dst.encoding = static_cast<uint8_t>(src.encoding);
  dst.definition_levels_byte_length = src.definition_levels_byte_length;
  dst.repetition_levels_byte_length = src.repetition_levels_byte_length;
  dst.is_compressed.tag = src.__isset.is_compressed ? FStar_Pervasives_Native_Some
                                                    : FStar_Pervasives_Native_None;
  dst.is_compressed.v = src.is_compressed;
  // statistics - none for now
  dst.statistics1.tag = FStar_Pervasives_Native_None;
  return dst;
}

Parquet_Pulse_Toplevel_page_header to_pulse_page_header(const parquet::PageHeader& src) {
  Parquet_Pulse_Toplevel_page_header dst;

  dst.ptype = static_cast<uint8_t>(src.type);

  dst.uncompressed_page_size = src.uncompressed_page_size;
  dst.compressed_page_size = src.compressed_page_size;

  // crc - none for now
  dst.crc.tag = FStar_Pervasives_Native_None;

  // page header variants
  if (src.__isset.data_page_header) {
    dst.data_page_header.tag = FStar_Pervasives_Native_Some;
    dst.data_page_header.v = to_pulse_data_page_header(src.data_page_header);
  }

  if (src.__isset.index_page_header) {
    dst.index_page_header = 0;
  }

  if (src.__isset.dictionary_page_header) {
    dst.dictionary_page_header.tag = FStar_Pervasives_Native_Some;
    dst.dictionary_page_header.v =
        to_pulse_dictionary_page_header(src.dictionary_page_header);
  }

  if (src.__isset.data_page_header_v2) {
    dst.data_page_header_v2.tag = FStar_Pervasives_Native_Some;
    dst.data_page_header_v2.v = to_pulse_data_page_header_v2(src.data_page_header_v2);
  }

  return dst;
}

using apache::thrift::protocol::TCompactProtocolT;
using apache::thrift::transport::TMemoryBuffer;
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

static parquet::OffsetIndex parse_offset_index_thrift(const uint8_t* oi_data,
                                                      size_t oi_size) {
  auto mem = std::make_shared<TMemoryBuffer>(const_cast<uint8_t*>(oi_data), oi_size);
  auto proto = std::make_shared<TCompactProtocolT<TMemoryBuffer>>(mem);
  parquet::OffsetIndex oi;
  oi.read(proto.get());
  return oi;
}

static parquet::PageHeader parse_page_header_thrift(const uint8_t* ph_data,
                                                    size_t ph_size) {
  auto mem = std::make_shared<TMemoryBuffer>(const_cast<uint8_t*>(ph_data), ph_size);
  auto proto = std::make_shared<TCompactProtocolT<TMemoryBuffer>>(mem);
  parquet::PageHeader ph;
  ph.read(proto.get());
  return ph;
}

extern "C" bool Parquet_Pulse_Toplevel0_validate_footer(
    Parquet_Pulse_Toplevel_bytes input, size_t* poffset) {
  try {
    parse_footer_thrift(input.data + *poffset, input.len - *poffset);
    *poffset = input.len;
    return true;
  } catch (apache::thrift::protocol::TProtocolException&) {
    return false;
  }
}

// Should only be called after validate_footer returned true.
extern "C" Parquet_Pulse_Toplevel_file_meta_data Parquet_Pulse_Toplevel0_read_footer(
    Parquet_Pulse_Toplevel_bytes footer) {
  parquet::FileMetaData meta = parse_footer_thrift(footer.data, footer.len);

  return shim_parquet_pulse::to_pulse_file_metadata(meta);
}

extern "C" bool Parquet_Pulse_Toplevel0_validate_offset_index(
    Parquet_Pulse_Toplevel_bytes input, size_t* poffset) {
  try {
    parse_offset_index_thrift(input.data + *poffset, input.len - *poffset);
    *poffset = input.len;
    return true;
  } catch (apache::thrift::protocol::TProtocolException&) {
    return false;
  }
}

extern "C" Parquet_Pulse_Toplevel_offset_index Parquet_Pulse_Toplevel0_read_offset_index(
    Parquet_Pulse_Toplevel_bytes input) {
  parquet::OffsetIndex oi = parse_offset_index_thrift(input.data, input.len);
  return to_pulse_offset_index(oi);
}

extern "C" bool Parquet_Pulse_Toplevel0_validate_page_header(
    Parquet_Pulse_Toplevel_bytes input, size_t* poffset) {
  try {
    parse_page_header_thrift(input.data + *poffset, input.len - *poffset);
    *poffset = input.len;
    return true;
  } catch (apache::thrift::protocol::TProtocolException&) {
    return false;
  }
}

extern "C" Parquet_Pulse_Toplevel_page_header Parquet_Pulse_Toplevel0_read_page_header(
    Parquet_Pulse_Toplevel_bytes input) {
  parquet::PageHeader ph = parse_page_header_thrift(input.data, input.len);
  return to_pulse_page_header(ph);
}

// ------ free helpers (do NOT free any strings) ------

// static void free_vec_strings(Parquet_Pulse_Toplevel_vec__Prims_string v) {
//   std::free(v.data);
// }
//
// static void free_vec_encodings(
//     Parquet_Pulse_Toplevel_vec__Parquet_Pulse_Toplevel_encoding v) {
//   std::free(v.data);
// }
//
// static void free_vec_page_encoding_stats(
//     Parquet_Pulse_Toplevel_vec__Parquet_Pulse_Toplevel_page_encoding_stats v) {
//   std::free(v.data);
// }
//
// static void free_vec_key_values(
//     Parquet_Pulse_Toplevel_vec__Parquet_Pulse_Toplevel_key_value v) {
//   std::free(v.data);
// }
//
// static void free_vec_schema(
//     Parquet_Pulse_Toplevel_vec__Parquet_Pulse_Toplevel_schema_element v) {
//   std::free(v.data);
// }
//
// static void free_column_meta_data(Parquet_Pulse_Toplevel_column_meta_data& md) {
//   free_vec_encodings(md.encodings);
//   free_vec_strings(md.path_in_schema);
//   if (md.key_value_metadata.tag == FStar_Pervasives_Native_Some) {
//     free_vec_key_values(md.key_value_metadata.v);
//   }
//   if (md.encoding_stats.tag == FStar_Pervasives_Native_Some) {
//     free_vec_page_encoding_stats(md.encoding_stats.v);
//   }
// }
//
// static void free_vec_column_chunks(
//     Parquet_Pulse_Vec_vec__Parquet_Pulse_Toplevel_column_chunk v) {
//   for (size_t i = 0; i < v.len; ++i) {
//     Parquet_Pulse_Toplevel_column_chunk& cc = v.data[i];
//     if (cc.meta_data.tag == FStar_Pervasives_Native_Some) {
//       free_column_meta_data(cc.meta_data.v);
//     }
//   }
//   std::free(v.data);
// }
//
// static void free_vec_row_groups(
//     Parquet_Pulse_Toplevel_vec__Parquet_Pulse_Toplevel_row_group v) {
//   for (size_t i = 0; i < v.len; ++i) {
//     free_vec_column_chunks(v.data[i].columns);
//   }
//   std::free(v.data);
// }
//
// void free_file_metadata(Parquet_Pulse_Toplevel_file_meta_data& m) {
//   free_vec_schema(m.schema);
//
//   free_vec_row_groups(m.row_groups);
//
//   if (m.key_value_metadata1.tag == FStar_Pervasives_Native_Some) {
//     free_vec_key_values(m.key_value_metadata1.v);
//   }
//
//   if (m.column_orders.tag == FStar_Pervasives_Native_Some) {
//     std::free(m.column_orders.v.data);
//   }
// }

}  // namespace shim_parquet_pulse
