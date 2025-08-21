module Parquet.Pulse.Toplevel
#lang-pulse
open Pulse.Lib.Pervasives
// include LowParse.Pulse.Base
// include Parquet.Spec.Jump

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module Vec = Pulse.Lib.Vec

module U32 = FStar.UInt32

module U8 = FStar.UInt8

module I8 = FStar.Int8

module I16 = FStar.Int16

module I32 = FStar.Int32

module I64 = FStar.Int64

module Seq = FStar.Seq

module List = FStar.List

open FStar.Real

open FStar.List.Tot

// a custom vector type for extractionnoeq
noeq
type vec (t:Type0) = {
  data: Vec.vec t;
  len: (len:SZ.t { SZ.v len == Vec.length data });
}

type byte = U8.byte
type bytes = vec byte

// Enumerated Types

[@@no_auto_projectors]
type physical_type =
  | BOOLEAN
  | INT32
  | INT64
  | INT96
  | FLOAT
  | DOUBLE
  | BYTE_ARRAY
  | FIXED_LEN_BYTE_ARRAY

[@@no_auto_projectors]
type converted_type =
  | DEPRECATED_UTF8
  | DEPRECATED_MAP
  | DEPRECATED_MAP_KEY_VALUE
  | DEPRECATED_LIST
  | DEPRECATED_ENUM
  | DEPRECATED_DECIMAL
  | DEPRECATED_DATE
  | DEPRECATED_TIME_MILLIS
  | DEPRECATED_TIME_MICROS
  | DEPRECATED_TIMESTAMP_MILLIS
  | DEPRECATED_TIMESTAMP_MICROS
  | DEPRECATED_UINT_8
  | DEPRECATED_UINT_16
  | DEPRECATED_UINT_32
  | DEPRECATED_UINT_64
  | DEPRECATED_INT_8
  | DEPRECATED_INT_16
  | DEPRECATED_INT_32
  | DEPRECATED_INT_64
  | DEPRECATED_JSON
  | DEPRECATED_BSON
  | DEPRECATED_INTERVAL

[@@no_auto_projectors]
type field_repetition_type =
  | REQUIRED
  | OPTIONAL
  | REPEATED

[@@no_auto_projectors]
type encoding =
  | PLAIN
  | GROUP_VAR_INT of (squash False) // deprecated; a hack s.t. the numbers of the variants are corrected 
  | PLAIN_DICTIONARY
  | RLE
  | BIT_PACKED
  | DELTA_BINARY_PACKED
  | DELTA_LENGTH_BYTE_ARRAY
  | DELTA_BYTE_ARRAY
  | RLE_DICTIONARY
  | BYTE_STREAM_SPLIT

[@@no_auto_projectors]
type compression_codec =
  | UNCOMPRESSED
  | SNAPPY
  | GZIP
  | LZO
  | BROTLI
  | LZ4
  | ZSTD
  | LZ4_RAW

[@@no_auto_projectors]
type page_type =
  | DATA_PAGE
  | INDEX_PAGE
  | DICTIONARY_PAGE
  | DATA_PAGE_V2

[@@no_auto_projectors]
type boundary_order =
  | UNORDERED
  | ASCENDING
  | DESCENDING

[@@no_auto_projectors]
type edge_interpolation_algorithm =
  | SPHERICAL
  | VINCENTY
  | THOMAS
  | ANDOYER
  | KARNEY



// Statistics and Metadata Structures

type int64 = I64.t

type int32 = I32.t

type int16 = I16.t

type int8 = I8.t

noeq
type size_statistics = {
  unencoded_byte_array_data_bytes:option int64;
  repetition_level_histogram:option (vec int64);
  definition_level_histogram:option (vec int64)
}

noeq
type bounding_box = {
  xmin:real;
  xmax:real;
  ymin:real;
  ymax:real;
  zmin:option real;
  zmax:option real;
  mmin:option real;
  mmax:option real
}

noeq
type geospatial_statistics = {
  bbox:option bounding_box;
  geospatial_types:option (vec int32)
}

noeq
type statistics = {
  max:option bytes;
  min:option bytes;
  null_count:option int64;
  distinct_count:option int64;
  max_value:option bytes;
  min_value:option bytes;
  is_max_value_exact:option bool;
  is_min_value_exact:option bool
}



// Logical Types

type string_type = unit

type uuid_type = unit

type map_type = unit

type list_type = unit

type enum_type = unit

type date_type = unit

type float16_type = unit

type null_type = unit

type json_type = unit

type bson_type = unit

type decimal_type = {
  scale:int32;
  precision:int32
}

type milli_seconds = unit

type micro_seconds = unit

type nano_seconds = unit

type time_unit =
  | MILLIS of milli_seconds
  | MICROS of micro_seconds
  | NANOS of nano_seconds

type timestamp_type = {
  isAdjustedToUTC:bool;
  unit:time_unit
}

type time_type = {
  isAdjustedToUTC:bool;
  unit:time_unit
}

type int_type = {
  bitWidth:int8;
  isSigned:bool
}

type variant_type = { specification_version:option int8 }

type geometry_type = { crs:option string }

type geography_type = {
  crs:option string;
  algorithm:option edge_interpolation_algorithm
}

type logical_type =
  | STRING of string_type
  | MAP of map_type
  | LIST of list_type
  | ENUM of enum_type
  | DECIMAL of decimal_type
  | DATE of date_type
  | TIME of time_type
  | TIMESTAMP of timestamp_type
  | INTEGER of int_type
  | UNKNOWN of null_type
  | JSON of json_type
  | BSON of bson_type
  | UUID of uuid_type
  | FLOAT16 of float16_type
  | VARIANT of variant_type
  | GEOMETRY of geometry_type
  | GEOGRAPHY of geography_type



// Schema elements

type schema_element = {
  type_:option physical_type;
  type_length:option int32;
  repetition_type:option field_repetition_type;
  name:string;
  num_children:option int32;
  converted_type:option converted_type;
  scale:option int32;
  precision:option int32;
  field_id:option int32;
  logical_type:option logical_type
}



// Page structures

noeq
type data_page_header = {
  num_values:int32;
  encoding_:encoding;
  definition_level_encoding:encoding;
  repetition_level_encoding:encoding;
  statistics:option statistics
}

type index_page_header = unit

type dictionary_page_header = {
  num_values:int32;
  encoding:encoding;
  is_sorted:option bool
}

noeq
type data_page_header_v2 = {
  num_values:int32;
  num_nulls:int32;
  num_rows:int32;
  encoding:encoding;
  definition_levels_byte_length:int32;
  repetition_levels_byte_length:int32;
  is_compressed:option bool;
  statistics:option statistics
}



// Bloom Filters

type split_block_algorithm = unit

type bloom_filter_algorithm = | BLOCK of split_block_algorithm

type xx_hash = unit

type bloom_filter_hash = | XXHASH of xx_hash

type uncompressed = unit

type bloom_filter_compression = | UN_COMPRESSED of uncompressed

type bloom_filter_header = {
  numBytes:int32;
  algorithm:bloom_filter_algorithm;
  hash:bloom_filter_hash;
  compression:bloom_filter_compression
}



// Column chunks

// type page_header_variants =
//   | DATA_PAGE_HEADER of data_page_header
//   | INDEX_PAGE_HEADER of index_page_header
//   | DICTIONARY_PAGE_HEADER of dictionary_page_header
//   | DATA_PAGE_HEADER_V2 of data_page_header_v2

noeq
type page_header = {
  ptype:page_type;
  uncompressed_page_size:int32;
  compressed_page_size:int32;
  crc:option int32;
  data_page_header:option data_page_header;
  index_page_header:option index_page_header;
  dictionary_page_header:option dictionary_page_header;
  data_page_header_v2:option data_page_header_v2
}



// header:page_header_variants // sum type instead of "tagged union"

type key_value = {
  key:string;
  value:option string
}

type sorting_column = {
  column_idx:int32;
  descending:bool;
  nulls_first:bool
}

type page_encoding_stats = {
  page_type:page_type;
  encoding:encoding;
  count:int32
}

noeq
type column_meta_data = {
  physical_type:physical_type;
  encodings:vec encoding;
  path_in_schema:vec string;
  codec:compression_codec;
  num_values:int64;
  total_uncompressed_size:int64;
  total_compressed_size:int64;
  key_value_metadata:option (vec key_value);
  data_page_offset:int64;
  index_page_offset:option int64;
  dictionary_page_offset:option int64;
  statistics:option statistics;
  encoding_stats:option (vec page_encoding_stats);
  bloom_filter_offset:option int64;
  bloom_filter_length:option int32;
  size_statistics:option size_statistics;
  geospatial_statistics:option geospatial_statistics
}

type encryption_with_footer_key = unit

noeq
type encryption_with_column_key = {
  path_in_schema:vec string;
  key_metadata:option string
}

noeq
type column_crypto_meta_data =
  | ENCRYPTION_WITH_FOOTER_KEY of encryption_with_footer_key
  | ENCRYPTION_WITH_COLUMN_KEY of encryption_with_column_key

noeq
type column_chunk = {
  file_path:option string;
  file_offset:int64;
  meta_data:option column_meta_data; // can be required for featherweight parquet
  offset_index_offset:option int64;
  offset_index_length:option int32;
  column_index_offset:option int64;
  column_index_length:option int32;
  crypto_metadata:option column_crypto_meta_data;
  encrypted_column_metadata:option string
}

noeq
type row_group = {
  columns:vec column_chunk;
  total_byte_size:int64;
  num_rows:int64;
  sorting_columns:option (vec sorting_column);
  file_offset:option int64;
  total_compressed_size:option int64;
  ordinal:option int16
}

type type_defined_order = unit

type column_order = | TYPE_ORDER of type_defined_order

type page_location = {
  offset:int64;
  compressed_page_size:int32;
  first_row_index:int64
}

noeq
type offset_index = {
  page_locations:vec page_location;
  unencoded_byte_array_data_bytes:option (vec int64)
}

noeq
type column_index = {
  null_pages:vec bool;
  min_values:vec string;
  max_values:vec string;
  boundary_order:boundary_order;
  null_counts:option (vec int64);
  repetition_level_histograms:option (vec int64);
  definition_level_histograms:option (Vec.vec int64)
}

type aes_gcm_v1 = {
  aad_prefix:option string;
  aad_file_unique:option string;
  supply_aad_prefix:option bool
}

type aes_gcm_ctr_v1 = {
  aad_prefix:option string;
  aad_file_unique:option string;
  supply_aad_prefix:option bool
}

type encryption_algorithm =
  | AES_GCM_V1 of aes_gcm_v1
  | AES_GCM_CTR_V1 of aes_gcm_ctr_v1

noeq
type file_meta_data = {
  version:int32;
  schema:vec schema_element;
  num_rows:int64;
  row_groups:vec row_group;
  key_value_metadata:option (vec key_value);
  created_by:option string;
  column_orders:option (vec column_order);
  encryption_algorithm:option encryption_algorithm;
  footer_signing_key_metadata:option string
}

type file_crypto_meta_data = {
  encryption_algorithm:encryption_algorithm;
  key_metadata:option string
}

