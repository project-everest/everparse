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

open Parquet.Pulse.Vec

module PS = Parquet.Spec.Toplevel

type byte = U8.byte
type bytes = vec byte

// Enumerated Types

type physical_type = PS.physical_type

type converted_type = PS.converted_type

type field_repetition_type = PS.field_repetition_type

type encoding = PS.encoding

type compression_codec = PS.compression_codec
  
type page_type = PS.page_type

type boundary_order = PS.boundary_order

type edge_interpolation_algorithm = PS.edge_interpolation_algorithm

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

type bounding_box = PS.bounding_box

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

type string_type = PS.string_type

type uuid_type = PS.uuid_type

type map_type = PS.map_type

type list_type = PS.list_type

type enum_type = PS.enum_type

type date_type = PS.date_type

type float16_type = PS.float16_type

type null_type = PS.null_type

type json_type = PS.json_type

type bson_type = PS.bson_type

type decimal_type = PS.decimal_type

type milli_seconds = PS.milli_seconds

type micro_seconds = PS.micro_seconds

type nano_seconds = PS.nano_seconds

type time_unit = PS.time_unit

type timestamp_type = PS.timestamp_type

type time_type = PS.time_type

type int_type = PS.int_type

type variant_type = PS.variant_type

type geometry_type = PS.geometry_type

type geography_type = PS.geography_type

type logical_type = PS.logical_type

// Schema elements

type schema_element = PS.schema_element

// Page structures

noeq
type data_page_header = {
  num_values:int32;
  encoding_:encoding;
  definition_level_encoding:encoding;
  repetition_level_encoding:encoding;
  statistics:option statistics
}

type index_page_header = PS.index_page_header

type dictionary_page_header = PS.dictionary_page_header

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

type split_block_algorithm = PS.split_block_algorithm

type bloom_filter_algorithm = PS.bloom_filter_algorithm

type xx_hash = PS.xx_hash

type bloom_filter_hash = PS.bloom_filter_hash

type uncompressed = PS.uncompressed

type bloom_filter_compression = PS.bloom_filter_compression

type bloom_filter_header = PS.bloom_filter_header



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

type key_value = PS.key_value

type sorting_column = PS.sorting_column

type page_encoding_stats = PS.page_encoding_stats

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

type encryption_with_footer_key = PS.encryption_with_footer_key

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

type type_defined_order = PS.type_defined_order

type column_order = PS.column_order

type page_location = PS.page_location

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
  definition_level_histograms:option (vec int64)
}

type aes_gcm_v1 = PS.aes_gcm_v1

type aes_gcm_ctr_v1 = PS.aes_gcm_ctr_v1

type encryption_algorithm = PS.encryption_algorithm

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

type file_crypto_meta_data = PS.file_crypto_meta_data

