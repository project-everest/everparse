open Prims
type byte = FStar_UInt8.t
type bytes = byte FStar_Seq_Base.seq
type physical_type =
  | BOOLEAN 
  | INT32 
  | INT64 
  | INT96 
  | FLOAT 
  | DOUBLE 
  | BYTE_ARRAY 
  | FIXED_LEN_BYTE_ARRAY 
let (uu___is_BOOLEAN : physical_type -> Prims.bool) =
  fun projectee -> match projectee with | BOOLEAN -> true | uu___ -> false
let (uu___is_INT32 : physical_type -> Prims.bool) =
  fun projectee -> match projectee with | INT32 -> true | uu___ -> false
let (uu___is_INT64 : physical_type -> Prims.bool) =
  fun projectee -> match projectee with | INT64 -> true | uu___ -> false
let (uu___is_INT96 : physical_type -> Prims.bool) =
  fun projectee -> match projectee with | INT96 -> true | uu___ -> false
let (uu___is_FLOAT : physical_type -> Prims.bool) =
  fun projectee -> match projectee with | FLOAT -> true | uu___ -> false
let (uu___is_DOUBLE : physical_type -> Prims.bool) =
  fun projectee -> match projectee with | DOUBLE -> true | uu___ -> false
let (uu___is_BYTE_ARRAY : physical_type -> Prims.bool) =
  fun projectee -> match projectee with | BYTE_ARRAY -> true | uu___ -> false
let (uu___is_FIXED_LEN_BYTE_ARRAY : physical_type -> Prims.bool) =
  fun projectee ->
    match projectee with | FIXED_LEN_BYTE_ARRAY -> true | uu___ -> false
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
let (uu___is_DEPRECATED_UTF8 : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_UTF8 -> true | uu___ -> false
let (uu___is_DEPRECATED_MAP : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_MAP -> true | uu___ -> false
let (uu___is_DEPRECATED_MAP_KEY_VALUE : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_MAP_KEY_VALUE -> true | uu___ -> false
let (uu___is_DEPRECATED_LIST : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_LIST -> true | uu___ -> false
let (uu___is_DEPRECATED_ENUM : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_ENUM -> true | uu___ -> false
let (uu___is_DEPRECATED_DECIMAL : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_DECIMAL -> true | uu___ -> false
let (uu___is_DEPRECATED_DATE : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_DATE -> true | uu___ -> false
let (uu___is_DEPRECATED_TIME_MILLIS : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_TIME_MILLIS -> true | uu___ -> false
let (uu___is_DEPRECATED_TIME_MICROS : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_TIME_MICROS -> true | uu___ -> false
let (uu___is_DEPRECATED_TIMESTAMP_MILLIS : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with
    | DEPRECATED_TIMESTAMP_MILLIS -> true
    | uu___ -> false
let (uu___is_DEPRECATED_TIMESTAMP_MICROS : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with
    | DEPRECATED_TIMESTAMP_MICROS -> true
    | uu___ -> false
let (uu___is_DEPRECATED_UINT_8 : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_UINT_8 -> true | uu___ -> false
let (uu___is_DEPRECATED_UINT_16 : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_UINT_16 -> true | uu___ -> false
let (uu___is_DEPRECATED_UINT_32 : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_UINT_32 -> true | uu___ -> false
let (uu___is_DEPRECATED_UINT_64 : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_UINT_64 -> true | uu___ -> false
let (uu___is_DEPRECATED_INT_8 : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_INT_8 -> true | uu___ -> false
let (uu___is_DEPRECATED_INT_16 : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_INT_16 -> true | uu___ -> false
let (uu___is_DEPRECATED_INT_32 : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_INT_32 -> true | uu___ -> false
let (uu___is_DEPRECATED_INT_64 : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_INT_64 -> true | uu___ -> false
let (uu___is_DEPRECATED_JSON : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_JSON -> true | uu___ -> false
let (uu___is_DEPRECATED_BSON : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_BSON -> true | uu___ -> false
let (uu___is_DEPRECATED_INTERVAL : converted_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DEPRECATED_INTERVAL -> true | uu___ -> false
type field_repetition_type =
  | REQUIRED 
  | OPTIONAL 
  | REPEATED 
let (uu___is_REQUIRED : field_repetition_type -> Prims.bool) =
  fun projectee -> match projectee with | REQUIRED -> true | uu___ -> false
let (uu___is_OPTIONAL : field_repetition_type -> Prims.bool) =
  fun projectee -> match projectee with | OPTIONAL -> true | uu___ -> false
let (uu___is_REPEATED : field_repetition_type -> Prims.bool) =
  fun projectee -> match projectee with | REPEATED -> true | uu___ -> false
type encoding =
  | PLAIN 
  | PLAIN_DICTIONARY 
  | RLE 
  | BIT_PACKED 
  | DELTA_BINARY_PACKED 
  | DELTA_LENGTH_BYTE_ARRAY 
  | DELTA_BYTE_ARRAY 
  | RLE_DICTIONARY 
  | BYTE_STREAM_SPLIT 
let (uu___is_PLAIN : encoding -> Prims.bool) =
  fun projectee -> match projectee with | PLAIN -> true | uu___ -> false
let (uu___is_PLAIN_DICTIONARY : encoding -> Prims.bool) =
  fun projectee ->
    match projectee with | PLAIN_DICTIONARY -> true | uu___ -> false
let (uu___is_RLE : encoding -> Prims.bool) =
  fun projectee -> match projectee with | RLE -> true | uu___ -> false
let (uu___is_BIT_PACKED : encoding -> Prims.bool) =
  fun projectee -> match projectee with | BIT_PACKED -> true | uu___ -> false
let (uu___is_DELTA_BINARY_PACKED : encoding -> Prims.bool) =
  fun projectee ->
    match projectee with | DELTA_BINARY_PACKED -> true | uu___ -> false
let (uu___is_DELTA_LENGTH_BYTE_ARRAY : encoding -> Prims.bool) =
  fun projectee ->
    match projectee with | DELTA_LENGTH_BYTE_ARRAY -> true | uu___ -> false
let (uu___is_DELTA_BYTE_ARRAY : encoding -> Prims.bool) =
  fun projectee ->
    match projectee with | DELTA_BYTE_ARRAY -> true | uu___ -> false
let (uu___is_RLE_DICTIONARY : encoding -> Prims.bool) =
  fun projectee ->
    match projectee with | RLE_DICTIONARY -> true | uu___ -> false
let (uu___is_BYTE_STREAM_SPLIT : encoding -> Prims.bool) =
  fun projectee ->
    match projectee with | BYTE_STREAM_SPLIT -> true | uu___ -> false
type compression_codec =
  | UNCOMPRESSED 
  | SNAPPY 
  | GZIP 
  | LZO 
  | BROTLI 
  | LZ4 
  | ZSTD 
  | LZ4_RAW 
let (uu___is_UNCOMPRESSED : compression_codec -> Prims.bool) =
  fun projectee ->
    match projectee with | UNCOMPRESSED -> true | uu___ -> false
let (uu___is_SNAPPY : compression_codec -> Prims.bool) =
  fun projectee -> match projectee with | SNAPPY -> true | uu___ -> false
let (uu___is_GZIP : compression_codec -> Prims.bool) =
  fun projectee -> match projectee with | GZIP -> true | uu___ -> false
let (uu___is_LZO : compression_codec -> Prims.bool) =
  fun projectee -> match projectee with | LZO -> true | uu___ -> false
let (uu___is_BROTLI : compression_codec -> Prims.bool) =
  fun projectee -> match projectee with | BROTLI -> true | uu___ -> false
let (uu___is_LZ4 : compression_codec -> Prims.bool) =
  fun projectee -> match projectee with | LZ4 -> true | uu___ -> false
let (uu___is_ZSTD : compression_codec -> Prims.bool) =
  fun projectee -> match projectee with | ZSTD -> true | uu___ -> false
let (uu___is_LZ4_RAW : compression_codec -> Prims.bool) =
  fun projectee -> match projectee with | LZ4_RAW -> true | uu___ -> false
type page_type =
  | DATA_PAGE 
  | INDEX_PAGE 
  | DICTIONARY_PAGE 
  | DATA_PAGE_V2 
let (uu___is_DATA_PAGE : page_type -> Prims.bool) =
  fun projectee -> match projectee with | DATA_PAGE -> true | uu___ -> false
let (uu___is_INDEX_PAGE : page_type -> Prims.bool) =
  fun projectee -> match projectee with | INDEX_PAGE -> true | uu___ -> false
let (uu___is_DICTIONARY_PAGE : page_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DICTIONARY_PAGE -> true | uu___ -> false
let (uu___is_DATA_PAGE_V2 : page_type -> Prims.bool) =
  fun projectee ->
    match projectee with | DATA_PAGE_V2 -> true | uu___ -> false
type boundary_order =
  | UNORDERED 
  | ASCENDING 
  | DESCENDING 
let (uu___is_UNORDERED : boundary_order -> Prims.bool) =
  fun projectee -> match projectee with | UNORDERED -> true | uu___ -> false
let (uu___is_ASCENDING : boundary_order -> Prims.bool) =
  fun projectee -> match projectee with | ASCENDING -> true | uu___ -> false
let (uu___is_DESCENDING : boundary_order -> Prims.bool) =
  fun projectee -> match projectee with | DESCENDING -> true | uu___ -> false
type edge_interpolation_algorithm =
  | SPHERICAL 
  | VINCENTY 
  | THOMAS 
  | ANDOYER 
  | KARNEY 
let (uu___is_SPHERICAL : edge_interpolation_algorithm -> Prims.bool) =
  fun projectee -> match projectee with | SPHERICAL -> true | uu___ -> false
let (uu___is_VINCENTY : edge_interpolation_algorithm -> Prims.bool) =
  fun projectee -> match projectee with | VINCENTY -> true | uu___ -> false
let (uu___is_THOMAS : edge_interpolation_algorithm -> Prims.bool) =
  fun projectee -> match projectee with | THOMAS -> true | uu___ -> false
let (uu___is_ANDOYER : edge_interpolation_algorithm -> Prims.bool) =
  fun projectee -> match projectee with | ANDOYER -> true | uu___ -> false
let (uu___is_KARNEY : edge_interpolation_algorithm -> Prims.bool) =
  fun projectee -> match projectee with | KARNEY -> true | uu___ -> false
type int64 = FStar_Int64.t
type int32 = FStar_Int32.t
type int16 = FStar_Int16.t
type int8 = FStar_Int8.t
type size_statistics =
  {
  unencoded_byte_array_data_bytes: int64 FStar_Pervasives_Native.option ;
  repetition_level_histogram: int64 Prims.list FStar_Pervasives_Native.option ;
  definition_level_histogram: int64 Prims.list FStar_Pervasives_Native.option }
let (__proj__Mksize_statistics__item__unencoded_byte_array_data_bytes :
  size_statistics -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { unencoded_byte_array_data_bytes; repetition_level_histogram;
        definition_level_histogram;_} -> unencoded_byte_array_data_bytes
let (__proj__Mksize_statistics__item__repetition_level_histogram :
  size_statistics -> int64 Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { unencoded_byte_array_data_bytes; repetition_level_histogram;
        definition_level_histogram;_} -> repetition_level_histogram
let (__proj__Mksize_statistics__item__definition_level_histogram :
  size_statistics -> int64 Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { unencoded_byte_array_data_bytes; repetition_level_histogram;
        definition_level_histogram;_} -> definition_level_histogram
type bounding_box =
  {
  xmin: unit ;
  xmax: unit ;
  ymin: unit ;
  ymax: unit ;
  zmin: unit FStar_Pervasives_Native.option ;
  zmax: unit FStar_Pervasives_Native.option ;
  mmin: unit FStar_Pervasives_Native.option ;
  mmax: unit FStar_Pervasives_Native.option }
let (__proj__Mkbounding_box__item__zmin :
  bounding_box -> unit FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { xmin; xmax; ymin; ymax; zmin; zmax; mmin; mmax;_} -> zmin
let (__proj__Mkbounding_box__item__zmax :
  bounding_box -> unit FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { xmin; xmax; ymin; ymax; zmin; zmax; mmin; mmax;_} -> zmax
let (__proj__Mkbounding_box__item__mmin :
  bounding_box -> unit FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { xmin; xmax; ymin; ymax; zmin; zmax; mmin; mmax;_} -> mmin
let (__proj__Mkbounding_box__item__mmax :
  bounding_box -> unit FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { xmin; xmax; ymin; ymax; zmin; zmax; mmin; mmax;_} -> mmax
type geospatial_statistics =
  {
  bbox: bounding_box FStar_Pervasives_Native.option ;
  geospatial_types: int32 Prims.list FStar_Pervasives_Native.option }
let (__proj__Mkgeospatial_statistics__item__bbox :
  geospatial_statistics -> bounding_box FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { bbox; geospatial_types;_} -> bbox
let (__proj__Mkgeospatial_statistics__item__geospatial_types :
  geospatial_statistics -> int32 Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { bbox; geospatial_types;_} -> geospatial_types
type statistics =
  {
  max: bytes FStar_Pervasives_Native.option ;
  min: bytes FStar_Pervasives_Native.option ;
  null_count: int64 FStar_Pervasives_Native.option ;
  distinct_count: int64 FStar_Pervasives_Native.option ;
  max_value: bytes FStar_Pervasives_Native.option ;
  min_value: bytes FStar_Pervasives_Native.option ;
  is_max_value_exact: Prims.bool FStar_Pervasives_Native.option ;
  is_min_value_exact: Prims.bool FStar_Pervasives_Native.option }
let (__proj__Mkstatistics__item__max :
  statistics -> bytes FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { max; min; null_count; distinct_count; max_value; min_value;
        is_max_value_exact; is_min_value_exact;_} -> max
let (__proj__Mkstatistics__item__min :
  statistics -> bytes FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { max; min; null_count; distinct_count; max_value; min_value;
        is_max_value_exact; is_min_value_exact;_} -> min
let (__proj__Mkstatistics__item__null_count :
  statistics -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { max; min; null_count; distinct_count; max_value; min_value;
        is_max_value_exact; is_min_value_exact;_} -> null_count
let (__proj__Mkstatistics__item__distinct_count :
  statistics -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { max; min; null_count; distinct_count; max_value; min_value;
        is_max_value_exact; is_min_value_exact;_} -> distinct_count
let (__proj__Mkstatistics__item__max_value :
  statistics -> bytes FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { max; min; null_count; distinct_count; max_value; min_value;
        is_max_value_exact; is_min_value_exact;_} -> max_value
let (__proj__Mkstatistics__item__min_value :
  statistics -> bytes FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { max; min; null_count; distinct_count; max_value; min_value;
        is_max_value_exact; is_min_value_exact;_} -> min_value
let (__proj__Mkstatistics__item__is_max_value_exact :
  statistics -> Prims.bool FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { max; min; null_count; distinct_count; max_value; min_value;
        is_max_value_exact; is_min_value_exact;_} -> is_max_value_exact
let (__proj__Mkstatistics__item__is_min_value_exact :
  statistics -> Prims.bool FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { max; min; null_count; distinct_count; max_value; min_value;
        is_max_value_exact; is_min_value_exact;_} -> is_min_value_exact
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
  scale: int32 ;
  precision: int32 }
let (__proj__Mkdecimal_type__item__scale : decimal_type -> int32) =
  fun projectee -> match projectee with | { scale; precision;_} -> scale
let (__proj__Mkdecimal_type__item__precision : decimal_type -> int32) =
  fun projectee -> match projectee with | { scale; precision;_} -> precision
type milli_seconds = unit
type micro_seconds = unit
type nano_seconds = unit
type time_unit =
  | MILLIS of unit 
  | MICROS of unit 
  | NANOS of unit 
let (uu___is_MILLIS : time_unit -> Prims.bool) =
  fun projectee -> match projectee with | MILLIS _0 -> true | uu___ -> false

let (uu___is_MICROS : time_unit -> Prims.bool) =
  fun projectee -> match projectee with | MICROS _0 -> true | uu___ -> false

let (uu___is_NANOS : time_unit -> Prims.bool) =
  fun projectee -> match projectee with | NANOS _0 -> true | uu___ -> false

type timestamp_type = {
  isAdjustedToUTC: Prims.bool ;
  unit: time_unit }
let (__proj__Mktimestamp_type__item__isAdjustedToUTC :
  timestamp_type -> Prims.bool) =
  fun projectee ->
    match projectee with | { isAdjustedToUTC; unit;_} -> isAdjustedToUTC
let (__proj__Mktimestamp_type__item__unit : timestamp_type -> time_unit) =
  fun projectee -> match projectee with | { isAdjustedToUTC; unit;_} -> unit
type time_type = {
  isAdjustedToUTC1: Prims.bool ;
  unit1: time_unit }
let (__proj__Mktime_type__item__isAdjustedToUTC : time_type -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { isAdjustedToUTC1 = isAdjustedToUTC; unit1 = unit;_} ->
        isAdjustedToUTC
let (__proj__Mktime_type__item__unit : time_type -> time_unit) =
  fun projectee ->
    match projectee with
    | { isAdjustedToUTC1 = isAdjustedToUTC; unit1 = unit;_} -> unit
type int_type = {
  bitWidth: int8 ;
  isSigned: Prims.bool }
let (__proj__Mkint_type__item__bitWidth : int_type -> int8) =
  fun projectee -> match projectee with | { bitWidth; isSigned;_} -> bitWidth
let (__proj__Mkint_type__item__isSigned : int_type -> Prims.bool) =
  fun projectee -> match projectee with | { bitWidth; isSigned;_} -> isSigned
type variant_type =
  {
  specification_version: int8 FStar_Pervasives_Native.option }
let (__proj__Mkvariant_type__item__specification_version :
  variant_type -> int8 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { specification_version;_} -> specification_version
type geometry_type = {
  crs: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkgeometry_type__item__crs :
  geometry_type -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { crs;_} -> crs
type geography_type =
  {
  crs1: Prims.string FStar_Pervasives_Native.option ;
  algorithm: edge_interpolation_algorithm FStar_Pervasives_Native.option }
let (__proj__Mkgeography_type__item__crs :
  geography_type -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { crs1 = crs; algorithm;_} -> crs
let (__proj__Mkgeography_type__item__algorithm :
  geography_type ->
    edge_interpolation_algorithm FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with | { crs1 = crs; algorithm;_} -> algorithm
type logical_type =
  | STRING of unit 
  | MAP of unit 
  | LIST of unit 
  | ENUM of unit 
  | DECIMAL of decimal_type 
  | DATE of unit 
  | TIME of time_type 
  | TIMESTAMP of timestamp_type 
  | INTEGER of int_type 
  | UNKNOWN of unit 
  | JSON of unit 
  | BSON of unit 
  | UUID of unit 
  | FLOAT16 of unit 
  | VARIANT of variant_type 
  | GEOMETRY of geometry_type 
  | GEOGRAPHY of geography_type 
let (uu___is_STRING : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | STRING _0 -> true | uu___ -> false

let (uu___is_MAP : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | MAP _0 -> true | uu___ -> false

let (uu___is_LIST : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | LIST _0 -> true | uu___ -> false

let (uu___is_ENUM : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | ENUM _0 -> true | uu___ -> false

let (uu___is_DECIMAL : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | DECIMAL _0 -> true | uu___ -> false
let (__proj__DECIMAL__item___0 : logical_type -> decimal_type) =
  fun projectee -> match projectee with | DECIMAL _0 -> _0
let (uu___is_DATE : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | DATE _0 -> true | uu___ -> false

let (uu___is_TIME : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | TIME _0 -> true | uu___ -> false
let (__proj__TIME__item___0 : logical_type -> time_type) =
  fun projectee -> match projectee with | TIME _0 -> _0
let (uu___is_TIMESTAMP : logical_type -> Prims.bool) =
  fun projectee ->
    match projectee with | TIMESTAMP _0 -> true | uu___ -> false
let (__proj__TIMESTAMP__item___0 : logical_type -> timestamp_type) =
  fun projectee -> match projectee with | TIMESTAMP _0 -> _0
let (uu___is_INTEGER : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | INTEGER _0 -> true | uu___ -> false
let (__proj__INTEGER__item___0 : logical_type -> int_type) =
  fun projectee -> match projectee with | INTEGER _0 -> _0
let (uu___is_UNKNOWN : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | UNKNOWN _0 -> true | uu___ -> false

let (uu___is_JSON : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | JSON _0 -> true | uu___ -> false

let (uu___is_BSON : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | BSON _0 -> true | uu___ -> false

let (uu___is_UUID : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | UUID _0 -> true | uu___ -> false

let (uu___is_FLOAT16 : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | FLOAT16 _0 -> true | uu___ -> false

let (uu___is_VARIANT : logical_type -> Prims.bool) =
  fun projectee -> match projectee with | VARIANT _0 -> true | uu___ -> false
let (__proj__VARIANT__item___0 : logical_type -> variant_type) =
  fun projectee -> match projectee with | VARIANT _0 -> _0
let (uu___is_GEOMETRY : logical_type -> Prims.bool) =
  fun projectee ->
    match projectee with | GEOMETRY _0 -> true | uu___ -> false
let (__proj__GEOMETRY__item___0 : logical_type -> geometry_type) =
  fun projectee -> match projectee with | GEOMETRY _0 -> _0
let (uu___is_GEOGRAPHY : logical_type -> Prims.bool) =
  fun projectee ->
    match projectee with | GEOGRAPHY _0 -> true | uu___ -> false
let (__proj__GEOGRAPHY__item___0 : logical_type -> geography_type) =
  fun projectee -> match projectee with | GEOGRAPHY _0 -> _0
type schema_element =
  {
  type_: physical_type FStar_Pervasives_Native.option ;
  type_length: int32 FStar_Pervasives_Native.option ;
  repetition_type: field_repetition_type FStar_Pervasives_Native.option ;
  name: Prims.string ;
  num_children: int32 FStar_Pervasives_Native.option ;
  converted_type: converted_type FStar_Pervasives_Native.option ;
  scale1: int32 FStar_Pervasives_Native.option ;
  precision1: int32 FStar_Pervasives_Native.option ;
  field_id: int32 FStar_Pervasives_Native.option ;
  logical_type: logical_type FStar_Pervasives_Native.option }
let (__proj__Mkschema_element__item__type_ :
  schema_element -> physical_type FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        type_
let (__proj__Mkschema_element__item__type_length :
  schema_element -> int32 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        type_length
let (__proj__Mkschema_element__item__repetition_type :
  schema_element -> field_repetition_type FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        repetition_type
let (__proj__Mkschema_element__item__name : schema_element -> Prims.string) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        name
let (__proj__Mkschema_element__item__num_children :
  schema_element -> int32 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        num_children
let (__proj__Mkschema_element__item__converted_type :
  schema_element -> converted_type FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        converted_type1
let (__proj__Mkschema_element__item__scale :
  schema_element -> int32 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        scale
let (__proj__Mkschema_element__item__precision :
  schema_element -> int32 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        precision
let (__proj__Mkschema_element__item__field_id :
  schema_element -> int32 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        field_id
let (__proj__Mkschema_element__item__logical_type :
  schema_element -> logical_type FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { type_; type_length; repetition_type; name; num_children;
        converted_type = converted_type1; scale1 = scale;
        precision1 = precision; field_id; logical_type = logical_type1;_} ->
        logical_type1
type data_page_header =
  {
  num_values: int32 ;
  encoding_: encoding ;
  definition_level_encoding: encoding ;
  repetition_level_encoding: encoding ;
  statistics: statistics FStar_Pervasives_Native.option }
let (__proj__Mkdata_page_header__item__num_values :
  data_page_header -> int32) =
  fun projectee ->
    match projectee with
    | { num_values; encoding_; definition_level_encoding;
        repetition_level_encoding; statistics = statistics1;_} -> num_values
let (__proj__Mkdata_page_header__item__encoding_ :
  data_page_header -> encoding) =
  fun projectee ->
    match projectee with
    | { num_values; encoding_; definition_level_encoding;
        repetition_level_encoding; statistics = statistics1;_} -> encoding_
let (__proj__Mkdata_page_header__item__definition_level_encoding :
  data_page_header -> encoding) =
  fun projectee ->
    match projectee with
    | { num_values; encoding_; definition_level_encoding;
        repetition_level_encoding; statistics = statistics1;_} ->
        definition_level_encoding
let (__proj__Mkdata_page_header__item__repetition_level_encoding :
  data_page_header -> encoding) =
  fun projectee ->
    match projectee with
    | { num_values; encoding_; definition_level_encoding;
        repetition_level_encoding; statistics = statistics1;_} ->
        repetition_level_encoding
let (__proj__Mkdata_page_header__item__statistics :
  data_page_header -> statistics FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { num_values; encoding_; definition_level_encoding;
        repetition_level_encoding; statistics = statistics1;_} -> statistics1
type index_page_header = unit
type dictionary_page_header =
  {
  num_values1: int32 ;
  encoding: encoding ;
  is_sorted: Prims.bool FStar_Pervasives_Native.option }
let (__proj__Mkdictionary_page_header__item__num_values :
  dictionary_page_header -> int32) =
  fun projectee ->
    match projectee with
    | { num_values1 = num_values; encoding = encoding1; is_sorted;_} ->
        num_values
let (__proj__Mkdictionary_page_header__item__encoding :
  dictionary_page_header -> encoding) =
  fun projectee ->
    match projectee with
    | { num_values1 = num_values; encoding = encoding1; is_sorted;_} ->
        encoding1
let (__proj__Mkdictionary_page_header__item__is_sorted :
  dictionary_page_header -> Prims.bool FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { num_values1 = num_values; encoding = encoding1; is_sorted;_} ->
        is_sorted
type data_page_header_v2 =
  {
  num_values2: int32 ;
  num_nulls: int32 ;
  num_rows: int32 ;
  encoding1: encoding ;
  definition_levels_byte_length: int32 ;
  repetition_levels_byte_length: int32 ;
  is_compressed: Prims.bool FStar_Pervasives_Native.option ;
  statistics1: statistics FStar_Pervasives_Native.option }
let (__proj__Mkdata_page_header_v2__item__num_values :
  data_page_header_v2 -> int32) =
  fun projectee ->
    match projectee with
    | { num_values2 = num_values; num_nulls; num_rows; encoding1;
        definition_levels_byte_length; repetition_levels_byte_length;
        is_compressed; statistics1;_} -> num_values
let (__proj__Mkdata_page_header_v2__item__num_nulls :
  data_page_header_v2 -> int32) =
  fun projectee ->
    match projectee with
    | { num_values2 = num_values; num_nulls; num_rows; encoding1;
        definition_levels_byte_length; repetition_levels_byte_length;
        is_compressed; statistics1;_} -> num_nulls
let (__proj__Mkdata_page_header_v2__item__num_rows :
  data_page_header_v2 -> int32) =
  fun projectee ->
    match projectee with
    | { num_values2 = num_values; num_nulls; num_rows; encoding1;
        definition_levels_byte_length; repetition_levels_byte_length;
        is_compressed; statistics1;_} -> num_rows
let (__proj__Mkdata_page_header_v2__item__encoding :
  data_page_header_v2 -> encoding) =
  fun projectee ->
    match projectee with
    | { num_values2 = num_values; num_nulls; num_rows; encoding1;
        definition_levels_byte_length; repetition_levels_byte_length;
        is_compressed; statistics1;_} -> encoding1
let (__proj__Mkdata_page_header_v2__item__definition_levels_byte_length :
  data_page_header_v2 -> int32) =
  fun projectee ->
    match projectee with
    | { num_values2 = num_values; num_nulls; num_rows; encoding1;
        definition_levels_byte_length; repetition_levels_byte_length;
        is_compressed; statistics1;_} -> definition_levels_byte_length
let (__proj__Mkdata_page_header_v2__item__repetition_levels_byte_length :
  data_page_header_v2 -> int32) =
  fun projectee ->
    match projectee with
    | { num_values2 = num_values; num_nulls; num_rows; encoding1;
        definition_levels_byte_length; repetition_levels_byte_length;
        is_compressed; statistics1;_} -> repetition_levels_byte_length
let (__proj__Mkdata_page_header_v2__item__is_compressed :
  data_page_header_v2 -> Prims.bool FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { num_values2 = num_values; num_nulls; num_rows; encoding1;
        definition_levels_byte_length; repetition_levels_byte_length;
        is_compressed; statistics1;_} -> is_compressed
let (__proj__Mkdata_page_header_v2__item__statistics :
  data_page_header_v2 -> statistics FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { num_values2 = num_values; num_nulls; num_rows; encoding1;
        definition_levels_byte_length; repetition_levels_byte_length;
        is_compressed; statistics1;_} -> statistics1
type split_block_algorithm = unit
type bloom_filter_algorithm =
  | BLOCK of unit 
let (uu___is_BLOCK : bloom_filter_algorithm -> Prims.bool) =
  fun projectee -> true

type xx_hash = unit
type bloom_filter_hash =
  | XXHASH of unit 
let (uu___is_XXHASH : bloom_filter_hash -> Prims.bool) =
  fun projectee -> true

type uncompressed = unit
type bloom_filter_compression =
  | UN_COMPRESSED of unit 
let (uu___is_UN_COMPRESSED : bloom_filter_compression -> Prims.bool) =
  fun projectee -> true

type bloom_filter_header =
  {
  numBytes: int32 ;
  algorithm1: bloom_filter_algorithm ;
  hash: bloom_filter_hash ;
  compression: bloom_filter_compression }
let (__proj__Mkbloom_filter_header__item__numBytes :
  bloom_filter_header -> int32) =
  fun projectee ->
    match projectee with
    | { numBytes; algorithm1 = algorithm; hash; compression;_} -> numBytes
let (__proj__Mkbloom_filter_header__item__algorithm :
  bloom_filter_header -> bloom_filter_algorithm) =
  fun projectee ->
    match projectee with
    | { numBytes; algorithm1 = algorithm; hash; compression;_} -> algorithm
let (__proj__Mkbloom_filter_header__item__hash :
  bloom_filter_header -> bloom_filter_hash) =
  fun projectee ->
    match projectee with
    | { numBytes; algorithm1 = algorithm; hash; compression;_} -> hash
let (__proj__Mkbloom_filter_header__item__compression :
  bloom_filter_header -> bloom_filter_compression) =
  fun projectee ->
    match projectee with
    | { numBytes; algorithm1 = algorithm; hash; compression;_} -> compression
type page_header =
  {
  ptype: page_type ;
  uncompressed_page_size: int32 ;
  compressed_page_size: int32 ;
  crc: int32 FStar_Pervasives_Native.option ;
  data_page_header: data_page_header FStar_Pervasives_Native.option ;
  index_page_header: unit FStar_Pervasives_Native.option ;
  dictionary_page_header:
    dictionary_page_header FStar_Pervasives_Native.option ;
  data_page_header_v2: data_page_header_v2 FStar_Pervasives_Native.option }
let (__proj__Mkpage_header__item__ptype : page_header -> page_type) =
  fun projectee ->
    match projectee with
    | { ptype; uncompressed_page_size; compressed_page_size; crc;
        data_page_header = data_page_header1;
        index_page_header = index_page_header1;
        dictionary_page_header = dictionary_page_header1;
        data_page_header_v2 = data_page_header_v21;_} -> ptype
let (__proj__Mkpage_header__item__uncompressed_page_size :
  page_header -> int32) =
  fun projectee ->
    match projectee with
    | { ptype; uncompressed_page_size; compressed_page_size; crc;
        data_page_header = data_page_header1;
        index_page_header = index_page_header1;
        dictionary_page_header = dictionary_page_header1;
        data_page_header_v2 = data_page_header_v21;_} ->
        uncompressed_page_size
let (__proj__Mkpage_header__item__compressed_page_size :
  page_header -> int32) =
  fun projectee ->
    match projectee with
    | { ptype; uncompressed_page_size; compressed_page_size; crc;
        data_page_header = data_page_header1;
        index_page_header = index_page_header1;
        dictionary_page_header = dictionary_page_header1;
        data_page_header_v2 = data_page_header_v21;_} -> compressed_page_size
let (__proj__Mkpage_header__item__crc :
  page_header -> int32 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ptype; uncompressed_page_size; compressed_page_size; crc;
        data_page_header = data_page_header1;
        index_page_header = index_page_header1;
        dictionary_page_header = dictionary_page_header1;
        data_page_header_v2 = data_page_header_v21;_} -> crc
let (__proj__Mkpage_header__item__data_page_header :
  page_header -> data_page_header FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ptype; uncompressed_page_size; compressed_page_size; crc;
        data_page_header = data_page_header1;
        index_page_header = index_page_header1;
        dictionary_page_header = dictionary_page_header1;
        data_page_header_v2 = data_page_header_v21;_} -> data_page_header1
let (__proj__Mkpage_header__item__index_page_header :
  page_header -> unit FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ptype; uncompressed_page_size; compressed_page_size; crc;
        data_page_header = data_page_header1;
        index_page_header = index_page_header1;
        dictionary_page_header = dictionary_page_header1;
        data_page_header_v2 = data_page_header_v21;_} -> index_page_header1
let (__proj__Mkpage_header__item__dictionary_page_header :
  page_header -> dictionary_page_header FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ptype; uncompressed_page_size; compressed_page_size; crc;
        data_page_header = data_page_header1;
        index_page_header = index_page_header1;
        dictionary_page_header = dictionary_page_header1;
        data_page_header_v2 = data_page_header_v21;_} ->
        dictionary_page_header1
let (__proj__Mkpage_header__item__data_page_header_v2 :
  page_header -> data_page_header_v2 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { ptype; uncompressed_page_size; compressed_page_size; crc;
        data_page_header = data_page_header1;
        index_page_header = index_page_header1;
        dictionary_page_header = dictionary_page_header1;
        data_page_header_v2 = data_page_header_v21;_} -> data_page_header_v21
type key_value =
  {
  key: Prims.string ;
  value: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkkey_value__item__key : key_value -> Prims.string) =
  fun projectee -> match projectee with | { key; value;_} -> key
let (__proj__Mkkey_value__item__value :
  key_value -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { key; value;_} -> value
type sorting_column =
  {
  column_idx: int32 ;
  descending: Prims.bool ;
  nulls_first: Prims.bool }
let (__proj__Mksorting_column__item__column_idx : sorting_column -> int32) =
  fun projectee ->
    match projectee with
    | { column_idx; descending; nulls_first;_} -> column_idx
let (__proj__Mksorting_column__item__descending :
  sorting_column -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { column_idx; descending; nulls_first;_} -> descending
let (__proj__Mksorting_column__item__nulls_first :
  sorting_column -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { column_idx; descending; nulls_first;_} -> nulls_first
type page_encoding_stats =
  {
  page_type: page_type ;
  encoding2: encoding ;
  count: int32 }
let (__proj__Mkpage_encoding_stats__item__page_type :
  page_encoding_stats -> page_type) =
  fun projectee ->
    match projectee with
    | { page_type = page_type1; encoding2 = encoding1; count;_} -> page_type1
let (__proj__Mkpage_encoding_stats__item__encoding :
  page_encoding_stats -> encoding) =
  fun projectee ->
    match projectee with
    | { page_type = page_type1; encoding2 = encoding1; count;_} -> encoding1
let (__proj__Mkpage_encoding_stats__item__count :
  page_encoding_stats -> int32) =
  fun projectee ->
    match projectee with
    | { page_type = page_type1; encoding2 = encoding1; count;_} -> count
type column_meta_data =
  {
  physical_type: physical_type ;
  encodings: encoding Prims.list ;
  path_in_schema: Prims.string Prims.list ;
  codec: compression_codec ;
  num_values3: int64 ;
  total_uncompressed_size: int64 ;
  total_compressed_size: int64 ;
  key_value_metadata: key_value Prims.list FStar_Pervasives_Native.option ;
  data_page_offset: int64 ;
  index_page_offset: int64 FStar_Pervasives_Native.option ;
  dictionary_page_offset: int64 FStar_Pervasives_Native.option ;
  statistics2: statistics FStar_Pervasives_Native.option ;
  encoding_stats:
    page_encoding_stats Prims.list FStar_Pervasives_Native.option ;
  bloom_filter_offset: int64 FStar_Pervasives_Native.option ;
  bloom_filter_length: int32 FStar_Pervasives_Native.option ;
  size_statistics: size_statistics FStar_Pervasives_Native.option ;
  geospatial_statistics: geospatial_statistics FStar_Pervasives_Native.option }
let (__proj__Mkcolumn_meta_data__item__physical_type :
  column_meta_data -> physical_type) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} -> physical_type1
let (__proj__Mkcolumn_meta_data__item__encodings :
  column_meta_data -> encoding Prims.list) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} -> encodings
let (__proj__Mkcolumn_meta_data__item__path_in_schema :
  column_meta_data -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} -> path_in_schema
let (__proj__Mkcolumn_meta_data__item__codec :
  column_meta_data -> compression_codec) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} -> codec
let (__proj__Mkcolumn_meta_data__item__num_values :
  column_meta_data -> int64) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} -> num_values
let (__proj__Mkcolumn_meta_data__item__total_uncompressed_size :
  column_meta_data -> int64) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} ->
        total_uncompressed_size
let (__proj__Mkcolumn_meta_data__item__total_compressed_size :
  column_meta_data -> int64) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} ->
        total_compressed_size
let (__proj__Mkcolumn_meta_data__item__key_value_metadata :
  column_meta_data -> key_value Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} ->
        key_value_metadata
let (__proj__Mkcolumn_meta_data__item__data_page_offset :
  column_meta_data -> int64) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} -> data_page_offset
let (__proj__Mkcolumn_meta_data__item__index_page_offset :
  column_meta_data -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} ->
        index_page_offset
let (__proj__Mkcolumn_meta_data__item__dictionary_page_offset :
  column_meta_data -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} ->
        dictionary_page_offset
let (__proj__Mkcolumn_meta_data__item__statistics :
  column_meta_data -> statistics FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} -> statistics1
let (__proj__Mkcolumn_meta_data__item__encoding_stats :
  column_meta_data ->
    page_encoding_stats Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} -> encoding_stats
let (__proj__Mkcolumn_meta_data__item__bloom_filter_offset :
  column_meta_data -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} ->
        bloom_filter_offset
let (__proj__Mkcolumn_meta_data__item__bloom_filter_length :
  column_meta_data -> int32 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} ->
        bloom_filter_length
let (__proj__Mkcolumn_meta_data__item__size_statistics :
  column_meta_data -> size_statistics FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} -> size_statistics1
let (__proj__Mkcolumn_meta_data__item__geospatial_statistics :
  column_meta_data -> geospatial_statistics FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { physical_type = physical_type1; encodings; path_in_schema; codec;
        num_values3 = num_values; total_uncompressed_size;
        total_compressed_size; key_value_metadata; data_page_offset;
        index_page_offset; dictionary_page_offset; statistics2 = statistics1;
        encoding_stats; bloom_filter_offset; bloom_filter_length;
        size_statistics = size_statistics1;
        geospatial_statistics = geospatial_statistics1;_} ->
        geospatial_statistics1
type encryption_with_footer_key = unit
type encryption_with_column_key =
  {
  path_in_schema1: Prims.string Prims.list ;
  key_metadata: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkencryption_with_column_key__item__path_in_schema :
  encryption_with_column_key -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { path_in_schema1 = path_in_schema; key_metadata;_} -> path_in_schema
let (__proj__Mkencryption_with_column_key__item__key_metadata :
  encryption_with_column_key -> Prims.string FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { path_in_schema1 = path_in_schema; key_metadata;_} -> key_metadata
type column_crypto_meta_data =
  | ENCRYPTION_WITH_FOOTER_KEY of unit 
  | ENCRYPTION_WITH_COLUMN_KEY of encryption_with_column_key 
let (uu___is_ENCRYPTION_WITH_FOOTER_KEY :
  column_crypto_meta_data -> Prims.bool) =
  fun projectee ->
    match projectee with
    | ENCRYPTION_WITH_FOOTER_KEY _0 -> true
    | uu___ -> false

let (uu___is_ENCRYPTION_WITH_COLUMN_KEY :
  column_crypto_meta_data -> Prims.bool) =
  fun projectee ->
    match projectee with
    | ENCRYPTION_WITH_COLUMN_KEY _0 -> true
    | uu___ -> false
let (__proj__ENCRYPTION_WITH_COLUMN_KEY__item___0 :
  column_crypto_meta_data -> encryption_with_column_key) =
  fun projectee -> match projectee with | ENCRYPTION_WITH_COLUMN_KEY _0 -> _0
type column_chunk =
  {
  file_path: Prims.string FStar_Pervasives_Native.option ;
  file_offset: int64 ;
  meta_data: column_meta_data FStar_Pervasives_Native.option ;
  offset_index_offset: int64 FStar_Pervasives_Native.option ;
  offset_index_length: int32 FStar_Pervasives_Native.option ;
  column_index_offset: int64 FStar_Pervasives_Native.option ;
  column_index_length: int32 FStar_Pervasives_Native.option ;
  crypto_metadata: column_crypto_meta_data FStar_Pervasives_Native.option ;
  encrypted_column_metadata: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkcolumn_chunk__item__file_path :
  column_chunk -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { file_path; file_offset; meta_data; offset_index_offset;
        offset_index_length; column_index_offset; column_index_length;
        crypto_metadata; encrypted_column_metadata;_} -> file_path
let (__proj__Mkcolumn_chunk__item__file_offset : column_chunk -> int64) =
  fun projectee ->
    match projectee with
    | { file_path; file_offset; meta_data; offset_index_offset;
        offset_index_length; column_index_offset; column_index_length;
        crypto_metadata; encrypted_column_metadata;_} -> file_offset
let (__proj__Mkcolumn_chunk__item__meta_data :
  column_chunk -> column_meta_data FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { file_path; file_offset; meta_data; offset_index_offset;
        offset_index_length; column_index_offset; column_index_length;
        crypto_metadata; encrypted_column_metadata;_} -> meta_data
let (__proj__Mkcolumn_chunk__item__offset_index_offset :
  column_chunk -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { file_path; file_offset; meta_data; offset_index_offset;
        offset_index_length; column_index_offset; column_index_length;
        crypto_metadata; encrypted_column_metadata;_} -> offset_index_offset
let (__proj__Mkcolumn_chunk__item__offset_index_length :
  column_chunk -> int32 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { file_path; file_offset; meta_data; offset_index_offset;
        offset_index_length; column_index_offset; column_index_length;
        crypto_metadata; encrypted_column_metadata;_} -> offset_index_length
let (__proj__Mkcolumn_chunk__item__column_index_offset :
  column_chunk -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { file_path; file_offset; meta_data; offset_index_offset;
        offset_index_length; column_index_offset; column_index_length;
        crypto_metadata; encrypted_column_metadata;_} -> column_index_offset
let (__proj__Mkcolumn_chunk__item__column_index_length :
  column_chunk -> int32 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { file_path; file_offset; meta_data; offset_index_offset;
        offset_index_length; column_index_offset; column_index_length;
        crypto_metadata; encrypted_column_metadata;_} -> column_index_length
let (__proj__Mkcolumn_chunk__item__crypto_metadata :
  column_chunk -> column_crypto_meta_data FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { file_path; file_offset; meta_data; offset_index_offset;
        offset_index_length; column_index_offset; column_index_length;
        crypto_metadata; encrypted_column_metadata;_} -> crypto_metadata
let (__proj__Mkcolumn_chunk__item__encrypted_column_metadata :
  column_chunk -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { file_path; file_offset; meta_data; offset_index_offset;
        offset_index_length; column_index_offset; column_index_length;
        crypto_metadata; encrypted_column_metadata;_} ->
        encrypted_column_metadata
type row_group =
  {
  columns: column_chunk Prims.list ;
  total_byte_size: int64 ;
  num_rows1: int64 ;
  sorting_columns: sorting_column Prims.list FStar_Pervasives_Native.option ;
  file_offset1: int64 FStar_Pervasives_Native.option ;
  total_compressed_size1: int64 FStar_Pervasives_Native.option ;
  ordinal: int16 FStar_Pervasives_Native.option }
let (__proj__Mkrow_group__item__columns :
  row_group -> column_chunk Prims.list) =
  fun projectee ->
    match projectee with
    | { columns; total_byte_size; num_rows1 = num_rows; sorting_columns;
        file_offset1 = file_offset;
        total_compressed_size1 = total_compressed_size; ordinal;_} -> columns
let (__proj__Mkrow_group__item__total_byte_size : row_group -> int64) =
  fun projectee ->
    match projectee with
    | { columns; total_byte_size; num_rows1 = num_rows; sorting_columns;
        file_offset1 = file_offset;
        total_compressed_size1 = total_compressed_size; ordinal;_} ->
        total_byte_size
let (__proj__Mkrow_group__item__num_rows : row_group -> int64) =
  fun projectee ->
    match projectee with
    | { columns; total_byte_size; num_rows1 = num_rows; sorting_columns;
        file_offset1 = file_offset;
        total_compressed_size1 = total_compressed_size; ordinal;_} ->
        num_rows
let (__proj__Mkrow_group__item__sorting_columns :
  row_group -> sorting_column Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { columns; total_byte_size; num_rows1 = num_rows; sorting_columns;
        file_offset1 = file_offset;
        total_compressed_size1 = total_compressed_size; ordinal;_} ->
        sorting_columns
let (__proj__Mkrow_group__item__file_offset :
  row_group -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { columns; total_byte_size; num_rows1 = num_rows; sorting_columns;
        file_offset1 = file_offset;
        total_compressed_size1 = total_compressed_size; ordinal;_} ->
        file_offset
let (__proj__Mkrow_group__item__total_compressed_size :
  row_group -> int64 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { columns; total_byte_size; num_rows1 = num_rows; sorting_columns;
        file_offset1 = file_offset;
        total_compressed_size1 = total_compressed_size; ordinal;_} ->
        total_compressed_size
let (__proj__Mkrow_group__item__ordinal :
  row_group -> int16 FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { columns; total_byte_size; num_rows1 = num_rows; sorting_columns;
        file_offset1 = file_offset;
        total_compressed_size1 = total_compressed_size; ordinal;_} -> ordinal
type type_defined_order = unit
type column_order =
  | TYPE_ORDER of unit 
let (uu___is_TYPE_ORDER : column_order -> Prims.bool) = fun projectee -> true

type page_location =
  {
  offset: int64 ;
  compressed_page_size1: int32 ;
  first_row_index: int64 }
let (__proj__Mkpage_location__item__offset : page_location -> int64) =
  fun projectee ->
    match projectee with
    | { offset; compressed_page_size1 = compressed_page_size;
        first_row_index;_} -> offset
let (__proj__Mkpage_location__item__compressed_page_size :
  page_location -> int32) =
  fun projectee ->
    match projectee with
    | { offset; compressed_page_size1 = compressed_page_size;
        first_row_index;_} -> compressed_page_size
let (__proj__Mkpage_location__item__first_row_index : page_location -> int64)
  =
  fun projectee ->
    match projectee with
    | { offset; compressed_page_size1 = compressed_page_size;
        first_row_index;_} -> first_row_index
type offset_index =
  {
  page_locations: page_location Prims.list ;
  unencoded_byte_array_data_bytes1:
    int64 Prims.list FStar_Pervasives_Native.option }
let (__proj__Mkoffset_index__item__page_locations :
  offset_index -> page_location Prims.list) =
  fun projectee ->
    match projectee with
    | { page_locations;
        unencoded_byte_array_data_bytes1 = unencoded_byte_array_data_bytes;_}
        -> page_locations
let (__proj__Mkoffset_index__item__unencoded_byte_array_data_bytes :
  offset_index -> int64 Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { page_locations;
        unencoded_byte_array_data_bytes1 = unencoded_byte_array_data_bytes;_}
        -> unencoded_byte_array_data_bytes
type column_index =
  {
  null_pages: Prims.bool Prims.list ;
  min_values: Prims.string Prims.list ;
  max_values: Prims.string Prims.list ;
  boundary_order: boundary_order ;
  null_counts: int64 Prims.list FStar_Pervasives_Native.option ;
  repetition_level_histograms:
    int64 Prims.list FStar_Pervasives_Native.option ;
  definition_level_histograms:
    int64 Prims.list FStar_Pervasives_Native.option }
let (__proj__Mkcolumn_index__item__null_pages :
  column_index -> Prims.bool Prims.list) =
  fun projectee ->
    match projectee with
    | { null_pages; min_values; max_values; boundary_order = boundary_order1;
        null_counts; repetition_level_histograms;
        definition_level_histograms;_} -> null_pages
let (__proj__Mkcolumn_index__item__min_values :
  column_index -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { null_pages; min_values; max_values; boundary_order = boundary_order1;
        null_counts; repetition_level_histograms;
        definition_level_histograms;_} -> min_values
let (__proj__Mkcolumn_index__item__max_values :
  column_index -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { null_pages; min_values; max_values; boundary_order = boundary_order1;
        null_counts; repetition_level_histograms;
        definition_level_histograms;_} -> max_values
let (__proj__Mkcolumn_index__item__boundary_order :
  column_index -> boundary_order) =
  fun projectee ->
    match projectee with
    | { null_pages; min_values; max_values; boundary_order = boundary_order1;
        null_counts; repetition_level_histograms;
        definition_level_histograms;_} -> boundary_order1
let (__proj__Mkcolumn_index__item__null_counts :
  column_index -> int64 Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { null_pages; min_values; max_values; boundary_order = boundary_order1;
        null_counts; repetition_level_histograms;
        definition_level_histograms;_} -> null_counts
let (__proj__Mkcolumn_index__item__repetition_level_histograms :
  column_index -> int64 Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { null_pages; min_values; max_values; boundary_order = boundary_order1;
        null_counts; repetition_level_histograms;
        definition_level_histograms;_} -> repetition_level_histograms
let (__proj__Mkcolumn_index__item__definition_level_histograms :
  column_index -> int64 Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { null_pages; min_values; max_values; boundary_order = boundary_order1;
        null_counts; repetition_level_histograms;
        definition_level_histograms;_} -> definition_level_histograms
type aes_gcm_v1 =
  {
  aad_prefix: Prims.string FStar_Pervasives_Native.option ;
  aad_file_unique: Prims.string FStar_Pervasives_Native.option ;
  supply_aad_prefix: Prims.bool FStar_Pervasives_Native.option }
let (__proj__Mkaes_gcm_v1__item__aad_prefix :
  aes_gcm_v1 -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { aad_prefix; aad_file_unique; supply_aad_prefix;_} -> aad_prefix
let (__proj__Mkaes_gcm_v1__item__aad_file_unique :
  aes_gcm_v1 -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { aad_prefix; aad_file_unique; supply_aad_prefix;_} -> aad_file_unique
let (__proj__Mkaes_gcm_v1__item__supply_aad_prefix :
  aes_gcm_v1 -> Prims.bool FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { aad_prefix; aad_file_unique; supply_aad_prefix;_} ->
        supply_aad_prefix
type aes_gcm_ctr_v1 =
  {
  aad_prefix1: Prims.string FStar_Pervasives_Native.option ;
  aad_file_unique1: Prims.string FStar_Pervasives_Native.option ;
  supply_aad_prefix1: Prims.bool FStar_Pervasives_Native.option }
let (__proj__Mkaes_gcm_ctr_v1__item__aad_prefix :
  aes_gcm_ctr_v1 -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { aad_prefix1 = aad_prefix; aad_file_unique1 = aad_file_unique;
        supply_aad_prefix1 = supply_aad_prefix;_} -> aad_prefix
let (__proj__Mkaes_gcm_ctr_v1__item__aad_file_unique :
  aes_gcm_ctr_v1 -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { aad_prefix1 = aad_prefix; aad_file_unique1 = aad_file_unique;
        supply_aad_prefix1 = supply_aad_prefix;_} -> aad_file_unique
let (__proj__Mkaes_gcm_ctr_v1__item__supply_aad_prefix :
  aes_gcm_ctr_v1 -> Prims.bool FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { aad_prefix1 = aad_prefix; aad_file_unique1 = aad_file_unique;
        supply_aad_prefix1 = supply_aad_prefix;_} -> supply_aad_prefix
type encryption_algorithm =
  | AES_GCM_V1 of aes_gcm_v1 
  | AES_GCM_CTR_V1 of aes_gcm_ctr_v1 
let (uu___is_AES_GCM_V1 : encryption_algorithm -> Prims.bool) =
  fun projectee ->
    match projectee with | AES_GCM_V1 _0 -> true | uu___ -> false
let (__proj__AES_GCM_V1__item___0 : encryption_algorithm -> aes_gcm_v1) =
  fun projectee -> match projectee with | AES_GCM_V1 _0 -> _0
let (uu___is_AES_GCM_CTR_V1 : encryption_algorithm -> Prims.bool) =
  fun projectee ->
    match projectee with | AES_GCM_CTR_V1 _0 -> true | uu___ -> false
let (__proj__AES_GCM_CTR_V1__item___0 :
  encryption_algorithm -> aes_gcm_ctr_v1) =
  fun projectee -> match projectee with | AES_GCM_CTR_V1 _0 -> _0
type file_meta_data =
  {
  version: int32 ;
  schema: schema_element Prims.list ;
  num_rows2: int64 ;
  row_groups: row_group Prims.list ;
  key_value_metadata1: key_value Prims.list FStar_Pervasives_Native.option ;
  created_by: Prims.string FStar_Pervasives_Native.option ;
  column_orders: column_order Prims.list FStar_Pervasives_Native.option ;
  encryption_algorithm: encryption_algorithm FStar_Pervasives_Native.option ;
  footer_signing_key_metadata: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkfile_meta_data__item__version : file_meta_data -> int32) =
  fun projectee ->
    match projectee with
    | { version; schema; num_rows2 = num_rows; row_groups;
        key_value_metadata1 = key_value_metadata; created_by; column_orders;
        encryption_algorithm = encryption_algorithm1;
        footer_signing_key_metadata;_} -> version
let (__proj__Mkfile_meta_data__item__schema :
  file_meta_data -> schema_element Prims.list) =
  fun projectee ->
    match projectee with
    | { version; schema; num_rows2 = num_rows; row_groups;
        key_value_metadata1 = key_value_metadata; created_by; column_orders;
        encryption_algorithm = encryption_algorithm1;
        footer_signing_key_metadata;_} -> schema
let (__proj__Mkfile_meta_data__item__num_rows : file_meta_data -> int64) =
  fun projectee ->
    match projectee with
    | { version; schema; num_rows2 = num_rows; row_groups;
        key_value_metadata1 = key_value_metadata; created_by; column_orders;
        encryption_algorithm = encryption_algorithm1;
        footer_signing_key_metadata;_} -> num_rows
let (__proj__Mkfile_meta_data__item__row_groups :
  file_meta_data -> row_group Prims.list) =
  fun projectee ->
    match projectee with
    | { version; schema; num_rows2 = num_rows; row_groups;
        key_value_metadata1 = key_value_metadata; created_by; column_orders;
        encryption_algorithm = encryption_algorithm1;
        footer_signing_key_metadata;_} -> row_groups
let (__proj__Mkfile_meta_data__item__key_value_metadata :
  file_meta_data -> key_value Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { version; schema; num_rows2 = num_rows; row_groups;
        key_value_metadata1 = key_value_metadata; created_by; column_orders;
        encryption_algorithm = encryption_algorithm1;
        footer_signing_key_metadata;_} -> key_value_metadata
let (__proj__Mkfile_meta_data__item__created_by :
  file_meta_data -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { version; schema; num_rows2 = num_rows; row_groups;
        key_value_metadata1 = key_value_metadata; created_by; column_orders;
        encryption_algorithm = encryption_algorithm1;
        footer_signing_key_metadata;_} -> created_by
let (__proj__Mkfile_meta_data__item__column_orders :
  file_meta_data -> column_order Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { version; schema; num_rows2 = num_rows; row_groups;
        key_value_metadata1 = key_value_metadata; created_by; column_orders;
        encryption_algorithm = encryption_algorithm1;
        footer_signing_key_metadata;_} -> column_orders
let (__proj__Mkfile_meta_data__item__encryption_algorithm :
  file_meta_data -> encryption_algorithm FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { version; schema; num_rows2 = num_rows; row_groups;
        key_value_metadata1 = key_value_metadata; created_by; column_orders;
        encryption_algorithm = encryption_algorithm1;
        footer_signing_key_metadata;_} -> encryption_algorithm1
let (__proj__Mkfile_meta_data__item__footer_signing_key_metadata :
  file_meta_data -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { version; schema; num_rows2 = num_rows; row_groups;
        key_value_metadata1 = key_value_metadata; created_by; column_orders;
        encryption_algorithm = encryption_algorithm1;
        footer_signing_key_metadata;_} -> footer_signing_key_metadata
type file_crypto_meta_data =
  {
  encryption_algorithm1: encryption_algorithm ;
  key_metadata1: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkfile_crypto_meta_data__item__encryption_algorithm :
  file_crypto_meta_data -> encryption_algorithm) =
  fun projectee ->
    match projectee with
    | { encryption_algorithm1; key_metadata1 = key_metadata;_} ->
        encryption_algorithm1
let (__proj__Mkfile_crypto_meta_data__item__key_metadata :
  file_crypto_meta_data -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { encryption_algorithm1; key_metadata1 = key_metadata;_} ->
        key_metadata
let rec zip : 'a 'b . 'a Prims.list -> 'b Prims.list -> ('a * 'b) Prims.list
  =
  fun xs ->
    fun ys ->
      match (xs, ys) with
      | ([], []) -> []
      | (x::xs', y::ys') -> (x, y) :: (zip xs' ys')
type range = {
  start: Prims.int ;
  len: Prims.int }
let (__proj__Mkrange__item__start : range -> Prims.int) =
  fun projectee -> match projectee with | { start; len;_} -> start
let (__proj__Mkrange__item__len : range -> Prims.int) =
  fun projectee -> match projectee with | { start; len;_} -> len
let (range_end : range -> Prims.int) = fun r -> r.start + r.len
let (disjoint : range -> range -> Prims.bool) =
  fun r1 ->
    fun r2 ->
      let end1 = range_end r1 in
      let end2 = range_end r2 in (r1.start >= end2) || (r2.start >= end1)
let rec (ranges_in_bound : range Prims.list -> Prims.int -> Prims.bool) =
  fun rs ->
    fun max_len ->
      match rs with
      | [] -> true
      | r::rest ->
          let end_ = range_end r in
          (end_ <= max_len) && (ranges_in_bound rest max_len)
let rec (ranges_disjoint : range Prims.list -> Prims.bool) =
  fun rs ->
    match rs with
    | [] -> true
    | uu___::[] -> true
    | x::xs ->
        (FStar_List_Tot_Base.for_all (disjoint x) xs) && (ranges_disjoint xs)
let rec (offsets_are_ordered :
  page_location -> page_location Prims.list -> Prims.bool) =
  fun prev ->
    fun locs ->
      match locs with
      | [] -> true
      | loc::rest ->
          ((FStar_Int64.v loc.offset) >= (FStar_Int64.v prev.offset)) &&
            (offsets_are_ordered loc rest)
let (validate_column_chunk : column_chunk -> Prims.bool) =
  fun cc ->
    let offsets_ok =
      match cc.meta_data with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some cmd ->
          let data_off = FStar_Int64.v cmd.data_page_offset in
          (match ((cmd.dictionary_page_offset), (cmd.index_page_offset)) with
           | (FStar_Pervasives_Native.None, uu___) -> true
           | (FStar_Pervasives_Native.Some dict_off,
              FStar_Pervasives_Native.None) ->
               (FStar_Int64.v dict_off) < data_off
           | (FStar_Pervasives_Native.Some dict_off,
              FStar_Pervasives_Native.Some idx_off) ->
               ((FStar_Int64.v dict_off) < data_off) &&
                 ((FStar_Int64.v dict_off) < (FStar_Int64.v idx_off))) in
    let idx_ok =
      match ((cc.offset_index_offset), (cc.offset_index_length),
              (cc.column_index_offset), (cc.column_index_length))
      with
      | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.Some
         uu___1, FStar_Pervasives_Native.Some uu___2,
         FStar_Pervasives_Native.Some uu___3) -> true
      | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.Some
         uu___1, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
          -> true
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
         FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> true
      | uu___ -> false in
    offsets_ok && idx_ok
type schema_tree =
  | Leaf of schema_element 
  | Node of schema_element * schema_tree Prims.list 
let (uu___is_Leaf : schema_tree -> Prims.bool) =
  fun projectee -> match projectee with | Leaf _0 -> true | uu___ -> false
let (__proj__Leaf__item___0 : schema_tree -> schema_element) =
  fun projectee -> match projectee with | Leaf _0 -> _0
let (uu___is_Node : schema_tree -> Prims.bool) =
  fun projectee ->
    match projectee with | Node (se, children) -> true | uu___ -> false
let (__proj__Node__item__se : schema_tree -> schema_element) =
  fun projectee -> match projectee with | Node (se, children) -> se
let (__proj__Node__item__children : schema_tree -> schema_tree Prims.list) =
  fun projectee -> match projectee with | Node (se, children) -> children
let (cols_size :
  column_chunk Prims.list -> Prims.int FStar_Pervasives_Native.option) =
  fun ccs ->
    let col_sizes =
      FStar_List_Tot_Base.map
        (fun cc ->
           match cc.meta_data with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some md ->
               FStar_Pervasives_Native.Some (md.total_compressed_size)) ccs in
    FStar_List_Tot_Base.fold_left
      (fun acc ->
         fun sz_opt ->
           match (acc, sz_opt) with
           | (FStar_Pervasives_Native.Some acc_sz,
              FStar_Pervasives_Native.Some sz) ->
               FStar_Pervasives_Native.Some (acc_sz + (FStar_Int64.v sz))
           | (uu___, uu___1) -> FStar_Pervasives_Native.None)
      (FStar_Pervasives_Native.Some Prims.int_zero) col_sizes
let (offset_of_column_chunk : column_meta_data -> int64) =
  fun cmd ->
    match cmd.dictionary_page_offset with
    | FStar_Pervasives_Native.Some off -> off
    | FStar_Pervasives_Native.None ->
        (match cmd.index_page_offset with
         | FStar_Pervasives_Native.Some off ->
             if (FStar_Int64.v off) < (FStar_Int64.v cmd.data_page_offset)
             then off
             else cmd.data_page_offset
         | FStar_Pervasives_Native.None -> cmd.data_page_offset)
let rec (columns_are_contiguous :
  column_chunk -> column_chunk Prims.list -> Prims.bool) =
  fun prev ->
    fun cols ->
      match cols with
      | [] -> true
      | cc::rest ->
          (match ((prev.meta_data), (cc.meta_data)) with
           | (FStar_Pervasives_Native.Some prev_md,
              FStar_Pervasives_Native.Some cc_md) ->
               let prev_md1 = prev_md in
               let prev_offset =
                 FStar_Int64.v (offset_of_column_chunk prev_md1) in
               let cc_offset = FStar_Int64.v (offset_of_column_chunk cc_md) in
               let prev_size = FStar_Int64.v prev_md1.total_compressed_size in
               ((prev_offset + prev_size) = cc_offset) &&
                 (columns_are_contiguous cc rest)
           | uu___ -> true)
let (validate_row_group : row_group -> Prims.bool) =
  fun rg ->
    let col_offset =
      match rg.columns with
      | [] -> FStar_Pervasives_Native.None
      | first::uu___ ->
          (match first.meta_data with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some cmd ->
               FStar_Pervasives_Native.Some (offset_of_column_chunk cmd)) in
    let offset_ok =
      match rg.file_offset1 with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some off ->
          (match col_offset with
           | FStar_Pervasives_Native.None -> true
           | FStar_Pervasives_Native.Some col_off ->
               (FStar_Int64.v off) = (FStar_Int64.v col_off)) in
    let rg_size_ok =
      match rg.total_compressed_size1 with
      | FStar_Pervasives_Native.None -> true
      | FStar_Pervasives_Native.Some sz ->
          let total_size = cols_size rg.columns in
          (match total_size with
           | FStar_Pervasives_Native.None -> true
           | FStar_Pervasives_Native.Some total_sz ->
               total_sz = (FStar_Int64.v sz)) in
    let contiguous_ok =
      match rg.columns with
      | [] -> true
      | first::rest -> columns_are_contiguous first rest in
    let cols_ok =
      FStar_List_Tot_Base.for_all (fun cc -> validate_column_chunk cc)
        rg.columns in
    ((offset_ok && rg_size_ok) && contiguous_ok) && cols_ok
let (cc_idx_ranges : column_chunk -> range Prims.list) =
  fun cc ->
    match ((cc.offset_index_offset), (cc.offset_index_length),
            (cc.column_index_offset), (cc.column_index_length))
    with
    | (FStar_Pervasives_Native.Some off, FStar_Pervasives_Native.Some len,
       FStar_Pervasives_Native.Some col_off, FStar_Pervasives_Native.Some
       col_len) ->
        let off_idx =
          { start = (FStar_Int64.v off); len = (FStar_Int32.v len) } in
        let col_idx =
          { start = (FStar_Int64.v col_off); len = (FStar_Int32.v col_len) } in
        [off_idx; col_idx]
    | (FStar_Pervasives_Native.Some off, FStar_Pervasives_Native.Some len,
       FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
        [{ start = (FStar_Int64.v off); len = (FStar_Int32.v len) }]
    | uu___ -> []
let (rg_range : row_group -> range FStar_Pervasives_Native.option) =
  fun rg ->
    match ((rg.file_offset1), (rg.total_compressed_size1)) with
    | (FStar_Pervasives_Native.Some off, FStar_Pervasives_Native.Some sz) ->
        FStar_Pervasives_Native.Some
          { start = (FStar_Int64.v off); len = (FStar_Int64.v sz) }
    | uu___ ->
        let total_size = cols_size rg.columns in
        (match rg.columns with
         | [] -> FStar_Pervasives_Native.None
         | first::uu___1 ->
             (match first.meta_data with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some cmd ->
                  (match total_size with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some total_sz ->
                       FStar_Pervasives_Native.Some
                         {
                           start =
                             (FStar_Int64.v (offset_of_column_chunk cmd));
                           len = total_sz
                         })))
let (get_all_page_offs : row_group Prims.list -> int64 Prims.list) =
  fun rgs ->
    FStar_List_Tot_Base.collect
      (fun rg ->
         FStar_List_Tot_Base.collect
           (fun cc ->
              match cc.meta_data with
              | FStar_Pervasives_Native.None -> []
              | FStar_Pervasives_Native.Some cmd ->
                  let dict_off =
                    match cmd.dictionary_page_offset with
                    | FStar_Pervasives_Native.None -> []
                    | FStar_Pervasives_Native.Some off -> [off] in
                  let idx_off =
                    match cmd.index_page_offset with
                    | FStar_Pervasives_Native.None -> []
                    | FStar_Pervasives_Native.Some off -> [off] in
                  let data_off = [cmd.data_page_offset] in
                  FStar_List_Tot_Base.op_At dict_off
                    (FStar_List_Tot_Base.op_At idx_off data_off)) rg.columns)
      rgs
let rec (page_offsets_are_distinct_and_inbound :
  int64 Prims.list -> int64 -> Prims.bool) =
  fun page_offs ->
    fun bound ->
      match page_offs with
      | [] -> true
      | x::xs ->
          ((Prims.op_Negation (FStar_List_Tot_Base.contains x xs)) &&
             ((FStar_Int64.v x) < (FStar_Int64.v bound)))
            && (page_offsets_are_distinct_and_inbound xs bound)
let (validate_file_meta_data : file_meta_data -> int64 -> Prims.bool) =
  fun fmd ->
    fun footer_start ->
      let page_offs = get_all_page_offs fmd.row_groups in
      let ranges =
        FStar_List_Tot_Base.collect
          (fun rg ->
             let rg_range_opt = rg_range rg in
             let cc_ranges =
               FStar_List_Tot_Base.collect cc_idx_ranges rg.columns in
             match rg_range_opt with
             | FStar_Pervasives_Native.None -> cc_ranges
             | FStar_Pervasives_Native.Some rg_range1 -> rg_range1 ::
                 cc_ranges) fmd.row_groups in
      (((page_offsets_are_distinct_and_inbound page_offs footer_start) &&
          (ranges_disjoint ranges))
         && (ranges_in_bound ranges (FStar_Int64.v footer_start)))
        &&
        (FStar_List_Tot_Base.for_all (fun rg -> validate_row_group rg)
           fmd.row_groups)
let rec (page_offsets_are_contiguous :
  page_location -> page_location Prims.list -> Prims.bool) =
  fun prev ->
    fun locs ->
      match locs with
      | [] -> true
      | loc::rest ->
          ((FStar_Int64.v loc.offset) =
             ((FStar_Int64.v prev.offset) +
                (FStar_Int32.v prev.compressed_page_size1)))
            && (page_offsets_are_contiguous loc rest)
let (validate_offset_index : offset_index -> column_chunk -> Prims.bool) =
  fun oi ->
    fun cc ->
      let locs = oi.page_locations in
      let first_loc =
        match locs with
        | [] -> FStar_Pervasives_Native.None
        | first::uu___ -> FStar_Pervasives_Native.Some first in
      let first_page_offset =
        match cc.meta_data with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some cmd ->
            FStar_Pervasives_Native.Some
              (FStar_Int64.v (offset_of_column_chunk cmd)) in
      let first_loc_ok =
        match (first_loc, first_page_offset) with
        | (FStar_Pervasives_Native.Some loc, FStar_Pervasives_Native.Some
           off) -> (FStar_Int64.v loc.offset) = off
        | uu___ -> true in
      let cc_page_offsets_ok =
        match cc.meta_data with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some cmd ->
            let all_page_offsets =
              FStar_List_Tot_Base.map (fun pl -> pl.offset) locs in
            let contains off =
              FStar_List_Tot_Base.contains off all_page_offsets in
            (match ((cmd.dictionary_page_offset), (cmd.index_page_offset))
             with
             | (FStar_Pervasives_Native.Some dict_off,
                FStar_Pervasives_Native.Some idx_off) ->
                 (contains dict_off) && (contains idx_off)
             | (FStar_Pervasives_Native.Some dict_off,
                FStar_Pervasives_Native.None) -> contains dict_off
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
                idx_off) -> contains idx_off
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                 -> true)
              && (contains cmd.data_page_offset) in
      let col_size_ok =
        match cc.meta_data with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some md ->
            let s =
              FStar_List_Tot_Base.fold_left
                (fun acc ->
                   fun pl -> acc + (FStar_Int32.v pl.compressed_page_size1))
                Prims.int_zero locs in
            s = (FStar_Int64.v md.total_compressed_size) in
      let contiguous_ok =
        match locs with
        | [] -> true
        | first::rest -> page_offsets_are_contiguous first rest in
      ((first_loc_ok && cc_page_offsets_ok) && col_size_ok) && contiguous_ok
