module Config

[@@ PpxDerivingYoJson]
type compile_time_flags = {
  flags : list string;
  include_file : string;
}

[@@ PpxDerivingYoJson]
type config = {
  compile_time_flags : compile_time_flags
}
