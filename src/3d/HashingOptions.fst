module HashingOptions

type check_hashes_t = | WeakHashes | StrongHashes | InplaceHashes

let is_weak = function
  | WeakHashes
  | InplaceHashes -> true
  | _ -> false

type micro_step_t =
  | MicroStepVerify
  | MicroStepExtract
  | MicroStepCopyClangFormat

type makefile_type =
  | MakefileGMake
  | MakefileNMake

type input_stream_binding_t =
  | InputStreamBuffer
  | InputStreamExtern

let string_of_input_stream_binding = function
  | InputStreamBuffer -> "buffer"
  | InputStreamExtern -> "extern"
