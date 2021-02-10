module HashingOptions

type check_hashes_t = | WeakHashes | StrongHashes | InplaceHashes

let is_weak = function
  | WeakHashes
  | InplaceHashes -> true
  | _ -> false

type micro_step_t =
  | MicroStepVerify
  | MicroStepExtract
