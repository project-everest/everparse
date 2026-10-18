This directory contains a F* and Pulse implementation for a generic
CBOR encoder and decoder, proven correct for memory safety, functional
correctness and (for the deterministic subset of CBOR) unique binary
representation.

* `./*.fsti`: F* interfaces with Pulse function signatures, with the
  functional correctness statement against the specifications in
  `../spec`. These interfaces are enough for verified clients. They
  can be typechecked without the rest of EverParse.

* `raw/`: Pulse implementations of those interfaces, proven correct
  wrt. the respective function signatures. The `raw/everparse/`
  subdirectory needs LowParse+Pulse to typecheck.

* `det/`: Karamel extraction rules and C and Rust extracted code for
  the deterministic subset of CBOR. The extracted code does not need
  F* to compile. The extracted C code only needs krmllib from Karamel.
