This directory contains the safe Rust code extracted from the verified
Deterministic CBOR validators, parsers and serializers written in F*
and Pulse with EverParse.

* `src/cbordet.rs` is the entrypoint of the library. It contains the
  user-facing API as handwritten unverified glue code calling into the
  verified API in `src/cbordetver.rs`. It accounts for Rust's `str`,
  `Iterator`, etc., which F* and Pulse currently do not model. As the
  user-facing API, its functions are all documented.

* `src/cbordetver.rs` contains the extracted code from the verified
  API in `../../CBOR.Pulse.API.Det.Rust.fsti`

* `src/cbordetveraux.rs` contains the bulk of the extracted code from
  the verified implementation, which the verified API calls into.

* `tests/example.rs` contains a fully commented example showing how to
  construct, serialize, parse and destruct Deterministic CBOR objects
  from this library.
