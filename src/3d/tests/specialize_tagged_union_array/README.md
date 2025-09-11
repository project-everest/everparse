This directory contains an example of EverParse/3d project with
support for non-contiguous parsing with probing functions, with
automatic specialization to 32-bit layouts.

The layout is similar to ../probe and ../specialize_test--please see the README
file there.

This directory tests support for probing variable-length arrays containing tagged unions

* `src/SpecializeTaggedUnionArray.3d` defines the data formats, using the
  specialize directive

* `src/main.c` defines the probing functions, and the
  main test function