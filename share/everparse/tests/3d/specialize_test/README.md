This directory contains an example of EverParse/3d project with
support for non-contiguous parsing with probing functions, with
automatic specialization to 32-bit layouts.

The layout is similar to ../probe---please see the README file there.

* `src/SpecializeABC.3d` defines the data formats, using the specialize
  directive

* `src/main.c` and `src/aux.h` define the probing functions, and the
  main test function