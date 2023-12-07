This directory contains an example of EverParse/3d project with
support for non-contiguous parsing with probing functions.

It contains a fully commented `Makefile`, to be used with GNU Make:
`make` will generate all the F\* specifications and Low\*
implementations of validators, verify them, compile them to C, and
compile that generated C code along with a handwritten test into a
test executable, and finally run that test executable, `obj/test.exe`

The `src/` subdirectory contains all the source files of this project,
all handwritten:

* `Probe.3d` defines the data formats in the 3D language, and declares
  the probing functions but does not define them.

* `main.c` defines the probing functions, and the main test function
  of the test program, which calls the validators for the data types
  marked `entrypoint` in `Probe.3d`. In this test here, `main.c` also
  defines some input data.

All intermediate files, output files (`*.h`, `*.c`) as well as the
`test.exe` test executable, are slated to be generated into the `obj/`
subdirectory.

The files `EverParse.h` and `EverParseEndianness.h` are static files
that are part of the EverParse binary package, in
`src/3d/prelude/buffer` and `src/3d` respectively.
