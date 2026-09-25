This directory contains an example of modular EverParse/3d project.

It contains a fully commented `Makefile`, to be used with GNU Make:
`make` will generate all the F\* specifications and Low\*
implementations of validators, verify them, compile them to C, and
compile that generated C code along with a handwritten test into a
test executable, and finally run that test executable.

The `src/` subdirectory contains all the source files of this project,
all handwritten:

* `Constants.3d` defines some constants. They are marked `export` so
  that they can be used in other 3d modules.

* `Point.3d` defines a `Point` data type. It is marked `export` so that it
  can be used by other 3d modules, but not `entrypoint` so its
  validator cannot be directly called by handwritten C code, and will
  be called only indirectly by other EverParse-generated validators
  for types that depend on it.

* `Point.3d.copyright.txt` defines the text that will be generated at
  the beginning of `PointWrapper.c`, `PointWrapper.h`, `Point.c` and
  `Point.h`. In particular, it uses the `EVEPRARSEHASHES` tag, which
  EverParse will replace with a hash to be checked by the
  `--check_inplace_hash` option of 3d as illustrated in the `ci` rule in
  the Makefile.

* `TPoint.3d`: similar to `Point.3d`, except that it reuses some types
  from `Point.3d`

* `Foobar.h`: defines the size of some `CIRCLE` array type.

* `Test.3d`: defines a `T` data type, which is marked `entrypoint` so
  a validator will be generated and made available in `TestWrapper.h`
  and `TestWrapper.c` to be called by handwritten C code. `Test.3d`
  also contains a `refines` clause to generate a static C assertion to
  check, at compile-time, that the size of data for the `CIRCLE` data
  type matches the size of the `CIRCLE` array type defined in
  `Foobar.h`.

* `main.c`: the main function of the test program, which calls the
  validator for the `T` data type defined in `Test.3d`.

All intermediate files (`*.fst*`, `*.krml`), output files (`*.h`,
`*.c`) as well as the `test.exe` test executable, are slated to be
generated into the `obj/` subdirectory.
