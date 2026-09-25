This directory contains an example of EverParse/3d project with
support for non-contiguous parsing with probing functions.

It is a copy of the sibling `probe/` test, adapted to build with the
3d `--use_error_handler_macro` option (see `MyErrorHandlerMacro.h` and
the `EVERPARSE_OPTIONS` variable in the `GNUmakefile`).  With that
option the generated validators no longer take a dynamic
`EVERPARSE_ERROR_HANDLER` function-pointer argument; instead they
invoke the `EVERPARSE_ERROR_HANDLER_MACRO` C macro directly.

Its purpose is to exercise the z3 test-case-generation modes under
`--use_error_handler_macro`.  These modes are emitted by
`src/3d/Z3TestGen.fst`, which generates a C test harness that calls the
validators.  In macro mode the validators take no dynamic
`EVERPARSE_ERROR_HANDLER` argument, so the harness omits the
`&TestErrorHandler` argument (and its definition) accordingly; it
therefore compiles and runs under the macro option:

* `make testgen`     — `--z3_test`      (`Z3TestGen.do_test`)
* `make difftest`    — `--z3_diff_test` (`Z3TestGen.do_diff_test`)
* `make checkertest` — `--test_checker` (`Z3TestGen.test_checker_c`)
* `make eprobetest`  — `--z3_test` on an `entrypoint probe` type

The core `make test` target builds the validators + their wrappers; the
four targets above additionally build the z3 test-case-generation
harnesses.  All of them are exercised by the default `world` target and
serve as regression tests that z3-testgen works under
`--use_error_handler_macro`.

Note on `entrypoint probe`: the specialized probe entrypoint that 3d
generates for such a type (e.g. `ProbeProbeInPlaceCheckTest1`, emitted
by `Target.fst`) is compile-tested by `make test`.  z3-testgen tests the
*underlying* validator (e.g. `ProbeValidateTest2`); the `checkertest`
(on `test1`) and `eprobetest` (on `test2`) targets cover `entrypoint
probe` types.

The `src/` subdirectory contains all the source files of this project,
all handwritten:

* `Probe.3d` defines the data formats in the 3D language, and declares
  the probing functions but does not define them.  `namedPlainVariant`
  is added (relative to `probe/`) so that `--z3_diff_test` has two
  same-signature parsers that disagree on some inputs.

* `MyErrorHandlerMacro.h` provides the `EVERPARSE_ERROR_HANDLER_MACRO`
  definition injected into every generated `.c`/`.h` via
  `--add_include`.

* `main.c` defines the probing functions, and the main test function
  of the test program, which calls the validators for the data types
  marked `entrypoint` in `Probe.3d`. In this test here, `main.c` also
  defines some input data.

All intermediate files, output files (`*.h`, `*.c`) as well as the
`test.exe` test executable, are slated to be generated into the `obj/`
subdirectory.  The `difftest`, `checkertest` and `eprobetest`
harnesses are generated into `obj.difftest/`, `obj.checkertest/` and
`obj.eprobetest/` respectively.

The files `EverParse.h` and `EverParseEndianness.h` are static files
that are part of the EverParse binary package, in
`src/3d/prelude/buffer` and `src/3d` respectively.

# Linux

This directory contains a fully commented `GNUmakefile`, to be used
with GNU Make: `make` will generate all the F\* specifications and
Low\* implementations of validators, verify them, compile them to C,
and compile that generated C code along with a handwritten test into a
test executable, and finally run that test executable, `obj/test.exe`

To build the project, run:

make EVERPARSE_HOME=/path/to/everparse

where /path/to/everparse is the full path to the EverParse binary
package directory.

# Windows

To build the project, run:

build.cmd \path\to\everparse

where \path\to\everparse is the full path to the EverParse binary
package directory.
