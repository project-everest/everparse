This directory is a copy of ../specialize_test (non-contiguous parsing
with probing functions, with automatic specialization to 32-bit
layouts), built with 3d's `--use_error_handler_macro` option (see
`EVERPARSE_OPTIONS` in the `GNUmakefile` and `src/MyErrorHandlerMacro.h`).

# What this test exercises

Under `--use_error_handler_macro` the generated validators do not take a
dynamic `EVERPARSE_ERROR_HANDLER` function-pointer argument; instead
they invoke the `EVERPARSE_ERROR_HANDLER_MACRO` C macro (defined in
`src/MyErrorHandlerMacro.h`, injected via `--add_include`).

Type-specialized (`specialize`) and coerce probes are the interesting
case: their probe helpers are extracted as standalone, shared functions
(e.g. `ProbePa`, `Specialized32ProbeA`, `ReadAndCoercePointer`) and the
shared validator `ValidateB` receives the probe as a function pointer.
Historically these helpers took the error handler as a first-class
function-pointer argument, so passing the `EVERPARSE_ERROR_HANDLER_MACRO`
macro to them produced a bare, uncompilable identifier.

The probe actions are now aligned with the validators: the probe monad
is parameterized by `use_error_handler`, so under the macro option the
handler argument is dropped everywhere (the helpers and the `ValidateB`
function-pointer type no longer mention `EVERPARSE_ERROR_HANDLER`) and
each error site calls `EVERPARSE_ERROR_HANDLER_MACRO(...)` directly, just
like the plain validators.

`make test` compiles the generated validators together with the
handwritten driver and runs it; this directory therefore serves as a
regression test that type-specialized/coerce probes build and run
correctly under `--use_error_handler_macro`.

The `src/` subdirectory contains all the handwritten source files:

* `src/SpecializeABC.3d` defines the data formats, using the specialize
  directive.

* `src/MyErrorHandlerMacro.h` provides the `EVERPARSE_ERROR_HANDLER_MACRO`
  definition injected into every generated `.c`/`.h` via `--add_include`.

* `src/main.c` and `src/probecallbacks.h` define the probing functions
  and the main test function.
