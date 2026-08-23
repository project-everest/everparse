3d/pulse: extract and compile all Pulse 3d tests

Removes the last KaRaMeL extraction blockers for the --pulse backend, so
that every test in share/everparse/tests/3d now goes all the way to C.
The exclusion list is gone and 61 C files compile (previously 40).

Runtime fixes:

- Actions.Base: probe_then_validate bound the pure external address
  conversion as `let a64 = as_u64 src` and applied it separately. That
  partial application of an extern cannot be closed over in C. Apply it
  fully, as validate_with_probe already did.

- action_field_ptr, action_field_ptr_after and
  action_field_ptr_after_with_setter now take the operation directly
  instead of an option plus a squash witness, and the interpreter does
  the Some?.v projection. Building the option at runtime forced KaRaMeL
  to keep a function type with unit arguments inside a data constructor,
  whose arity no longer matched after unused-parameter elimination.
  Since Some?.v is already in specialization_steps, the projection is
  discharged by the normalizer, provided the backend definitions unfold:
  hence the new specialize_backend attribute in Actions.Common, which
  the backends can reference without depending on the interpreter.

C plumbing:

- Under --pulse the copy buffer is a concrete struct emitted into
  EverParse.h, which clashed with the legacy `typedef void*
  EVERPARSE_COPY_BUFFER_T` of EverParseEndianness.h. That typedef is now
  guarded, and --pulse code includes the new EverParsePulseEndianness.h,
  which defines the guard before delegating. Pulse wrapper headers also
  include EverParse.h so that the struct is in scope.

Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>
