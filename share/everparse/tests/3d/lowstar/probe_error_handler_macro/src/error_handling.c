#include <stdio.h>

// ERROR HANDLING

// `ProbeEverParseError` is declared in the generated
// ../obj/ProbeWrapper.c, but we have to define it by hand here. It is
// the callback function called if any validator for a type defined in
// Probe.3d fails.

void ProbeEverParseError(char *StructName, char *FieldName, char *Reason) {
  printf("Validation failed in Probe, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}
