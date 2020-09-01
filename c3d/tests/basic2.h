// A demo on writing custom attributes in the everparse annotation format.
// These attributes are processed by c3d, a clang frontend plugin that
// generates a c3d file based on those attributes.

// We start with some auxiliary type definitions.
typedef int uint32_t;

typedef uint32_t FOO_ID;

void f(void) __attribute__((availability(macos,introduced=10.4,deprecated=10.6,obsoleted=10.7)));

// Note here how the attribute is strategically located after the "struct"
// keyword to make sure it gets attached to the struct, not to the typedef.
typedef struct
[[ everparse::process, everparse::entrypoint ]]
_FOO {
  uint32_t MessageBodyLength
      __attribute__(( everparse_constraint(MessageBodyLength == sizeof(this)) ));
  FOO_ID RequestId;
  uint32_t MajorVersion
      [[ everparse::constraint(MajorVersion == FOO_MAJOR_VERSION) ]];
  uint32_t MinorVersion
      [[ everparse::constraint(MinorVersion == FOO_MINOR_VERSION) ]];
  uint32_t MaxTransferSize;
} FOO, *PFOO;
