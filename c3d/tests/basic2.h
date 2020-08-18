// A demo on writing custom attributes in the everparse annotation format.
// These attributes are processed by c3d, a clang frontend plugin that
// generates a c3d file based on those attributes.

// We start with some auxiliary type definitions.
typedef int uint32_t;

typedef uint32_t RNDIS_REQUEST_ID;

void f(void) __attribute__((availability(macos,introduced=10.4,deprecated=10.6,obsoleted=10.7)));

// Note here how the attribute is strategically located after the "struct"
// keyword to make sure it gets attached to the struct, not to the typedef.
typedef struct
[[ everparse::process, everparse::entrypoint ]]
_RNDIS_INITIALIZE_REQUEST {
  uint32_t MessageBodyLength
      __attribute__(( everparse_constraint(MessageBodyLength == sizeof(this)) ));
  RNDIS_REQUEST_ID RequestId;
  uint32_t MajorVersion
      [[ everparse::constraint(MajorVersion == RNDIS_MAJOR_VERSION) ]];
  uint32_t MinorVersion
      [[ everparse::constraint(MinorVersion == RNDIS_MINOR_VERSION) ]];
  uint32_t MaxTransferSize;
} RNDIS_INITIALIZE_REQUEST, *PRNDIS_INITIALIZE_REQUEST;
