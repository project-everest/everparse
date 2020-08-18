typedef int uint32_t;

typedef uint32_t RNDIS_REQUEST_ID;

#define RNDIS_MAJOR_VERSION 0
#define RNDIS_MINOR_VERSION 0

typedef struct
[[
  everparse::entrypoint,
  everparse::process,
  everparse::parameter(uint32_t MessageBodyLength),
  everparse::where(MessageBodyLength == sizeof(this))
]]
_RNDIS_INITIALIZE_REQUEST {
  RNDIS_REQUEST_ID RequestId;
  uint32_t MajorVersion
      [[everparse::constraint(MajorVersion == RNDIS_MAJOR_VERSION && MajorVersion == 0)]];
  uint32_t MinorVersion
      [[everparse::constraint(MinorVersion == MajorVersion),
        everparse::constraint(MinorVersion == 1)]];
  uint32_t MaxTransferSize
      [[everparse::constraint(MaxTransferSize <= MessageBodyLength)]];
} RNDIS_INITIALIZE_REQUEST, *PRNDIS_INITIALIZE_REQUEST;
