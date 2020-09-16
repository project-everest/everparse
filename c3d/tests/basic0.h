#include <stdint.h>

enum
  [[everparse::process(1)]]
{
	KIND_INT = 1,
	KIND_CHAR = 2,
};

enum
  [[everparse::process(1)]]
Enum8 {
	  Enum8_1 = 0,
	  Enum8_2,
	  Enum8_3,
	  Enum8_100 = 0x64,
	  Enum8_101 = 101,
	  Enum8_103,
	  Enum8_104,
};

union
  [[everparse::process(1)]]
  [[everparse::entrypoint]]
  [[everparse::switch(uint32_t kind)]]
sum {
	uint32_t i [[everparse::case(KIND_INT)]];
	uint8_t c [[everparse::case(KIND_CHAR)]];
};

// struct
//   [[everparse::process(1)]]
//   [[everparse::entrypoint]]
//   [[everparse::parameter(uint32_t MessageBodyLength)]]
//   [[everparse::where(MessageBodyLength == sizeof(this))]]
// _FOO {
//   FOO_ID RequestId;
//   uint32_t MajorVersion
//       [[everparse::constraint(MajorVersion == FOO_MAJOR_VERSION && MajorVersion == 0)]];
//   uint32_t MinorVersion
//       [[everparse::constraint(MinorVersion == MajorVersion),
//         everparse::constraint(MinorVersion == 1)]];
//   uint32_t MaxTransferSize
//       [[everparse::constraint(MaxTransferSize <= MessageBodyLength)]];
// };

// typedef struct
// [[
//   everparse::process(1),
//   everparse::entrypoint,
//   everparse::parameter(uint32_t MessageBodyLength),
//   everparse::where(MessageBodyLength == sizeof(this)),
// ]]
// _BAR {
//   BAR_ID RequestId;
//   uint32_t MajorVersion
//       [[everparse::constraint(MajorVersion == BAR_MAJOR_VERSION && MajorVersion == 0)]];
//   uint32_t MinorVersion
//       [[everparse::constraint(MinorVersion == MajorVersion),
//         everparse::constraint(MinorVersion == 1)]];
//   uint32_t MaxTransferSize
//       [[everparse::constraint(MaxTransferSize <= MessageBodyLength)]];
// } BAR, *PBAR;
