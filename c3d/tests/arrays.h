
typedef struct [[
  everparse::process(0),
  everparse::entrypoint
]] _POINT3
{
  UINT32  x[3];
} POINT3, *PPOINT3;

// typedef struct [[
//   everparse::process(0),
//   everparse::entrypoint
// ]] _POINTN
// {
//   char dummy;
//   UINT32  x[];
// } POINTN, *PPOINTN;

typedef struct [[
  everparse::process(0),
  everparse::entrypoint,
  everparse::parameter(UINT32 len)
]] _POINTNPARAM
{
  char dummy;
  UINT32  x                 [[everparse::byte_size(123)]]
            [EVERPARSE_VLA];
} POINTNPARAM, *PPOINTNPARAM;
