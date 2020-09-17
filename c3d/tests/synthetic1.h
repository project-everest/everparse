// Some constants explicitly in u32
#define V2              0x00000002ul
#define V3              3ul
#define V4              0x00000004ul
#define V5              0x5ul
#define V6              0x00000006ul
#define V7              0x00000007ul
#define V8              0x00000008ul
#define V9              0x000009ul

// Some typedefs
typedef UINT32 UINT32_Alias1;
typedef UINT32 UINT32_Alias2;
typedef UINT32 UINT32_Alias3;
typedef UINT32 UINT32_Alias4;
typedef UINT32 UINT32_Alias5;
typedef UINT32 ULONG;
typedef UINT64 ULONG64;

//Struct with a where clause and sizeof
typedef struct [[
  everparse::process(0),
  everparse::parameter(UINT32 Len),
  everparse::where(Len == sizeof(this))
]] _STRUCT_1
{
  UINT32_Alias1 f1;
  UINT32        f2;
  UINT32        f3;
  UINT32        f4;
} STRUCT_1;

// Struct with where clause
// -- Field dependency
// -- instantiation of parameterized type
// -- unfolding type alias
typedef struct [[
  everparse::process(0),
  everparse::parameter(UINT32 Len),
  everparse::where (Len == sizeof(this))
]] _STRUCT_2 
{
  UINT32_Alias3   len [[ everparse::process(0) ]];
  STRUCT_1   field_1 [[ everparse::parameter(len) ]];
} STRUCT_2;


typedef struct [[
  everparse::process(0),
  everparse::parameter(UINT32 Len)
]] _STRUCT_3
{
    UINT32_Alias1   f1;
    UINT32_Alias2   f2;
    ULONG           len;
    UINT32          offset
        [[everparse::constraint(
            is_range_okay(TotalLen, offset, len) &&
            offset >= sizeof(this)
        )]];
    UINT32_Alias4   f4 [[everparse::constraint(f4 == 0)]];
    UINT8        buffer [0] [[everparse::constraint(size == TotalLen - sizeof(this))]];
} STRUCT_3;

