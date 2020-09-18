// Some constants explicitly in u32
enum
[[
  everparse::process(0)
]] {
  V2 = 0x00000002ul,
  V3 = 3ul,
  V4 = 0x00000004ul,
  V5 = 0x5ul,
  V6 = 0x00000006ul,
  V7 = 0x00000007ul,
  V8 = 0x00000008ul,
  V9 = 0x000009ul,
};

typedef uint8_t UINT8;
typedef uint16_t UINT16;
typedef uint32_t UINT32;
typedef uint64_t UINT64;

typedef struct {} unit;

// Some typedefs
typedef UINT32 UINT32_Alias1     [[everparse::process(1)]]     ;
typedef UINT32 UINT32_Alias2     [[everparse::process(1)]]     ;
typedef UINT32 UINT32_Alias3     [[everparse::process(1)]]     ;
typedef UINT32 UINT32_Alias4     [[everparse::process(1)]]     ;
typedef UINT32 UINT32_Alias5     [[everparse::process(1)]]     ;
typedef UINT32 ULONG             [[everparse::process(1)]]     ;
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

