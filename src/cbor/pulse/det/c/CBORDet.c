

#include "internal/CBORDet.h"

static CBOR_Spec_Raw_Base_raw_uint64 mk_raw_uint64(uint64_t x)
{
  uint8_t size;
  if (x <= (uint64_t)MAX_SIMPLE_VALUE_ADDITIONAL_INFO)
    size = 0U;
  else if (x < 256ULL)
    size = 1U;
  else if (x < 65536ULL)
    size = 2U;
  else if (x < 4294967296ULL)
    size = 3U;
  else
    size = 4U;
  return ((CBOR_Spec_Raw_Base_raw_uint64){ .size = size, .value = x });
}

static uint8_t get_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi)
{
  uint8_t op1 = (uint32_t)x << 8U - hi;
  return (uint32_t)op1 >> 8U - hi + lo;
}

static uint8_t set_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi, uint8_t v)
{
  uint8_t op0 = 255U;
  uint8_t op1 = (uint32_t)op0 >> 8U - (hi - lo);
  uint8_t op2 = (uint32_t)op1 << lo;
  uint8_t op3 = ~op2;
  uint8_t op4 = (uint32_t)x & (uint32_t)op3;
  uint8_t op5 = (uint32_t)v << lo;
  return (uint32_t)op4 | (uint32_t)op5;
}

#define ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS (24U)

#define ADDITIONAL_INFO_UNASSIGNED_MIN (28U)

typedef struct initial_byte_t_s
{
  uint8_t major_type;
  uint8_t additional_info;
}
initial_byte_t;

#define ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS (25U)

#define ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS (26U)

#define ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS (27U)

#define LongArgumentSimpleValue 0
#define LongArgumentU8 1
#define LongArgumentU16 2
#define LongArgumentU32 3
#define LongArgumentU64 4
#define LongArgumentOther 5

typedef uint8_t long_argument_tags;

typedef struct long_argument_s
{
  long_argument_tags tag;
  union {
    uint8_t case_LongArgumentSimpleValue;
    uint8_t case_LongArgumentU8;
    uint16_t case_LongArgumentU16;
    uint32_t case_LongArgumentU32;
    uint64_t case_LongArgumentU64;
  }
  ;
}
long_argument;

typedef struct header_s
{
  initial_byte_t fst;
  long_argument snd;
}
header;

static uint64_t argument_as_uint64(initial_byte_t b, long_argument x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == LongArgumentU8)
  {
    uint8_t v = x.case_LongArgumentU8;
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)v });
  }
  else if (x.tag == LongArgumentU16)
  {
    uint16_t v = x.case_LongArgumentU16;
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)v });
  }
  else if (x.tag == LongArgumentU32)
  {
    uint32_t v = x.case_LongArgumentU32;
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)v });
  }
  else if (x.tag == LongArgumentU64)
  {
    uint64_t v = x.case_LongArgumentU64;
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = v });
  }
  else if (x.tag == LongArgumentOther)
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

static header raw_uint64_as_argument(uint8_t t, CBOR_Spec_Raw_Base_raw_uint64 x)
{
  if (x.size == 0U)
    return
      (
        (header){
          .fst = { .major_type = t, .additional_info = (uint8_t)x.value },
          .snd = { .tag = LongArgumentOther }
        }
      );
  else if (x.size == 1U)
    return
      (
        (header){
          .fst = { .major_type = t, .additional_info = ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS },
          .snd = { .tag = LongArgumentU8, { .case_LongArgumentU8 = (uint8_t)x.value } }
        }
      );
  else if (x.size == 2U)
    return
      (
        (header){
          .fst = { .major_type = t, .additional_info = ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS },
          .snd = { .tag = LongArgumentU16, { .case_LongArgumentU16 = (uint16_t)x.value } }
        }
      );
  else if (x.size == 3U)
    return
      (
        (header){
          .fst = { .major_type = t, .additional_info = ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS },
          .snd = { .tag = LongArgumentU32, { .case_LongArgumentU32 = (uint32_t)x.value } }
        }
      );
  else
    return
      (
        (header){
          .fst = { .major_type = t, .additional_info = ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS },
          .snd = { .tag = LongArgumentU64, { .case_LongArgumentU64 = x.value } }
        }
      );
}

static header simple_value_as_argument(uint8_t x)
{
  if (x <= MAX_SIMPLE_VALUE_ADDITIONAL_INFO)
    return
      (
        (header){
          .fst = { .major_type = CBOR_MAJOR_TYPE_SIMPLE_VALUE, .additional_info = x },
          .snd = { .tag = LongArgumentOther }
        }
      );
  else
    return
      (
        (header){
          .fst = {
            .major_type = CBOR_MAJOR_TYPE_SIMPLE_VALUE,
            .additional_info = ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS
          },
          .snd = { .tag = LongArgumentSimpleValue, { .case_LongArgumentSimpleValue = x } }
        }
      );
}

static uint8_t get_header_major_type(header h)
{
  initial_byte_t b = h.fst;
  return b.major_type;
}

static void
copy__uint8_t(Pulse_Lib_Slice_slice__uint8_t dst, Pulse_Lib_Slice_slice__uint8_t src)
{
  memcpy(dst.elt, src.elt, src.len * sizeof (uint8_t));
}

static void
cbor_match_serialized_payload_array_copy(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t c_
)
{
  copy__uint8_t(c_, c);
}

static void
cbor_match_serialized_payload_map_copy(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t c_
)
{
  copy__uint8_t(c_, c);
}

static void
cbor_match_serialized_payload_tagged_copy(
  Pulse_Lib_Slice_slice__uint8_t c,
  Pulse_Lib_Slice_slice__uint8_t c_
)
{
  copy__uint8_t(c_, c);
}

static cbor_string cbor_string_reset_perm(cbor_string c)
{
  return
    (
      (cbor_string){
        .cbor_string_type = c.cbor_string_type,
        .cbor_string_size = c.cbor_string_size,
        .cbor_string_ptr = c.cbor_string_ptr
      }
    );
}

static cbor_serialized cbor_serialized_reset_perm(cbor_serialized c)
{
  return
    (
      (cbor_serialized){
        .cbor_serialized_header = c.cbor_serialized_header,
        .cbor_serialized_payload = c.cbor_serialized_payload
      }
    );
}

static cbor_tagged cbor_tagged_reset_perm(cbor_tagged c)
{
  return
    ((cbor_tagged){ .cbor_tagged_tag = c.cbor_tagged_tag, .cbor_tagged_ptr = c.cbor_tagged_ptr });
}

static cbor_array cbor_array_reset_perm(cbor_array c)
{
  return
    (
      (cbor_array){
        .cbor_array_length_size = c.cbor_array_length_size,
        .cbor_array_ptr = c.cbor_array_ptr
      }
    );
}

static cbor_map cbor_map_reset_perm(cbor_map c)
{
  return
    ((cbor_map){ .cbor_map_length_size = c.cbor_map_length_size, .cbor_map_ptr = c.cbor_map_ptr });
}

static cbor_raw cbor_raw_reset_perm_tot(cbor_raw c)
{
  if (c.tag == CBOR_Case_String)
  {
    cbor_string v = c.case_CBOR_Case_String;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_String,
          { .case_CBOR_Case_String = cbor_string_reset_perm(v) }
        }
      );
  }
  else if (c.tag == CBOR_Case_Tagged)
  {
    cbor_tagged v = c.case_CBOR_Case_Tagged;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Tagged,
          { .case_CBOR_Case_Tagged = cbor_tagged_reset_perm(v) }
        }
      );
  }
  else if (c.tag == CBOR_Case_Array)
  {
    cbor_array v = c.case_CBOR_Case_Array;
    return
      ((cbor_raw){ .tag = CBOR_Case_Array, { .case_CBOR_Case_Array = cbor_array_reset_perm(v) } });
  }
  else if (c.tag == CBOR_Case_Map)
  {
    cbor_map v = c.case_CBOR_Case_Map;
    return ((cbor_raw){ .tag = CBOR_Case_Map, { .case_CBOR_Case_Map = cbor_map_reset_perm(v) } });
  }
  else if (c.tag == CBOR_Case_Serialized_Tagged)
  {
    cbor_serialized v = c.case_CBOR_Case_Serialized_Tagged;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Tagged,
          { .case_CBOR_Case_Serialized_Tagged = cbor_serialized_reset_perm(v) }
        }
      );
  }
  else if (c.tag == CBOR_Case_Serialized_Array)
  {
    cbor_serialized v = c.case_CBOR_Case_Serialized_Array;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Array,
          { .case_CBOR_Case_Serialized_Array = cbor_serialized_reset_perm(v) }
        }
      );
  }
  else if (c.tag == CBOR_Case_Serialized_Map)
  {
    cbor_serialized v = c.case_CBOR_Case_Serialized_Map;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Map,
          { .case_CBOR_Case_Serialized_Map = cbor_serialized_reset_perm(v) }
        }
      );
  }
  else
    return c;
}

static cbor_map_entry cbor_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  cbor_map_entry
  res =
    {
      .cbor_map_entry_key = cbor_raw_reset_perm_tot(xk),
      .cbor_map_entry_value = cbor_raw_reset_perm_tot(xv)
    };
  return res;
}

static size_t len__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.len;
}

static uint8_t op_Array_Access__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i)
{
  return a.elt[i];
}

static bool impl_correct(Pulse_Lib_Slice_slice__uint8_t s)
{
  bool pres = true;
  size_t pi = (size_t)0U;
  size_t len = len__uint8_t(s);
  bool res = pres;
  bool cond;
  if (res)
  {
    size_t i = pi;
    cond = i < len;
  }
  else
    cond = false;
  while (cond)
  {
    size_t i0 = pi;
    uint8_t byte1 = op_Array_Access__uint8_t(s, i0);
    size_t i1 = i0 + (size_t)1U;
    if (byte1 <= 0x7FU)
      pi = i1;
    else if (i1 == len)
      pres = false;
    else
    {
      uint8_t byte2 = op_Array_Access__uint8_t(s, i1);
      size_t i2 = i1 + (size_t)1U;
      if (0xC2U <= byte1 && byte1 <= 0xDFU && 0x80U <= byte2 && byte2 <= 0xBFU)
        pi = i2;
      else if (i2 == len)
        pres = false;
      else
      {
        uint8_t byte3 = op_Array_Access__uint8_t(s, i2);
        size_t i3 = i2 + (size_t)1U;
        if (!(0x80U <= byte3 && byte3 <= 0xBFU))
          pres = false;
        else if (byte1 == 0xE0U)
          if (0xA0U <= byte2 && byte2 <= 0xBFU)
            pi = i3;
          else
            pres = false;
        else if (byte1 == 0xEDU)
          if (0x80U <= byte2 && byte2 <= 0x9FU)
            pi = i3;
          else
            pres = false;
        else if (0xE1U <= byte1 && byte1 <= 0xEFU && 0x80U <= byte2 && byte2 <= 0xBFU)
          pi = i3;
        else if (i3 == len)
          pres = false;
        else
        {
          uint8_t byte4 = op_Array_Access__uint8_t(s, i3);
          size_t i4 = i3 + (size_t)1U;
          if (!(0x80U <= byte4 && byte4 <= 0xBFU))
            pres = false;
          else if (byte1 == 0xF0U && 0x90U <= byte2 && byte2 <= 0xBFU)
            pi = i4;
          else if (0xF1U <= byte1 && byte1 <= 0xF3U && 0x80U <= byte2 && byte2 <= 0xBFU)
            pi = i4;
          else if (byte1 == 0xF4U && 0x80U <= byte2 && byte2 <= 0x8FU)
            pi = i4;
          else
            pres = false;
        }
      }
    }
    bool res = pres;
    bool ite;
    if (res)
    {
      size_t i = pi;
      ite = i < len;
    }
    else
      ite = false;
    cond = ite;
  }
  return pres;
}

static initial_byte_t read_initial_byte_t(Pulse_Lib_Slice_slice__uint8_t input)
{
  uint8_t last = op_Array_Access__uint8_t(input, (size_t)0U);
  uint8_t res = last;
  uint8_t x = res;
  initial_byte_t
  res0 =
    { .major_type = get_bitfield_gen8(x, 5U, 8U), .additional_info = get_bitfield_gen8(x, 0U, 5U) };
  initial_byte_t res1 = res0;
  initial_byte_t res2 = res1;
  initial_byte_t res3 = res2;
  return res3;
}

typedef struct __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t_s
{
  Pulse_Lib_Slice_slice__uint8_t fst;
  Pulse_Lib_Slice_slice__uint8_t snd;
}
__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t;

static __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
split__uint8_t(Pulse_Lib_Slice_slice__uint8_t s, size_t i)
{
  uint8_t *elt_ = s.elt + i;
  Pulse_Lib_Slice_slice__uint8_t s1 = { .elt = s.elt, .len = i };
  Pulse_Lib_Slice_slice__uint8_t s2 = { .elt = elt_, .len = s.len - i };
  return
    ((__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){ .fst = s1, .snd = s2 });
}

static header read_header(Pulse_Lib_Slice_slice__uint8_t input)
{
  size_t i = (size_t)1U;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(input, i);
  Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = s.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s1, .snd = s2 };
  Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern.fst;
  Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern0 = { .fst = input10, .snd = input20 };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern0.fst;
  Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern0.snd;
  initial_byte_t x = read_initial_byte_t(input1);
  initial_byte_t res = x;
  initial_byte_t x1 = res;
  long_argument x2;
  if (x1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    if (x1.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    {
      uint8_t last = op_Array_Access__uint8_t(input2, (size_t)0U);
      uint8_t res = last;
      uint8_t x = res;
      long_argument
      res0 = { .tag = LongArgumentSimpleValue, { .case_LongArgumentSimpleValue = x } };
      long_argument res1 = res0;
      long_argument res2 = res1;
      x2 = res2;
    }
    else
    {
      uint8_t last = op_Array_Access__uint8_t(input2, (size_t)0U);
      uint8_t res = last;
      uint8_t x = res;
      long_argument res0 = { .tag = LongArgumentU8, { .case_LongArgumentU8 = x } };
      long_argument res1 = res0;
      x2 = res1;
    }
  else if (x1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
  {
    size_t pos_ = (size_t)1U;
    uint8_t last = op_Array_Access__uint8_t(input2, pos_);
    uint8_t last1 = op_Array_Access__uint8_t(input2, (size_t)0U);
    uint16_t n = (uint16_t)last1;
    uint16_t blast = (uint16_t)last;
    uint16_t res = (uint32_t)blast + (uint32_t)n * 256U;
    uint16_t x = res;
    long_argument res0 = { .tag = LongArgumentU16, { .case_LongArgumentU16 = x } };
    long_argument res1 = res0;
    x2 = res1;
  }
  else if (x1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
  {
    size_t pos_ = (size_t)3U;
    uint8_t last = op_Array_Access__uint8_t(input2, pos_);
    size_t pos_1 = pos_ - (size_t)1U;
    uint8_t last1 = op_Array_Access__uint8_t(input2, pos_1);
    size_t pos_2 = pos_1 - (size_t)1U;
    uint8_t last2 = op_Array_Access__uint8_t(input2, pos_2);
    uint8_t last3 = op_Array_Access__uint8_t(input2, (size_t)0U);
    uint32_t n = (uint32_t)last3;
    uint32_t blast0 = (uint32_t)last2;
    uint32_t n0 = blast0 + n * 256U;
    uint32_t blast1 = (uint32_t)last1;
    uint32_t n1 = blast1 + n0 * 256U;
    uint32_t blast = (uint32_t)last;
    uint32_t res = blast + n1 * 256U;
    uint32_t x = res;
    long_argument res0 = { .tag = LongArgumentU32, { .case_LongArgumentU32 = x } };
    long_argument res1 = res0;
    x2 = res1;
  }
  else if (x1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
  {
    size_t pos_ = (size_t)7U;
    uint8_t last = op_Array_Access__uint8_t(input2, pos_);
    size_t pos_1 = pos_ - (size_t)1U;
    uint8_t last1 = op_Array_Access__uint8_t(input2, pos_1);
    size_t pos_2 = pos_1 - (size_t)1U;
    uint8_t last2 = op_Array_Access__uint8_t(input2, pos_2);
    size_t pos_3 = pos_2 - (size_t)1U;
    uint8_t last3 = op_Array_Access__uint8_t(input2, pos_3);
    size_t pos_4 = pos_3 - (size_t)1U;
    uint8_t last4 = op_Array_Access__uint8_t(input2, pos_4);
    size_t pos_5 = pos_4 - (size_t)1U;
    uint8_t last5 = op_Array_Access__uint8_t(input2, pos_5);
    size_t pos_6 = pos_5 - (size_t)1U;
    uint8_t last6 = op_Array_Access__uint8_t(input2, pos_6);
    uint8_t last7 = op_Array_Access__uint8_t(input2, (size_t)0U);
    uint64_t n = (uint64_t)last7;
    uint64_t blast0 = (uint64_t)last6;
    uint64_t n0 = blast0 + n * 256ULL;
    uint64_t blast1 = (uint64_t)last5;
    uint64_t n1 = blast1 + n0 * 256ULL;
    uint64_t blast2 = (uint64_t)last4;
    uint64_t n2 = blast2 + n1 * 256ULL;
    uint64_t blast3 = (uint64_t)last3;
    uint64_t n3 = blast3 + n2 * 256ULL;
    uint64_t blast4 = (uint64_t)last2;
    uint64_t n4 = blast4 + n3 * 256ULL;
    uint64_t blast5 = (uint64_t)last1;
    uint64_t n5 = blast5 + n4 * 256ULL;
    uint64_t blast = (uint64_t)last;
    uint64_t res = blast + n5 * 256ULL;
    uint64_t x = res;
    long_argument res0 = { .tag = LongArgumentU64, { .case_LongArgumentU64 = x } };
    long_argument res1 = res0;
    x2 = res1;
  }
  else
    x2 = ((long_argument){ .tag = LongArgumentOther });
  header res0 = { .fst = x1, .snd = x2 };
  return res0;
}

static bool validate_header(Pulse_Lib_Slice_slice__uint8_t input, size_t *poffset)
{
  size_t offset1 = *poffset;
  size_t offset2 = *poffset;
  size_t offset30 = *poffset;
  bool is_valid0;
  if (len__uint8_t(input) - offset30 < (size_t)1U)
    is_valid0 = false;
  else
  {
    *poffset = offset30 + (size_t)1U;
    is_valid0 = true;
  }
  bool is_valid1;
  if (is_valid0)
  {
    size_t off = *poffset;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    s_ = split__uint8_t(input, offset2);
    Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s10, .snd = s20 };
    Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
    size_t consumed = off - offset2;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(input23, consumed);
    Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern1.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern1.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern10 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t left = _letpattern10.fst;
    Pulse_Lib_Slice_slice__uint8_t right = _letpattern10.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern11 = { .fst = left, .snd = right };
    Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern11.fst;
    initial_byte_t res = read_initial_byte_t(input_);
    initial_byte_t x = res;
    bool ite;
    if (x.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      ite = x.additional_info <= ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS;
    else
      ite = true;
    is_valid1 = ite && x.additional_info < ADDITIONAL_INFO_UNASSIGNED_MIN;
  }
  else
    is_valid1 = false;
  if (is_valid1)
  {
    size_t off = *poffset;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    s_ = split__uint8_t(input, offset1);
    Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s10, .snd = s20 };
    Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
    size_t consumed0 = off - offset1;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(input23, consumed0);
    Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern1.fst;
    Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern1.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern10 = { .fst = s11, .snd = s21 };
    Pulse_Lib_Slice_slice__uint8_t left0 = _letpattern10.fst;
    Pulse_Lib_Slice_slice__uint8_t right0 = _letpattern10.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern11 = { .fst = left0, .snd = right0 };
    Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern11.fst;
    initial_byte_t x = read_initial_byte_t(input_);
    initial_byte_t res = x;
    initial_byte_t res0 = res;
    initial_byte_t x0 = res0;
    if (x0.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
      if (x0.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      {
        size_t offset2 = *poffset;
        size_t offset3 = *poffset;
        bool is_valid;
        if (len__uint8_t(input) - offset3 < (size_t)1U)
          is_valid = false;
        else
        {
          *poffset = offset3 + (size_t)1U;
          is_valid = true;
        }
        if (is_valid)
        {
          size_t off1 = *poffset;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          s_ = split__uint8_t(input, offset2);
          Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
          Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern = { .fst = s10, .snd = s20 };
          Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
          size_t consumed = off1 - offset2;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern1 = split__uint8_t(input23, consumed);
          Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern1.fst;
          Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern1.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern10 = { .fst = s1, .snd = s2 };
          Pulse_Lib_Slice_slice__uint8_t left = _letpattern10.fst;
          Pulse_Lib_Slice_slice__uint8_t right = _letpattern10.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern11 = { .fst = left, .snd = right };
          Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern11.fst;
          uint8_t last = op_Array_Access__uint8_t(input_, (size_t)0U);
          uint8_t res = last;
          uint8_t res0 = res;
          uint8_t x1 = res0;
          return MIN_SIMPLE_VALUE_LONG_ARGUMENT <= x1;
        }
        else
          return false;
      }
      else
      {
        size_t offset2 = *poffset;
        if (len__uint8_t(input) - offset2 < (size_t)1U)
          return false;
        else
        {
          *poffset = offset2 + (size_t)1U;
          return true;
        }
      }
    else if (x0.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    {
      size_t offset2 = *poffset;
      if (len__uint8_t(input) - offset2 < (size_t)2U)
        return false;
      else
      {
        *poffset = offset2 + (size_t)2U;
        return true;
      }
    }
    else if (x0.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    {
      size_t offset2 = *poffset;
      if (len__uint8_t(input) - offset2 < (size_t)4U)
        return false;
      else
      {
        *poffset = offset2 + (size_t)4U;
        return true;
      }
    }
    else if (x0.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    {
      size_t offset2 = *poffset;
      if (len__uint8_t(input) - offset2 < (size_t)8U)
        return false;
      else
      {
        *poffset = offset2 + (size_t)8U;
        return true;
      }
    }
    else
      return true;
  }
  else
    return false;
}

static size_t jump_header(Pulse_Lib_Slice_slice__uint8_t input, size_t offset)
{
  size_t off1 = offset + (size_t)1U;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  s_ = split__uint8_t(input, offset);
  Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
  Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s10, .snd = s20 };
  Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
  size_t consumed = off1 - offset;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern1 = split__uint8_t(input23, consumed);
  Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern1.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern1.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern10 = { .fst = s1, .snd = s2 };
  Pulse_Lib_Slice_slice__uint8_t left = _letpattern10.fst;
  Pulse_Lib_Slice_slice__uint8_t right = _letpattern10.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern11 = { .fst = left, .snd = right };
  Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern11.fst;
  initial_byte_t x = read_initial_byte_t(input_);
  initial_byte_t res = x;
  initial_byte_t res0 = res;
  initial_byte_t x0 = res0;
  if (x0.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    return off1 + (size_t)1U;
  else if (x0.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    return off1 + (size_t)2U;
  else if (x0.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    return off1 + (size_t)4U;
  else if (x0.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    return off1 + (size_t)8U;
  else
    return off1 + (size_t)0U;
}

static bool
validate_recursive_step_count_leaf(
  Pulse_Lib_Slice_slice__uint8_t a,
  size_t bound,
  size_t *prem
)
{
  size_t i = jump_header(a, (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(a, i);
  Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = s.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s1, .snd = s2 };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern.fst;
  Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern0 = { .fst = input1, .snd = input2 };
  Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern0.fst;
  header h = read_header(input10);
  uint8_t typ = get_header_major_type(h);
  if (typ == CBOR_MAJOR_TYPE_ARRAY)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    uint64_t arg64 = argument_as_uint64(b, l);
    *prem = (size_t)arg64;
    return false;
  }
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    uint64_t arg64 = argument_as_uint64(b, l);
    size_t arg = (size_t)arg64;
    if (arg > bound)
      return true;
    else if (bound - arg < arg)
      return true;
    else
    {
      *prem = arg + arg;
      return false;
    }
  }
  else if (typ == CBOR_MAJOR_TYPE_TAGGED)
  {
    *prem = (size_t)1U;
    return false;
  }
  else
  {
    *prem = (size_t)0U;
    return false;
  }
}

static size_t jump_recursive_step_count_leaf(Pulse_Lib_Slice_slice__uint8_t a)
{
  size_t i = jump_header(a, (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(a, i);
  Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = s.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s1, .snd = s2 };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern.fst;
  Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern0 = { .fst = input1, .snd = input2 };
  Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern0.fst;
  header h = read_header(input10);
  uint8_t typ = get_header_major_type(h);
  if (typ == CBOR_MAJOR_TYPE_ARRAY)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    uint64_t arg64 = argument_as_uint64(b, l);
    return (size_t)arg64;
  }
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    uint64_t arg64 = argument_as_uint64(b, l);
    size_t arg = (size_t)arg64;
    return arg + arg;
  }
  else if (typ == CBOR_MAJOR_TYPE_TAGGED)
    return (size_t)1U;
  else
    return (size_t)0U;
}

static bool validate_raw_data_item(Pulse_Lib_Slice_slice__uint8_t input, size_t *poffset)
{
  size_t pn = (size_t)1U;
  bool pres = true;
  bool res0 = pres;
  size_t n0 = pn;
  bool cond = res0 && n0 > (size_t)0U;
  while (cond)
  {
    size_t off = *poffset;
    size_t n0 = pn;
    if (n0 > len__uint8_t(input) - off)
      pres = false;
    else
    {
      size_t offset1 = *poffset;
      bool is_valid1 = validate_header(input, poffset);
      bool res1;
      if (is_valid1)
      {
        size_t off1 = *poffset;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        s_ = split__uint8_t(input, offset1);
        Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
        Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern = { .fst = s10, .snd = s20 };
        Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
        size_t consumed0 = off1 - offset1;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern1 = split__uint8_t(input23, consumed0);
        Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern1.fst;
        Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern1.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern10 = { .fst = s11, .snd = s21 };
        Pulse_Lib_Slice_slice__uint8_t left0 = _letpattern10.fst;
        Pulse_Lib_Slice_slice__uint8_t right0 = _letpattern10.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern11 = { .fst = left0, .snd = right0 };
        Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern11.fst;
        header res0 = read_header(input_);
        header x = res0;
        initial_byte_t b = x.fst;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        {
          initial_byte_t b = x.fst;
          long_argument l = x.snd;
          size_t n1 = (size_t)argument_as_uint64(b, l);
          size_t offset2 = *poffset;
          size_t offset3 = *poffset;
          bool is_valid;
          if (len__uint8_t(input) - offset3 < n1)
            is_valid = false;
          else
          {
            *poffset = offset3 + n1;
            is_valid = true;
          }
          if (is_valid)
          {
            size_t off2 = *poffset;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            s_ = split__uint8_t(input, offset2);
            Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
            Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern = { .fst = s10, .snd = s20 };
            Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
            size_t consumed = off2 - offset2;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern1 = split__uint8_t(input23, consumed);
            Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern1.fst;
            Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern1.snd;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern10 = { .fst = s1, .snd = s2 };
            Pulse_Lib_Slice_slice__uint8_t left = _letpattern10.fst;
            Pulse_Lib_Slice_slice__uint8_t right = _letpattern10.snd;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern11 = { .fst = left, .snd = right };
            Pulse_Lib_Slice_slice__uint8_t x1 = _letpattern11.fst;
            bool res0;
            if (get_header_major_type(x) == CBOR_MAJOR_TYPE_BYTE_STRING)
              res0 = true;
            else
            {
              bool res = impl_correct(x1);
              res0 = res;
            }
            res1 = res0;
          }
          else
            res1 = false;
        }
        else
          res1 = true;
      }
      else
        res1 = false;
      if (!res1)
        pres = false;
      else
      {
        size_t offset1 = *poffset;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        s_ = split__uint8_t(input, off);
        Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
        Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern = { .fst = s10, .snd = s20 };
        Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
        size_t consumed = offset1 - off;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern1 = split__uint8_t(input23, consumed);
        Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern1.fst;
        Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern1.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern10 = { .fst = s1, .snd = s2 };
        Pulse_Lib_Slice_slice__uint8_t left = _letpattern10.fst;
        Pulse_Lib_Slice_slice__uint8_t right = _letpattern10.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern11 = { .fst = left, .snd = right };
        Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern11.fst;
        size_t bound = len__uint8_t(input) - off - n0;
        bool res2 = validate_recursive_step_count_leaf(input1, bound, &pn);
        size_t count = pn;
        if (res2 || count > bound)
          pres = false;
        else
        {
          size_t n_ = n0 - (size_t)1U + count;
          pn = n_;
        }
      }
    }
    bool res = pres;
    size_t n = pn;
    cond = res && n > (size_t)0U;
  }
  return pres;
}

static size_t jump_raw_data_item(Pulse_Lib_Slice_slice__uint8_t input, size_t offset)
{
  size_t poffset = offset;
  size_t pn = (size_t)1U;
  size_t n0 = pn;
  bool cond = n0 > (size_t)0U;
  while (cond)
  {
    size_t off = poffset;
    size_t off10 = jump_header(input, off);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(input, off);
    Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s10, .snd = s20 };
    Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
    size_t consumed0 = off10 - off;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(input23, consumed0);
    Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern1.fst;
    Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern1.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern10 = { .fst = s11, .snd = s21 };
    Pulse_Lib_Slice_slice__uint8_t left0 = _letpattern10.fst;
    Pulse_Lib_Slice_slice__uint8_t right0 = _letpattern10.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern11 = { .fst = left0, .snd = right0 };
    Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern11.fst;
    header res = read_header(input_);
    header x = res;
    initial_byte_t b0 = x.fst;
    size_t off1;
    if
    (b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      initial_byte_t b = x.fst;
      long_argument l = x.snd;
      off1 = off10 + (size_t)argument_as_uint64(b, l);
    }
    else
      off1 = off10 + (size_t)0U;
    poffset = off1;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_0 = split__uint8_t(input, off);
    Pulse_Lib_Slice_slice__uint8_t s12 = s_0.fst;
    Pulse_Lib_Slice_slice__uint8_t s22 = s_0.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern0 = { .fst = s12, .snd = s22 };
    Pulse_Lib_Slice_slice__uint8_t input230 = _letpattern0.snd;
    size_t consumed = off1 - off;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern12 = split__uint8_t(input230, consumed);
    Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern12.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern12.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern13 = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t left = _letpattern13.fst;
    Pulse_Lib_Slice_slice__uint8_t right = _letpattern13.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern14 = { .fst = left, .snd = right };
    Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern14.fst;
    size_t n = pn;
    size_t unused = len__uint8_t(input) - off1;
    KRML_MAYBE_UNUSED_VAR(unused);
    size_t count = jump_recursive_step_count_leaf(input1);
    pn = n - (size_t)1U + count;
    size_t n0 = pn;
    cond = n0 > (size_t)0U;
  }
  return poffset;
}

static cbor_raw cbor_read(Pulse_Lib_Slice_slice__uint8_t input)
{
  header
  ph =
    {
      .fst = { .major_type = CBOR_MAJOR_TYPE_SIMPLE_VALUE, .additional_info = 0U },
      .snd = { .tag = LongArgumentOther }
    };
  size_t i0 = jump_header(input, (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(input, i0);
  Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = s.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s1, .snd = s2 };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern.fst;
  Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern0 = { .fst = input1, .snd = input2 };
  Pulse_Lib_Slice_slice__uint8_t ph1 = _letpattern0.fst;
  Pulse_Lib_Slice_slice__uint8_t outc = _letpattern0.snd;
  header h0 = read_header(ph1);
  ph = h0;
  Pulse_Lib_Slice_slice__uint8_t pc = outc;
  header h = ph;
  uint8_t typ = h.fst.major_type;
  if (typ == CBOR_MAJOR_TYPE_UINT64 || typ == CBOR_MAJOR_TYPE_NEG_INT64)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 i;
    if (l.tag == LongArgumentU8)
    {
      uint8_t v1 = l.case_LongArgumentU8;
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU16)
    {
      uint16_t v1 = l.case_LongArgumentU16;
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU32)
    {
      uint32_t v1 = l.case_LongArgumentU32;
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU64)
    {
      uint64_t v1 = l.case_LongArgumentU64;
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = v1 });
    }
    else if (l.tag == LongArgumentOther)
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      i =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    cbor_int resi = { .cbor_int_type = typ, .cbor_int_size = i.size, .cbor_int_value = i.value };
    return ((cbor_raw){ .tag = CBOR_Case_Int, { .case_CBOR_Case_Int = resi } });
  }
  else if (typ == CBOR_MAJOR_TYPE_TEXT_STRING || typ == CBOR_MAJOR_TYPE_BYTE_STRING)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 i;
    if (l.tag == LongArgumentU8)
    {
      uint8_t v1 = l.case_LongArgumentU8;
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU16)
    {
      uint16_t v1 = l.case_LongArgumentU16;
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU32)
    {
      uint32_t v1 = l.case_LongArgumentU32;
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU64)
    {
      uint64_t v1 = l.case_LongArgumentU64;
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = v1 });
    }
    else if (l.tag == LongArgumentOther)
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      i =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    cbor_string
    ress = { .cbor_string_type = typ, .cbor_string_size = i.size, .cbor_string_ptr = pc };
    return ((cbor_raw){ .tag = CBOR_Case_String, { .case_CBOR_Case_String = ress } });
  }
  else if (typ == CBOR_MAJOR_TYPE_TAGGED)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 tag;
    if (l.tag == LongArgumentU8)
    {
      uint8_t v1 = l.case_LongArgumentU8;
      tag = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU16)
    {
      uint16_t v1 = l.case_LongArgumentU16;
      tag = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU32)
    {
      uint32_t v1 = l.case_LongArgumentU32;
      tag = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU64)
    {
      uint64_t v1 = l.case_LongArgumentU64;
      tag = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = v1 });
    }
    else if (l.tag == LongArgumentOther)
      tag = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      tag =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    cbor_serialized rest = { .cbor_serialized_header = tag, .cbor_serialized_payload = pc };
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Tagged,
          { .case_CBOR_Case_Serialized_Tagged = rest }
        }
      );
  }
  else if (typ == CBOR_MAJOR_TYPE_ARRAY)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (l.tag == LongArgumentU8)
    {
      uint8_t v1 = l.case_LongArgumentU8;
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU16)
    {
      uint16_t v1 = l.case_LongArgumentU16;
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU32)
    {
      uint32_t v1 = l.case_LongArgumentU32;
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU64)
    {
      uint64_t v1 = l.case_LongArgumentU64;
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = v1 });
    }
    else if (l.tag == LongArgumentOther)
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    cbor_serialized resa = { .cbor_serialized_header = len, .cbor_serialized_payload = pc };
    return
      ((cbor_raw){ .tag = CBOR_Case_Serialized_Array, { .case_CBOR_Case_Serialized_Array = resa } });
  }
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (l.tag == LongArgumentU8)
    {
      uint8_t v1 = l.case_LongArgumentU8;
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU16)
    {
      uint16_t v1 = l.case_LongArgumentU16;
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU32)
    {
      uint32_t v1 = l.case_LongArgumentU32;
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)v1 });
    }
    else if (l.tag == LongArgumentU64)
    {
      uint64_t v1 = l.case_LongArgumentU64;
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = v1 });
    }
    else if (l.tag == LongArgumentOther)
      len = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    cbor_serialized resa = { .cbor_serialized_header = len, .cbor_serialized_payload = pc };
    return
      ((cbor_raw){ .tag = CBOR_Case_Serialized_Map, { .case_CBOR_Case_Serialized_Map = resa } });
  }
  else
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    uint8_t i;
    if (l.tag == LongArgumentOther)
      i = b.additional_info;
    else if (l.tag == LongArgumentSimpleValue)
      i = l.case_LongArgumentSimpleValue;
    else
      i = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = i } });
  }
}

static cbor_raw cbor_match_serialized_tagged_get_payload(cbor_serialized c)
{
  cbor_raw res = cbor_read(c.cbor_serialized_payload);
  return res;
}

static cbor_raw cbor_serialized_array_item(cbor_serialized c, uint64_t i)
{
  size_t j = (size_t)i;
  size_t pi = (size_t)0U;
  Pulse_Lib_Slice_slice__uint8_t pres = c.cbor_serialized_payload;
  size_t i10 = pi;
  bool cond = i10 < j;
  while (cond)
  {
    Pulse_Lib_Slice_slice__uint8_t res = pres;
    size_t i1 = pi;
    size_t i2 = jump_raw_data_item(res, (size_t)0U);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(res, i2);
    Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern.fst;
    Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern0 = { .fst = input10, .snd = input20 };
    Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern0.fst;
    Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern0.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = { .fst = input1, .snd = input2 };
    Pulse_Lib_Slice_slice__uint8_t res1 = _letpattern1.snd;
    Pulse_Lib_Slice_slice__uint8_t res2 = res1;
    pi = i1 + (size_t)1U;
    pres = res2;
    size_t i10 = pi;
    cond = i10 < j;
  }
  Pulse_Lib_Slice_slice__uint8_t res = pres;
  size_t i1 = jump_raw_data_item(res, (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(res, i1);
  Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = s.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s1, .snd = s2 };
  Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern.fst;
  Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern0 = { .fst = input10, .snd = input20 };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern0.fst;
  Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern0.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern1 = { .fst = input1, .snd = input2 };
  Pulse_Lib_Slice_slice__uint8_t res1 = _letpattern1.fst;
  Pulse_Lib_Slice_slice__uint8_t res2 = res1;
  Pulse_Lib_Slice_slice__uint8_t elt = res2;
  cbor_raw res0 = cbor_read(elt);
  return res0;
}

static CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
cbor_serialized_array_iterator_init(cbor_serialized c)
{
  return
    (
      (CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator){
        .s = c.cbor_serialized_payload,
        .len = c.cbor_serialized_header.value
      }
    );
}

static bool
cbor_serialized_array_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator c
)
{
  return c.len == 0ULL;
}

static uint64_t
cbor_serialized_array_iterator_length(
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator c
)
{
  return c.len;
}

static cbor_raw
cbor_serialized_array_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw *pi,
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator i
)
{
  size_t i1 = jump_raw_data_item(i.s, (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(i.s, i1);
  Pulse_Lib_Slice_slice__uint8_t s10 = s.fst;
  Pulse_Lib_Slice_slice__uint8_t s20 = s.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s10, .snd = s20 };
  Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern.fst;
  Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern0 = { .fst = input10, .snd = input20 };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern0.fst;
  Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern0.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern1 = { .fst = input1, .snd = input2 };
  Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern1.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern1.snd;
  cbor_raw res = cbor_read(s1);
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
  i_ = { .s = s2, .len = i.len - 1ULL };
  *pi =
    (
      (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
        .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = i_ }
      }
    );
  return res;
}

static CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
cbor_serialized_array_iterator_truncate(
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator c,
  uint64_t len
)
{
  return ((CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator){ .s = c.s, .len = len });
}

static CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
cbor_serialized_map_iterator_init(cbor_serialized c)
{
  return
    (
      (CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator){
        .s = c.cbor_serialized_payload,
        .len = c.cbor_serialized_header.value
      }
    );
}

static bool
cbor_serialized_map_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator c
)
{
  return c.len == 0ULL;
}

static cbor_map_entry
cbor_serialized_map_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry *pi,
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator i
)
{
  size_t off1 = jump_raw_data_item(i.s, (size_t)0U);
  size_t i10 = jump_raw_data_item(i.s, off1);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(i.s, i10);
  Pulse_Lib_Slice_slice__uint8_t s10 = s.fst;
  Pulse_Lib_Slice_slice__uint8_t s20 = s.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s10, .snd = s20 };
  Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern.fst;
  Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern0 = { .fst = input10, .snd = input20 };
  Pulse_Lib_Slice_slice__uint8_t input11 = _letpattern0.fst;
  Pulse_Lib_Slice_slice__uint8_t input21 = _letpattern0.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern1 = { .fst = input11, .snd = input21 };
  Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern1.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern1.snd;
  size_t i1 = jump_raw_data_item(s1, (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s0 = split__uint8_t(s1, i1);
  Pulse_Lib_Slice_slice__uint8_t s110 = s0.fst;
  Pulse_Lib_Slice_slice__uint8_t s210 = s0.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern10 = { .fst = s110, .snd = s210 };
  Pulse_Lib_Slice_slice__uint8_t input12 = _letpattern10.fst;
  Pulse_Lib_Slice_slice__uint8_t input22 = _letpattern10.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern11 = { .fst = input12, .snd = input22 };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern11.fst;
  Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern11.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern12 = { .fst = input1, .snd = input2 };
  Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern12.fst;
  Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern12.snd;
  cbor_raw res1 = cbor_read(s11);
  cbor_raw res2 = cbor_read(s21);
  cbor_map_entry res = { .cbor_map_entry_key = res1, .cbor_map_entry_value = res2 };
  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
  i_ = { .s = s2, .len = i.len - 1ULL };
  *pi =
    (
      (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
        .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = i_ }
      }
    );
  return res;
}

static cbor_raw cbor_match_tagged_get_payload(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Tagged)
  {
    cbor_serialized cs = c.case_CBOR_Case_Serialized_Tagged;
    cbor_raw res = cbor_match_serialized_tagged_get_payload(cs);
    return res;
  }
  else if (c.tag == CBOR_Case_Tagged)
  {
    cbor_tagged ct = c.case_CBOR_Case_Tagged;
    return *ct.cbor_tagged_ptr;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_raw
op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw a,
  size_t i
)
{
  return a.elt[i];
}

static cbor_raw cbor_array_item(cbor_raw c, uint64_t i)
{
  if (c.tag == CBOR_Case_Serialized_Array)
  {
    cbor_serialized c_ = c.case_CBOR_Case_Serialized_Array;
    cbor_raw res = cbor_serialized_array_item(c_, i);
    return res;
  }
  else if (c.tag == CBOR_Case_Array)
  {
    cbor_array c_ = c.case_CBOR_Case_Array;
    cbor_raw res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr, (size_t)i);
    return res;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_array_iterator_init(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Array)
  {
    cbor_serialized c_ = c.case_CBOR_Case_Serialized_Array;
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
    i_ = cbor_serialized_array_iterator_init(c_);
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
          { .case_CBOR_Raw_Iterator_Serialized = i_ }
        }
      );
  }
  else if (c.tag == CBOR_Case_Array)
  {
    cbor_array c_ = c.case_CBOR_Case_Array;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i = c_.cbor_array_ptr;
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = i }
        }
      );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static size_t
len__CBOR_Pulse_Raw_Type_cbor_raw(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s)
{
  return s.len;
}

static bool
cbor_array_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw c
)
{
  if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw c_ = c.case_CBOR_Raw_Iterator_Slice;
    bool res = len__CBOR_Pulse_Raw_Type_cbor_raw(c_) == (size_t)0U;
    bool res0 = res;
    return res0;
  }
  else if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
  {
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
    c_ = c.case_CBOR_Raw_Iterator_Serialized;
    bool res = cbor_serialized_array_iterator_is_empty(c_);
    return res;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static uint64_t
cbor_array_iterator_length(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw c
)
{
  if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw c_ = c.case_CBOR_Raw_Iterator_Slice;
    uint64_t res = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_);
    uint64_t res0 = res;
    return res0;
  }
  else if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
  {
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
    c_ = c.case_CBOR_Raw_Iterator_Serialized;
    uint64_t res = cbor_serialized_array_iterator_length(c_);
    return res;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct
__Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_s
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw fst;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw snd;
}
__Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw;

static __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
split__CBOR_Pulse_Raw_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s,
  size_t i
)
{
  cbor_raw *elt_ = s.elt + i;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s1 = { .elt = s.elt, .len = i };
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s2 = { .elt = elt_, .len = s.len - i };
  return
    (
      (__Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw){
        .fst = s1,
        .snd = s2
      }
    );
}

static cbor_raw
cbor_array_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw *pi
)
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw i0 = *pi;
  if (i0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i1 = i0.case_CBOR_Raw_Iterator_Slice;
    cbor_raw res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i1, (size_t)0U);
    __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
    _letpattern = split__CBOR_Pulse_Raw_Type_cbor_raw(i1, (size_t)1U);
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s_ = _letpattern.snd;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i11 = s_;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i_ = i11;
    *pi =
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = i_ }
        }
      );
    cbor_raw res0 = res;
    return res0;
  }
  else if (i0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
  {
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
    i1 = i0.case_CBOR_Raw_Iterator_Serialized;
    cbor_raw res = cbor_serialized_array_iterator_next(pi, i1);
    return res;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_array_iterator_truncate(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw c,
  uint64_t len
)
{
  if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw c_ = c.case_CBOR_Raw_Iterator_Slice;
    __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
    s_ = split__CBOR_Pulse_Raw_Type_cbor_raw(c_, (size_t)len);
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s11 = s_.fst;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s21 = s_.snd;
    __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
    _letpattern = { .fst = s11, .snd = s21 };
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw sl1 = _letpattern.fst;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw c1 = sl1;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw c_1 = c1;
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = c_1 }
        }
      );
  }
  else if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
  {
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
    c_ = c.case_CBOR_Raw_Iterator_Serialized;
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
    sres = cbor_serialized_array_iterator_truncate(c_, len);
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
          { .case_CBOR_Raw_Iterator_Serialized = sres }
        }
      );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
cbor_map_iterator_init(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Map)
  {
    cbor_serialized c_ = c.case_CBOR_Case_Serialized_Map;
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
    i_ = cbor_serialized_map_iterator_init(c_);
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
          { .case_CBOR_Raw_Iterator_Serialized = i_ }
        }
      );
  }
  else if (c.tag == CBOR_Case_Map)
  {
    cbor_map c_ = c.case_CBOR_Case_Map;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry i = c_.cbor_map_ptr;
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = i }
        }
      );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static size_t
len__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry s
)
{
  return s.len;
}

static bool
cbor_map_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry c
)
{
  if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry c_ = c.case_CBOR_Raw_Iterator_Slice;
    bool res = len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_) == (size_t)0U;
    bool res0 = res;
    return res0;
  }
  else if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
  {
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
    c_ = c.case_CBOR_Raw_Iterator_Serialized;
    bool res = cbor_serialized_map_iterator_is_empty(c_);
    return res;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_map_entry
op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a,
  size_t i
)
{
  return a.elt[i];
}

typedef struct
__Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry fst;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry snd;
}
__Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry;

static __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
split__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry s,
  size_t i
)
{
  cbor_map_entry *elt_ = s.elt + i;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry s1 = { .elt = s.elt, .len = i };
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
  s2 = { .elt = elt_, .len = s.len - i };
  return
    (
      (__Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry){
        .fst = s1,
        .snd = s2
      }
    );
}

static cbor_map_entry
cbor_map_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry *pi
)
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry i0 = *pi;
  if (i0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry i1 = i0.case_CBOR_Raw_Iterator_Slice;
    cbor_map_entry res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i1, (size_t)0U);
    __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
    _letpattern = split__CBOR_Pulse_Raw_Type_cbor_map_entry(i1, (size_t)1U);
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry s_ = _letpattern.snd;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry i11 = s_;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry i_ = i11;
    *pi =
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = i_ }
        }
      );
    cbor_map_entry res0 = res;
    return res0;
  }
  else if (i0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
  {
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
    i1 = i0.case_CBOR_Raw_Iterator_Serialized;
    cbor_map_entry res = cbor_serialized_map_iterator_next(pi, i1);
    return res;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static initial_byte_t
__proj__Mkdtuple2__item___1__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  header pair
)
{
  return pair.fst;
}

static initial_byte_t
dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(header t)
{
  return
    __proj__Mkdtuple2__item___1__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(t);
}

static void op_Array_Assignment__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i, uint8_t v)
{
  a.elt[i] = v;
}

static long_argument
__proj__Mkdtuple2__item___2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
  header pair
)
{
  return pair.snd;
}

static long_argument
dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(header t)
{
  return
    __proj__Mkdtuple2__item___2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(t);
}

static size_t write_header(header x, Pulse_Lib_Slice_slice__uint8_t out, size_t offset)
{
  initial_byte_t
  xh1 = dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  size_t pos_ = offset + (size_t)1U;
  uint8_t
  n_ =
    set_bitfield_gen8(set_bitfield_gen8(0U, 0U, 5U, xh1.additional_info),
      5U,
      8U,
      xh1.major_type);
  op_Array_Assignment__uint8_t(out, pos_ - (size_t)1U, n_);
  size_t res1 = pos_;
  long_argument
  x2_ = dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  size_t res;
  if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    if (xh1.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    {
      size_t pos_ = res1 + (size_t)1U;
      uint8_t n_;
      if (x2_.tag == LongArgumentSimpleValue)
        n_ = x2_.case_LongArgumentSimpleValue;
      else
        n_ = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      op_Array_Assignment__uint8_t(out, pos_ - (size_t)1U, n_);
      res = pos_;
    }
    else
    {
      size_t pos_ = res1 + (size_t)1U;
      uint8_t n_;
      if (x2_.tag == LongArgumentU8)
        n_ = x2_.case_LongArgumentU8;
      else
        n_ = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      op_Array_Assignment__uint8_t(out, pos_ - (size_t)1U, n_);
      res = pos_;
    }
  else if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
  {
    size_t pos_ = res1 + (size_t)2U;
    uint16_t ite0;
    if (x2_.tag == LongArgumentU16)
      ite0 = x2_.case_LongArgumentU16;
    else
      ite0 = KRML_EABORT(uint16_t, "unreachable (pattern matches are exhaustive in F*)");
    uint8_t lo = (uint8_t)ite0;
    uint16_t ite;
    if (x2_.tag == LongArgumentU16)
      ite = x2_.case_LongArgumentU16;
    else
      ite = KRML_EABORT(uint16_t, "unreachable (pattern matches are exhaustive in F*)");
    uint16_t hi = (uint32_t)ite / 256U;
    size_t pos_1 = pos_ - (size_t)1U;
    uint8_t n_ = (uint8_t)hi;
    op_Array_Assignment__uint8_t(out, pos_1 - (size_t)1U, n_);
    op_Array_Assignment__uint8_t(out, pos_1, lo);
    res = pos_;
  }
  else if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
  {
    size_t pos_ = res1 + (size_t)4U;
    uint32_t ite0;
    if (x2_.tag == LongArgumentU32)
      ite0 = x2_.case_LongArgumentU32;
    else
      ite0 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
    uint8_t lo = (uint8_t)ite0;
    uint32_t ite;
    if (x2_.tag == LongArgumentU32)
      ite = x2_.case_LongArgumentU32;
    else
      ite = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
    uint32_t hi = ite / 256U;
    size_t pos_1 = pos_ - (size_t)1U;
    uint8_t lo1 = (uint8_t)hi;
    uint32_t hi1 = hi / 256U;
    size_t pos_2 = pos_1 - (size_t)1U;
    uint8_t lo2 = (uint8_t)hi1;
    uint32_t hi2 = hi1 / 256U;
    size_t pos_3 = pos_2 - (size_t)1U;
    uint8_t n_ = (uint8_t)hi2;
    op_Array_Assignment__uint8_t(out, pos_3 - (size_t)1U, n_);
    op_Array_Assignment__uint8_t(out, pos_3, lo2);
    op_Array_Assignment__uint8_t(out, pos_2, lo1);
    op_Array_Assignment__uint8_t(out, pos_1, lo);
    res = pos_;
  }
  else if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
  {
    size_t pos_ = res1 + (size_t)8U;
    uint64_t ite0;
    if (x2_.tag == LongArgumentU64)
      ite0 = x2_.case_LongArgumentU64;
    else
      ite0 = KRML_EABORT(uint64_t, "unreachable (pattern matches are exhaustive in F*)");
    uint8_t lo = (uint8_t)ite0;
    uint64_t ite;
    if (x2_.tag == LongArgumentU64)
      ite = x2_.case_LongArgumentU64;
    else
      ite = KRML_EABORT(uint64_t, "unreachable (pattern matches are exhaustive in F*)");
    uint64_t hi = ite / 256ULL;
    size_t pos_1 = pos_ - (size_t)1U;
    uint8_t lo1 = (uint8_t)hi;
    uint64_t hi1 = hi / 256ULL;
    size_t pos_2 = pos_1 - (size_t)1U;
    uint8_t lo2 = (uint8_t)hi1;
    uint64_t hi2 = hi1 / 256ULL;
    size_t pos_3 = pos_2 - (size_t)1U;
    uint8_t lo3 = (uint8_t)hi2;
    uint64_t hi3 = hi2 / 256ULL;
    size_t pos_4 = pos_3 - (size_t)1U;
    uint8_t lo4 = (uint8_t)hi3;
    uint64_t hi4 = hi3 / 256ULL;
    size_t pos_5 = pos_4 - (size_t)1U;
    uint8_t lo5 = (uint8_t)hi4;
    uint64_t hi5 = hi4 / 256ULL;
    size_t pos_6 = pos_5 - (size_t)1U;
    uint8_t lo6 = (uint8_t)hi5;
    uint64_t hi6 = hi5 / 256ULL;
    size_t pos_7 = pos_6 - (size_t)1U;
    uint8_t n_ = (uint8_t)hi6;
    op_Array_Assignment__uint8_t(out, pos_7 - (size_t)1U, n_);
    op_Array_Assignment__uint8_t(out, pos_7, lo6);
    op_Array_Assignment__uint8_t(out, pos_6, lo5);
    op_Array_Assignment__uint8_t(out, pos_5, lo4);
    op_Array_Assignment__uint8_t(out, pos_4, lo3);
    op_Array_Assignment__uint8_t(out, pos_3, lo2);
    op_Array_Assignment__uint8_t(out, pos_2, lo1);
    op_Array_Assignment__uint8_t(out, pos_1, lo);
    res = pos_;
  }
  else
    res = res1;
  size_t res2 = res;
  size_t res0 = res2;
  return res0;
}

static bool size_header(header x, size_t *out)
{
  initial_byte_t
  xh1 = dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  size_t capacity0 = *out;
  bool res0;
  if (capacity0 < (size_t)1U)
    res0 = false;
  else
  {
    *out = capacity0 - (size_t)1U;
    res0 = true;
  }
  bool res1 = res0;
  if (res1)
  {
    long_argument
    x2_ = dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
    KRML_MAYBE_UNUSED_VAR(x2_);
    bool res0;
    if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    {
      size_t capacity = *out;
      bool res;
      if (capacity < (size_t)1U)
        res = false;
      else
      {
        *out = capacity - (size_t)1U;
        res = true;
      }
      res0 = res;
    }
    else if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    {
      size_t capacity = *out;
      bool res;
      if (capacity < (size_t)2U)
        res = false;
      else
      {
        *out = capacity - (size_t)2U;
        res = true;
      }
      res0 = res;
    }
    else if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    {
      size_t capacity = *out;
      bool res;
      if (capacity < (size_t)4U)
        res = false;
      else
      {
        *out = capacity - (size_t)4U;
        res = true;
      }
      res0 = res;
    }
    else if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    {
      size_t capacity = *out;
      bool res;
      if (capacity < (size_t)8U)
        res = false;
      else
      {
        *out = capacity - (size_t)8U;
        res = true;
      }
      res0 = res;
    }
    else
      res0 = true;
    bool res2 = res0;
    return res2;
  }
  else
    return false;
}

static header cbor_raw_get_header(cbor_raw xl)
{
  if (xl.tag == CBOR_Case_Int)
  {
    cbor_raw _letpattern0 = xl;
    uint8_t ty;
    if (_letpattern0.tag == CBOR_Case_Int)
    {
      cbor_int c_ = _letpattern0.case_CBOR_Case_Int;
      ty = c_.cbor_int_type;
    }
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    cbor_raw _letpattern = xl;
    CBOR_Spec_Raw_Base_raw_uint64 v;
    if (_letpattern.tag == CBOR_Case_Int)
    {
      cbor_int c_ = _letpattern.case_CBOR_Case_Int;
      v = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
    }
    else
      v =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(ty, v);
  }
  else if (xl.tag == CBOR_Case_String)
  {
    cbor_raw _letpattern0 = xl;
    uint8_t ty;
    if (_letpattern0.tag == CBOR_Case_String)
    {
      cbor_string c_ = _letpattern0.case_CBOR_Case_String;
      ty = c_.cbor_string_type;
    }
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    cbor_raw _letpattern = xl;
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (_letpattern.tag == CBOR_Case_String)
    {
      cbor_string c_ = _letpattern.case_CBOR_Case_String;
      CBOR_Spec_Raw_Base_raw_uint64
      res = { .size = c_.cbor_string_size, .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr) };
      len = res;
    }
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(ty, len);
  }
  else if (xl.tag == CBOR_Case_Tagged)
  {
    CBOR_Spec_Raw_Base_raw_uint64 tag;
    if (xl.tag == CBOR_Case_Tagged)
    {
      cbor_tagged c_ = xl.case_CBOR_Case_Tagged;
      tag = c_.cbor_tagged_tag;
    }
    else if (xl.tag == CBOR_Case_Serialized_Tagged)
    {
      cbor_serialized c_ = xl.case_CBOR_Case_Serialized_Tagged;
      tag = c_.cbor_serialized_header;
    }
    else
      tag =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED, tag);
  }
  else if (xl.tag == CBOR_Case_Serialized_Tagged)
  {
    CBOR_Spec_Raw_Base_raw_uint64 tag;
    if (xl.tag == CBOR_Case_Tagged)
    {
      cbor_tagged c_ = xl.case_CBOR_Case_Tagged;
      tag = c_.cbor_tagged_tag;
    }
    else if (xl.tag == CBOR_Case_Serialized_Tagged)
    {
      cbor_serialized c_ = xl.case_CBOR_Case_Serialized_Tagged;
      tag = c_.cbor_serialized_header;
    }
    else
      tag =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED, tag);
  }
  else if (xl.tag == CBOR_Case_Array)
  {
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (xl.tag == CBOR_Case_Array)
    {
      cbor_array c_ = xl.case_CBOR_Case_Array;
      len =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_array_length_size,
            .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
          }
        );
    }
    else if (xl.tag == CBOR_Case_Serialized_Array)
    {
      cbor_serialized c_ = xl.case_CBOR_Case_Serialized_Array;
      len = c_.cbor_serialized_header;
    }
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY, len);
  }
  else if (xl.tag == CBOR_Case_Serialized_Array)
  {
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (xl.tag == CBOR_Case_Array)
    {
      cbor_array c_ = xl.case_CBOR_Case_Array;
      len =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_array_length_size,
            .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
          }
        );
    }
    else if (xl.tag == CBOR_Case_Serialized_Array)
    {
      cbor_serialized c_ = xl.case_CBOR_Case_Serialized_Array;
      len = c_.cbor_serialized_header;
    }
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY, len);
  }
  else if (xl.tag == CBOR_Case_Map)
  {
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (xl.tag == CBOR_Case_Map)
    {
      cbor_map c_ = xl.case_CBOR_Case_Map;
      len =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_map_length_size,
            .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
          }
        );
    }
    else if (xl.tag == CBOR_Case_Serialized_Map)
    {
      cbor_serialized c_ = xl.case_CBOR_Case_Serialized_Map;
      len = c_.cbor_serialized_header;
    }
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP, len);
  }
  else if (xl.tag == CBOR_Case_Serialized_Map)
  {
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (xl.tag == CBOR_Case_Map)
    {
      cbor_map c_ = xl.case_CBOR_Case_Map;
      len =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_map_length_size,
            .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
          }
        );
    }
    else if (xl.tag == CBOR_Case_Serialized_Map)
    {
      cbor_serialized c_ = xl.case_CBOR_Case_Serialized_Map;
      len = c_.cbor_serialized_header;
    }
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP, len);
  }
  else if (xl.tag == CBOR_Case_Simple)
  {
    cbor_raw _letpattern = xl;
    uint8_t v;
    if (_letpattern.tag == CBOR_Case_Simple)
      v = _letpattern.case_CBOR_Case_Simple;
    else
      v = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return simple_value_as_argument(v);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static header cbor_raw_with_perm_get_header(cbor_raw xl)
{
  header res = cbor_raw_get_header(xl);
  return res;
}

#define None 0
#define Some 1

typedef uint8_t
option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_tags;

typedef struct
option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_s
{
  option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_tags
  tag;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw v;
}
option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw;

typedef struct
option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_tags
  tag;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry v;
}
option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry;

size_t
CBOR_Pulse_Raw_Format_Serialize_ser_(
  cbor_raw x_,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t offset
)
{
  header res0 = cbor_raw_with_perm_get_header(x_);
  header xh1 = res0;
  size_t res1 = write_header(xh1, out, offset);
  initial_byte_t b0 = xh1.fst;
  size_t res2;
  if
  (b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
  {
    cbor_raw _letpattern0 = x_;
    Pulse_Lib_Slice_slice__uint8_t s;
    if (_letpattern0.tag == CBOR_Case_String)
    {
      cbor_string c_ = _letpattern0.case_CBOR_Case_String;
      s = c_.cbor_string_ptr;
    }
    else
      s =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    Pulse_Lib_Slice_slice__uint8_t x2_ = s;
    size_t length = len__uint8_t(x2_);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = split__uint8_t(out, res1);
    Pulse_Lib_Slice_slice__uint8_t sp12 = _letpattern.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(sp12, length);
    Pulse_Lib_Slice_slice__uint8_t sp21 = _letpattern1.fst;
    copy__uint8_t(sp21, x2_);
    size_t res = res1 + length;
    size_t res0 = res;
    size_t res1 = res0;
    res2 = res1;
  }
  else
  {
    initial_byte_t b = xh1.fst;
    if (b.major_type == CBOR_MAJOR_TYPE_ARRAY)
    {
      bool ite;
      if (x_.tag == CBOR_Case_Array)
        ite = true;
      else
        ite = false;
      if (ite)
      {
        cbor_raw x2_ = x_;
        cbor_raw scrut0 = x2_;
        option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
        scrut;
        if (scrut0.tag == CBOR_Case_Array)
        {
          cbor_array a = scrut0.case_CBOR_Case_Array;
          scrut =
            (
              (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw){
                .tag = Some,
                .v = a.cbor_array_ptr
              }
            );
        }
        else
          scrut =
            (
              (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw){
                .tag = None
              }
            );
        Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw a;
        if (scrut.tag == Some)
          a = scrut.v;
        else
          a =
            KRML_EABORT(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t pres = res1;
        size_t pi = (size_t)0U;
        size_t i0 = pi;
        bool cond = i0 < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
        while (cond)
        {
          size_t i = pi;
          size_t off = pres;
          cbor_raw e = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(a, i);
          size_t i_ = i + (size_t)1U;
          cbor_raw x2_1 = e;
          size_t res = CBOR_Pulse_Raw_Format_Serialize_ser_(x2_1, out, off);
          size_t res0 = res;
          size_t res1 = res0;
          pi = i_;
          pres = res1;
          size_t i0 = pi;
          cond = i0 < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
        }
        size_t res = pres;
        size_t res0 = res;
        size_t res1 = res0;
        res2 = res1;
      }
      else
      {
        cbor_raw _letpattern0 = x_;
        Pulse_Lib_Slice_slice__uint8_t x2_;
        if (_letpattern0.tag == CBOR_Case_Serialized_Array)
        {
          cbor_serialized xs = _letpattern0.case_CBOR_Case_Serialized_Array;
          x2_ = xs.cbor_serialized_payload;
        }
        else
          x2_ =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = len__uint8_t(x2_);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern = split__uint8_t(out, res1);
        Pulse_Lib_Slice_slice__uint8_t sp12 = _letpattern.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern1 = split__uint8_t(sp12, length);
        Pulse_Lib_Slice_slice__uint8_t sp21 = _letpattern1.fst;
        copy__uint8_t(sp21, x2_);
        size_t res = res1 + length;
        size_t res0 = res;
        size_t res1 = res0;
        res2 = res1;
      }
    }
    else
    {
      initial_byte_t b = xh1.fst;
      if (b.major_type == CBOR_MAJOR_TYPE_MAP)
      {
        bool ite;
        if (x_.tag == CBOR_Case_Map)
          ite = true;
        else
          ite = false;
        if (ite)
        {
          cbor_raw x2_ = x_;
          cbor_raw scrut0 = x2_;
          option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
          scrut;
          if (scrut0.tag == CBOR_Case_Map)
          {
            cbor_map a = scrut0.case_CBOR_Case_Map;
            scrut =
              (
                (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry){
                  .tag = Some,
                  .v = a.cbor_map_ptr
                }
              );
          }
          else
            scrut =
              (
                (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry){
                  .tag = None
                }
              );
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a;
          if (scrut.tag == Some)
            a = scrut.v;
          else
            a =
              KRML_EABORT(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry,
                "unreachable (pattern matches are exhaustive in F*)");
          size_t pres = res1;
          size_t pi = (size_t)0U;
          size_t i0 = pi;
          bool cond = i0 < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
          while (cond)
          {
            size_t i = pi;
            size_t off = pres;
            cbor_map_entry e = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i);
            size_t i_ = i + (size_t)1U;
            cbor_raw x11 = e.cbor_map_entry_key;
            size_t res = CBOR_Pulse_Raw_Format_Serialize_ser_(x11, out, off);
            size_t res11 = res;
            cbor_raw x2 = e.cbor_map_entry_value;
            size_t res0 = CBOR_Pulse_Raw_Format_Serialize_ser_(x2, out, res11);
            size_t res2 = res0;
            size_t res1 = res2;
            pi = i_;
            pres = res1;
            size_t i0 = pi;
            cond = i0 < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
          }
          size_t res = pres;
          size_t res0 = res;
          size_t res1 = res0;
          res2 = res1;
        }
        else
        {
          cbor_raw _letpattern0 = x_;
          Pulse_Lib_Slice_slice__uint8_t x2_;
          if (_letpattern0.tag == CBOR_Case_Serialized_Map)
          {
            cbor_serialized xs = _letpattern0.case_CBOR_Case_Serialized_Map;
            x2_ = xs.cbor_serialized_payload;
          }
          else
            x2_ =
              KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
                "unreachable (pattern matches are exhaustive in F*)");
          size_t length = len__uint8_t(x2_);
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern = split__uint8_t(out, res1);
          Pulse_Lib_Slice_slice__uint8_t sp12 = _letpattern.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern1 = split__uint8_t(sp12, length);
          Pulse_Lib_Slice_slice__uint8_t sp21 = _letpattern1.fst;
          copy__uint8_t(sp21, x2_);
          size_t res = res1 + length;
          size_t res0 = res;
          size_t res1 = res0;
          res2 = res1;
        }
      }
      else
      {
        initial_byte_t b = xh1.fst;
        if (b.major_type == CBOR_MAJOR_TYPE_TAGGED)
        {
          bool ite;
          if (x_.tag == CBOR_Case_Tagged)
            ite = true;
          else
            ite = false;
          size_t res;
          if (ite)
          {
            cbor_raw _letpattern = x_;
            cbor_raw x2_;
            if (_letpattern.tag == CBOR_Case_Tagged)
            {
              cbor_tagged tg = _letpattern.case_CBOR_Case_Tagged;
              x2_ = *tg.cbor_tagged_ptr;
            }
            else
              x2_ = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
            size_t res0 = CBOR_Pulse_Raw_Format_Serialize_ser_(x2_, out, res1);
            size_t res1 = res0;
            size_t res2 = res1;
            res = res2;
          }
          else
          {
            cbor_raw _letpattern0 = x_;
            Pulse_Lib_Slice_slice__uint8_t x2_;
            if (_letpattern0.tag == CBOR_Case_Serialized_Tagged)
            {
              cbor_serialized ser = _letpattern0.case_CBOR_Case_Serialized_Tagged;
              x2_ = ser.cbor_serialized_payload;
            }
            else
              x2_ =
                KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
                  "unreachable (pattern matches are exhaustive in F*)");
            size_t length = len__uint8_t(x2_);
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern = split__uint8_t(out, res1);
            Pulse_Lib_Slice_slice__uint8_t sp12 = _letpattern.snd;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            _letpattern1 = split__uint8_t(sp12, length);
            Pulse_Lib_Slice_slice__uint8_t sp21 = _letpattern1.fst;
            copy__uint8_t(sp21, x2_);
            size_t res0 = res1 + length;
            size_t res1 = res0;
            res = res1;
          }
          res2 = res;
        }
        else
          res2 = res1;
      }
    }
  }
  size_t res = res2;
  size_t res3 = res;
  return res3;
}

static size_t ser(cbor_raw x1_, Pulse_Lib_Slice_slice__uint8_t out, size_t offset)
{
  cbor_raw x2_ = x1_;
  size_t res = CBOR_Pulse_Raw_Format_Serialize_ser_(x2_, out, offset);
  size_t res0 = res;
  return res0;
}

static size_t cbor_serialize(cbor_raw x, Pulse_Lib_Slice_slice__uint8_t output)
{
  size_t res = ser(x, output, (size_t)0U);
  return res;
}

bool CBOR_Pulse_Raw_Format_Serialize_siz_(cbor_raw x_, size_t *out)
{
  header res0 = cbor_raw_with_perm_get_header(x_);
  header xh1 = res0;
  bool res1 = size_header(xh1, out);
  bool res3;
  if (res1)
  {
    initial_byte_t b0 = xh1.fst;
    bool res2;
    if
    (b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      cbor_raw _letpattern = x_;
      Pulse_Lib_Slice_slice__uint8_t s;
      if (_letpattern.tag == CBOR_Case_String)
      {
        cbor_string c_ = _letpattern.case_CBOR_Case_String;
        s = c_.cbor_string_ptr;
      }
      else
        s =
          KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
            "unreachable (pattern matches are exhaustive in F*)");
      Pulse_Lib_Slice_slice__uint8_t x2_ = s;
      size_t length = len__uint8_t(x2_);
      size_t cur = *out;
      bool res;
      if (cur < length)
        res = false;
      else
      {
        *out = cur - length;
        res = true;
      }
      bool res0 = res;
      bool res1 = res0;
      res2 = res1;
    }
    else
    {
      initial_byte_t b = xh1.fst;
      if (b.major_type == CBOR_MAJOR_TYPE_ARRAY)
      {
        bool ite;
        if (x_.tag == CBOR_Case_Array)
          ite = true;
        else
          ite = false;
        if (ite)
        {
          cbor_raw x2_ = x_;
          cbor_raw scrut0 = x2_;
          option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
          scrut;
          if (scrut0.tag == CBOR_Case_Array)
          {
            cbor_array a = scrut0.case_CBOR_Case_Array;
            scrut =
              (
                (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw){
                  .tag = Some,
                  .v = a.cbor_array_ptr
                }
              );
          }
          else
            scrut =
              (
                (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw){
                  .tag = None
                }
              );
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw a;
          if (scrut.tag == Some)
            a = scrut.v;
          else
            a =
              KRML_EABORT(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          bool pres = true;
          size_t pi = (size_t)0U;
          bool res = pres;
          size_t i0 = pi;
          bool cond = res && i0 < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
          while (cond)
          {
            size_t i0 = pi;
            cbor_raw e = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(a, i0);
            cbor_raw x2_1 = e;
            bool res = CBOR_Pulse_Raw_Format_Serialize_siz_(x2_1, out);
            bool res0 = res;
            bool res1 = res0;
            if (res1)
            {
              size_t i_ = i0 + (size_t)1U;
              pi = i_;
            }
            else
              pres = false;
            bool res2 = pres;
            size_t i = pi;
            cond = res2 && i < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
          }
          bool res0 = pres;
          bool res1 = res0;
          bool res3 = res1;
          res2 = res3;
        }
        else
        {
          cbor_raw _letpattern = x_;
          Pulse_Lib_Slice_slice__uint8_t x2_;
          if (_letpattern.tag == CBOR_Case_Serialized_Array)
          {
            cbor_serialized xs = _letpattern.case_CBOR_Case_Serialized_Array;
            x2_ = xs.cbor_serialized_payload;
          }
          else
            x2_ =
              KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
                "unreachable (pattern matches are exhaustive in F*)");
          size_t length = len__uint8_t(x2_);
          size_t cur = *out;
          bool res;
          if (cur < length)
            res = false;
          else
          {
            *out = cur - length;
            res = true;
          }
          bool res0 = res;
          bool res1 = res0;
          res2 = res1;
        }
      }
      else
      {
        initial_byte_t b = xh1.fst;
        if (b.major_type == CBOR_MAJOR_TYPE_MAP)
        {
          bool ite;
          if (x_.tag == CBOR_Case_Map)
            ite = true;
          else
            ite = false;
          if (ite)
          {
            cbor_raw x2_ = x_;
            cbor_raw scrut0 = x2_;
            option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
            scrut;
            if (scrut0.tag == CBOR_Case_Map)
            {
              cbor_map a = scrut0.case_CBOR_Case_Map;
              scrut =
                (
                  (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry){
                    .tag = Some,
                    .v = a.cbor_map_ptr
                  }
                );
            }
            else
              scrut =
                (
                  (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry){
                    .tag = None
                  }
                );
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a;
            if (scrut.tag == Some)
              a = scrut.v;
            else
              a =
                KRML_EABORT(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry,
                  "unreachable (pattern matches are exhaustive in F*)");
            bool pres = true;
            size_t pi = (size_t)0U;
            bool res0 = pres;
            size_t i0 = pi;
            bool cond = res0 && i0 < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
            while (cond)
            {
              size_t i0 = pi;
              cbor_map_entry e = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i0);
              cbor_raw x11 = e.cbor_map_entry_key;
              bool res0 = CBOR_Pulse_Raw_Format_Serialize_siz_(x11, out);
              bool res11 = res0;
              bool res;
              if (res11)
              {
                cbor_raw x2 = e.cbor_map_entry_value;
                bool res0 = CBOR_Pulse_Raw_Format_Serialize_siz_(x2, out);
                bool res2 = res0;
                res = res2;
              }
              else
                res = false;
              if (res)
              {
                size_t i_ = i0 + (size_t)1U;
                pi = i_;
              }
              else
                pres = false;
              bool res1 = pres;
              size_t i = pi;
              cond = res1 && i < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
            }
            bool res = pres;
            bool res1 = res;
            bool res3 = res1;
            res2 = res3;
          }
          else
          {
            cbor_raw _letpattern = x_;
            Pulse_Lib_Slice_slice__uint8_t x2_;
            if (_letpattern.tag == CBOR_Case_Serialized_Map)
            {
              cbor_serialized xs = _letpattern.case_CBOR_Case_Serialized_Map;
              x2_ = xs.cbor_serialized_payload;
            }
            else
              x2_ =
                KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
                  "unreachable (pattern matches are exhaustive in F*)");
            size_t length = len__uint8_t(x2_);
            size_t cur = *out;
            bool res;
            if (cur < length)
              res = false;
            else
            {
              *out = cur - length;
              res = true;
            }
            bool res0 = res;
            bool res1 = res0;
            res2 = res1;
          }
        }
        else
        {
          initial_byte_t b = xh1.fst;
          if (b.major_type == CBOR_MAJOR_TYPE_TAGGED)
          {
            bool ite;
            if (x_.tag == CBOR_Case_Tagged)
              ite = true;
            else
              ite = false;
            bool res0;
            if (ite)
            {
              cbor_raw _letpattern = x_;
              cbor_raw x2_;
              if (_letpattern.tag == CBOR_Case_Tagged)
              {
                cbor_tagged tg = _letpattern.case_CBOR_Case_Tagged;
                x2_ = *tg.cbor_tagged_ptr;
              }
              else
                x2_ = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
              bool res = CBOR_Pulse_Raw_Format_Serialize_siz_(x2_, out);
              bool res1 = res;
              bool res2 = res1;
              res0 = res2;
            }
            else
            {
              cbor_raw _letpattern = x_;
              Pulse_Lib_Slice_slice__uint8_t x2_;
              if (_letpattern.tag == CBOR_Case_Serialized_Tagged)
              {
                cbor_serialized ser1 = _letpattern.case_CBOR_Case_Serialized_Tagged;
                x2_ = ser1.cbor_serialized_payload;
              }
              else
                x2_ =
                  KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
                    "unreachable (pattern matches are exhaustive in F*)");
              size_t length = len__uint8_t(x2_);
              size_t cur = *out;
              bool res;
              if (cur < length)
                res = false;
              else
              {
                *out = cur - length;
                res = true;
              }
              bool res1 = res;
              res0 = res1;
            }
            res2 = res0;
          }
          else
            res2 = true;
        }
      }
    }
    res3 = res2;
  }
  else
    res3 = false;
  bool res = res3;
  return res;
}

static bool siz(cbor_raw x1_, size_t *out)
{
  cbor_raw x2_ = x1_;
  bool res = CBOR_Pulse_Raw_Format_Serialize_siz_(x2_, out);
  bool res0 = res;
  return res0;
}

static size_t cbor_size(cbor_raw x, size_t bound)
{
  size_t output = bound;
  bool res = siz(x, &output);
  if (res)
  {
    size_t rem = output;
    return bound - rem;
  }
  else
    return (size_t)0U;
}

static int16_t impl_uint8_compare(uint8_t x1, uint8_t x2)
{
  if (x1 < x2)
    return (int16_t)-1;
  else if (x1 > x2)
    return (int16_t)1;
  else
    return (int16_t)0;
}

static int16_t
lex_compare_bytes(Pulse_Lib_Slice_slice__uint8_t s1, Pulse_Lib_Slice_slice__uint8_t s2)
{
  Pulse_Lib_Slice_slice__uint8_t sp1 = s1;
  Pulse_Lib_Slice_slice__uint8_t sp2 = s2;
  size_t pi1 = (size_t)0U;
  size_t pi2 = (size_t)0U;
  size_t n1 = len__uint8_t(sp1);
  size_t n2 = len__uint8_t(sp2);
  int16_t ite;
  if ((size_t)0U < n1)
    if ((size_t)0U < n2)
      ite = (int16_t)0;
    else
      ite = (int16_t)1;
  else if ((size_t)0U < n2)
    ite = (int16_t)-1;
  else
    ite = (int16_t)0;
  int16_t pres = ite;
  int16_t res = pres;
  size_t i10 = pi1;
  bool cond = res == (int16_t)0 && i10 < n1;
  while (cond)
  {
    size_t i10 = pi1;
    uint8_t x1 = op_Array_Access__uint8_t(sp1, i10);
    size_t i2 = pi2;
    uint8_t x2 = op_Array_Access__uint8_t(sp2, i2);
    int16_t res = impl_uint8_compare(x1, x2);
    int16_t c = res;
    if (c == (int16_t)0)
    {
      size_t i1_ = i10 + (size_t)1U;
      size_t i2_ = i2 + (size_t)1U;
      bool ci1_ = i1_ < n1;
      bool ci2_ = i2_ < n2;
      if (ci2_ && !ci1_)
        pres = (int16_t)-1;
      else if (ci1_ && !ci2_)
        pres = (int16_t)1;
      else
      {
        pi1 = i1_;
        pi2 = i2_;
      }
    }
    else
      pres = c;
    int16_t res0 = pres;
    size_t i1 = pi1;
    cond = res0 == (int16_t)0 && i1 < n1;
  }
  int16_t res0 = pres;
  int16_t res1 = res0;
  return res1;
}

static size_t cbor_validate(Pulse_Lib_Slice_slice__uint8_t input)
{
  size_t poffset = (size_t)0U;
  bool is_valid = validate_raw_data_item(input, &poffset);
  if (is_valid)
    return poffset;
  else
    return (size_t)0U;
}

static bool impl_raw_uint64_optimal(CBOR_Spec_Raw_Base_raw_uint64 x)
{
  if (x.value <= (uint64_t)MAX_SIMPLE_VALUE_ADDITIONAL_INFO == (x.size == 0U))
    if (x.size <= 1U)
      return true;
    else if (x.size == 2U)
      return 256ULL <= x.value;
    else if (x.size == 3U)
      return 65536ULL <= x.value;
    else
      return 4294967296ULL <= x.value;
  else
    return false;
}

static bool cbor_raw_ints_optimal(Pulse_Lib_Slice_slice__uint8_t a)
{
  size_t i = jump_header(a, (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(a, i);
  Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = s.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s1, .snd = s2 };
  Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern.fst;
  Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern0 = { .fst = input10, .snd = input20 };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern0.fst;
  Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern0.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern1 = { .fst = input1, .snd = input2 };
  Pulse_Lib_Slice_slice__uint8_t input11 = _letpattern1.fst;
  header h = read_header(input11);
  if (get_header_major_type(h) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return true;
  else
  {
    long_argument scrut = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (scrut.tag == LongArgumentU8)
    {
      uint8_t v = scrut.case_LongArgumentU8;
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)v });
    }
    else if (scrut.tag == LongArgumentU16)
    {
      uint16_t v = scrut.case_LongArgumentU16;
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)v });
    }
    else if (scrut.tag == LongArgumentU32)
    {
      uint32_t v = scrut.case_LongArgumentU32;
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)v });
    }
    else if (scrut.tag == LongArgumentU64)
    {
      uint64_t v = scrut.case_LongArgumentU64;
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = v });
    }
    else if (scrut.tag == LongArgumentOther)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)h.fst.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return impl_raw_uint64_optimal(ite);
  }
}

static bool
impl_deterministically_encoded_cbor_map_key_order(
  Pulse_Lib_Slice_slice__uint8_t a1,
  Pulse_Lib_Slice_slice__uint8_t a2
)
{
  int16_t res = lex_compare_bytes(a1, a2);
  return res < (int16_t)0;
}

static bool cbor_raw_sorted(Pulse_Lib_Slice_slice__uint8_t a)
{
  size_t i0 = jump_header(a, (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(a, i0);
  Pulse_Lib_Slice_slice__uint8_t s10 = s.fst;
  Pulse_Lib_Slice_slice__uint8_t s20 = s.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s10, .snd = s20 };
  Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern.fst;
  Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern0 = { .fst = input10, .snd = input20 };
  Pulse_Lib_Slice_slice__uint8_t input12 = _letpattern0.fst;
  Pulse_Lib_Slice_slice__uint8_t input22 = _letpattern0.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern1 = { .fst = input12, .snd = input22 };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern1.fst;
  Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern1.snd;
  header h = read_header(input1);
  if (get_header_major_type(h) == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t nbpairs = argument_as_uint64(h.fst, h.snd);
    if (nbpairs < 2ULL)
      return true;
    else
    {
      initial_byte_t b0 = h.fst;
      size_t i0;
      if
      (b0.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
      {
        initial_byte_t b = h.fst;
        long_argument l = h.snd;
        i0 = (size_t)0U + (size_t)argument_as_uint64(b, l);
      }
      else
        i0 = (size_t)0U;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(input2, i0);
      Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
      Pulse_Lib_Slice_slice__uint8_t s20 = s.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern1 = { .fst = s1, .snd = s20 };
      Pulse_Lib_Slice_slice__uint8_t input110 = _letpattern1.fst;
      Pulse_Lib_Slice_slice__uint8_t input210 = _letpattern1.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern10 = { .fst = input110, .snd = input210 };
      Pulse_Lib_Slice_slice__uint8_t input111 = _letpattern10.fst;
      Pulse_Lib_Slice_slice__uint8_t input211 = _letpattern10.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern11 = { .fst = input111, .snd = input211 };
      Pulse_Lib_Slice_slice__uint8_t input3 = _letpattern11.snd;
      size_t i1 = jump_raw_data_item(input3, (size_t)0U);
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      s10 = split__uint8_t(input3, i1);
      Pulse_Lib_Slice_slice__uint8_t s110 = s10.fst;
      Pulse_Lib_Slice_slice__uint8_t s21 = s10.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern12 = { .fst = s110, .snd = s21 };
      Pulse_Lib_Slice_slice__uint8_t input112 = _letpattern12.fst;
      Pulse_Lib_Slice_slice__uint8_t input212 = _letpattern12.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern13 = { .fst = input112, .snd = input212 };
      Pulse_Lib_Slice_slice__uint8_t input113 = _letpattern13.fst;
      Pulse_Lib_Slice_slice__uint8_t input213 = _letpattern13.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern14 = { .fst = input113, .snd = input213 };
      Pulse_Lib_Slice_slice__uint8_t hd0 = _letpattern14.fst;
      Pulse_Lib_Slice_slice__uint8_t tl0 = _letpattern14.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern15 = { .fst = hd0, .snd = tl0 };
      Pulse_Lib_Slice_slice__uint8_t hd4 = _letpattern15.fst;
      Pulse_Lib_Slice_slice__uint8_t input4 = _letpattern15.snd;
      size_t i2 = jump_raw_data_item(input4, (size_t)0U);
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      s12 = split__uint8_t(input4, i2);
      Pulse_Lib_Slice_slice__uint8_t s111 = s12.fst;
      Pulse_Lib_Slice_slice__uint8_t s22 = s12.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = { .fst = s111, .snd = s22 };
      Pulse_Lib_Slice_slice__uint8_t input114 = _letpattern2.fst;
      Pulse_Lib_Slice_slice__uint8_t input214 = _letpattern2.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern20 = { .fst = input114, .snd = input214 };
      Pulse_Lib_Slice_slice__uint8_t input115 = _letpattern20.fst;
      Pulse_Lib_Slice_slice__uint8_t input215 = _letpattern20.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern21 = { .fst = input115, .snd = input215 };
      Pulse_Lib_Slice_slice__uint8_t hd1 = _letpattern21.fst;
      Pulse_Lib_Slice_slice__uint8_t tl1 = _letpattern21.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern22 = { .fst = hd1, .snd = tl1 };
      Pulse_Lib_Slice_slice__uint8_t input5 = _letpattern22.snd;
      Pulse_Lib_Slice_slice__uint8_t pkey = hd4;
      uint64_t pairs = nbpairs - 1ULL;
      uint64_t ppairs = pairs;
      Pulse_Lib_Slice_slice__uint8_t ptail = input5;
      bool pres = true;
      bool res = pres;
      uint64_t pairs10 = ppairs;
      bool cond = res && pairs10 > 0ULL;
      while (cond)
      {
        Pulse_Lib_Slice_slice__uint8_t tail = ptail;
        size_t i = jump_raw_data_item(tail, (size_t)0U);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s1 = split__uint8_t(tail, i);
        Pulse_Lib_Slice_slice__uint8_t s110 = s1.fst;
        Pulse_Lib_Slice_slice__uint8_t s20 = s1.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern2 = { .fst = s110, .snd = s20 };
        Pulse_Lib_Slice_slice__uint8_t input110 = _letpattern2.fst;
        Pulse_Lib_Slice_slice__uint8_t input210 = _letpattern2.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern20 = { .fst = input110, .snd = input210 };
        Pulse_Lib_Slice_slice__uint8_t input111 = _letpattern20.fst;
        Pulse_Lib_Slice_slice__uint8_t input211 = _letpattern20.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern21 = { .fst = input111, .snd = input211 };
        Pulse_Lib_Slice_slice__uint8_t hd0 = _letpattern21.fst;
        Pulse_Lib_Slice_slice__uint8_t tl0 = _letpattern21.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern22 = { .fst = hd0, .snd = tl0 };
        Pulse_Lib_Slice_slice__uint8_t key2 = _letpattern22.fst;
        Pulse_Lib_Slice_slice__uint8_t tail2 = _letpattern22.snd;
        Pulse_Lib_Slice_slice__uint8_t key1 = pkey;
        bool res = impl_deterministically_encoded_cbor_map_key_order(key1, key2);
        if (res)
        {
          size_t i = jump_raw_data_item(tail2, (size_t)0U);
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          s1 = split__uint8_t(tail2, i);
          Pulse_Lib_Slice_slice__uint8_t s11 = s1.fst;
          Pulse_Lib_Slice_slice__uint8_t s2 = s1.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern3 = { .fst = s11, .snd = s2 };
          Pulse_Lib_Slice_slice__uint8_t input110 = _letpattern3.fst;
          Pulse_Lib_Slice_slice__uint8_t input210 = _letpattern3.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern30 = { .fst = input110, .snd = input210 };
          Pulse_Lib_Slice_slice__uint8_t input11 = _letpattern30.fst;
          Pulse_Lib_Slice_slice__uint8_t input21 = _letpattern30.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern31 = { .fst = input11, .snd = input21 };
          Pulse_Lib_Slice_slice__uint8_t hd = _letpattern31.fst;
          Pulse_Lib_Slice_slice__uint8_t tl = _letpattern31.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern32 = { .fst = hd, .snd = tl };
          Pulse_Lib_Slice_slice__uint8_t tail_ = _letpattern32.snd;
          pkey = key2;
          uint64_t pairs1 = ppairs;
          uint64_t pairs_ = pairs1 - 1ULL;
          ppairs = pairs_;
          ptail = tail_;
        }
        else
          pres = false;
        bool res0 = pres;
        uint64_t pairs1 = ppairs;
        cond = res0 && pairs1 > 0ULL;
      }
      return pres;
    }
  }
  else
    return true;
}

static size_t cbor_validate_det_(Pulse_Lib_Slice_slice__uint8_t input)
{
  size_t len = cbor_validate(input);
  if (len == (size_t)0U)
    return len;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    s_ = split__uint8_t(input, (size_t)0U);
    Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s10, .snd = s20 };
    Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
    size_t consumed0 = len - (size_t)0U;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern1 = split__uint8_t(input23, consumed0);
    Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern1.fst;
    Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern1.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern10 = { .fst = s11, .snd = s21 };
    Pulse_Lib_Slice_slice__uint8_t left0 = _letpattern10.fst;
    Pulse_Lib_Slice_slice__uint8_t right0 = _letpattern10.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern11 = { .fst = left0, .snd = right0 };
    Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern11.fst;
    bool check = false;
    KRML_HOST_IGNORE(&check);
    size_t pn = (size_t)1U;
    bool pres0 = true;
    Pulse_Lib_Slice_slice__uint8_t ppi0 = input1;
    bool res0 = pres0;
    size_t n0 = pn;
    bool cond = res0 && n0 > (size_t)0U;
    while (cond)
    {
      size_t n0 = pn;
      Pulse_Lib_Slice_slice__uint8_t pi = ppi0;
      bool res = cbor_raw_ints_optimal(pi);
      if (!res)
        pres0 = false;
      else
      {
        size_t off1 = jump_header(pi, (size_t)0U);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        s_ = split__uint8_t(pi, (size_t)0U);
        Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
        Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern = { .fst = s10, .snd = s20 };
        Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
        size_t consumed = off1 - (size_t)0U;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern1 = split__uint8_t(input23, consumed);
        Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern1.fst;
        Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern1.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern10 = { .fst = s11, .snd = s21 };
        Pulse_Lib_Slice_slice__uint8_t left = _letpattern10.fst;
        Pulse_Lib_Slice_slice__uint8_t right = _letpattern10.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern11 = { .fst = left, .snd = right };
        Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern11.fst;
        header res1 = read_header(input_);
        header x = res1;
        initial_byte_t b0 = x.fst;
        size_t i;
        if
        (
          b0.major_type
          == CBOR_MAJOR_TYPE_BYTE_STRING
          || b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
        )
        {
          initial_byte_t b = x.fst;
          long_argument l = x.snd;
          i = off1 + (size_t)argument_as_uint64(b, l);
        }
        else
          i = off1 + (size_t)0U;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(pi, i);
        Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
        Pulse_Lib_Slice_slice__uint8_t s2 = s.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern0 = { .fst = s1, .snd = s2 };
        Pulse_Lib_Slice_slice__uint8_t input11 = _letpattern0.fst;
        Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern0.snd;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        _letpattern2 = { .fst = input11, .snd = input2 };
        Pulse_Lib_Slice_slice__uint8_t ph = _letpattern2.fst;
        Pulse_Lib_Slice_slice__uint8_t pc = _letpattern2.snd;
        size_t unused = len__uint8_t(pc);
        KRML_MAYBE_UNUSED_VAR(unused);
        size_t count = jump_recursive_step_count_leaf(ph);
        pn = n0 - (size_t)1U + count;
        ppi0 = pc;
      }
      bool res0 = pres0;
      size_t n = pn;
      cond = res0 && n > (size_t)0U;
    }
    bool res1 = pres0;
    bool check1 = res1;
    if (!check1)
      return (size_t)0U;
    else
    {
      size_t pn = (size_t)1U;
      bool pres = true;
      Pulse_Lib_Slice_slice__uint8_t ppi = input1;
      bool res0 = pres;
      size_t n0 = pn;
      bool cond = res0 && n0 > (size_t)0U;
      while (cond)
      {
        size_t n0 = pn;
        Pulse_Lib_Slice_slice__uint8_t pi = ppi;
        bool res = cbor_raw_sorted(pi);
        if (!res)
          pres = false;
        else
        {
          size_t off1 = jump_header(pi, (size_t)0U);
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          s_ = split__uint8_t(pi, (size_t)0U);
          Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
          Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern = { .fst = s10, .snd = s20 };
          Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
          size_t consumed = off1 - (size_t)0U;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern1 = split__uint8_t(input23, consumed);
          Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern1.fst;
          Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern1.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern10 = { .fst = s11, .snd = s21 };
          Pulse_Lib_Slice_slice__uint8_t left = _letpattern10.fst;
          Pulse_Lib_Slice_slice__uint8_t right = _letpattern10.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern11 = { .fst = left, .snd = right };
          Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern11.fst;
          header res1 = read_header(input_);
          header x = res1;
          initial_byte_t b0 = x.fst;
          size_t i;
          if
          (
            b0.major_type
            == CBOR_MAJOR_TYPE_BYTE_STRING
            || b0.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
          )
          {
            initial_byte_t b = x.fst;
            long_argument l = x.snd;
            i = off1 + (size_t)argument_as_uint64(b, l);
          }
          else
            i = off1 + (size_t)0U;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s = split__uint8_t(pi, i);
          Pulse_Lib_Slice_slice__uint8_t s1 = s.fst;
          Pulse_Lib_Slice_slice__uint8_t s2 = s.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern0 = { .fst = s1, .snd = s2 };
          Pulse_Lib_Slice_slice__uint8_t input11 = _letpattern0.fst;
          Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern0.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern2 = { .fst = input11, .snd = input2 };
          Pulse_Lib_Slice_slice__uint8_t ph = _letpattern2.fst;
          Pulse_Lib_Slice_slice__uint8_t pc = _letpattern2.snd;
          size_t unused = len__uint8_t(pc);
          KRML_MAYBE_UNUSED_VAR(unused);
          size_t count = jump_recursive_step_count_leaf(ph);
          pn = n0 - (size_t)1U + count;
          ppi = pc;
        }
        bool res0 = pres;
        size_t n = pn;
        cond = res0 && n > (size_t)0U;
      }
      bool res = pres;
      bool check2 = res;
      if (!check2)
        return (size_t)0U;
      else
        return len;
    }
  }
}

static size_t cbor_validate_det(Pulse_Lib_Slice_slice__uint8_t input)
{
  size_t res = cbor_validate_det_(input);
  return res;
}

static cbor_raw cbor_parse(Pulse_Lib_Slice_slice__uint8_t input, size_t len)
{
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  s_ = split__uint8_t(input, (size_t)0U);
  Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
  Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern = { .fst = s10, .snd = s20 };
  Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
  size_t consumed = len - (size_t)0U;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern1 = split__uint8_t(input23, consumed);
  Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern1.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern1.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern10 = { .fst = s1, .snd = s2 };
  Pulse_Lib_Slice_slice__uint8_t left = _letpattern10.fst;
  Pulse_Lib_Slice_slice__uint8_t right = _letpattern10.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  _letpattern11 = { .fst = left, .snd = right };
  Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern11.fst;
  cbor_raw res = cbor_read(input1);
  return res;
}

static int16_t cbor_match_compare_serialized_tagged(cbor_serialized c1, cbor_serialized c2)
{
  int16_t res = lex_compare_bytes(c1.cbor_serialized_payload, c2.cbor_serialized_payload);
  return res;
}

static int16_t cbor_match_compare_serialized_array(cbor_serialized c1, cbor_serialized c2)
{
  int16_t res = lex_compare_bytes(c1.cbor_serialized_payload, c2.cbor_serialized_payload);
  return res;
}

static int16_t cbor_match_compare_serialized_map(cbor_serialized c1, cbor_serialized c2)
{
  int16_t res = lex_compare_bytes(c1.cbor_serialized_payload, c2.cbor_serialized_payload);
  return res;
}

static uint8_t impl_major_type(cbor_raw x)
{
  if (x.tag == CBOR_Case_Simple)
    return CBOR_MAJOR_TYPE_SIMPLE_VALUE;
  else if (x.tag == CBOR_Case_Int)
  {
    cbor_raw _letpattern = x;
    if (_letpattern.tag == CBOR_Case_Int)
    {
      cbor_int c_ = _letpattern.case_CBOR_Case_Int;
      return c_.cbor_int_type;
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (x.tag == CBOR_Case_String)
  {
    cbor_raw _letpattern = x;
    if (_letpattern.tag == CBOR_Case_String)
    {
      cbor_string c_ = _letpattern.case_CBOR_Case_String;
      return c_.cbor_string_type;
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (x.tag == CBOR_Case_Tagged)
    return CBOR_MAJOR_TYPE_TAGGED;
  else if (x.tag == CBOR_Case_Serialized_Tagged)
    return CBOR_MAJOR_TYPE_TAGGED;
  else if (x.tag == CBOR_Case_Array)
    return CBOR_MAJOR_TYPE_ARRAY;
  else if (x.tag == CBOR_Case_Serialized_Array)
    return CBOR_MAJOR_TYPE_ARRAY;
  else if (x.tag == CBOR_Case_Map)
    return CBOR_MAJOR_TYPE_MAP;
  else if (x.tag == CBOR_Case_Serialized_Map)
    return CBOR_MAJOR_TYPE_MAP;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static int16_t uint64_compare(uint64_t x1, uint64_t x2)
{
  if (x1 < x2)
    return (int16_t)-1;
  else if (x1 > x2)
    return (int16_t)1;
  else
    return (int16_t)0;
}

static int16_t
impl_raw_uint64_compare(CBOR_Spec_Raw_Base_raw_uint64 x1, CBOR_Spec_Raw_Base_raw_uint64 x2)
{
  int16_t c = impl_uint8_compare(x1.size, x2.size);
  if (c == (int16_t)0)
    return uint64_compare(x1.value, x2.value);
  else
    return c;
}

typedef struct __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized_s
{
  cbor_serialized fst;
  cbor_serialized snd;
}
__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized;

typedef struct
option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized__s
{
  option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_tags
  tag;
  __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized v;
}
option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_;

static option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_
cbor_pair_is_serialized(cbor_raw c1, cbor_raw c2)
{
  if (c1.tag == CBOR_Case_Serialized_Tagged)
  {
    cbor_serialized s1 = c1.case_CBOR_Case_Serialized_Tagged;
    if (c2.tag == CBOR_Case_Serialized_Tagged)
    {
      cbor_serialized s2 = c2.case_CBOR_Case_Serialized_Tagged;
      return
        (
          (option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_){
            .tag = Some,
            .v = { .fst = s1, .snd = s2 }
          }
        );
    }
    else
      return
        (
          (option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_){
            .tag = None
          }
        );
  }
  else
    return
      (
        (option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_){
          .tag = None
        }
      );
}

static cbor_serialized
fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(
  __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized x
)
{
  return x.fst;
}

static cbor_serialized
snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(
  __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized x
)
{
  return x.snd;
}

int16_t CBOR_Pulse_Raw_Compare_impl_cbor_compare(cbor_raw x1, cbor_raw x2)
{
  uint8_t ty1 = impl_major_type(x1);
  uint8_t ty2 = impl_major_type(x2);
  int16_t c = impl_uint8_compare(ty1, ty2);
  if (c == (int16_t)0)
    if (ty1 == CBOR_MAJOR_TYPE_UINT64 || ty1 == CBOR_MAJOR_TYPE_NEG_INT64)
    {
      cbor_raw _letpattern0 = x1;
      CBOR_Spec_Raw_Base_raw_uint64 i1;
      if (_letpattern0.tag == CBOR_Case_Int)
      {
        cbor_int c_ = _letpattern0.case_CBOR_Case_Int;
        i1 =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
      }
      else
        i1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      cbor_raw _letpattern = x2;
      CBOR_Spec_Raw_Base_raw_uint64 i2;
      if (_letpattern.tag == CBOR_Case_Int)
      {
        cbor_int c_ = _letpattern.case_CBOR_Case_Int;
        i2 =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
      }
      else
        i2 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      return impl_raw_uint64_compare(i1, i2);
    }
    else if (ty1 == CBOR_MAJOR_TYPE_BYTE_STRING || ty1 == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      cbor_raw _letpattern0 = x1;
      CBOR_Spec_Raw_Base_raw_uint64 i1;
      if (_letpattern0.tag == CBOR_Case_String)
      {
        cbor_string c_ = _letpattern0.case_CBOR_Case_String;
        CBOR_Spec_Raw_Base_raw_uint64
        res = { .size = c_.cbor_string_size, .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr) };
        i1 = res;
      }
      else
        i1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      cbor_raw _letpattern1 = x2;
      CBOR_Spec_Raw_Base_raw_uint64 i2;
      if (_letpattern1.tag == CBOR_Case_String)
      {
        cbor_string c_ = _letpattern1.case_CBOR_Case_String;
        CBOR_Spec_Raw_Base_raw_uint64
        res = { .size = c_.cbor_string_size, .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr) };
        i2 = res;
      }
      else
        i2 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      int16_t c1 = impl_raw_uint64_compare(i1, i2);
      if (c1 == (int16_t)0)
      {
        cbor_raw _letpattern0 = x1;
        Pulse_Lib_Slice_slice__uint8_t pl1;
        if (_letpattern0.tag == CBOR_Case_String)
        {
          cbor_string c_ = _letpattern0.case_CBOR_Case_String;
          pl1 = c_.cbor_string_ptr;
        }
        else
          pl1 =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        cbor_raw _letpattern = x2;
        Pulse_Lib_Slice_slice__uint8_t pl2;
        if (_letpattern.tag == CBOR_Case_String)
        {
          cbor_string c_ = _letpattern.case_CBOR_Case_String;
          pl2 = c_.cbor_string_ptr;
        }
        else
          pl2 =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        int16_t res = lex_compare_bytes(pl1, pl2);
        return res;
      }
      else
        return c1;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_TAGGED)
    {
      CBOR_Spec_Raw_Base_raw_uint64 tag1;
      if (x1.tag == CBOR_Case_Tagged)
      {
        cbor_tagged c_ = x1.case_CBOR_Case_Tagged;
        tag1 = c_.cbor_tagged_tag;
      }
      else if (x1.tag == CBOR_Case_Serialized_Tagged)
      {
        cbor_serialized c_ = x1.case_CBOR_Case_Serialized_Tagged;
        tag1 = c_.cbor_serialized_header;
      }
      else
        tag1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 tag2;
      if (x2.tag == CBOR_Case_Tagged)
      {
        cbor_tagged c_ = x2.case_CBOR_Case_Tagged;
        tag2 = c_.cbor_tagged_tag;
      }
      else if (x2.tag == CBOR_Case_Serialized_Tagged)
      {
        cbor_serialized c_ = x2.case_CBOR_Case_Serialized_Tagged;
        tag2 = c_.cbor_serialized_header;
      }
      else
        tag2 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      int16_t c1 = impl_raw_uint64_compare(tag1, tag2);
      if (c1 == (int16_t)0)
      {
        option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_
        scrut = cbor_pair_is_serialized(x1, x2);
        if (scrut.tag == Some)
        {
          __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized pair = scrut.v;
          int16_t
          res =
            cbor_match_compare_serialized_tagged(fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair),
              snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair));
          return res;
        }
        else
        {
          cbor_raw pl1 = cbor_match_tagged_get_payload(x1);
          cbor_raw pl2 = cbor_match_tagged_get_payload(x2);
          int16_t res = CBOR_Pulse_Raw_Compare_impl_cbor_compare(pl1, pl2);
          return res;
        }
      }
      else
        return c1;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_ARRAY)
    {
      CBOR_Spec_Raw_Base_raw_uint64 len1;
      if (x1.tag == CBOR_Case_Array)
      {
        cbor_array c_ = x1.case_CBOR_Case_Array;
        len1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_array_length_size,
              .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
            }
          );
      }
      else if (x1.tag == CBOR_Case_Serialized_Array)
      {
        cbor_serialized c_ = x1.case_CBOR_Case_Serialized_Array;
        len1 = c_.cbor_serialized_header;
      }
      else
        len1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 len2;
      if (x2.tag == CBOR_Case_Array)
      {
        cbor_array c_ = x2.case_CBOR_Case_Array;
        len2 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_array_length_size,
              .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
            }
          );
      }
      else if (x2.tag == CBOR_Case_Serialized_Array)
      {
        cbor_serialized c_ = x2.case_CBOR_Case_Serialized_Array;
        len2 = c_.cbor_serialized_header;
      }
      else
        len2 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      int16_t c1 = impl_raw_uint64_compare(len1, len2);
      if (c1 == (int16_t)0)
      {
        option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_
        scrut = cbor_pair_is_serialized(x1, x2);
        if (scrut.tag == Some)
        {
          __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized pair = scrut.v;
          int16_t
          res =
            cbor_match_compare_serialized_array(fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair),
              snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair));
          return res;
        }
        else
        {
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
          i1 = cbor_array_iterator_init(x1);
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
          i2 = cbor_array_iterator_init(x2);
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw pl1 = i1;
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw pl2 = i2;
          bool fin1;
          if (pl1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
          {
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
            c_ = pl1.case_CBOR_Raw_Iterator_Slice;
            bool res = len__CBOR_Pulse_Raw_Type_cbor_raw(c_) == (size_t)0U;
            bool res0 = res;
            fin1 = res0;
          }
          else if (pl1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
          {
            CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
            c_ = pl1.case_CBOR_Raw_Iterator_Serialized;
            bool res = cbor_serialized_array_iterator_is_empty(c_);
            fin1 = res;
          }
          else
            fin1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          bool fin2;
          if (pl2.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
          {
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
            c_ = pl2.case_CBOR_Raw_Iterator_Slice;
            bool res = len__CBOR_Pulse_Raw_Type_cbor_raw(c_) == (size_t)0U;
            bool res0 = res;
            fin2 = res0;
          }
          else if (pl2.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
          {
            CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
            c_ = pl2.case_CBOR_Raw_Iterator_Serialized;
            bool res = cbor_serialized_array_iterator_is_empty(c_);
            fin2 = res;
          }
          else
            fin2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          int16_t res0;
          if (fin1)
            if (fin2)
              res0 = (int16_t)0;
            else
              res0 = (int16_t)-1;
          else if (fin2)
            res0 = (int16_t)1;
          else
          {
            CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw pi1 = pl1;
            CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw pi2 = pl2;
            int16_t pres = (int16_t)0;
            bool pfin1 = false;
            int16_t res1 = pres;
            bool fin110 = pfin1;
            bool cond = res1 == (int16_t)0 && !fin110;
            while (cond)
            {
              CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw i00 = pi1;
              cbor_raw elt1;
              if (i00.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
                i = i00.case_CBOR_Raw_Iterator_Slice;
                cbor_raw res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)0U);
                __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
                _letpattern = split__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)1U);
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s_ = _letpattern.snd;
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i11 = s_;
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i_ = i11;
                pi1 =
                  (
                    (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
                      .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
                      { .case_CBOR_Raw_Iterator_Slice = i_ }
                    }
                  );
                cbor_raw res0 = res;
                elt1 = res0;
              }
              else if (i00.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
              {
                CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
                i = i00.case_CBOR_Raw_Iterator_Serialized;
                cbor_raw res = cbor_serialized_array_iterator_next(&pi1, i);
                elt1 = res;
              }
              else
                elt1 = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
              CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw i0 = pi2;
              cbor_raw elt2;
              if (i0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
                i = i0.case_CBOR_Raw_Iterator_Slice;
                cbor_raw res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)0U);
                __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
                _letpattern = split__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)1U);
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw s_ = _letpattern.snd;
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i11 = s_;
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i_ = i11;
                pi2 =
                  (
                    (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
                      .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
                      { .case_CBOR_Raw_Iterator_Slice = i_ }
                    }
                  );
                cbor_raw res0 = res;
                elt2 = res0;
              }
              else if (i0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
              {
                CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
                i = i0.case_CBOR_Raw_Iterator_Serialized;
                cbor_raw res = cbor_serialized_array_iterator_next(&pi2, i);
                elt2 = res;
              }
              else
                elt2 = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
              cbor_raw pelt1 = elt1;
              cbor_raw pelt2 = elt2;
              int16_t res = CBOR_Pulse_Raw_Compare_impl_cbor_compare(pelt1, pelt2);
              int16_t c2 = res;
              if (c2 == (int16_t)0)
              {
                CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw i11 = pi1;
                bool fin11;
                if (i11.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
                {
                  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
                  c_ = i11.case_CBOR_Raw_Iterator_Slice;
                  bool res = len__CBOR_Pulse_Raw_Type_cbor_raw(c_) == (size_t)0U;
                  bool res0 = res;
                  fin11 = res0;
                }
                else if (i11.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                {
                  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
                  c_ = i11.case_CBOR_Raw_Iterator_Serialized;
                  bool res = cbor_serialized_array_iterator_is_empty(c_);
                  fin11 = res;
                }
                else
                  fin11 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw i21 = pi2;
                bool fin21;
                if (i21.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
                {
                  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
                  c_ = i21.case_CBOR_Raw_Iterator_Slice;
                  bool res = len__CBOR_Pulse_Raw_Type_cbor_raw(c_) == (size_t)0U;
                  bool res0 = res;
                  fin21 = res0;
                }
                else if (i21.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                {
                  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
                  c_ = i21.case_CBOR_Raw_Iterator_Serialized;
                  bool res = cbor_serialized_array_iterator_is_empty(c_);
                  fin21 = res;
                }
                else
                  fin21 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                if (fin11 == fin21)
                  pfin1 = fin11;
                else if (fin11)
                  pres = (int16_t)-1;
                else
                  pres = (int16_t)1;
              }
              else
                pres = c2;
              int16_t res0 = pres;
              bool fin11 = pfin1;
              cond = res0 == (int16_t)0 && !fin11;
            }
            res0 = pres;
          }
          int16_t res = res0;
          return res;
        }
      }
      else
        return c1;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_MAP)
    {
      CBOR_Spec_Raw_Base_raw_uint64 len1;
      if (x1.tag == CBOR_Case_Map)
      {
        cbor_map c_ = x1.case_CBOR_Case_Map;
        len1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_map_length_size,
              .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
            }
          );
      }
      else if (x1.tag == CBOR_Case_Serialized_Map)
      {
        cbor_serialized c_ = x1.case_CBOR_Case_Serialized_Map;
        len1 = c_.cbor_serialized_header;
      }
      else
        len1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 len2;
      if (x2.tag == CBOR_Case_Map)
      {
        cbor_map c_ = x2.case_CBOR_Case_Map;
        len2 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_map_length_size,
              .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
            }
          );
      }
      else if (x2.tag == CBOR_Case_Serialized_Map)
      {
        cbor_serialized c_ = x2.case_CBOR_Case_Serialized_Map;
        len2 = c_.cbor_serialized_header;
      }
      else
        len2 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      int16_t c1 = impl_raw_uint64_compare(len1, len2);
      if (c1 == (int16_t)0)
      {
        option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_
        scrut = cbor_pair_is_serialized(x1, x2);
        if (scrut.tag == Some)
        {
          __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized pair = scrut.v;
          int16_t
          res =
            cbor_match_compare_serialized_map(fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair),
              snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair));
          return res;
        }
        else
        {
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
          i1 = cbor_map_iterator_init(x1);
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
          i2 = cbor_map_iterator_init(x2);
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry pl1 = i1;
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry pl2 = i2;
          bool fin1;
          if (pl1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
          {
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
            c_ = pl1.case_CBOR_Raw_Iterator_Slice;
            bool res = len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_) == (size_t)0U;
            bool res0 = res;
            fin1 = res0;
          }
          else if (pl1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
          {
            CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
            c_ = pl1.case_CBOR_Raw_Iterator_Serialized;
            bool res = cbor_serialized_map_iterator_is_empty(c_);
            fin1 = res;
          }
          else
            fin1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          bool fin2;
          if (pl2.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
          {
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
            c_ = pl2.case_CBOR_Raw_Iterator_Slice;
            bool res = len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_) == (size_t)0U;
            bool res0 = res;
            fin2 = res0;
          }
          else if (pl2.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
          {
            CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
            c_ = pl2.case_CBOR_Raw_Iterator_Serialized;
            bool res = cbor_serialized_map_iterator_is_empty(c_);
            fin2 = res;
          }
          else
            fin2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          int16_t res0;
          if (fin1)
            if (fin2)
              res0 = (int16_t)0;
            else
              res0 = (int16_t)-1;
          else if (fin2)
            res0 = (int16_t)1;
          else
          {
            CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry pi1 = pl1;
            CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry pi2 = pl2;
            int16_t pres = (int16_t)0;
            bool pfin1 = false;
            int16_t res1 = pres;
            bool fin110 = pfin1;
            bool cond = res1 == (int16_t)0 && !fin110;
            while (cond)
            {
              CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
              i00 = pi1;
              cbor_map_entry elt1;
              if (i00.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
                i = i00.case_CBOR_Raw_Iterator_Slice;
                cbor_map_entry
                res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i, (size_t)0U);
                __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
                _letpattern = split__CBOR_Pulse_Raw_Type_cbor_map_entry(i, (size_t)1U);
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry s_ = _letpattern.snd;
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry i11 = s_;
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry i_ = i11;
                pi1 =
                  (
                    (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
                      .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
                      { .case_CBOR_Raw_Iterator_Slice = i_ }
                    }
                  );
                cbor_map_entry res0 = res;
                elt1 = res0;
              }
              else if (i00.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
              {
                CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
                i = i00.case_CBOR_Raw_Iterator_Serialized;
                cbor_map_entry res = cbor_serialized_map_iterator_next(&pi1, i);
                elt1 = res;
              }
              else
                elt1 =
                  KRML_EABORT(cbor_map_entry,
                    "unreachable (pattern matches are exhaustive in F*)");
              CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
              i0 = pi2;
              cbor_map_entry elt2;
              if (i0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
                i = i0.case_CBOR_Raw_Iterator_Slice;
                cbor_map_entry
                res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i, (size_t)0U);
                __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
                _letpattern = split__CBOR_Pulse_Raw_Type_cbor_map_entry(i, (size_t)1U);
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry s_ = _letpattern.snd;
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry i11 = s_;
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry i_ = i11;
                pi2 =
                  (
                    (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
                      .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
                      { .case_CBOR_Raw_Iterator_Slice = i_ }
                    }
                  );
                cbor_map_entry res0 = res;
                elt2 = res0;
              }
              else if (i0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
              {
                CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
                i = i0.case_CBOR_Raw_Iterator_Serialized;
                cbor_map_entry res = cbor_serialized_map_iterator_next(&pi2, i);
                elt2 = res;
              }
              else
                elt2 =
                  KRML_EABORT(cbor_map_entry,
                    "unreachable (pattern matches are exhaustive in F*)");
              cbor_map_entry pelt1 = elt1;
              cbor_map_entry pelt2 = elt2;
              int16_t
              c20 =
                CBOR_Pulse_Raw_Compare_impl_cbor_compare(pelt1.cbor_map_entry_key,
                  pelt2.cbor_map_entry_key);
              int16_t c2;
              if (c20 == (int16_t)0)
              {
                int16_t
                c3 =
                  CBOR_Pulse_Raw_Compare_impl_cbor_compare(pelt1.cbor_map_entry_value,
                    pelt2.cbor_map_entry_value);
                c2 = c3;
              }
              else
                c2 = c20;
              if (c2 == (int16_t)0)
              {
                CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                i11 = pi1;
                bool fin11;
                if (i11.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
                {
                  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
                  c_ = i11.case_CBOR_Raw_Iterator_Slice;
                  bool res = len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_) == (size_t)0U;
                  bool res0 = res;
                  fin11 = res0;
                }
                else if (i11.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                {
                  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
                  c_ = i11.case_CBOR_Raw_Iterator_Serialized;
                  bool res = cbor_serialized_map_iterator_is_empty(c_);
                  fin11 = res;
                }
                else
                  fin11 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                i21 = pi2;
                bool fin21;
                if (i21.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
                {
                  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
                  c_ = i21.case_CBOR_Raw_Iterator_Slice;
                  bool res = len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_) == (size_t)0U;
                  bool res0 = res;
                  fin21 = res0;
                }
                else if (i21.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                {
                  CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator
                  c_ = i21.case_CBOR_Raw_Iterator_Serialized;
                  bool res = cbor_serialized_map_iterator_is_empty(c_);
                  fin21 = res;
                }
                else
                  fin21 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                if (fin11 == fin21)
                  pfin1 = fin11;
                else if (fin11)
                  pres = (int16_t)-1;
                else
                  pres = (int16_t)1;
              }
              else
                pres = c2;
              int16_t res = pres;
              bool fin11 = pfin1;
              cond = res == (int16_t)0 && !fin11;
            }
            res0 = pres;
          }
          int16_t res = res0;
          return res;
        }
      }
      else
        return c1;
    }
    else
    {
      cbor_raw _letpattern0 = x1;
      uint8_t val1;
      if (_letpattern0.tag == CBOR_Case_Simple)
        val1 = _letpattern0.case_CBOR_Case_Simple;
      else
        val1 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      cbor_raw _letpattern = x2;
      uint8_t val2;
      if (_letpattern.tag == CBOR_Case_Simple)
        val2 = _letpattern.case_CBOR_Case_Simple;
      else
        val2 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      return impl_uint8_compare(val1, val2);
    }
  else
    return c;
}

void cbor_free_(cbor_freeable0 x)
{
  if (!(x.tag == CBOR_Copy_Unit))
    if (x.tag == CBOR_Copy_Bytes)
    {
      uint8_t *v = x.case_CBOR_Copy_Bytes;
      KRML_HOST_FREE(v);
    }
    else if (x.tag == CBOR_Copy_Box)
    {
      cbor_freeable_box b = x.case_CBOR_Copy_Box;
      KRML_HOST_FREE(b.box_cbor);
      cbor_freeable0 b_ = *b.box_footprint;
      cbor_free_(b_);
      KRML_HOST_FREE(b.box_footprint);
    }
    else if (x.tag == CBOR_Copy_Array)
    {
      cbor_freeable_array a = x.case_CBOR_Copy_Array;
      KRML_HOST_FREE(a.array_cbor);
      size_t len = a.array_len;
      size_t pi = (size_t)0U;
      size_t i0 = pi;
      bool cond = i0 < len;
      while (cond)
      {
        size_t i = pi;
        cbor_freeable0 x_ = a.array_footprint[i];
        cbor_free_(x_);
        pi = i + (size_t)1U;
        size_t i0 = pi;
        cond = i0 < len;
      }
      KRML_HOST_FREE(a.array_footprint);
    }
    else if (x.tag == CBOR_Copy_Map)
    {
      cbor_freeable_map a = x.case_CBOR_Copy_Map;
      KRML_HOST_FREE(a.map_cbor);
      size_t len = a.map_len;
      size_t pi = (size_t)0U;
      size_t i0 = pi;
      bool cond = i0 < len;
      while (cond)
      {
        size_t i = pi;
        cbor_freeable_map_entry x_ = a.map_footprint[i];
        cbor_free_(x_.map_entry_key);
        cbor_free_(x_.map_entry_value);
        pi = i + (size_t)1U;
        size_t i0 = pi;
        cond = i0 < len;
      }
      KRML_HOST_FREE(a.map_footprint);
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
}

static void cbor_free0(cbor_freeable x)
{
  cbor_free_(x.footprint);
}

static Pulse_Lib_Slice_slice__uint8_t from_array__uint8_t(uint8_t *a, size_t alen)
{
  uint8_t *ptr = a;
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = ptr, .len = alen });
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
from_array__CBOR_Pulse_Raw_Type_cbor_raw(cbor_raw *a, size_t alen)
{
  cbor_raw *ptr = a;
  return ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw){ .elt = ptr, .len = alen });
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(cbor_map_entry *a, size_t alen)
{
  cbor_map_entry *ptr = a;
  return
    ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry){ .elt = ptr, .len = alen });
}

typedef struct __CBOR_Pulse_Raw_Copy_cbor_freeable_CBOR_Pulse_Raw_Copy_cbor_freeable_s
{
  cbor_freeable fst;
  cbor_freeable snd;
}
__CBOR_Pulse_Raw_Copy_cbor_freeable_CBOR_Pulse_Raw_Copy_cbor_freeable;

cbor_freeable cbor_copy0(cbor_raw x)
{
  if (x.tag == CBOR_Case_Int)
  {
    cbor_raw _letpattern0 = x;
    uint8_t ty;
    if (_letpattern0.tag == CBOR_Case_Int)
    {
      cbor_int c_ = _letpattern0.case_CBOR_Case_Int;
      ty = c_.cbor_int_type;
    }
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    cbor_raw _letpattern = x;
    CBOR_Spec_Raw_Base_raw_uint64 w;
    if (_letpattern.tag == CBOR_Case_Int)
    {
      cbor_int c_ = _letpattern.case_CBOR_Case_Int;
      w = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
    }
    else
      w =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    cbor_int resi = { .cbor_int_type = ty, .cbor_int_size = w.size, .cbor_int_value = w.value };
    cbor_raw c_ = { .tag = CBOR_Case_Int, { .case_CBOR_Case_Int = resi } };
    return ((cbor_freeable){ .cbor = c_, .footprint = { .tag = CBOR_Copy_Unit } });
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    cbor_raw _letpattern = x;
    uint8_t w;
    if (_letpattern.tag == CBOR_Case_Simple)
      w = _letpattern.case_CBOR_Case_Simple;
    else
      w = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    cbor_raw c_ = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = w } };
    return ((cbor_freeable){ .cbor = c_, .footprint = { .tag = CBOR_Copy_Unit } });
  }
  else if (x.tag == CBOR_Case_String)
  {
    cbor_raw _letpattern0 = x;
    uint8_t ty;
    if (_letpattern0.tag == CBOR_Case_String)
    {
      cbor_string c_ = _letpattern0.case_CBOR_Case_String;
      ty = c_.cbor_string_type;
    }
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    cbor_raw _letpattern1 = x;
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (_letpattern1.tag == CBOR_Case_String)
    {
      cbor_string c_ = _letpattern1.case_CBOR_Case_String;
      CBOR_Spec_Raw_Base_raw_uint64
      res = { .size = c_.cbor_string_size, .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr) };
      len = res;
    }
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    cbor_raw _letpattern = x;
    Pulse_Lib_Slice_slice__uint8_t pl;
    if (_letpattern.tag == CBOR_Case_String)
    {
      cbor_string c_ = _letpattern.case_CBOR_Case_String;
      pl = c_.cbor_string_ptr;
    }
    else
      pl =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    size_t len_sz = len__uint8_t(pl);
    KRML_CHECK_SIZE(sizeof (uint8_t), len_sz);
    uint8_t *v_ = KRML_HOST_CALLOC(len_sz, sizeof (uint8_t));
    Pulse_Lib_Slice_slice__uint8_t s_ = from_array__uint8_t(v_, len_sz);
    copy__uint8_t(s_, pl);
    cbor_string
    ress = { .cbor_string_type = ty, .cbor_string_size = len.size, .cbor_string_ptr = s_ };
    cbor_raw c_ = { .tag = CBOR_Case_String, { .case_CBOR_Case_String = ress } };
    return
      (
        (cbor_freeable){
          .cbor = c_,
          .footprint = { .tag = CBOR_Copy_Bytes, { .case_CBOR_Copy_Bytes = v_ } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Tagged)
  {
    CBOR_Spec_Raw_Base_raw_uint64 tag;
    if (x.tag == CBOR_Case_Tagged)
    {
      cbor_tagged c_ = x.case_CBOR_Case_Tagged;
      tag = c_.cbor_tagged_tag;
    }
    else if (x.tag == CBOR_Case_Serialized_Tagged)
    {
      cbor_serialized c_ = x.case_CBOR_Case_Serialized_Tagged;
      tag = c_.cbor_serialized_header;
    }
    else
      tag =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    cbor_raw pl = cbor_match_tagged_get_payload(x);
    cbor_freeable cpl_ = cbor_copy0(pl);
    cbor_freeable0 *bf = KRML_HOST_MALLOC(sizeof (cbor_freeable0));
    if (bf != NULL)
      bf[0U] = cpl_.footprint;
    cbor_raw *b = KRML_HOST_MALLOC(sizeof (cbor_raw));
    if (b != NULL)
      b[0U] = cpl_.cbor;
    cbor_tagged res_ = { .cbor_tagged_tag = tag, .cbor_tagged_ptr = b };
    cbor_raw c_ = { .tag = CBOR_Case_Tagged, { .case_CBOR_Case_Tagged = res_ } };
    cbor_freeable_box fb = { .box_cbor = b, .box_footprint = bf };
    return
      (
        (cbor_freeable){
          .cbor = c_,
          .footprint = { .tag = CBOR_Copy_Box, { .case_CBOR_Copy_Box = fb } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Array)
  {
    cbor_array a = x.case_CBOR_Case_Array;
    CBOR_Spec_Raw_Base_raw_uint64
    len64 =
      {
        .size = a.cbor_array_length_size,
        .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(a.cbor_array_ptr)
      };
    cbor_array a1 = a;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw ar = a1.cbor_array_ptr;
    size_t len = len__CBOR_Pulse_Raw_Type_cbor_raw(ar);
    KRML_CHECK_SIZE(sizeof (cbor_raw), len);
    cbor_raw *v_ = KRML_HOST_MALLOC(sizeof (cbor_raw) * len);
    if (v_ != NULL)
      for (uint32_t _i = 0U; _i < len; ++_i)
        v_[_i] = ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } });
    KRML_CHECK_SIZE(sizeof (cbor_freeable0), len);
    cbor_freeable0 *vf = KRML_HOST_MALLOC(sizeof (cbor_freeable0) * len);
    if (vf != NULL)
      for (uint32_t _i = 0U; _i < len; ++_i)
        vf[_i] = ((cbor_freeable0){ .tag = CBOR_Copy_Unit });
    size_t pi = (size_t)0U;
    size_t i0 = pi;
    bool cond = i0 < len;
    while (cond)
    {
      size_t i = pi;
      cbor_raw c = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(ar, i);
      cbor_freeable c_ = cbor_copy0(c);
      v_[i] = c_.cbor;
      vf[i] = c_.footprint;
      pi = i + (size_t)1U;
      size_t i0 = pi;
      cond = i0 < len;
    }
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
    ar_ = from_array__CBOR_Pulse_Raw_Type_cbor_raw(v_, len);
    cbor_array res_ = { .cbor_array_length_size = len64.size, .cbor_array_ptr = ar_ };
    cbor_raw c_ = { .tag = CBOR_Case_Array, { .case_CBOR_Case_Array = res_ } };
    cbor_freeable_array fa = { .array_cbor = v_, .array_footprint = vf, .array_len = len };
    return
      (
        (cbor_freeable){
          .cbor = c_,
          .footprint = { .tag = CBOR_Copy_Array, { .case_CBOR_Copy_Array = fa } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Map)
  {
    cbor_map a = x.case_CBOR_Case_Map;
    CBOR_Spec_Raw_Base_raw_uint64
    len64 =
      {
        .size = a.cbor_map_length_size,
        .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(a.cbor_map_ptr)
      };
    cbor_map a1 = a;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry ar = a1.cbor_map_ptr;
    size_t len = len__CBOR_Pulse_Raw_Type_cbor_map_entry(ar);
    KRML_CHECK_SIZE(sizeof (cbor_map_entry), len);
    cbor_map_entry *v_ = KRML_HOST_MALLOC(sizeof (cbor_map_entry) * len);
    if (v_ != NULL)
      for (uint32_t _i = 0U; _i < len; ++_i)
        v_[_i]
        =
          (
            (cbor_map_entry){
              .cbor_map_entry_key = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } },
              .cbor_map_entry_value = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } }
            }
          );
    KRML_CHECK_SIZE(sizeof (cbor_freeable_map_entry), len);
    cbor_freeable_map_entry *vf = KRML_HOST_MALLOC(sizeof (cbor_freeable_map_entry) * len);
    if (vf != NULL)
      for (uint32_t _i = 0U; _i < len; ++_i)
        vf[_i]
        =
          (
            (cbor_freeable_map_entry){
              .map_entry_key = { .tag = CBOR_Copy_Unit },
              .map_entry_value = { .tag = CBOR_Copy_Unit }
            }
          );
    size_t pi = (size_t)0U;
    size_t i0 = pi;
    bool cond = i0 < len;
    while (cond)
    {
      size_t i = pi;
      cbor_map_entry c = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(ar, i);
      cbor_freeable key = cbor_copy0(c.cbor_map_entry_key);
      cbor_freeable value = cbor_copy0(c.cbor_map_entry_value);
      __CBOR_Pulse_Raw_Copy_cbor_freeable_CBOR_Pulse_Raw_Copy_cbor_freeable
      _letpattern = { .fst = key, .snd = value };
      cbor_freeable key_ = _letpattern.fst;
      cbor_freeable value_ = _letpattern.snd;
      cbor_map_entry
      cme_ = { .cbor_map_entry_key = key_.cbor, .cbor_map_entry_value = value_.cbor };
      v_[i] = cme_;
      cbor_freeable_map_entry
      cfp_ = { .map_entry_key = key_.footprint, .map_entry_value = value_.footprint };
      vf[i] = cfp_;
      pi = i + (size_t)1U;
      size_t i0 = pi;
      cond = i0 < len;
    }
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
    ar_ = from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(v_, len);
    cbor_map res_ = { .cbor_map_length_size = len64.size, .cbor_map_ptr = ar_ };
    cbor_raw c_ = { .tag = CBOR_Case_Map, { .case_CBOR_Case_Map = res_ } };
    cbor_freeable_map fa = { .map_cbor = v_, .map_footprint = vf, .map_len = len };
    return
      (
        (cbor_freeable){
          .cbor = c_,
          .footprint = { .tag = CBOR_Copy_Map, { .case_CBOR_Copy_Map = fa } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Array)
  {
    cbor_serialized a = x.case_CBOR_Case_Serialized_Array;
    size_t len = len__uint8_t(a.cbor_serialized_payload);
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t *v_ = KRML_HOST_CALLOC(len, sizeof (uint8_t));
    Pulse_Lib_Slice_slice__uint8_t s_ = from_array__uint8_t(v_, len);
    cbor_match_serialized_payload_array_copy(a.cbor_serialized_payload, s_);
    cbor_serialized
    a_ = { .cbor_serialized_header = a.cbor_serialized_header, .cbor_serialized_payload = s_ };
    return
      (
        (cbor_freeable){
          .cbor = { .tag = CBOR_Case_Serialized_Array, { .case_CBOR_Case_Serialized_Array = a_ } },
          .footprint = { .tag = CBOR_Copy_Bytes, { .case_CBOR_Copy_Bytes = v_ } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Map)
  {
    cbor_serialized a = x.case_CBOR_Case_Serialized_Map;
    size_t len = len__uint8_t(a.cbor_serialized_payload);
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t *v_ = KRML_HOST_CALLOC(len, sizeof (uint8_t));
    Pulse_Lib_Slice_slice__uint8_t s_ = from_array__uint8_t(v_, len);
    cbor_match_serialized_payload_map_copy(a.cbor_serialized_payload, s_);
    cbor_serialized
    a_ = { .cbor_serialized_header = a.cbor_serialized_header, .cbor_serialized_payload = s_ };
    return
      (
        (cbor_freeable){
          .cbor = { .tag = CBOR_Case_Serialized_Map, { .case_CBOR_Case_Serialized_Map = a_ } },
          .footprint = { .tag = CBOR_Copy_Bytes, { .case_CBOR_Copy_Bytes = v_ } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Tagged)
  {
    cbor_serialized a = x.case_CBOR_Case_Serialized_Tagged;
    size_t len = len__uint8_t(a.cbor_serialized_payload);
    KRML_CHECK_SIZE(sizeof (uint8_t), len);
    uint8_t *v_ = KRML_HOST_CALLOC(len, sizeof (uint8_t));
    Pulse_Lib_Slice_slice__uint8_t s_ = from_array__uint8_t(v_, len);
    cbor_match_serialized_payload_tagged_copy(a.cbor_serialized_payload, s_);
    cbor_serialized
    a_ = { .cbor_serialized_header = a.cbor_serialized_header, .cbor_serialized_payload = s_ };
    return
      (
        (cbor_freeable){
          .cbor = { .tag = CBOR_Case_Serialized_Tagged, { .case_CBOR_Case_Serialized_Tagged = a_ } },
          .footprint = { .tag = CBOR_Copy_Bytes, { .case_CBOR_Copy_Bytes = v_ } }
        }
      );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

typedef cbor_raw cbor_det_t;

typedef cbor_map_entry cbor_det_map_entry_t;

typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_t;

typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
cbor_det_map_iterator_t;

cbor_raw cbor_det_reset_perm(cbor_raw x1)
{
  cbor_raw res = cbor_raw_reset_perm_tot(x1);
  return res;
}

size_t cbor_det_size(cbor_raw x, size_t bound)
{
  size_t res = cbor_size(x, bound);
  return res;
}

cbor_raw cbor_det_mk_simple_value(uint8_t v)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = v } });
}

cbor_raw cbor_det_mk_int64(uint8_t ty, uint64_t v)
{
  cbor_int
  res =
    {
      .cbor_int_type = ty,
      .cbor_int_size = mk_raw_uint64(v).size,
      .cbor_int_value = mk_raw_uint64(v).value
    };
  cbor_int resi = res;
  cbor_raw res0 = { .tag = CBOR_Case_Int, { .case_CBOR_Case_Int = resi } };
  return res0;
}

cbor_raw cbor_det_mk_tagged(uint64_t tag, cbor_raw *r)
{
  CBOR_Spec_Raw_Base_raw_uint64 tag64 = mk_raw_uint64(tag);
  cbor_tagged res_ = { .cbor_tagged_tag = tag64, .cbor_tagged_ptr = r };
  return ((cbor_raw){ .tag = CBOR_Case_Tagged, { .case_CBOR_Case_Tagged = res_ } });
}

static int16_t cbor_raw_compare(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Compare_impl_cbor_compare(x1, x2);
}

static int16_t cbor_map_entry_raw_compare(cbor_map_entry x1, cbor_map_entry x2)
{
  int16_t res = cbor_raw_compare(x1.cbor_map_entry_key, x2.cbor_map_entry_key);
  return res;
}

static void
op_Array_Assignment__CBOR_Pulse_Raw_Type_cbor_map_entry(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a,
  size_t i,
  cbor_map_entry v
)
{
  a.elt[i] = v;
}

bool cbor_raw_sort_aux(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a)
{
  size_t len = len__CBOR_Pulse_Raw_Type_cbor_map_entry(a);
  if (len < (size_t)2U)
    return true;
  else
  {
    size_t len_half = len / (size_t)2U;
    size_t mi = len_half;
    __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
    _letpattern = split__CBOR_Pulse_Raw_Type_cbor_map_entry(a, mi);
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a1 = _letpattern.fst;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a2 = _letpattern.snd;
    bool res = cbor_raw_sort_aux(a1);
    if (!res)
      return false;
    else
    {
      bool res1 = cbor_raw_sort_aux(a2);
      if (!res1)
        return false;
      else
      {
        size_t pi1 = (size_t)0U;
        size_t pi2 = mi;
        bool pres = true;
        size_t i10 = pi1;
        size_t i20 = pi2;
        bool res20 = pres;
        bool cont = res20 && !(i10 == i20 || i20 == len__CBOR_Pulse_Raw_Type_cbor_map_entry(a));
        bool cond = cont;
        while (cond)
        {
          size_t i1 = pi1;
          cbor_map_entry x1 = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i1);
          size_t i20 = pi2;
          cbor_map_entry x2 = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i20);
          int16_t comp = cbor_map_entry_raw_compare(x1, x2);
          if (comp == (int16_t)0)
            pres = false;
          else if (comp < (int16_t)0)
          {
            size_t i1_ = i1 + (size_t)1U;
            pi1 = i1_;
          }
          else
          {
            size_t i2_ = i20 + (size_t)1U;
            __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
            _letpattern1 = split__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i2_);
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry ac01 = _letpattern1.fst;
            __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
            _letpattern2 = split__CBOR_Pulse_Raw_Type_cbor_map_entry(ac01, i1);
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry ac1 = _letpattern2.snd;
            if
            (!(i20 - i1 == (size_t)0U || i20 - i1 == len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1)))
            {
              size_t pn = len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1);
              size_t pl = i20 - i1;
              size_t l30 = pl;
              bool cond = l30 > (size_t)0U;
              while (cond)
              {
                size_t n = pn;
                size_t l3 = pl;
                size_t l_ = n % l3;
                pn = l3;
                pl = l_;
                size_t l30 = pl;
                cond = l30 > (size_t)0U;
              }
              size_t d = pn;
              size_t q = len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1) / d;
              size_t pi = (size_t)0U;
              size_t i0 = pi;
              bool cond0 = i0 < d;
              while (cond0)
              {
                size_t i = pi;
                cbor_map_entry save = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1, i);
                size_t pj = (size_t)0U;
                size_t pidx = i;
                size_t j0 = pj;
                bool cond = j0 < q - (size_t)1U;
                while (cond)
                {
                  size_t j = pj;
                  size_t idx = pidx;
                  size_t idx_;
                  if (idx - (size_t)0U >= len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1) - (i20 - i1))
                    idx_ = idx - (len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1) - (i20 - i1));
                  else
                    idx_ = idx + i20 - i1 - (size_t)0U;
                  cbor_map_entry x = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1, idx_);
                  size_t j_ = j + (size_t)1U;
                  op_Array_Assignment__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1, idx, x);
                  pj = j_;
                  pidx = idx_;
                  size_t j0 = pj;
                  cond = j0 < q - (size_t)1U;
                }
                size_t idx = pidx;
                op_Array_Assignment__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1, idx, save);
                size_t i_ = i + (size_t)1U;
                pi = i_;
                size_t i0 = pi;
                cond0 = i0 < d;
              }
            }
            size_t i1_ = i1 + (size_t)1U;
            pi1 = i1_;
            pi2 = i2_;
          }
          size_t i10 = pi1;
          size_t i2 = pi2;
          bool res2 = pres;
          bool cont = res2 && !(i10 == i2 || i2 == len__CBOR_Pulse_Raw_Type_cbor_map_entry(a));
          cond = cont;
        }
        bool res2 = pres;
        return res2;
      }
    }
  }
}

static bool cbor_raw_sort(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a)
{
  bool res = cbor_raw_sort_aux(a);
  return res;
}

cbor_map_entry cbor_det_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  cbor_map_entry res = cbor_mk_map_entry(xk, xv);
  return res;
}

bool cbor_det_equal(cbor_raw x1, cbor_raw x2)
{
  int16_t comp = CBOR_Pulse_Raw_Compare_impl_cbor_compare(x1, x2);
  return comp == (int16_t)0;
}

uint8_t cbor_det_major_type(cbor_raw x)
{
  uint8_t res = impl_major_type(x);
  return res;
}

uint8_t cbor_det_read_simple_value(cbor_raw x)
{
  cbor_raw _letpattern = x;
  if (_letpattern.tag == CBOR_Case_Simple)
    return _letpattern.case_CBOR_Case_Simple;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint64_t cbor_det_read_uint64(cbor_raw x)
{
  cbor_raw _letpattern = x;
  CBOR_Spec_Raw_Base_raw_uint64 res;
  if (_letpattern.tag == CBOR_Case_Int)
  {
    cbor_int c_ = _letpattern.case_CBOR_Case_Int;
    res = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
  }
  else
    res =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return res.value;
}

uint64_t cbor_det_get_string_length(cbor_raw x)
{
  cbor_raw _letpattern = x;
  CBOR_Spec_Raw_Base_raw_uint64 res;
  if (_letpattern.tag == CBOR_Case_String)
  {
    cbor_string c_ = _letpattern.case_CBOR_Case_String;
    CBOR_Spec_Raw_Base_raw_uint64
    res0 = { .size = c_.cbor_string_size, .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr) };
    res = res0;
  }
  else
    res =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return res.value;
}

uint64_t cbor_det_get_tagged_tag(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 res;
  if (x.tag == CBOR_Case_Tagged)
  {
    cbor_tagged c_ = x.case_CBOR_Case_Tagged;
    res = c_.cbor_tagged_tag;
  }
  else if (x.tag == CBOR_Case_Serialized_Tagged)
  {
    cbor_serialized c_ = x.case_CBOR_Case_Serialized_Tagged;
    res = c_.cbor_serialized_header;
  }
  else
    res =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return res.value;
}

cbor_raw cbor_det_get_tagged_payload(cbor_raw x)
{
  cbor_raw res = cbor_match_tagged_get_payload(x);
  return res;
}

uint64_t cbor_det_get_array_length(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 res;
  if (x.tag == CBOR_Case_Array)
  {
    cbor_array c_ = x.case_CBOR_Case_Array;
    res =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = c_.cbor_array_length_size,
          .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Array)
  {
    cbor_serialized c_ = x.case_CBOR_Case_Serialized_Array;
    res = c_.cbor_serialized_header;
  }
  else
    res =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return res.value;
}

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_start(cbor_raw x)
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
  res = cbor_array_iterator_init(x);
  return res;
}

bool
cbor_det_array_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x
)
{
  bool res = cbor_array_iterator_is_empty(x);
  return res;
}

uint64_t
cbor_det_array_iterator_length(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x
)
{
  uint64_t res = cbor_array_iterator_length(x);
  return res;
}

cbor_raw
cbor_det_array_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw *x
)
{
  cbor_raw res = cbor_array_iterator_next(x);
  return res;
}

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_truncate(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x,
  uint64_t len
)
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
  res = cbor_array_iterator_truncate(x, len);
  return res;
}

cbor_raw cbor_det_get_array_item(cbor_raw x, uint64_t i)
{
  cbor_raw res = cbor_array_item(x, i);
  return res;
}

uint64_t cbor_det_get_map_length(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 res;
  if (x.tag == CBOR_Case_Map)
  {
    cbor_map c_ = x.case_CBOR_Case_Map;
    res =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = c_.cbor_map_length_size,
          .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Map)
  {
    cbor_serialized c_ = x.case_CBOR_Case_Serialized_Map;
    res = c_.cbor_serialized_header;
  }
  else
    res =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return res.value;
}

static int16_t impl_cbor_det_compare(cbor_raw x1, cbor_raw x2)
{
  int16_t res = CBOR_Pulse_Raw_Compare_impl_cbor_compare(x1, x2);
  return res;
}

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
cbor_det_map_iterator_start(cbor_raw x)
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
  res = cbor_map_iterator_init(x);
  return res;
}

bool
cbor_det_map_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry x
)
{
  bool res = cbor_map_iterator_is_empty(x);
  return res;
}

cbor_map_entry
cbor_det_map_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry *x
)
{
  cbor_map_entry res = cbor_map_iterator_next(x);
  return res;
}

cbor_raw cbor_det_map_entry_key(cbor_map_entry x2)
{
  return x2.cbor_map_entry_key;
}

cbor_raw cbor_det_map_entry_value(cbor_map_entry x2)
{
  return x2.cbor_map_entry_value;
}

static Pulse_Lib_Slice_slice__uint8_t arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

size_t cbor_det_validate(uint8_t *input, size_t input_len)
{
  Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(input, input_len);
  Pulse_Lib_Slice_slice__uint8_t s0 = s;
  size_t res = cbor_validate_det(s0);
  size_t res0 = res;
  return res0;
}

cbor_raw cbor_det_parse(uint8_t *input, size_t len)
{
  Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(input, len);
  Pulse_Lib_Slice_slice__uint8_t s0 = s;
  size_t len1 = len__uint8_t(s0);
  cbor_raw res = cbor_parse(s0, len1);
  cbor_raw res0 = res;
  return res0;
}

size_t cbor_det_serialize(cbor_raw x, uint8_t *output, size_t output_len)
{
  Pulse_Lib_Slice_slice__uint8_t ou = arrayptr_to_slice_intro__uint8_t(output, output_len);
  size_t res = cbor_serialize(x, ou);
  size_t res0 = res;
  return res0;
}

cbor_raw cbor_det_mk_string_from_array(uint8_t ty, uint8_t *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__uint8_t s = from_array__uint8_t(a, (size_t)len);
  CBOR_Spec_Raw_Base_raw_uint64 len64 = mk_raw_uint64((uint64_t)len__uint8_t(s));
  cbor_string
  ress = { .cbor_string_type = ty, .cbor_string_size = len64.size, .cbor_string_ptr = s };
  cbor_raw res = { .tag = CBOR_Case_String, { .case_CBOR_Case_String = ress } };
  return res;
}

cbor_raw cbor_det_mk_array_from_array(cbor_raw *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
  s = from_array__CBOR_Pulse_Raw_Type_cbor_raw(a, (size_t)len);
  CBOR_Spec_Raw_Base_raw_uint64
  len64 = mk_raw_uint64((uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(s));
  cbor_array res_ = { .cbor_array_length_size = len64.size, .cbor_array_ptr = s };
  cbor_raw res = { .tag = CBOR_Case_Array, { .case_CBOR_Case_Array = res_ } };
  return res;
}

cbor_raw cbor_det_mk_map_from_array(cbor_map_entry *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
  s = from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(a, (size_t)len);
  cbor_raw dest = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } };
  bool ite;
  if (len__CBOR_Pulse_Raw_Type_cbor_map_entry(s) > (size_t)18446744073709551615ULL)
    ite = false;
  else
  {
    bool correct = cbor_raw_sort(s);
    if (correct)
    {
      CBOR_Spec_Raw_Base_raw_uint64
      raw_len = mk_raw_uint64((uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(s));
      cbor_map res_ = { .cbor_map_length_size = raw_len.size, .cbor_map_ptr = s };
      cbor_raw res = { .tag = CBOR_Case_Map, { .case_CBOR_Case_Map = res_ } };
      dest = res;
      ite = true;
    }
    else
      ite = false;
  }
  KRML_MAYBE_UNUSED_VAR(ite);
  cbor_raw res = dest;
  return res;
}

static uint8_t *slice_to_arrayptr_intro__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.elt;
}

uint8_t *cbor_det_get_string(cbor_raw x)
{
  cbor_raw _letpattern = x;
  Pulse_Lib_Slice_slice__uint8_t sl;
  if (_letpattern.tag == CBOR_Case_String)
  {
    cbor_string c_ = _letpattern.case_CBOR_Case_String;
    sl = c_.cbor_string_ptr;
  }
  else
    sl =
      KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
        "unreachable (pattern matches are exhaustive in F*)");
  uint8_t *a = slice_to_arrayptr_intro__uint8_t(sl);
  uint8_t *res = a;
  return res;
}

typedef struct option__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_tags
  tag;
  cbor_raw v;
}
option__CBOR_Pulse_Raw_Type_cbor_raw;

bool cbor_det_map_get(cbor_raw x, cbor_raw k, cbor_raw *dest)
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
  res = cbor_map_iterator_init(x);
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry i = res;
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry pi = i;
  option__CBOR_Pulse_Raw_Type_cbor_raw pres = { .tag = None };
  bool i_is_empty = cbor_det_map_iterator_is_empty(i);
  bool cont = !i_is_empty;
  bool pcont = cont;
  while (pcont)
  {
    cbor_map_entry entry = cbor_det_map_iterator_next(&pi);
    cbor_raw key = cbor_det_map_entry_key(entry);
    int16_t comp = impl_cbor_det_compare(key, k);
    if (comp == (int16_t)0)
    {
      cbor_raw value = cbor_det_map_entry_value(entry);
      pres = ((option__CBOR_Pulse_Raw_Type_cbor_raw){ .tag = Some, .v = value });
      pcont = false;
    }
    else if (comp > (int16_t)0)
      pcont = false;
    else
    {
      CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry i_ = pi;
      bool is_empty = cbor_det_map_iterator_is_empty(i_);
      bool cont1 = !is_empty;
      pcont = cont1;
    }
  }
  option__CBOR_Pulse_Raw_Type_cbor_raw res0 = pres;
  if (res0.tag == None)
    return false;
  else if (res0.tag == Some)
  {
    cbor_raw vres = res0.v;
    *dest = vres;
    return true;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

typedef cbor_freeable cbor_det_freeable_t;

cbor_raw cbor_get_from_freeable(cbor_freeable x)
{
  return x.cbor;
}

cbor_freeable cbor_copy(cbor_raw c)
{
  cbor_freeable res = cbor_copy0(c);
  return res;
}

void cbor_free(cbor_freeable x)
{
  cbor_free0(x);
}

