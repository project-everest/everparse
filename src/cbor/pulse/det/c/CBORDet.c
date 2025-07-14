

#include "internal/CBORDet.h"

static uint8_t get_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi)
{
  return ((uint32_t)x << 8U - hi & 0xFFU) >> 8U - hi + lo;
}

static uint8_t set_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi, uint8_t v)
{
  return (uint32_t)x & (uint32_t)~(255U >> 8U - (hi - lo) << lo) | (uint32_t)v << lo;
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
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)x.case_LongArgumentU8 });
  else if (x.tag == LongArgumentU16)
    ite =
      ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)x.case_LongArgumentU16 });
  else if (x.tag == LongArgumentU32)
    ite =
      ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)x.case_LongArgumentU32 });
  else if (x.tag == LongArgumentU64)
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = x.case_LongArgumentU64 });
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
  return h.fst.major_type;
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
  bool cond;
  if (pres)
    cond = pi < len;
  else
    cond = false;
  while (cond)
  {
    size_t i = pi;
    uint8_t byte1 = op_Array_Access__uint8_t(s, i);
    size_t i1 = i + (size_t)1U;
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
    bool ite;
    if (pres)
      ite = pi < len;
    else
      ite = false;
    cond = ite;
  }
  return pres;
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
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_String,
          { .case_CBOR_Case_String = cbor_string_reset_perm(c.case_CBOR_Case_String) }
        }
      );
  else if (c.tag == CBOR_Case_Tagged)
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Tagged,
          { .case_CBOR_Case_Tagged = cbor_tagged_reset_perm(c.case_CBOR_Case_Tagged) }
        }
      );
  else if (c.tag == CBOR_Case_Array)
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Array,
          { .case_CBOR_Case_Array = cbor_array_reset_perm(c.case_CBOR_Case_Array) }
        }
      );
  else if (c.tag == CBOR_Case_Map)
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Map,
          { .case_CBOR_Case_Map = cbor_map_reset_perm(c.case_CBOR_Case_Map) }
        }
      );
  else if (c.tag == CBOR_Case_Serialized_Tagged)
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Tagged,
          {
            .case_CBOR_Case_Serialized_Tagged = cbor_serialized_reset_perm(c.case_CBOR_Case_Serialized_Tagged)
          }
        }
      );
  else if (c.tag == CBOR_Case_Serialized_Array)
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Array,
          {
            .case_CBOR_Case_Serialized_Array = cbor_serialized_reset_perm(c.case_CBOR_Case_Serialized_Array)
          }
        }
      );
  else if (c.tag == CBOR_Case_Serialized_Map)
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Map,
          {
            .case_CBOR_Case_Serialized_Map = cbor_serialized_reset_perm(c.case_CBOR_Case_Serialized_Map)
          }
        }
      );
  else
    return c;
}

static cbor_map_entry cbor_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  return
    (
      (cbor_map_entry){
        .cbor_map_entry_key = cbor_raw_reset_perm_tot(xk),
        .cbor_map_entry_value = cbor_raw_reset_perm_tot(xv)
      }
    );
}

static CBOR_Spec_Raw_Base_raw_uint64 mk_raw_uint64(uint64_t x)
{
  uint8_t ite;
  if (x <= (uint64_t)MAX_SIMPLE_VALUE_ADDITIONAL_INFO)
    ite = 0U;
  else if (x < 256ULL)
    ite = 1U;
  else if (x < 65536ULL)
    ite = 2U;
  else if (x < 4294967296ULL)
    ite = 3U;
  else
    ite = 4U;
  return ((CBOR_Spec_Raw_Base_raw_uint64){ .size = ite, .value = x });
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
  while (pres == (int16_t)0 && pi1 < n1)
  {
    size_t i1 = pi1;
    uint8_t x1 = op_Array_Access__uint8_t(sp1, i1);
    size_t i2 = pi2;
    int16_t c = impl_uint8_compare(x1, op_Array_Access__uint8_t(sp2, i2));
    if (c == (int16_t)0)
    {
      size_t i1_ = i1 + (size_t)1U;
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
  }
  return pres;
}

static initial_byte_t read_initial_byte_t(Pulse_Lib_Slice_slice__uint8_t input)
{
  uint8_t x = op_Array_Access__uint8_t(input, (size_t)0U);
  return
    (
      (initial_byte_t){
        .major_type = get_bitfield_gen8(x, 5U, 8U),
        .additional_info = get_bitfield_gen8(x, 0U, 5U)
      }
    );
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
  return
    (
      (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static header read_header(Pulse_Lib_Slice_slice__uint8_t input)
{
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut = split__uint8_t(input, (size_t)1U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.snd;
  initial_byte_t x1 = read_initial_byte_t(scrut1.fst);
  long_argument ite;
  if (x1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    if (x1.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      ite =
        (
          (long_argument){
            .tag = LongArgumentSimpleValue,
            { .case_LongArgumentSimpleValue = op_Array_Access__uint8_t(input2, (size_t)0U) }
          }
        );
    else
      ite =
        (
          (long_argument){
            .tag = LongArgumentU8,
            { .case_LongArgumentU8 = op_Array_Access__uint8_t(input2, (size_t)0U) }
          }
        );
  else if (x1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
  {
    uint8_t last = op_Array_Access__uint8_t(input2, (size_t)1U);
    ite =
      (
        (long_argument){
          .tag = LongArgumentU16,
          {
            .case_LongArgumentU16 = (uint32_t)(uint16_t)last +
              (uint32_t)(uint16_t)op_Array_Access__uint8_t(input2, (size_t)0U) * 256U
          }
        }
      );
  }
  else if (x1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
  {
    uint8_t last = op_Array_Access__uint8_t(input2, (size_t)3U);
    uint8_t last1 = op_Array_Access__uint8_t(input2, (size_t)3U - (size_t)1U);
    uint8_t last2 = op_Array_Access__uint8_t(input2, (size_t)3U - (size_t)1U - (size_t)1U);
    ite =
      (
        (long_argument){
          .tag = LongArgumentU32,
          {
            .case_LongArgumentU32 = (uint32_t)last +
              ((uint32_t)last1 +
                ((uint32_t)last2 + (uint32_t)op_Array_Access__uint8_t(input2, (size_t)0U) * 256U) *
                  256U)
              * 256U
          }
        }
      );
  }
  else if (x1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
  {
    uint8_t last = op_Array_Access__uint8_t(input2, (size_t)7U);
    uint8_t last1 = op_Array_Access__uint8_t(input2, (size_t)7U - (size_t)1U);
    uint8_t last2 = op_Array_Access__uint8_t(input2, (size_t)7U - (size_t)1U - (size_t)1U);
    uint8_t
    last3 = op_Array_Access__uint8_t(input2, (size_t)7U - (size_t)1U - (size_t)1U - (size_t)1U);
    size_t pos_4 = (size_t)7U - (size_t)1U - (size_t)1U - (size_t)1U - (size_t)1U;
    uint8_t last4 = op_Array_Access__uint8_t(input2, pos_4);
    size_t pos_5 = pos_4 - (size_t)1U;
    uint8_t last5 = op_Array_Access__uint8_t(input2, pos_5);
    uint8_t last6 = op_Array_Access__uint8_t(input2, pos_5 - (size_t)1U);
    ite =
      (
        (long_argument){
          .tag = LongArgumentU64,
          {
            .case_LongArgumentU64 = (uint64_t)last +
              ((uint64_t)last1 +
                ((uint64_t)last2 +
                  ((uint64_t)last3 +
                    ((uint64_t)last4 +
                      ((uint64_t)last5 +
                        ((uint64_t)last6 +
                          (uint64_t)op_Array_Access__uint8_t(input2, (size_t)0U) * 256ULL)
                        * 256ULL)
                      * 256ULL)
                    * 256ULL)
                  * 256ULL)
                * 256ULL)
              * 256ULL
          }
        }
      );
  }
  else
    ite = ((long_argument){ .tag = LongArgumentOther });
  return ((header){ .fst = x1, .snd = ite });
}

static bool validate_header(Pulse_Lib_Slice_slice__uint8_t input, size_t *poffset)
{
  size_t offset1 = *poffset;
  size_t offset2 = *poffset;
  size_t offset30 = *poffset;
  bool ite0;
  if (len__uint8_t(input) - offset30 < (size_t)1U)
    ite0 = false;
  else
  {
    *poffset = offset30 + (size_t)1U;
    ite0 = true;
  }
  bool ite1;
  if (ite0)
  {
    size_t off = *poffset;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut = split__uint8_t(input, offset2);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut0 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut.fst,
            .snd = scrut.snd
          }
        ).snd,
        off - offset2);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
    initial_byte_t
    x =
      read_initial_byte_t((
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut1.fst,
            .snd = scrut1.snd
          }
        ).fst);
    bool ite;
    if (x.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      ite = x.additional_info <= ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS;
    else
      ite = true;
    ite1 = ite && x.additional_info < ADDITIONAL_INFO_UNASSIGNED_MIN;
  }
  else
    ite1 = false;
  if (ite1)
  {
    size_t off = *poffset;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut0 = split__uint8_t(input, offset1);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).snd,
        off - offset1);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    initial_byte_t
    x =
      read_initial_byte_t((
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut2.fst,
            .snd = scrut2.snd
          }
        ).fst);
    if (x.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
      if (x.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
      {
        size_t offset2 = *poffset;
        size_t offset3 = *poffset;
        bool ite;
        if (len__uint8_t(input) - offset3 < (size_t)1U)
          ite = false;
        else
        {
          *poffset = offset3 + (size_t)1U;
          ite = true;
        }
        if (ite)
        {
          size_t off1 = *poffset;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut = split__uint8_t(input, offset2);
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut0 =
            split__uint8_t((
                (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                  .fst = scrut.fst,
                  .snd = scrut.snd
                }
              ).snd,
              off1 - offset2);
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          return
            MIN_SIMPLE_VALUE_LONG_ARGUMENT <=
              op_Array_Access__uint8_t((
                  (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                    .fst = scrut1.fst,
                    .snd = scrut1.snd
                  }
                ).fst,
                (size_t)0U);
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
    else if (x.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
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
    else if (x.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
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
    else if (x.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
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
  scrut = split__uint8_t(input, offset);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 =
    split__uint8_t((
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut.fst,
          .snd = scrut.snd
        }
      ).snd,
      off1 - offset);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  initial_byte_t
  x =
    read_initial_byte_t((
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut1.fst,
          .snd = scrut1.snd
        }
      ).fst);
  if (x.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    return off1 + (size_t)1U;
  else if (x.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    return off1 + (size_t)2U;
  else if (x.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    return off1 + (size_t)4U;
  else if (x.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
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
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut = split__uint8_t(a, jump_header(a, (size_t)0U));
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  header
  h =
    read_header((
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut0.fst,
          .snd = scrut0.snd
        }
      ).fst);
  uint8_t typ = get_header_major_type(h);
  if (typ == CBOR_MAJOR_TYPE_ARRAY)
  {
    *prem = (size_t)argument_as_uint64(h.fst, h.snd);
    return false;
  }
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    size_t arg = (size_t)argument_as_uint64(h.fst, h.snd);
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
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut = split__uint8_t(a, jump_header(a, (size_t)0U));
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  header
  h =
    read_header((
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut0.fst,
          .snd = scrut0.snd
        }
      ).fst);
  uint8_t typ = get_header_major_type(h);
  if (typ == CBOR_MAJOR_TYPE_ARRAY)
    return (size_t)argument_as_uint64(h.fst, h.snd);
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    size_t arg = (size_t)argument_as_uint64(h.fst, h.snd);
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
  while (pres && pn > (size_t)0U)
  {
    size_t off = *poffset;
    size_t n = pn;
    if (n > len__uint8_t(input) - off)
      pres = false;
    else
    {
      size_t offset1 = *poffset;
      bool ite0;
      if (validate_header(input, poffset))
      {
        size_t off1 = *poffset;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut0 = split__uint8_t(input, offset1);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut1 =
          split__uint8_t((
              (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                .fst = scrut0.fst,
                .snd = scrut0.snd
              }
            ).snd,
            off1 - offset1);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        header
        x =
          read_header((
              (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                .fst = scrut2.fst,
                .snd = scrut2.snd
              }
            ).fst);
        initial_byte_t b = x.fst;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        {
          size_t n1 = (size_t)argument_as_uint64(x.fst, x.snd);
          size_t offset2 = *poffset;
          size_t offset3 = *poffset;
          bool ite;
          if (len__uint8_t(input) - offset3 < n1)
            ite = false;
          else
          {
            *poffset = offset3 + n1;
            ite = true;
          }
          if (ite)
          {
            size_t off2 = *poffset;
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            scrut = split__uint8_t(input, offset2);
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            scrut0 =
              split__uint8_t((
                  (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                    .fst = scrut.fst,
                    .snd = scrut.snd
                  }
                ).snd,
                off2 - offset2);
            __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
            scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
            Pulse_Lib_Slice_slice__uint8_t
            x1 =
              (
                (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                  .fst = scrut1.fst,
                  .snd = scrut1.snd
                }
              ).fst;
            if (get_header_major_type(x) == CBOR_MAJOR_TYPE_BYTE_STRING)
              ite0 = true;
            else
              ite0 = impl_correct(x1);
          }
          else
            ite0 = false;
        }
        else
          ite0 = true;
      }
      else
        ite0 = false;
      if (!ite0)
        pres = false;
      else
      {
        size_t offset1 = *poffset;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut = split__uint8_t(input, off);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut0 =
          split__uint8_t((
              (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                .fst = scrut.fst,
                .snd = scrut.snd
              }
            ).snd,
            offset1 - off);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        Pulse_Lib_Slice_slice__uint8_t
        input1 =
          (
            (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
              .fst = scrut1.fst,
              .snd = scrut1.snd
            }
          ).fst;
        size_t bound = len__uint8_t(input) - off - n;
        bool res2 = validate_recursive_step_count_leaf(input1, bound, &pn);
        size_t count = pn;
        if (res2 || count > bound)
          pres = false;
        else
          pn = n - (size_t)1U + count;
      }
    }
  }
  return pres;
}

static size_t jump_raw_data_item(Pulse_Lib_Slice_slice__uint8_t input, size_t offset)
{
  size_t poffset = offset;
  size_t pn = (size_t)1U;
  while (pn > (size_t)0U)
  {
    size_t off = poffset;
    size_t off10 = jump_header(input, off);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut0 = split__uint8_t(input, off);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).snd,
        off10 - off);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    header
    x =
      read_header((
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut2.fst,
            .snd = scrut2.snd
          }
        ).fst);
    initial_byte_t b = x.fst;
    size_t off1;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
      off1 = off10 + (size_t)argument_as_uint64(x.fst, x.snd);
    else
      off1 = off10 + (size_t)0U;
    poffset = off1;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut = split__uint8_t(input, off);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut3 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut.fst,
            .snd = scrut.snd
          }
        ).snd,
        off1 - off);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
    Pulse_Lib_Slice_slice__uint8_t
    input1 =
      (
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut4.fst,
          .snd = scrut4.snd
        }
      ).fst;
    size_t n = pn;
    size_t unused = len__uint8_t(input) - off1;
    KRML_MAYBE_UNUSED_VAR(unused);
    pn = n - (size_t)1U + jump_recursive_step_count_leaf(input1);
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
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut = split__uint8_t(input, jump_header(input, (size_t)0U));
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  Pulse_Lib_Slice_slice__uint8_t outc = scrut1.snd;
  ph = read_header(scrut1.fst);
  Pulse_Lib_Slice_slice__uint8_t pc = outc;
  header h = ph;
  uint8_t typ = h.fst.major_type;
  if (typ == CBOR_MAJOR_TYPE_UINT64 || typ == CBOR_MAJOR_TYPE_NEG_INT64)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 i;
    if (l.tag == LongArgumentU8)
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)l.case_LongArgumentU8 });
    else if (l.tag == LongArgumentU16)
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)l.case_LongArgumentU16 });
    else if (l.tag == LongArgumentU32)
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)l.case_LongArgumentU32 });
    else if (l.tag == LongArgumentU64)
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = l.case_LongArgumentU64 });
    else if (l.tag == LongArgumentOther)
      i = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      i =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Int,
          {
            .case_CBOR_Case_Int = {
              .cbor_int_type = typ,
              .cbor_int_size = i.size,
              .cbor_int_value = i.value
            }
          }
        }
      );
  }
  else if (typ == CBOR_MAJOR_TYPE_TEXT_STRING || typ == CBOR_MAJOR_TYPE_BYTE_STRING)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (l.tag == LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)l.case_LongArgumentU8 });
    else if (l.tag == LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)l.case_LongArgumentU16 });
    else if (l.tag == LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)l.case_LongArgumentU32 });
    else if (l.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = l.case_LongArgumentU64 });
    else if (l.tag == LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_String,
          {
            .case_CBOR_Case_String = {
              .cbor_string_type = typ,
              .cbor_string_size = ite.size,
              .cbor_string_ptr = pc
            }
          }
        }
      );
  }
  else if (typ == CBOR_MAJOR_TYPE_TAGGED)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (l.tag == LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)l.case_LongArgumentU8 });
    else if (l.tag == LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)l.case_LongArgumentU16 });
    else if (l.tag == LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)l.case_LongArgumentU32 });
    else if (l.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = l.case_LongArgumentU64 });
    else if (l.tag == LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Tagged,
          {
            .case_CBOR_Case_Serialized_Tagged = {
              .cbor_serialized_header = ite,
              .cbor_serialized_payload = pc
            }
          }
        }
      );
  }
  else if (typ == CBOR_MAJOR_TYPE_ARRAY)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (l.tag == LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)l.case_LongArgumentU8 });
    else if (l.tag == LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)l.case_LongArgumentU16 });
    else if (l.tag == LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)l.case_LongArgumentU32 });
    else if (l.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = l.case_LongArgumentU64 });
    else if (l.tag == LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Array,
          {
            .case_CBOR_Case_Serialized_Array = {
              .cbor_serialized_header = ite,
              .cbor_serialized_payload = pc
            }
          }
        }
      );
  }
  else if (typ == CBOR_MAJOR_TYPE_MAP)
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (l.tag == LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)l.case_LongArgumentU8 });
    else if (l.tag == LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)l.case_LongArgumentU16 });
    else if (l.tag == LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)l.case_LongArgumentU32 });
    else if (l.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = l.case_LongArgumentU64 });
    else if (l.tag == LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Serialized_Map,
          {
            .case_CBOR_Case_Serialized_Map = {
              .cbor_serialized_header = ite,
              .cbor_serialized_payload = pc
            }
          }
        }
      );
  }
  else
  {
    initial_byte_t b = h.fst;
    long_argument l = h.snd;
    uint8_t ite;
    if (l.tag == LongArgumentOther)
      ite = b.additional_info;
    else if (l.tag == LongArgumentSimpleValue)
      ite = l.case_LongArgumentSimpleValue;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = ite } });
  }
}

static size_t cbor_validate(Pulse_Lib_Slice_slice__uint8_t input)
{
  size_t poffset = (size_t)0U;
  if (validate_raw_data_item(input, &poffset))
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
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 = split__uint8_t(a, jump_header(a, (size_t)0U));
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
  header
  h =
    read_header((
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut2.fst,
          .snd = scrut2.snd
        }
      ).fst);
  if (get_header_major_type(h) == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    return true;
  else
  {
    long_argument scrut = h.snd;
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (scrut.tag == LongArgumentU8)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 1U,
            .value = (uint64_t)scrut.case_LongArgumentU8
          }
        );
    else if (scrut.tag == LongArgumentU16)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 2U,
            .value = (uint64_t)scrut.case_LongArgumentU16
          }
        );
    else if (scrut.tag == LongArgumentU32)
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = 3U,
            .value = (uint64_t)scrut.case_LongArgumentU32
          }
        );
    else if (scrut.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = scrut.case_LongArgumentU64 });
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
  return lex_compare_bytes(a1, a2) < (int16_t)0;
}

static bool cbor_raw_sorted(Pulse_Lib_Slice_slice__uint8_t a)
{
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 = split__uint8_t(a, jump_header(a, (size_t)0U));
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
  Pulse_Lib_Slice_slice__uint8_t input2 = scrut3.snd;
  header h = read_header(scrut3.fst);
  if (get_header_major_type(h) == CBOR_MAJOR_TYPE_MAP)
  {
    uint64_t nbpairs = argument_as_uint64(h.fst, h.snd);
    if (nbpairs < 2ULL)
      return true;
    else
    {
      initial_byte_t b = h.fst;
      size_t ite;
      if
      (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
        ite = (size_t)0U + (size_t)argument_as_uint64(h.fst, h.snd);
      else
        ite = (size_t)0U;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut0 = split__uint8_t(input2, ite);
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
      Pulse_Lib_Slice_slice__uint8_t
      input3 =
        (
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut2.fst,
            .snd = scrut2.snd
          }
        ).snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut3 = split__uint8_t(input3, jump_raw_data_item(input3, (size_t)0U));
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut5 = { .fst = scrut4.fst, .snd = scrut4.snd };
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
      Pulse_Lib_Slice_slice__uint8_t input4 = scrut7.snd;
      Pulse_Lib_Slice_slice__uint8_t pkey = scrut7.fst;
      uint64_t ppairs = nbpairs - 1ULL;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut = split__uint8_t(input4, jump_raw_data_item(input4, (size_t)0U));
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut8 = { .fst = scrut.fst, .snd = scrut.snd };
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      scrut10 = { .fst = scrut9.fst, .snd = scrut9.snd };
      Pulse_Lib_Slice_slice__uint8_t
      ptail =
        (
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut10.fst,
            .snd = scrut10.snd
          }
        ).snd;
      bool pres = true;
      while (pres && ppairs > 0ULL)
      {
        Pulse_Lib_Slice_slice__uint8_t tail = ptail;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut = split__uint8_t(tail, jump_raw_data_item(tail, (size_t)0U));
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
        Pulse_Lib_Slice_slice__uint8_t key2 = scrut3.fst;
        Pulse_Lib_Slice_slice__uint8_t tail2 = scrut3.snd;
        if (impl_deterministically_encoded_cbor_map_key_order(pkey, key2))
        {
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut = split__uint8_t(tail2, jump_raw_data_item(tail2, (size_t)0U));
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
          Pulse_Lib_Slice_slice__uint8_t
          tail_ =
            (
              (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                .fst = scrut2.fst,
                .snd = scrut2.snd
              }
            ).snd;
          pkey = key2;
          ppairs = ppairs - 1ULL;
          ptail = tail_;
        }
        else
          pres = false;
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
    scrut0 = split__uint8_t(input, (size_t)0U);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).snd,
        len - (size_t)0U);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    Pulse_Lib_Slice_slice__uint8_t
    input1 =
      (
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut2.fst,
          .snd = scrut2.snd
        }
      ).fst;
    bool buf = false;
    KRML_HOST_IGNORE(&buf);
    size_t pn = (size_t)1U;
    bool pres0 = true;
    Pulse_Lib_Slice_slice__uint8_t ppi0 = input1;
    while (pres0 && pn > (size_t)0U)
    {
      size_t n = pn;
      Pulse_Lib_Slice_slice__uint8_t pi = ppi0;
      if (!cbor_raw_ints_optimal(pi))
        pres0 = false;
      else
      {
        size_t off1 = jump_header(pi, (size_t)0U);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut = split__uint8_t(pi, (size_t)0U);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut0 =
          split__uint8_t((
              (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                .fst = scrut.fst,
                .snd = scrut.snd
              }
            ).snd,
            off1 - (size_t)0U);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        header
        x =
          read_header((
              (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                .fst = scrut1.fst,
                .snd = scrut1.snd
              }
            ).fst);
        initial_byte_t b = x.fst;
        size_t ite;
        if
        (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
          ite = off1 + (size_t)argument_as_uint64(x.fst, x.snd);
        else
          ite = off1 + (size_t)0U;
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut2 = split__uint8_t(pi, ite);
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
        __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
        scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
        Pulse_Lib_Slice_slice__uint8_t ph = scrut4.fst;
        Pulse_Lib_Slice_slice__uint8_t pc = scrut4.snd;
        size_t unused = len__uint8_t(pc);
        KRML_MAYBE_UNUSED_VAR(unused);
        pn = n - (size_t)1U + jump_recursive_step_count_leaf(ph);
        ppi0 = pc;
      }
    }
    if (!pres0)
      return (size_t)0U;
    else
    {
      size_t pn = (size_t)1U;
      bool pres = true;
      Pulse_Lib_Slice_slice__uint8_t ppi = input1;
      while (pres && pn > (size_t)0U)
      {
        size_t n = pn;
        Pulse_Lib_Slice_slice__uint8_t pi = ppi;
        if (!cbor_raw_sorted(pi))
          pres = false;
        else
        {
          size_t off1 = jump_header(pi, (size_t)0U);
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut = split__uint8_t(pi, (size_t)0U);
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut0 =
            split__uint8_t((
                (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                  .fst = scrut.fst,
                  .snd = scrut.snd
                }
              ).snd,
              off1 - (size_t)0U);
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          header
          x =
            read_header((
                (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
                  .fst = scrut1.fst,
                  .snd = scrut1.snd
                }
              ).fst);
          initial_byte_t b = x.fst;
          size_t ite;
          if
          (
            b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING ||
              b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING
          )
            ite = off1 + (size_t)argument_as_uint64(x.fst, x.snd);
          else
            ite = off1 + (size_t)0U;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut2 = split__uint8_t(pi, ite);
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
          Pulse_Lib_Slice_slice__uint8_t ph = scrut4.fst;
          Pulse_Lib_Slice_slice__uint8_t pc = scrut4.snd;
          size_t unused = len__uint8_t(pc);
          KRML_MAYBE_UNUSED_VAR(unused);
          pn = n - (size_t)1U + jump_recursive_step_count_leaf(ph);
          ppi = pc;
        }
      }
      if (!pres)
        return (size_t)0U;
      else
        return len;
    }
  }
}

static size_t cbor_validate_det(Pulse_Lib_Slice_slice__uint8_t input)
{
  return cbor_validate_det_(input);
}

static cbor_raw cbor_parse(Pulse_Lib_Slice_slice__uint8_t input, size_t len)
{
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut = split__uint8_t(input, (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 =
    split__uint8_t((
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut.fst,
          .snd = scrut.snd
        }
      ).snd,
      len - (size_t)0U);
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  return
    cbor_read((
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut1.fst,
          .snd = scrut1.snd
        }
      ).fst);
}

static size_t cbor_jump(Pulse_Lib_Slice_slice__uint8_t input, size_t off)
{
  return jump_raw_data_item(input, off);
}

#define CFailure 0
#define CInProgress 1
#define CSuccess 2

typedef uint8_t cbor_raw_map_insert_result;

static bool uu___is_CInProgress(cbor_raw_map_insert_result projectee)
{
  switch (projectee)
  {
    case CInProgress:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

static void op_Array_Assignment__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i, uint8_t v)
{
  a.elt[i] = v;
}

static bool cbor_raw_map_insert(Pulse_Lib_Slice_slice__uint8_t out, size_t off2, size_t off3)
{
  size_t poff = (size_t)0U;
  cbor_raw_map_insert_result pres = CInProgress;
  bool cond;
  if (uu___is_CInProgress(pres))
    cond = poff < off2;
  else
    cond = false;
  while (cond)
  {
    size_t off = poff;
    Pulse_Lib_Slice_slice__uint8_t out2kv = split__uint8_t(out, off).snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut0 = split__uint8_t(out2kv, off2 - off);
    Pulse_Lib_Slice_slice__uint8_t out2 = scrut0.fst;
    Pulse_Lib_Slice_slice__uint8_t outk = split__uint8_t(scrut0.snd, off3 - off2).fst;
    size_t offk = cbor_jump(out2, (size_t)0U);
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut = split__uint8_t(out2, offk);
    Pulse_Lib_Slice_slice__uint8_t outvq = scrut.snd;
    int16_t c = lex_compare_bytes(scrut.fst, outk);
    if (c < (int16_t)0)
      poff = off + offk + cbor_jump(outvq, (size_t)0U);
    else if (c > (int16_t)0)
    {
      if (!(off2 - off == (size_t)0U || off2 - off == len__uint8_t(out2kv)))
      {
        size_t pn = len__uint8_t(out2kv);
        size_t pl = off2 - off;
        while (pl > (size_t)0U)
        {
          size_t l = pl;
          size_t l_ = pn % l;
          pn = l;
          pl = l_;
        }
        size_t d = pn;
        size_t q = len__uint8_t(out2kv) / d;
        size_t pi = (size_t)0U;
        while (pi < d)
        {
          size_t i = pi;
          uint8_t save = op_Array_Access__uint8_t(out2kv, i);
          size_t pj = (size_t)0U;
          size_t pidx = i;
          while (pj < q - (size_t)1U)
          {
            size_t j = pj;
            size_t idx = pidx;
            size_t idx_;
            if (idx - (size_t)0U >= len__uint8_t(out2kv) - (off2 - off))
              idx_ = idx - (len__uint8_t(out2kv) - (off2 - off));
            else
              idx_ = idx + off2 - off - (size_t)0U;
            size_t j_ = j + (size_t)1U;
            op_Array_Assignment__uint8_t(out2kv, idx, op_Array_Access__uint8_t(out2kv, idx_));
            pj = j_;
            pidx = idx_;
          }
          op_Array_Assignment__uint8_t(out2kv, pidx, save);
          pi = i + (size_t)1U;
        }
      }
      pres = CSuccess;
    }
    else
      pres = CFailure;
    bool ite;
    if (uu___is_CInProgress(pres))
      ite = poff < off2;
    else
      ite = false;
    cond = ite;
  }
  switch (pres)
  {
    case CSuccess:
      {
        return true;
      }
    case CFailure:
      {
        return false;
      }
    case CInProgress:
      {
        return true;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static cbor_raw cbor_match_serialized_tagged_get_payload(cbor_serialized c)
{
  return cbor_read(c.cbor_serialized_payload);
}

static cbor_raw cbor_serialized_array_item(cbor_serialized c, uint64_t i)
{
  size_t pi = (size_t)0U;
  Pulse_Lib_Slice_slice__uint8_t pres = c.cbor_serialized_payload;
  while (pi < (size_t)i)
  {
    Pulse_Lib_Slice_slice__uint8_t res = pres;
    size_t i1 = pi;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut = split__uint8_t(res, jump_raw_data_item(res, (size_t)0U));
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
    Pulse_Lib_Slice_slice__uint8_t
    res2 =
      (
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut1.fst,
          .snd = scrut1.snd
        }
      ).snd;
    pi = i1 + (size_t)1U;
    pres = res2;
  }
  Pulse_Lib_Slice_slice__uint8_t res = pres;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut = split__uint8_t(res, jump_raw_data_item(res, (size_t)0U));
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  return
    cbor_read((
        (__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t){
          .fst = scrut1.fst,
          .snd = scrut1.snd
        }
      ).fst);
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
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut = split__uint8_t(i.s, jump_raw_data_item(i.s, (size_t)0U));
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
  Pulse_Lib_Slice_slice__uint8_t s2 = scrut2.snd;
  cbor_raw res = cbor_read(scrut2.fst);
  *pi =
    (
      (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
        .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = { .s = s2, .len = i.len - 1ULL } }
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
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut0 = split__uint8_t(i.s, jump_raw_data_item(i.s, jump_raw_data_item(i.s, (size_t)0U)));
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
  Pulse_Lib_Slice_slice__uint8_t s1 = scrut3.fst;
  Pulse_Lib_Slice_slice__uint8_t s2 = scrut3.snd;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut = split__uint8_t(s1, jump_raw_data_item(s1, (size_t)0U));
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut4 = { .fst = scrut.fst, .snd = scrut.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut5 = { .fst = scrut4.fst, .snd = scrut4.snd };
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
  scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
  Pulse_Lib_Slice_slice__uint8_t s21 = scrut6.snd;
  cbor_raw res1 = cbor_read(scrut6.fst);
  cbor_map_entry res = { .cbor_map_entry_key = res1, .cbor_map_entry_value = cbor_read(s21) };
  *pi =
    (
      (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
        .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
        { .case_CBOR_Raw_Iterator_Serialized = { .s = s2, .len = i.len - 1ULL } }
      }
    );
  return res;
}

static cbor_raw cbor_match_tagged_get_payload(cbor_raw c)
{
  if (c.tag == CBOR_Case_Serialized_Tagged)
    return cbor_match_serialized_tagged_get_payload(c.case_CBOR_Case_Serialized_Tagged);
  else if (c.tag == CBOR_Case_Tagged)
    return *c.case_CBOR_Case_Tagged.cbor_tagged_ptr;
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
    return cbor_serialized_array_item(c.case_CBOR_Case_Serialized_Array, i);
  else if (c.tag == CBOR_Case_Array)
    return
      op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(c.case_CBOR_Case_Array.cbor_array_ptr,
        (size_t)i);
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
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = cbor_serialized_array_iterator_init(c.case_CBOR_Case_Serialized_Array)
          }
        }
      );
  else if (c.tag == CBOR_Case_Array)
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = c.case_CBOR_Case_Array.cbor_array_ptr }
        }
      );
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
    return len__CBOR_Pulse_Raw_Type_cbor_raw(c.case_CBOR_Raw_Iterator_Slice) == (size_t)0U;
  else if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
    return cbor_serialized_array_iterator_is_empty(c.case_CBOR_Raw_Iterator_Serialized);
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
    return (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c.case_CBOR_Raw_Iterator_Slice);
  else if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
    return cbor_serialized_array_iterator_length(c.case_CBOR_Raw_Iterator_Serialized);
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
  return
    (
      (__Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static cbor_raw
cbor_array_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw *pi
)
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw scrut = *pi;
  if (scrut.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw i1 = scrut.case_CBOR_Raw_Iterator_Slice;
    cbor_raw res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i1, (size_t)0U);
    *pi =
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          {
            .case_CBOR_Raw_Iterator_Slice = split__CBOR_Pulse_Raw_Type_cbor_raw(i1, (size_t)1U).snd
          }
        }
      );
    return res;
  }
  else if (scrut.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
    return cbor_serialized_array_iterator_next(pi, scrut.case_CBOR_Raw_Iterator_Serialized);
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
    __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
    scrut = split__CBOR_Pulse_Raw_Type_cbor_raw(c.case_CBOR_Raw_Iterator_Slice, (size_t)len);
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          {
            .case_CBOR_Raw_Iterator_Slice = (
              (__Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw){
                .fst = scrut.fst,
                .snd = scrut.snd
              }
            ).fst
          }
        }
      );
  }
  else if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = cbor_serialized_array_iterator_truncate(c.case_CBOR_Raw_Iterator_Serialized,
              len)
          }
        }
      );
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
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized,
          {
            .case_CBOR_Raw_Iterator_Serialized = cbor_serialized_map_iterator_init(c.case_CBOR_Case_Serialized_Map)
          }
        }
      );
  else if (c.tag == CBOR_Case_Map)
    return
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          { .case_CBOR_Raw_Iterator_Slice = c.case_CBOR_Case_Map.cbor_map_ptr }
        }
      );
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
    return len__CBOR_Pulse_Raw_Type_cbor_map_entry(c.case_CBOR_Raw_Iterator_Slice) == (size_t)0U;
  else if (c.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
    return cbor_serialized_map_iterator_is_empty(c.case_CBOR_Raw_Iterator_Serialized);
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
  return
    (
      (__Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static cbor_map_entry
cbor_map_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry *pi
)
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry scrut = *pi;
  if (scrut.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
  {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
    i1 = scrut.case_CBOR_Raw_Iterator_Slice;
    cbor_map_entry res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i1, (size_t)0U);
    *pi =
      (
        (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
          .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
          {
            .case_CBOR_Raw_Iterator_Slice = split__CBOR_Pulse_Raw_Type_cbor_map_entry(i1,
              (size_t)1U).snd
          }
        }
      );
    return res;
  }
  else if (scrut.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
    return cbor_serialized_map_iterator_next(pi, scrut.case_CBOR_Raw_Iterator_Serialized);
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
  op_Array_Assignment__uint8_t(out,
    pos_ - (size_t)1U,
    set_bitfield_gen8(set_bitfield_gen8(0U, 0U, 5U, xh1.additional_info), 5U, 8U, xh1.major_type));
  size_t res1 = pos_;
  long_argument
  x2_ = dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    if (xh1.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    {
      size_t pos_ = res1 + (size_t)1U;
      uint8_t ite;
      if (x2_.tag == LongArgumentSimpleValue)
        ite = x2_.case_LongArgumentSimpleValue;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      op_Array_Assignment__uint8_t(out, pos_ - (size_t)1U, ite);
      return pos_;
    }
    else
    {
      size_t pos_ = res1 + (size_t)1U;
      uint8_t ite;
      if (x2_.tag == LongArgumentU8)
        ite = x2_.case_LongArgumentU8;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      op_Array_Assignment__uint8_t(out, pos_ - (size_t)1U, ite);
      return pos_;
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
    size_t pos_1 = pos_ - (size_t)1U;
    uint16_t ite;
    if (x2_.tag == LongArgumentU16)
      ite = x2_.case_LongArgumentU16;
    else
      ite = KRML_EABORT(uint16_t, "unreachable (pattern matches are exhaustive in F*)");
    op_Array_Assignment__uint8_t(out, pos_1 - (size_t)1U, (uint8_t)((uint32_t)ite / 256U));
    op_Array_Assignment__uint8_t(out, pos_1, lo);
    return pos_;
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
    size_t pos_3 = pos_2 - (size_t)1U;
    op_Array_Assignment__uint8_t(out, pos_3 - (size_t)1U, (uint8_t)(hi1 / 256U));
    op_Array_Assignment__uint8_t(out, pos_3, lo2);
    op_Array_Assignment__uint8_t(out, pos_2, lo1);
    op_Array_Assignment__uint8_t(out, pos_1, lo);
    return pos_;
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
    size_t pos_7 = pos_6 - (size_t)1U;
    op_Array_Assignment__uint8_t(out, pos_7 - (size_t)1U, (uint8_t)(hi5 / 256ULL));
    op_Array_Assignment__uint8_t(out, pos_7, lo6);
    op_Array_Assignment__uint8_t(out, pos_6, lo5);
    op_Array_Assignment__uint8_t(out, pos_5, lo4);
    op_Array_Assignment__uint8_t(out, pos_4, lo3);
    op_Array_Assignment__uint8_t(out, pos_3, lo2);
    op_Array_Assignment__uint8_t(out, pos_2, lo1);
    op_Array_Assignment__uint8_t(out, pos_1, lo);
    return pos_;
  }
  else
    return res1;
}

static bool size_header(header x, size_t *out)
{
  initial_byte_t
  xh1 = dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
  size_t capacity = *out;
  bool ite;
  if (capacity < (size_t)1U)
    ite = false;
  else
  {
    *out = capacity - (size_t)1U;
    ite = true;
  }
  if (ite)
  {
    dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
    if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_8_BITS)
    {
      size_t capacity = *out;
      if (capacity < (size_t)1U)
        return false;
      else
      {
        *out = capacity - (size_t)1U;
        return true;
      }
    }
    else if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_16_BITS)
    {
      size_t capacity = *out;
      if (capacity < (size_t)2U)
        return false;
      else
      {
        *out = capacity - (size_t)2U;
        return true;
      }
    }
    else if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_32_BITS)
    {
      size_t capacity = *out;
      if (capacity < (size_t)4U)
        return false;
      else
      {
        *out = capacity - (size_t)4U;
        return true;
      }
    }
    else if (xh1.additional_info == ADDITIONAL_INFO_LONG_ARGUMENT_64_BITS)
    {
      size_t capacity = *out;
      if (capacity < (size_t)8U)
        return false;
      else
      {
        *out = capacity - (size_t)8U;
        return true;
      }
    }
    else
      return true;
  }
  else
    return false;
}

static header cbor_raw_get_header(cbor_raw xl)
{
  if (xl.tag == CBOR_Case_Int)
  {
    uint8_t ty;
    if (xl.tag == CBOR_Case_Int)
      ty = xl.case_CBOR_Case_Int.cbor_int_type;
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_Int)
    {
      cbor_int c_ = xl.case_CBOR_Case_Int;
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
    }
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(ty, ite);
  }
  else if (xl.tag == CBOR_Case_String)
  {
    uint8_t ty;
    if (xl.tag == CBOR_Case_String)
      ty = xl.case_CBOR_Case_String.cbor_string_type;
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_String)
    {
      cbor_string c_ = xl.case_CBOR_Case_String;
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_string_size,
            .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr)
          }
        );
    }
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(ty, ite);
  }
  else if (xl.tag == CBOR_Case_Tagged)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_Tagged)
      ite = xl.case_CBOR_Case_Tagged.cbor_tagged_tag;
    else if (xl.tag == CBOR_Case_Serialized_Tagged)
      ite = xl.case_CBOR_Case_Serialized_Tagged.cbor_serialized_header;
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED, ite);
  }
  else if (xl.tag == CBOR_Case_Serialized_Tagged)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_Tagged)
      ite = xl.case_CBOR_Case_Tagged.cbor_tagged_tag;
    else if (xl.tag == CBOR_Case_Serialized_Tagged)
      ite = xl.case_CBOR_Case_Serialized_Tagged.cbor_serialized_header;
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED, ite);
  }
  else if (xl.tag == CBOR_Case_Array)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_Array)
    {
      cbor_array c_ = xl.case_CBOR_Case_Array;
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_array_length_size,
            .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
          }
        );
    }
    else if (xl.tag == CBOR_Case_Serialized_Array)
      ite = xl.case_CBOR_Case_Serialized_Array.cbor_serialized_header;
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY, ite);
  }
  else if (xl.tag == CBOR_Case_Serialized_Array)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_Array)
    {
      cbor_array c_ = xl.case_CBOR_Case_Array;
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_array_length_size,
            .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
          }
        );
    }
    else if (xl.tag == CBOR_Case_Serialized_Array)
      ite = xl.case_CBOR_Case_Serialized_Array.cbor_serialized_header;
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY, ite);
  }
  else if (xl.tag == CBOR_Case_Map)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_Map)
    {
      cbor_map c_ = xl.case_CBOR_Case_Map;
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_map_length_size,
            .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
          }
        );
    }
    else if (xl.tag == CBOR_Case_Serialized_Map)
      ite = xl.case_CBOR_Case_Serialized_Map.cbor_serialized_header;
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP, ite);
  }
  else if (xl.tag == CBOR_Case_Serialized_Map)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (xl.tag == CBOR_Case_Map)
    {
      cbor_map c_ = xl.case_CBOR_Case_Map;
      ite =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_map_length_size,
            .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
          }
        );
    }
    else if (xl.tag == CBOR_Case_Serialized_Map)
      ite = xl.case_CBOR_Case_Serialized_Map.cbor_serialized_header;
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP, ite);
  }
  else if (xl.tag == CBOR_Case_Simple)
  {
    uint8_t ite;
    if (xl.tag == CBOR_Case_Simple)
      ite = xl.case_CBOR_Case_Simple;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return simple_value_as_argument(ite);
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
  return cbor_raw_get_header(xl);
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
  header xh1 = cbor_raw_with_perm_get_header(x_);
  size_t res1 = write_header(xh1, out, offset);
  initial_byte_t b = xh1.fst;
  if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
  {
    cbor_raw scrut = x_;
    Pulse_Lib_Slice_slice__uint8_t x2_;
    if (scrut.tag == CBOR_Case_String)
      x2_ = scrut.case_CBOR_Case_String.cbor_string_ptr;
    else
      x2_ =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    size_t length = len__uint8_t(x2_);
    copy__uint8_t(split__uint8_t(split__uint8_t(out, res1).snd, length).fst, x2_);
    return res1 + length;
  }
  else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_ARRAY)
  {
    bool ite;
    if (x_.tag == CBOR_Case_Array)
      ite = true;
    else
      ite = false;
    if (ite)
    {
      cbor_raw scrut0 = x_;
      option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
      scrut;
      if (scrut0.tag == CBOR_Case_Array)
        scrut =
          (
            (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw){
              .tag = Some,
              .v = scrut0.case_CBOR_Case_Array.cbor_array_ptr
            }
          );
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
        size_t i_ = i + (size_t)1U;
        size_t
        res =
          CBOR_Pulse_Raw_Format_Serialize_ser_(op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(a, i),
            out,
            off);
        pi = i_;
        pres = res;
        size_t i0 = pi;
        cond = i0 < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
      }
      return pres;
    }
    else
    {
      cbor_raw scrut = x_;
      Pulse_Lib_Slice_slice__uint8_t x2_;
      if (scrut.tag == CBOR_Case_Serialized_Array)
        x2_ = scrut.case_CBOR_Case_Serialized_Array.cbor_serialized_payload;
      else
        x2_ =
          KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
            "unreachable (pattern matches are exhaustive in F*)");
      size_t length = len__uint8_t(x2_);
      copy__uint8_t(split__uint8_t(split__uint8_t(out, res1).snd, length).fst, x2_);
      return res1 + length;
    }
  }
  else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_MAP)
  {
    bool ite;
    if (x_.tag == CBOR_Case_Map)
      ite = true;
    else
      ite = false;
    if (ite)
    {
      cbor_raw scrut0 = x_;
      option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
      scrut;
      if (scrut0.tag == CBOR_Case_Map)
        scrut =
          (
            (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry){
              .tag = Some,
              .v = scrut0.case_CBOR_Case_Map.cbor_map_ptr
            }
          );
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
        size_t
        res =
          CBOR_Pulse_Raw_Format_Serialize_ser_(e.cbor_map_entry_value,
            out,
            CBOR_Pulse_Raw_Format_Serialize_ser_(e.cbor_map_entry_key, out, off));
        pi = i_;
        pres = res;
        size_t i0 = pi;
        cond = i0 < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
      }
      return pres;
    }
    else
    {
      cbor_raw scrut = x_;
      Pulse_Lib_Slice_slice__uint8_t x2_;
      if (scrut.tag == CBOR_Case_Serialized_Map)
        x2_ = scrut.case_CBOR_Case_Serialized_Map.cbor_serialized_payload;
      else
        x2_ =
          KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
            "unreachable (pattern matches are exhaustive in F*)");
      size_t length = len__uint8_t(x2_);
      copy__uint8_t(split__uint8_t(split__uint8_t(out, res1).snd, length).fst, x2_);
      return res1 + length;
    }
  }
  else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_TAGGED)
  {
    bool ite0;
    if (x_.tag == CBOR_Case_Tagged)
      ite0 = true;
    else
      ite0 = false;
    if (ite0)
    {
      cbor_raw scrut = x_;
      cbor_raw ite;
      if (scrut.tag == CBOR_Case_Tagged)
        ite = *scrut.case_CBOR_Case_Tagged.cbor_tagged_ptr;
      else
        ite = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
      return CBOR_Pulse_Raw_Format_Serialize_ser_(ite, out, res1);
    }
    else
    {
      cbor_raw scrut = x_;
      Pulse_Lib_Slice_slice__uint8_t x2_;
      if (scrut.tag == CBOR_Case_Serialized_Tagged)
        x2_ = scrut.case_CBOR_Case_Serialized_Tagged.cbor_serialized_payload;
      else
        x2_ =
          KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
            "unreachable (pattern matches are exhaustive in F*)");
      size_t length = len__uint8_t(x2_);
      copy__uint8_t(split__uint8_t(split__uint8_t(out, res1).snd, length).fst, x2_);
      return res1 + length;
    }
  }
  else
    return res1;
}

static size_t ser(cbor_raw x1_, Pulse_Lib_Slice_slice__uint8_t out, size_t offset)
{
  return CBOR_Pulse_Raw_Format_Serialize_ser_(x1_, out, offset);
}

static size_t cbor_serialize(cbor_raw x, Pulse_Lib_Slice_slice__uint8_t output)
{
  return ser(x, output, (size_t)0U);
}

bool CBOR_Pulse_Raw_Format_Serialize_siz_(cbor_raw x_, size_t *out)
{
  header xh1 = cbor_raw_with_perm_get_header(x_);
  if (size_header(xh1, out))
  {
    initial_byte_t b = xh1.fst;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      cbor_raw scrut = x_;
      Pulse_Lib_Slice_slice__uint8_t ite;
      if (scrut.tag == CBOR_Case_String)
        ite = scrut.case_CBOR_Case_String.cbor_string_ptr;
      else
        ite =
          KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
            "unreachable (pattern matches are exhaustive in F*)");
      size_t length = len__uint8_t(ite);
      size_t cur = *out;
      if (cur < length)
        return false;
      else
      {
        *out = cur - length;
        return true;
      }
    }
    else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_ARRAY)
    {
      bool ite0;
      if (x_.tag == CBOR_Case_Array)
        ite0 = true;
      else
        ite0 = false;
      if (ite0)
      {
        cbor_raw scrut0 = x_;
        option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw
        scrut;
        if (scrut0.tag == CBOR_Case_Array)
          scrut =
            (
              (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw){
                .tag = Some,
                .v = scrut0.case_CBOR_Case_Array.cbor_array_ptr
              }
            );
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
          if
          (
            CBOR_Pulse_Raw_Format_Serialize_siz_(op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(a,
                i0),
              out)
          )
            pi = i0 + (size_t)1U;
          else
            pres = false;
          bool res = pres;
          size_t i = pi;
          cond = res && i < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
        }
        return pres;
      }
      else
      {
        cbor_raw scrut = x_;
        Pulse_Lib_Slice_slice__uint8_t ite;
        if (scrut.tag == CBOR_Case_Serialized_Array)
          ite = scrut.case_CBOR_Case_Serialized_Array.cbor_serialized_payload;
        else
          ite =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = len__uint8_t(ite);
        size_t cur = *out;
        if (cur < length)
          return false;
        else
        {
          *out = cur - length;
          return true;
        }
      }
    }
    else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_MAP)
    {
      bool ite0;
      if (x_.tag == CBOR_Case_Map)
        ite0 = true;
      else
        ite0 = false;
      if (ite0)
      {
        cbor_raw scrut0 = x_;
        option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
        scrut;
        if (scrut0.tag == CBOR_Case_Map)
          scrut =
            (
              (option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry){
                .tag = Some,
                .v = scrut0.case_CBOR_Case_Map.cbor_map_ptr
              }
            );
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
        bool res = pres;
        size_t i0 = pi;
        bool cond = res && i0 < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
        while (cond)
        {
          size_t i0 = pi;
          cbor_map_entry e = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i0);
          bool ite;
          if (CBOR_Pulse_Raw_Format_Serialize_siz_(e.cbor_map_entry_key, out))
            ite = CBOR_Pulse_Raw_Format_Serialize_siz_(e.cbor_map_entry_value, out);
          else
            ite = false;
          if (ite)
            pi = i0 + (size_t)1U;
          else
            pres = false;
          bool res = pres;
          size_t i = pi;
          cond = res && i < (size_t)argument_as_uint64(xh1.fst, xh1.snd);
        }
        return pres;
      }
      else
      {
        cbor_raw scrut = x_;
        Pulse_Lib_Slice_slice__uint8_t ite;
        if (scrut.tag == CBOR_Case_Serialized_Map)
          ite = scrut.case_CBOR_Case_Serialized_Map.cbor_serialized_payload;
        else
          ite =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = len__uint8_t(ite);
        size_t cur = *out;
        if (cur < length)
          return false;
        else
        {
          *out = cur - length;
          return true;
        }
      }
    }
    else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_TAGGED)
    {
      bool ite0;
      if (x_.tag == CBOR_Case_Tagged)
        ite0 = true;
      else
        ite0 = false;
      if (ite0)
      {
        cbor_raw scrut = x_;
        cbor_raw ite;
        if (scrut.tag == CBOR_Case_Tagged)
          ite = *scrut.case_CBOR_Case_Tagged.cbor_tagged_ptr;
        else
          ite = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
        return CBOR_Pulse_Raw_Format_Serialize_siz_(ite, out);
      }
      else
      {
        cbor_raw scrut = x_;
        Pulse_Lib_Slice_slice__uint8_t ite;
        if (scrut.tag == CBOR_Case_Serialized_Tagged)
          ite = scrut.case_CBOR_Case_Serialized_Tagged.cbor_serialized_payload;
        else
          ite =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        size_t length = len__uint8_t(ite);
        size_t cur = *out;
        if (cur < length)
          return false;
        else
        {
          *out = cur - length;
          return true;
        }
      }
    }
    else
      return true;
  }
  else
    return false;
}

static bool siz(cbor_raw x1_, size_t *out)
{
  return CBOR_Pulse_Raw_Format_Serialize_siz_(x1_, out);
}

static size_t cbor_size(cbor_raw x, size_t bound)
{
  size_t output = bound;
  if (siz(x, &output))
    return bound - output;
  else
    return (size_t)0U;
}

static size_t
cbor_serialize_tag(CBOR_Spec_Raw_Base_raw_uint64 tag, Pulse_Lib_Slice_slice__uint8_t output)
{
  header h = raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED, tag);
  size_t buf = len__uint8_t(output);
  if (size_header(h, &buf))
    return write_header(h, output, (size_t)0U);
  else
    return (size_t)0U;
}

static size_t
cbor_serialize_array_(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t off
)
{
  size_t rem = len__uint8_t(out) - off;
  header h = raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY, len);
  if (size_header(h, &rem))
  {
    size_t llen = write_header(h, out, off);
    Pulse_Lib_Slice_slice__uint8_t sp1 = split__uint8_t(out, llen).fst;
    if (!(off == (size_t)0U || off == len__uint8_t(sp1)))
    {
      size_t pn = len__uint8_t(sp1);
      size_t pl = off;
      while (pl > (size_t)0U)
      {
        size_t l1 = pl;
        size_t l_ = pn % l1;
        pn = l1;
        pl = l_;
      }
      size_t d = pn;
      size_t q = len__uint8_t(sp1) / d;
      size_t pi = (size_t)0U;
      while (pi < d)
      {
        size_t i = pi;
        uint8_t save = op_Array_Access__uint8_t(sp1, i);
        size_t pj = (size_t)0U;
        size_t pidx = i;
        while (pj < q - (size_t)1U)
        {
          size_t j = pj;
          size_t idx = pidx;
          size_t idx_;
          if (idx - (size_t)0U >= len__uint8_t(sp1) - off)
            idx_ = idx - (len__uint8_t(sp1) - off);
          else
            idx_ = idx + off - (size_t)0U;
          size_t j_ = j + (size_t)1U;
          op_Array_Assignment__uint8_t(sp1, idx, op_Array_Access__uint8_t(sp1, idx_));
          pj = j_;
          pidx = idx_;
        }
        op_Array_Assignment__uint8_t(sp1, pidx, save);
        pi = i + (size_t)1U;
      }
    }
    return llen;
  }
  else
    return (size_t)0U;
}

static size_t
cbor_serialize_array(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t off
)
{
  return cbor_serialize_array_(len, out, off);
}

static size_t
cbor_serialize_string(
  uint8_t ty,
  CBOR_Spec_Raw_Base_raw_uint64 off,
  Pulse_Lib_Slice_slice__uint8_t out
)
{
  size_t soff = (size_t)off.value;
  size_t rem = len__uint8_t(out) - soff;
  header h = raw_uint64_as_argument(ty, off);
  if (size_header(h, &rem))
  {
    size_t llen = write_header(h, out, soff);
    Pulse_Lib_Slice_slice__uint8_t sp1 = split__uint8_t(out, llen).fst;
    if (!(soff == (size_t)0U || soff == len__uint8_t(sp1)))
    {
      size_t pn = len__uint8_t(sp1);
      size_t pl = soff;
      while (pl > (size_t)0U)
      {
        size_t l = pl;
        size_t l_ = pn % l;
        pn = l;
        pl = l_;
      }
      size_t d = pn;
      size_t q = len__uint8_t(sp1) / d;
      size_t pi = (size_t)0U;
      while (pi < d)
      {
        size_t i = pi;
        uint8_t save = op_Array_Access__uint8_t(sp1, i);
        size_t pj = (size_t)0U;
        size_t pidx = i;
        while (pj < q - (size_t)1U)
        {
          size_t j = pj;
          size_t idx = pidx;
          size_t idx_;
          if (idx - (size_t)0U >= len__uint8_t(sp1) - soff)
            idx_ = idx - (len__uint8_t(sp1) - soff);
          else
            idx_ = idx + soff - (size_t)0U;
          size_t j_ = j + (size_t)1U;
          op_Array_Assignment__uint8_t(sp1, idx, op_Array_Access__uint8_t(sp1, idx_));
          pj = j_;
          pidx = idx_;
        }
        op_Array_Assignment__uint8_t(sp1, pidx, save);
        pi = i + (size_t)1U;
      }
    }
    return llen;
  }
  else
    return (size_t)0U;
}

static size_t
cbor_serialize_map_(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t off
)
{
  size_t rem = len__uint8_t(out) - off;
  header h = raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP, len);
  if (size_header(h, &rem))
  {
    size_t llen = write_header(h, out, off);
    Pulse_Lib_Slice_slice__uint8_t sp1 = split__uint8_t(out, llen).fst;
    if (!(off == (size_t)0U || off == len__uint8_t(sp1)))
    {
      size_t pn = len__uint8_t(sp1);
      size_t pl = off;
      while (pl > (size_t)0U)
      {
        size_t l1 = pl;
        size_t l_ = pn % l1;
        pn = l1;
        pl = l_;
      }
      size_t d = pn;
      size_t q = len__uint8_t(sp1) / d;
      size_t pi = (size_t)0U;
      while (pi < d)
      {
        size_t i = pi;
        uint8_t save = op_Array_Access__uint8_t(sp1, i);
        size_t pj = (size_t)0U;
        size_t pidx = i;
        while (pj < q - (size_t)1U)
        {
          size_t j = pj;
          size_t idx = pidx;
          size_t idx_;
          if (idx - (size_t)0U >= len__uint8_t(sp1) - off)
            idx_ = idx - (len__uint8_t(sp1) - off);
          else
            idx_ = idx + off - (size_t)0U;
          size_t j_ = j + (size_t)1U;
          op_Array_Assignment__uint8_t(sp1, idx, op_Array_Access__uint8_t(sp1, idx_));
          pj = j_;
          pidx = idx_;
        }
        op_Array_Assignment__uint8_t(sp1, pidx, save);
        pi = i + (size_t)1U;
      }
    }
    return llen;
  }
  else
    return (size_t)0U;
}

static size_t
cbor_serialize_map(
  CBOR_Spec_Raw_Base_raw_uint64 len,
  Pulse_Lib_Slice_slice__uint8_t out,
  size_t off
)
{
  return cbor_serialize_map_(len, out, off);
}

static int16_t cbor_match_compare_serialized_tagged(cbor_serialized c1, cbor_serialized c2)
{
  return lex_compare_bytes(c1.cbor_serialized_payload, c2.cbor_serialized_payload);
}

static int16_t cbor_match_compare_serialized_array(cbor_serialized c1, cbor_serialized c2)
{
  return lex_compare_bytes(c1.cbor_serialized_payload, c2.cbor_serialized_payload);
}

static int16_t cbor_match_compare_serialized_map(cbor_serialized c1, cbor_serialized c2)
{
  return lex_compare_bytes(c1.cbor_serialized_payload, c2.cbor_serialized_payload);
}

static uint8_t impl_major_type(cbor_raw x)
{
  if (x.tag == CBOR_Case_Simple)
    return CBOR_MAJOR_TYPE_SIMPLE_VALUE;
  else if (x.tag == CBOR_Case_Int)
    if (x.tag == CBOR_Case_Int)
      return x.case_CBOR_Case_Int.cbor_int_type;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  else if (x.tag == CBOR_Case_String)
    if (x.tag == CBOR_Case_String)
      return x.case_CBOR_Case_String.cbor_string_type;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
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
      return
        (
          (option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_){
            .tag = Some,
            .v = { .fst = s1, .snd = c2.case_CBOR_Case_Serialized_Tagged }
          }
        );
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
  int16_t c = impl_uint8_compare(ty1, impl_major_type(x2));
  if (c == (int16_t)0)
    if (ty1 == CBOR_MAJOR_TYPE_UINT64 || ty1 == CBOR_MAJOR_TYPE_NEG_INT64)
    {
      CBOR_Spec_Raw_Base_raw_uint64 i1;
      if (x1.tag == CBOR_Case_Int)
      {
        cbor_int c_ = x1.case_CBOR_Case_Int;
        i1 =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
      }
      else
        i1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Int)
      {
        cbor_int c_ = x2.case_CBOR_Case_Int;
        ite =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
      }
      else
        ite =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      return impl_raw_uint64_compare(i1, ite);
    }
    else if (ty1 == CBOR_MAJOR_TYPE_BYTE_STRING || ty1 == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      CBOR_Spec_Raw_Base_raw_uint64 i1;
      if (x1.tag == CBOR_Case_String)
      {
        cbor_string c_ = x1.case_CBOR_Case_String;
        i1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_string_size,
              .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr)
            }
          );
      }
      else
        i1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 ite0;
      if (x2.tag == CBOR_Case_String)
      {
        cbor_string c_ = x2.case_CBOR_Case_String;
        ite0 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_string_size,
              .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr)
            }
          );
      }
      else
        ite0 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      int16_t c1 = impl_raw_uint64_compare(i1, ite0);
      if (c1 == (int16_t)0)
      {
        Pulse_Lib_Slice_slice__uint8_t pl1;
        if (x1.tag == CBOR_Case_String)
          pl1 = x1.case_CBOR_Case_String.cbor_string_ptr;
        else
          pl1 =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        Pulse_Lib_Slice_slice__uint8_t ite;
        if (x2.tag == CBOR_Case_String)
          ite = x2.case_CBOR_Case_String.cbor_string_ptr;
        else
          ite =
            KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
              "unreachable (pattern matches are exhaustive in F*)");
        return lex_compare_bytes(pl1, ite);
      }
      else
        return c1;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_TAGGED)
    {
      CBOR_Spec_Raw_Base_raw_uint64 tag1;
      if (x1.tag == CBOR_Case_Tagged)
        tag1 = x1.case_CBOR_Case_Tagged.cbor_tagged_tag;
      else if (x1.tag == CBOR_Case_Serialized_Tagged)
        tag1 = x1.case_CBOR_Case_Serialized_Tagged.cbor_serialized_header;
      else
        tag1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Tagged)
        ite = x2.case_CBOR_Case_Tagged.cbor_tagged_tag;
      else if (x2.tag == CBOR_Case_Serialized_Tagged)
        ite = x2.case_CBOR_Case_Serialized_Tagged.cbor_serialized_header;
      else
        ite =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      int16_t c1 = impl_raw_uint64_compare(tag1, ite);
      if (c1 == (int16_t)0)
      {
        option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_
        scrut = cbor_pair_is_serialized(x1, x2);
        if (scrut.tag == Some)
        {
          __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized pair = scrut.v;
          return
            cbor_match_compare_serialized_tagged(fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair),
              snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair));
        }
        else
        {
          cbor_raw pl1 = cbor_match_tagged_get_payload(x1);
          return CBOR_Pulse_Raw_Compare_impl_cbor_compare(pl1, cbor_match_tagged_get_payload(x2));
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
        len1 = x1.case_CBOR_Case_Serialized_Array.cbor_serialized_header;
      else
        len1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 ite0;
      if (x2.tag == CBOR_Case_Array)
      {
        cbor_array c_ = x2.case_CBOR_Case_Array;
        ite0 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_array_length_size,
              .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
            }
          );
      }
      else if (x2.tag == CBOR_Case_Serialized_Array)
        ite0 = x2.case_CBOR_Case_Serialized_Array.cbor_serialized_header;
      else
        ite0 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      int16_t c1 = impl_raw_uint64_compare(len1, ite0);
      if (c1 == (int16_t)0)
      {
        option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_
        scrut0 = cbor_pair_is_serialized(x1, x2);
        if (scrut0.tag == Some)
        {
          __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized pair = scrut0.v;
          return
            cbor_match_compare_serialized_array(fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair),
              snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair));
        }
        else
        {
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
          pl1 = cbor_array_iterator_init(x1);
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
          pl2 = cbor_array_iterator_init(x2);
          bool fin1;
          if (pl1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
            fin1 = len__CBOR_Pulse_Raw_Type_cbor_raw(pl1.case_CBOR_Raw_Iterator_Slice) == (size_t)0U;
          else if (pl1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
            fin1 = cbor_serialized_array_iterator_is_empty(pl1.case_CBOR_Raw_Iterator_Serialized);
          else
            fin1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          bool fin2;
          if (pl2.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
            fin2 = len__CBOR_Pulse_Raw_Type_cbor_raw(pl2.case_CBOR_Raw_Iterator_Slice) == (size_t)0U;
          else if (pl2.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
            fin2 = cbor_serialized_array_iterator_is_empty(pl2.case_CBOR_Raw_Iterator_Serialized);
          else
            fin2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          if (fin1)
            if (fin2)
              return (int16_t)0;
            else
              return (int16_t)-1;
          else if (fin2)
            return (int16_t)1;
          else
          {
            CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw pi1 = pl1;
            CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw pi2 = pl2;
            int16_t pres = (int16_t)0;
            bool pfin1 = false;
            while (pres == (int16_t)0 && !pfin1)
            {
              CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw scrut0 = pi1;
              cbor_raw elt1;
              if (scrut0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
                i = scrut0.case_CBOR_Raw_Iterator_Slice;
                cbor_raw res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)0U);
                pi1 =
                  (
                    (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
                      .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
                      {
                        .case_CBOR_Raw_Iterator_Slice = split__CBOR_Pulse_Raw_Type_cbor_raw(i,
                          (size_t)1U).snd
                      }
                    }
                  );
                elt1 = res;
              }
              else if (scrut0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                elt1 =
                  cbor_serialized_array_iterator_next(&pi1,
                    scrut0.case_CBOR_Raw_Iterator_Serialized);
              else
                elt1 = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
              CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw scrut1 = pi2;
              cbor_raw ite0;
              if (scrut1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
                i = scrut1.case_CBOR_Raw_Iterator_Slice;
                cbor_raw res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(i, (size_t)0U);
                pi2 =
                  (
                    (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw){
                      .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
                      {
                        .case_CBOR_Raw_Iterator_Slice = split__CBOR_Pulse_Raw_Type_cbor_raw(i,
                          (size_t)1U).snd
                      }
                    }
                  );
                ite0 = res;
              }
              else if (scrut1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                ite0 =
                  cbor_serialized_array_iterator_next(&pi2,
                    scrut1.case_CBOR_Raw_Iterator_Serialized);
              else
                ite0 = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
              int16_t c2 = CBOR_Pulse_Raw_Compare_impl_cbor_compare(elt1, ite0);
              if (c2 == (int16_t)0)
              {
                CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                scrut0 = pi1;
                bool fin11;
                if (scrut0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
                  fin11 =
                    len__CBOR_Pulse_Raw_Type_cbor_raw(scrut0.case_CBOR_Raw_Iterator_Slice) ==
                      (size_t)0U;
                else if (scrut0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                  fin11 =
                    cbor_serialized_array_iterator_is_empty(scrut0.case_CBOR_Raw_Iterator_Serialized);
                else
                  fin11 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw scrut = pi2;
                bool ite;
                if (scrut.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
                  ite =
                    len__CBOR_Pulse_Raw_Type_cbor_raw(scrut.case_CBOR_Raw_Iterator_Slice) ==
                      (size_t)0U;
                else if (scrut.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                  ite =
                    cbor_serialized_array_iterator_is_empty(scrut.case_CBOR_Raw_Iterator_Serialized);
                else
                  ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                if (fin11 == ite)
                  pfin1 = fin11;
                else if (fin11)
                  pres = (int16_t)-1;
                else
                  pres = (int16_t)1;
              }
              else
                pres = c2;
            }
            return pres;
          }
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
        len1 = x1.case_CBOR_Case_Serialized_Map.cbor_serialized_header;
      else
        len1 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      CBOR_Spec_Raw_Base_raw_uint64 ite0;
      if (x2.tag == CBOR_Case_Map)
      {
        cbor_map c_ = x2.case_CBOR_Case_Map;
        ite0 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = c_.cbor_map_length_size,
              .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
            }
          );
      }
      else if (x2.tag == CBOR_Case_Serialized_Map)
        ite0 = x2.case_CBOR_Case_Serialized_Map.cbor_serialized_header;
      else
        ite0 =
          KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
            "unreachable (pattern matches are exhaustive in F*)");
      int16_t c1 = impl_raw_uint64_compare(len1, ite0);
      if (c1 == (int16_t)0)
      {
        option___CBOR_Pulse_Raw_Type_cbor_serialized___CBOR_Pulse_Raw_Type_cbor_serialized_
        scrut0 = cbor_pair_is_serialized(x1, x2);
        if (scrut0.tag == Some)
        {
          __CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized pair = scrut0.v;
          return
            cbor_match_compare_serialized_map(fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair),
              snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(pair));
        }
        else
        {
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
          pl1 = cbor_map_iterator_init(x1);
          CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
          pl2 = cbor_map_iterator_init(x2);
          bool fin1;
          if (pl1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
            fin1 =
              len__CBOR_Pulse_Raw_Type_cbor_map_entry(pl1.case_CBOR_Raw_Iterator_Slice) ==
                (size_t)0U;
          else if (pl1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
            fin1 = cbor_serialized_map_iterator_is_empty(pl1.case_CBOR_Raw_Iterator_Serialized);
          else
            fin1 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          bool fin2;
          if (pl2.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
            fin2 =
              len__CBOR_Pulse_Raw_Type_cbor_map_entry(pl2.case_CBOR_Raw_Iterator_Slice) ==
                (size_t)0U;
          else if (pl2.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
            fin2 = cbor_serialized_map_iterator_is_empty(pl2.case_CBOR_Raw_Iterator_Serialized);
          else
            fin2 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
          if (fin1)
            if (fin2)
              return (int16_t)0;
            else
              return (int16_t)-1;
          else if (fin2)
            return (int16_t)1;
          else
          {
            CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry pi1 = pl1;
            CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry pi2 = pl2;
            int16_t pres = (int16_t)0;
            bool pfin1 = false;
            while (pres == (int16_t)0 && !pfin1)
            {
              CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
              scrut0 = pi1;
              cbor_map_entry pelt1;
              if (scrut0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
                i = scrut0.case_CBOR_Raw_Iterator_Slice;
                cbor_map_entry
                res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i, (size_t)0U);
                pi1 =
                  (
                    (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
                      .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
                      {
                        .case_CBOR_Raw_Iterator_Slice = split__CBOR_Pulse_Raw_Type_cbor_map_entry(i,
                          (size_t)1U).snd
                      }
                    }
                  );
                pelt1 = res;
              }
              else if (scrut0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                pelt1 =
                  cbor_serialized_map_iterator_next(&pi1,
                    scrut0.case_CBOR_Raw_Iterator_Serialized);
              else
                pelt1 =
                  KRML_EABORT(cbor_map_entry,
                    "unreachable (pattern matches are exhaustive in F*)");
              CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
              scrut1 = pi2;
              cbor_map_entry pelt2;
              if (scrut1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
              {
                Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
                i = scrut1.case_CBOR_Raw_Iterator_Slice;
                cbor_map_entry
                res = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(i, (size_t)0U);
                pi2 =
                  (
                    (CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry){
                      .tag = CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice,
                      {
                        .case_CBOR_Raw_Iterator_Slice = split__CBOR_Pulse_Raw_Type_cbor_map_entry(i,
                          (size_t)1U).snd
                      }
                    }
                  );
                pelt2 = res;
              }
              else if (scrut1.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                pelt2 =
                  cbor_serialized_map_iterator_next(&pi2,
                    scrut1.case_CBOR_Raw_Iterator_Serialized);
              else
                pelt2 =
                  KRML_EABORT(cbor_map_entry,
                    "unreachable (pattern matches are exhaustive in F*)");
              int16_t
              c20 =
                CBOR_Pulse_Raw_Compare_impl_cbor_compare(pelt1.cbor_map_entry_key,
                  pelt2.cbor_map_entry_key);
              int16_t c2;
              if (c20 == (int16_t)0)
                c2 =
                  CBOR_Pulse_Raw_Compare_impl_cbor_compare(pelt1.cbor_map_entry_value,
                    pelt2.cbor_map_entry_value);
              else
                c2 = c20;
              if (c2 == (int16_t)0)
              {
                CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                scrut0 = pi1;
                bool fin11;
                if (scrut0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
                  fin11 =
                    len__CBOR_Pulse_Raw_Type_cbor_map_entry(scrut0.case_CBOR_Raw_Iterator_Slice) ==
                      (size_t)0U;
                else if (scrut0.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                  fin11 =
                    cbor_serialized_map_iterator_is_empty(scrut0.case_CBOR_Raw_Iterator_Serialized);
                else
                  fin11 = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                scrut = pi2;
                bool ite;
                if (scrut.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice)
                  ite =
                    len__CBOR_Pulse_Raw_Type_cbor_map_entry(scrut.case_CBOR_Raw_Iterator_Slice) ==
                      (size_t)0U;
                else if (scrut.tag == CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized)
                  ite =
                    cbor_serialized_map_iterator_is_empty(scrut.case_CBOR_Raw_Iterator_Serialized);
                else
                  ite = KRML_EABORT(bool, "unreachable (pattern matches are exhaustive in F*)");
                if (fin11 == ite)
                  pfin1 = fin11;
                else if (fin11)
                  pres = (int16_t)-1;
                else
                  pres = (int16_t)1;
              }
              else
                pres = c2;
            }
            return pres;
          }
        }
      }
      else
        return c1;
    }
    else
    {
      uint8_t val1;
      if (x1.tag == CBOR_Case_Simple)
        val1 = x1.case_CBOR_Case_Simple;
      else
        val1 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      uint8_t ite;
      if (x2.tag == CBOR_Case_Simple)
        ite = x2.case_CBOR_Case_Simple;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      return impl_uint8_compare(val1, ite);
    }
  else
    return c;
}

static int16_t cbor_raw_compare(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Compare_impl_cbor_compare(x1, x2);
}

static int16_t cbor_map_entry_raw_compare(cbor_map_entry x1, cbor_map_entry x2)
{
  return cbor_raw_compare(x1.cbor_map_entry_key, x2.cbor_map_entry_key);
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

bool
CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a
)
{
  size_t len = len__CBOR_Pulse_Raw_Type_cbor_map_entry(a);
  if (len < (size_t)2U)
    return true;
  else
  {
    size_t mi = len / (size_t)2U;
    __Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_map_entry
    scrut = split__CBOR_Pulse_Raw_Type_cbor_map_entry(a, mi);
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a2 = scrut.snd;
    if (!CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(scrut.fst))
      return false;
    else if (!CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(a2))
      return false;
    else
    {
      size_t pi1 = (size_t)0U;
      size_t pi2 = mi;
      bool pres = true;
      size_t i10 = pi1;
      size_t i20 = pi2;
      bool res20 = pres;
      bool cond = res20 && !(i10 == i20 || i20 == len__CBOR_Pulse_Raw_Type_cbor_map_entry(a));
      while (cond)
      {
        size_t i1 = pi1;
        cbor_map_entry x1 = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i1);
        size_t i20 = pi2;
        int16_t
        comp =
          cbor_map_entry_raw_compare(x1,
            op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(a, i20));
        if (comp == (int16_t)0)
          pres = false;
        else if (comp < (int16_t)0)
          pi1 = i1 + (size_t)1U;
        else
        {
          size_t i2_ = i20 + (size_t)1U;
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
          ac1 =
            split__CBOR_Pulse_Raw_Type_cbor_map_entry(split__CBOR_Pulse_Raw_Type_cbor_map_entry(a,
                i2_).fst,
              i1).snd;
          if (!(i20 - i1 == (size_t)0U || i20 - i1 == len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1)))
          {
            size_t pn = len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1);
            size_t pl = i20 - i1;
            while (pl > (size_t)0U)
            {
              size_t l3 = pl;
              size_t l_ = pn % l3;
              pn = l3;
              pl = l_;
            }
            size_t d = pn;
            size_t q = len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1) / d;
            size_t pi = (size_t)0U;
            while (pi < d)
            {
              size_t i = pi;
              cbor_map_entry save = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1, i);
              size_t pj = (size_t)0U;
              size_t pidx = i;
              while (pj < q - (size_t)1U)
              {
                size_t j = pj;
                size_t idx = pidx;
                size_t idx_;
                if (idx - (size_t)0U >= len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1) - (i20 - i1))
                  idx_ = idx - (len__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1) - (i20 - i1));
                else
                  idx_ = idx + i20 - i1 - (size_t)0U;
                size_t j_ = j + (size_t)1U;
                op_Array_Assignment__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1,
                  idx,
                  op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1, idx_));
                pj = j_;
                pidx = idx_;
              }
              op_Array_Assignment__CBOR_Pulse_Raw_Type_cbor_map_entry(ac1, pidx, save);
              pi = i + (size_t)1U;
            }
          }
          pi1 = i1 + (size_t)1U;
          pi2 = i2_;
        }
        size_t i10 = pi1;
        size_t i2 = pi2;
        bool res2 = pres;
        cond = res2 && !(i10 == i2 || i2 == len__CBOR_Pulse_Raw_Type_cbor_map_entry(a));
      }
      return pres;
    }
  }
}

static bool cbor_raw_sort(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a)
{
  return CBOR_Pulse_API_Det_Common_cbor_raw_sort_aux(a);
}

static int16_t impl_cbor_det_compare(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Compare_impl_cbor_compare(x1, x2);
}

void cbor_free_(cbor_freeable0 x)
{
  if (!(x.tag == CBOR_Copy_Unit))
    if (x.tag == CBOR_Copy_Bytes)
      KRML_HOST_FREE(x.case_CBOR_Copy_Bytes);
    else if (x.tag == CBOR_Copy_Box)
    {
      cbor_freeable_box b = x.case_CBOR_Copy_Box;
      KRML_HOST_FREE(b.box_cbor);
      cbor_free_(*b.box_footprint);
      KRML_HOST_FREE(b.box_footprint);
    }
    else if (x.tag == CBOR_Copy_Array)
    {
      cbor_freeable_array a = x.case_CBOR_Copy_Array;
      KRML_HOST_FREE(a.array_cbor);
      size_t pi = (size_t)0U;
      while (pi < a.array_len)
      {
        size_t i = pi;
        cbor_free_(a.array_footprint[i]);
        pi = i + (size_t)1U;
      }
      KRML_HOST_FREE(a.array_footprint);
    }
    else if (x.tag == CBOR_Copy_Map)
    {
      cbor_freeable_map a = x.case_CBOR_Copy_Map;
      KRML_HOST_FREE(a.map_cbor);
      size_t pi = (size_t)0U;
      while (pi < a.map_len)
      {
        size_t i = pi;
        cbor_freeable_map_entry x_ = a.map_footprint[i];
        cbor_free_(x_.map_entry_key);
        cbor_free_(x_.map_entry_value);
        pi = i + (size_t)1U;
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
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
from_array__CBOR_Pulse_Raw_Type_cbor_raw(cbor_raw *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw){ .elt = a, .len = alen });
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(cbor_map_entry *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry){ .elt = a, .len = alen });
}

cbor_freeable cbor_copy0(cbor_raw x)
{
  if (x.tag == CBOR_Case_Int)
  {
    uint8_t ty;
    if (x.tag == CBOR_Case_Int)
      ty = x.case_CBOR_Case_Int.cbor_int_type;
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 w;
    if (x.tag == CBOR_Case_Int)
    {
      cbor_int c_ = x.case_CBOR_Case_Int;
      w = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
    }
    else
      w =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Int,
            {
              .case_CBOR_Case_Int = {
                .cbor_int_type = ty,
                .cbor_int_size = w.size,
                .cbor_int_value = w.value
              }
            }
          },
          .footprint = { .tag = CBOR_Copy_Unit }
        }
      );
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    uint8_t ite;
    if (x.tag == CBOR_Case_Simple)
      ite = x.case_CBOR_Case_Simple;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_freeable){
          .cbor = { .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = ite } },
          .footprint = { .tag = CBOR_Copy_Unit }
        }
      );
  }
  else if (x.tag == CBOR_Case_String)
  {
    uint8_t ty;
    if (x.tag == CBOR_Case_String)
      ty = x.case_CBOR_Case_String.cbor_string_type;
    else
      ty = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 len;
    if (x.tag == CBOR_Case_String)
    {
      cbor_string c_ = x.case_CBOR_Case_String;
      len =
        (
          (CBOR_Spec_Raw_Base_raw_uint64){
            .size = c_.cbor_string_size,
            .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr)
          }
        );
    }
    else
      len =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    Pulse_Lib_Slice_slice__uint8_t pl;
    if (x.tag == CBOR_Case_String)
      pl = x.case_CBOR_Case_String.cbor_string_ptr;
    else
      pl =
        KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
          "unreachable (pattern matches are exhaustive in F*)");
    size_t len_sz = len__uint8_t(pl);
    KRML_CHECK_SIZE(sizeof (uint8_t), len_sz);
    uint8_t *v_ = KRML_HOST_CALLOC(len_sz, sizeof (uint8_t));
    Pulse_Lib_Slice_slice__uint8_t s_ = from_array__uint8_t(v_, len_sz);
    copy__uint8_t(s_, pl);
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_String,
            {
              .case_CBOR_Case_String = {
                .cbor_string_type = ty,
                .cbor_string_size = len.size,
                .cbor_string_ptr = s_
              }
            }
          },
          .footprint = { .tag = CBOR_Copy_Bytes, { .case_CBOR_Copy_Bytes = v_ } }
        }
      );
  }
  else if (x.tag == CBOR_Case_Tagged)
  {
    CBOR_Spec_Raw_Base_raw_uint64 tag;
    if (x.tag == CBOR_Case_Tagged)
      tag = x.case_CBOR_Case_Tagged.cbor_tagged_tag;
    else if (x.tag == CBOR_Case_Serialized_Tagged)
      tag = x.case_CBOR_Case_Serialized_Tagged.cbor_serialized_header;
    else
      tag =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    cbor_freeable cpl_ = cbor_copy0(cbor_match_tagged_get_payload(x));
    cbor_raw *b = KRML_HOST_MALLOC(sizeof (cbor_raw));
    if (b != NULL)
      b[0U] = cpl_.cbor;
    cbor_freeable0 *buf = KRML_HOST_MALLOC(sizeof (cbor_freeable0));
    if (buf != NULL)
      buf[0U] = cpl_.footprint;
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Tagged,
            { .case_CBOR_Case_Tagged = { .cbor_tagged_tag = tag, .cbor_tagged_ptr = b } }
          },
          .footprint = {
            .tag = CBOR_Copy_Box,
            { .case_CBOR_Copy_Box = { .box_cbor = b, .box_footprint = buf } }
          }
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
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw ar = a.cbor_array_ptr;
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
    while (pi < len)
    {
      size_t i = pi;
      cbor_freeable c_ = cbor_copy0(op_Array_Access__CBOR_Pulse_Raw_Type_cbor_raw(ar, i));
      v_[i] = c_.cbor;
      vf[i] = c_.footprint;
      pi = i + (size_t)1U;
    }
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Array,
            {
              .case_CBOR_Case_Array = {
                .cbor_array_length_size = len64.size,
                .cbor_array_ptr = from_array__CBOR_Pulse_Raw_Type_cbor_raw(v_, len)
              }
            }
          },
          .footprint = {
            .tag = CBOR_Copy_Array,
            {
              .case_CBOR_Copy_Array = { .array_cbor = v_, .array_footprint = vf, .array_len = len }
            }
          }
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
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry ar = a.cbor_map_ptr;
    size_t len = len__CBOR_Pulse_Raw_Type_cbor_map_entry(ar);
    KRML_CHECK_SIZE(sizeof (cbor_map_entry), len);
    cbor_map_entry *v_ = KRML_HOST_MALLOC(sizeof (cbor_map_entry) * len);
    if (v_ != NULL)
      for (uint32_t _i = 0U; _i < len; ++_i)
        v_[_i] =
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
        vf[_i] =
          (
            (cbor_freeable_map_entry){
              .map_entry_key = { .tag = CBOR_Copy_Unit },
              .map_entry_value = { .tag = CBOR_Copy_Unit }
            }
          );
    size_t pi = (size_t)0U;
    while (pi < len)
    {
      size_t i = pi;
      cbor_map_entry c = op_Array_Access__CBOR_Pulse_Raw_Type_cbor_map_entry(ar, i);
      cbor_freeable key_ = cbor_copy0(c.cbor_map_entry_key);
      cbor_freeable value_ = cbor_copy0(c.cbor_map_entry_value);
      v_[i] =
        ((cbor_map_entry){ .cbor_map_entry_key = key_.cbor, .cbor_map_entry_value = value_.cbor });
      vf[i] =
        (
          (cbor_freeable_map_entry){
            .map_entry_key = key_.footprint,
            .map_entry_value = value_.footprint
          }
        );
      pi = i + (size_t)1U;
    }
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Map,
            {
              .case_CBOR_Case_Map = {
                .cbor_map_length_size = len64.size,
                .cbor_map_ptr = from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(v_, len)
              }
            }
          },
          .footprint = {
            .tag = CBOR_Copy_Map,
            { .case_CBOR_Copy_Map = { .map_cbor = v_, .map_footprint = vf, .map_len = len } }
          }
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
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Serialized_Array,
            {
              .case_CBOR_Case_Serialized_Array = {
                .cbor_serialized_header = a.cbor_serialized_header,
                .cbor_serialized_payload = s_
              }
            }
          },
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
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Serialized_Map,
            {
              .case_CBOR_Case_Serialized_Map = {
                .cbor_serialized_header = a.cbor_serialized_header,
                .cbor_serialized_payload = s_
              }
            }
          },
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
    return
      (
        (cbor_freeable){
          .cbor = {
            .tag = CBOR_Case_Serialized_Tagged,
            {
              .case_CBOR_Case_Serialized_Tagged = {
                .cbor_serialized_header = a.cbor_serialized_header,
                .cbor_serialized_payload = s_
              }
            }
          },
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

cbor_raw dummy_cbor_det_t(void)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } });
}

cbor_raw cbor_det_reset_perm(cbor_raw x1)
{
  return cbor_raw_reset_perm_tot(x1);
}

static Pulse_Lib_Slice_slice__uint8_t arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

size_t cbor_det_validate(uint8_t *input, size_t input_len)
{
  return cbor_validate_det(arrayptr_to_slice_intro__uint8_t(input, input_len));
}

cbor_raw cbor_det_parse(uint8_t *input, size_t len)
{
  Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(input, len);
  return cbor_parse(s, len__uint8_t(s));
}

size_t cbor_det_size(cbor_raw x, size_t bound)
{
  return cbor_size(x, bound);
}

size_t cbor_det_serialize(cbor_raw x, uint8_t *output, size_t output_len)
{
  return cbor_serialize(x, arrayptr_to_slice_intro__uint8_t(output, output_len));
}

size_t cbor_det_serialize_safe(cbor_raw x, uint8_t *output, size_t output_len)
{
  size_t sz = cbor_det_size(x, output_len);
  if (sz == (size_t)0U)
    return (size_t)0U;
  else
    return cbor_det_serialize(x, output, sz);
}

bool cbor_det_impl_utf8_correct_from_array(uint8_t *s, size_t len)
{
  return impl_correct(arrayptr_to_slice_intro__uint8_t(s, len));
}

cbor_raw cbor_det_mk_simple_value(uint8_t v)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = v } });
}

cbor_raw cbor_det_mk_int64(uint8_t ty, uint64_t v)
{
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Int,
        {
          .case_CBOR_Case_Int = {
            .cbor_int_type = ty,
            .cbor_int_size = mk_raw_uint64(v).size,
            .cbor_int_value = mk_raw_uint64(v).value
          }
        }
      }
    );
}

cbor_raw cbor_det_mk_tagged(uint64_t tag, cbor_raw *r)
{
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Tagged,
        { .case_CBOR_Case_Tagged = { .cbor_tagged_tag = mk_raw_uint64(tag), .cbor_tagged_ptr = r } }
      }
    );
}

cbor_raw cbor_det_mk_string_from_arrayptr(uint8_t ty, uint8_t *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_String,
        {
          .case_CBOR_Case_String = {
            .cbor_string_type = ty,
            .cbor_string_size = mk_raw_uint64((uint64_t)len__uint8_t(s)).size,
            .cbor_string_ptr = s
          }
        }
      }
    );
}

cbor_raw cbor_det_mk_array_from_array(cbor_raw *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw
  s = from_array__CBOR_Pulse_Raw_Type_cbor_raw(a, (size_t)len);
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Array,
        {
          .case_CBOR_Case_Array = {
            .cbor_array_length_size = mk_raw_uint64((uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(s)).size,
            .cbor_array_ptr = s
          }
        }
      }
    );
}

cbor_map_entry cbor_det_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  return cbor_mk_map_entry(xk, xv);
}

cbor_raw cbor_det_mk_map_from_array(cbor_map_entry *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
  s = from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(a, (size_t)len);
  cbor_raw dest = dummy_cbor_det_t();
  bool ite;
  if (len__CBOR_Pulse_Raw_Type_cbor_map_entry(s) > (size_t)18446744073709551615ULL)
    ite = false;
  else if (cbor_raw_sort(s))
  {
    dest =
      (
        (cbor_raw){
          .tag = CBOR_Case_Map,
          {
            .case_CBOR_Case_Map = {
              .cbor_map_length_size = mk_raw_uint64((uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(s)).size,
              .cbor_map_ptr = s
            }
          }
        }
      );
    ite = true;
  }
  else
    ite = false;
  KRML_MAYBE_UNUSED_VAR(ite);
  return dest;
}

bool cbor_det_mk_map_from_array_safe(cbor_map_entry *a, uint64_t len, cbor_raw *dest)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry
  s = from_array__CBOR_Pulse_Raw_Type_cbor_map_entry(a, (size_t)len);
  if (len__CBOR_Pulse_Raw_Type_cbor_map_entry(s) > (size_t)18446744073709551615ULL)
    return false;
  else if (cbor_raw_sort(s))
  {
    *dest =
      (
        (cbor_raw){
          .tag = CBOR_Case_Map,
          {
            .case_CBOR_Case_Map = {
              .cbor_map_length_size = mk_raw_uint64((uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(s)).size,
              .cbor_map_ptr = s
            }
          }
        }
      );
    return true;
  }
  else
    return false;
}

bool cbor_det_equal(cbor_raw x1, cbor_raw x2)
{
  return CBOR_Pulse_Raw_Compare_impl_cbor_compare(x1, x2) == (int16_t)0;
}

uint8_t cbor_det_major_type(cbor_raw x)
{
  return impl_major_type(x);
}

uint8_t cbor_det_read_simple_value(cbor_raw x)
{
  if (x.tag == CBOR_Case_Simple)
    return x.case_CBOR_Case_Simple;
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
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_Int)
  {
    cbor_int c_ = x.case_CBOR_Case_Int;
    ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = c_.cbor_int_size, .value = c_.cbor_int_value });
  }
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

uint64_t cbor_det_get_string_length(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_String)
  {
    cbor_string c_ = x.case_CBOR_Case_String;
    ite =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = c_.cbor_string_size,
          .value = (uint64_t)len__uint8_t(c_.cbor_string_ptr)
        }
      );
  }
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

uint64_t cbor_det_get_tagged_tag(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_Tagged)
    ite = x.case_CBOR_Case_Tagged.cbor_tagged_tag;
  else if (x.tag == CBOR_Case_Serialized_Tagged)
    ite = x.case_CBOR_Case_Serialized_Tagged.cbor_serialized_header;
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

cbor_raw cbor_det_get_tagged_payload(cbor_raw x)
{
  return cbor_match_tagged_get_payload(x);
}

static uint8_t *slice_to_arrayptr_intro__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.elt;
}

uint8_t *cbor_det_get_string(cbor_raw x)
{
  Pulse_Lib_Slice_slice__uint8_t ite;
  if (x.tag == CBOR_Case_String)
    ite = x.case_CBOR_Case_String.cbor_string_ptr;
  else
    ite =
      KRML_EABORT(Pulse_Lib_Slice_slice__uint8_t,
        "unreachable (pattern matches are exhaustive in F*)");
  return slice_to_arrayptr_intro__uint8_t(ite);
}

uint64_t cbor_det_get_array_length(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_Array)
  {
    cbor_array c_ = x.case_CBOR_Case_Array;
    ite =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = c_.cbor_array_length_size,
          .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_raw(c_.cbor_array_ptr)
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Array)
    ite = x.case_CBOR_Case_Serialized_Array.cbor_serialized_header;
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_start(cbor_raw x)
{
  return cbor_array_iterator_init(x);
}

bool
cbor_det_array_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x
)
{
  return cbor_array_iterator_is_empty(x);
}

uint64_t
cbor_det_array_iterator_length(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x
)
{
  return cbor_array_iterator_length(x);
}

cbor_raw
cbor_det_array_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw *x
)
{
  return cbor_array_iterator_next(x);
}

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_truncate(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x,
  uint64_t len
)
{
  return cbor_array_iterator_truncate(x, len);
}

cbor_raw cbor_det_get_array_item(cbor_raw x, uint64_t i)
{
  return cbor_array_item(x, i);
}

uint64_t cbor_det_get_map_length(cbor_raw x)
{
  CBOR_Spec_Raw_Base_raw_uint64 ite;
  if (x.tag == CBOR_Case_Map)
  {
    cbor_map c_ = x.case_CBOR_Case_Map;
    ite =
      (
        (CBOR_Spec_Raw_Base_raw_uint64){
          .size = c_.cbor_map_length_size,
          .value = (uint64_t)len__CBOR_Pulse_Raw_Type_cbor_map_entry(c_.cbor_map_ptr)
        }
      );
  }
  else if (x.tag == CBOR_Case_Serialized_Map)
    ite = x.case_CBOR_Case_Serialized_Map.cbor_serialized_header;
  else
    ite =
      KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
        "unreachable (pattern matches are exhaustive in F*)");
  return ite.value;
}

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
cbor_det_map_iterator_start(cbor_raw x)
{
  return cbor_map_iterator_init(x);
}

bool
cbor_det_map_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry x
)
{
  return cbor_map_iterator_is_empty(x);
}

cbor_map_entry
cbor_det_map_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry *x
)
{
  return cbor_map_iterator_next(x);
}

cbor_raw cbor_det_map_entry_key(cbor_map_entry x2)
{
  return x2.cbor_map_entry_key;
}

cbor_raw cbor_det_map_entry_value(cbor_map_entry x2)
{
  return x2.cbor_map_entry_value;
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
  i = cbor_map_iterator_init(x);
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry pi = i;
  option__CBOR_Pulse_Raw_Type_cbor_raw pres = { .tag = None };
  bool pcont = !cbor_map_iterator_is_empty(i);
  while (pcont)
  {
    cbor_map_entry entry = cbor_map_iterator_next(&pi);
    int16_t comp = impl_cbor_det_compare(entry.cbor_map_entry_key, k);
    if (comp == (int16_t)0)
    {
      pres =
        ((option__CBOR_Pulse_Raw_Type_cbor_raw){ .tag = Some, .v = entry.cbor_map_entry_value });
      pcont = false;
    }
    else if (comp > (int16_t)0)
      pcont = false;
    else
      pcont = !cbor_map_iterator_is_empty(pi);
  }
  option__CBOR_Pulse_Raw_Type_cbor_raw scrut = pres;
  if (scrut.tag == None)
    return false;
  else if (scrut.tag == Some)
  {
    *dest = scrut.v;
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

size_t cbor_det_serialize_tag_to_array(uint64_t tag, uint8_t *out, size_t out_len)
{
  Pulse_Lib_Slice_slice__uint8_t sout = arrayptr_to_slice_intro__uint8_t(out, out_len);
  return cbor_serialize_tag(mk_raw_uint64(tag), sout);
}

size_t
cbor_det_serialize_array_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off)
{
  Pulse_Lib_Slice_slice__uint8_t sout = arrayptr_to_slice_intro__uint8_t(out, out_len);
  return cbor_serialize_array(mk_raw_uint64(len), sout, off);
}

size_t
cbor_det_serialize_string_to_array(uint8_t ty, uint64_t off, uint8_t *out, size_t out_len)
{
  Pulse_Lib_Slice_slice__uint8_t sout = arrayptr_to_slice_intro__uint8_t(out, out_len);
  return cbor_serialize_string(ty, mk_raw_uint64(off), sout);
}

bool
cbor_det_serialize_map_insert_to_array(uint8_t *out, size_t out_len, size_t off2, size_t off3)
{
  return cbor_raw_map_insert(arrayptr_to_slice_intro__uint8_t(out, out_len), off2, off3);
}

size_t cbor_det_serialize_map_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off)
{
  Pulse_Lib_Slice_slice__uint8_t sout = arrayptr_to_slice_intro__uint8_t(out, out_len);
  return cbor_serialize_map(mk_raw_uint64(len), sout, off);
}

cbor_raw cbor_get_from_freeable(cbor_freeable x)
{
  return x.cbor;
}

cbor_freeable cbor_copy(cbor_raw c)
{
  return cbor_copy0(c);
}

void cbor_free(cbor_freeable x)
{
  cbor_free0(x);
}

