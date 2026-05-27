

#include "internal/CBORDet.h"

static uint8_t get_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi)
{
  return ((uint32_t)x << (8U - hi) & 0xFFU) >> (8U - hi + lo);
}

static uint8_t set_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi, uint8_t v)
{
  return ((uint32_t)x & (uint32_t)~(255U >> (8U - (hi - lo)) << lo)) | (uint32_t)v << lo;
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

static size_t len__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.len;
}

static uint8_t op_Array_Access__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i)
{
  return a.elt[i];
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

static size_t append_n_before_sz(size_t off, size_t n, size_t cb)
{
  if (off >= cb)
    return (size_t)0U;
  else
  {
    size_t diff = cb - off;
    if (n <= diff)
      return n;
    else
      return diff;
  }
}

static size_t append_n_after_sz(size_t off, size_t n, size_t cb)
{
  return n - append_n_before_sz(off, n, cb);
}

static size_t append_off_before_sz(size_t off, size_t ob, size_t cb)
{
  size_t ite;
  if (off >= cb)
    ite = cb;
  else
    ite = off;
  return ob + ite;
}

static size_t append_off_after_sz(size_t off, size_t oa, size_t cb)
{
  size_t ite;
  if (off >= cb)
    ite = off - cb;
  else
    ite = (size_t)0U;
  return oa + ite;
}

static bool impl_correct(Pulse_Lib_Slice_slice__uint8_t s)
{
  bool pres = true;
  size_t pi = (size_t)0U;
  size_t len = len__uint8_t(s);
  while (pres && pi < len)
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

typedef struct __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t_s
{
  Pulse_Lib_Slice_slice__uint8_t fst;
  Pulse_Lib_Slice_slice__uint8_t snd;
}
__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t;

static __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
split__uint8_t(Pulse_Lib_Slice_slice__uint8_t s, size_t i)
{
  return
    (
      (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

static header read_header(Pulse_Lib_Slice_slice__uint8_t input)
{
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut = split__uint8_t(input, (size_t)1U);
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
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
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(input, offset2);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut.fst,
            .snd = scrut.snd
          }
        ).snd,
        off - offset2);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
    initial_byte_t
    x =
      read_initial_byte_t((
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = split__uint8_t(input, offset1);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).snd,
        off - offset1);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    initial_byte_t
    x =
      read_initial_byte_t((
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut = split__uint8_t(input, offset2);
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut0 =
            split__uint8_t((
                (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                  .fst = scrut.fst,
                  .snd = scrut.snd
                }
              ).snd,
              off1 - offset2);
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          return
            MIN_SIMPLE_VALUE_LONG_ARGUMENT <=
              op_Array_Access__uint8_t((
                  (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut = split__uint8_t(input, offset);
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 =
    split__uint8_t((
        (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut.fst,
          .snd = scrut.snd
        }
      ).snd,
      off1 - offset);
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  initial_byte_t
  x =
    read_initial_byte_t((
        (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
    return off1;
}

static bool
validate_recursive_step_count_leaf(
  Pulse_Lib_Slice_slice__uint8_t a,
  size_t bound,
  size_t *prem
)
{
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut = split__uint8_t(a, jump_header(a, (size_t)0U));
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  header
  h =
    read_header((
        (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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

static size_t impl_remaining_data_items_header(header h)
{
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

static size_t jump_recursive_step_count_leaf(Pulse_Lib_Slice_slice__uint8_t a)
{
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut = split__uint8_t(a, jump_header(a, (size_t)0U));
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  return
    impl_remaining_data_items_header(read_header((
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).fst));
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
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 = split__uint8_t(input, offset1);
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 =
          split__uint8_t((
              (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                .fst = scrut0.fst,
                .snd = scrut0.snd
              }
            ).snd,
            off1 - offset1);
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        header
        x =
          read_header((
              (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
            __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut = split__uint8_t(input, offset2);
            __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut0 =
              split__uint8_t((
                  (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                    .fst = scrut.fst,
                    .snd = scrut.snd
                  }
                ).snd,
                off2 - offset2);
            __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
            scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
            Pulse_Lib_Slice_slice__uint8_t
            x1 =
              (
                (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut = split__uint8_t(input, off);
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 =
          split__uint8_t((
              (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                .fst = scrut.fst,
                .snd = scrut.snd
              }
            ).snd,
            offset1 - off);
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        Pulse_Lib_Slice_slice__uint8_t
        input1 =
          (
            (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = split__uint8_t(input, off);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).snd,
        off10 - off);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    header
    x =
      read_header((
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut2.fst,
            .snd = scrut2.snd
          }
        ).fst);
    initial_byte_t b = x.fst;
    size_t off1;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
      off1 = off10 + (size_t)argument_as_uint64(x.fst, x.snd);
    else
      off1 = off10;
    poffset = off1;
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(input, off);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut3 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut.fst,
            .snd = scrut.snd
          }
        ).snd,
        off1 - off);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
    Pulse_Lib_Slice_slice__uint8_t
    input1 =
      (
        (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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

static size_t jump_raw_data_item_eta(Pulse_Lib_Slice_slice__uint8_t input, size_t offset)
{
  return jump_raw_data_item(input, offset);
}

static size_t
jump_nondep_then_raw_data_item_eta(Pulse_Lib_Slice_slice__uint8_t input, size_t offset)
{
  return jump_raw_data_item_eta(input, jump_raw_data_item_eta(input, offset));
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

static cbor_raw cbor_raw_read_match_aux(Pulse_Lib_Slice_slice__uint8_t input)
{
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = split__uint8_t(input, jump_header(input, (size_t)0U));
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.snd;
  header v1 = read_header(scrut1.fst);
  initial_byte_t
  b = dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(v1);
  long_argument
  la = dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(v1);
  if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
  {
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(input2, (size_t)argument_as_uint64(b, la));
    Pulse_Lib_Slice_slice__uint8_t
    input11 =
      (
        (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut.fst,
          .snd = scrut.snd
        }
      ).fst;
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == LongArgumentOther)
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
              .cbor_string_type = b.major_type,
              .cbor_string_size = ite.size,
              .cbor_string_ptr = input11
            }
          }
        }
      );
  }
  else if (b.major_type == CBOR_MAJOR_TYPE_ARRAY)
  {
    size_t n = (size_t)argument_as_uint64(b, la);
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Array,
          {
            .case_CBOR_Case_Array = {
              .cbor_array_length_size = ite.size,
              .cbor_array_ptr = {
                .tag = LowParse_PulseParse_Iterator_Type_Base,
                {
                  .case_Base = {
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    { .case_Serialized = { .count = n, .payload = input2 } }
                  }
                }
              }
            }
          }
        }
      );
  }
  else if (b.major_type == CBOR_MAJOR_TYPE_MAP)
  {
    size_t n = (size_t)argument_as_uint64(b, la);
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Map,
          {
            .case_CBOR_Case_Map = {
              .cbor_map_length_size = ite.size,
              .cbor_map_ptr = {
                .tag = LowParse_PulseParse_Iterator_Type_Base,
                {
                  .case_Base = {
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    { .case_Serialized = { .count = n, .payload = input2 } }
                  }
                }
              }
            }
          }
        }
      );
  }
  else if (b.major_type == CBOR_MAJOR_TYPE_TAGGED)
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Tagged_Serialized,
          {
            .case_CBOR_Case_Tagged_Serialized = {
              .cbor_tagged_serialized_tag = ite,
              .cbor_tagged_serialized_ptr = input2
            }
          }
        }
      );
  }
  else if (b.major_type == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
  {
    uint8_t ite;
    if (la.tag == LongArgumentOther)
      ite = b.additional_info;
    else if (la.tag == LongArgumentSimpleValue)
      ite = la.case_LongArgumentSimpleValue;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = ite } });
  }
  else
  {
    CBOR_Spec_Raw_Base_raw_uint64 ite0;
    if (la.tag == LongArgumentU8)
      ite0 =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == LongArgumentU16)
      ite0 =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == LongArgumentU32)
      ite0 =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == LongArgumentU64)
      ite0 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == LongArgumentOther)
      ite0 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite0 =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    CBOR_Spec_Raw_Base_raw_uint64 ite;
    if (la.tag == LongArgumentU8)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 1U, .value = (uint64_t)la.case_LongArgumentU8 });
    else if (la.tag == LongArgumentU16)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 2U, .value = (uint64_t)la.case_LongArgumentU16 });
    else if (la.tag == LongArgumentU32)
      ite =
        ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 3U, .value = (uint64_t)la.case_LongArgumentU32 });
    else if (la.tag == LongArgumentU64)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 4U, .value = la.case_LongArgumentU64 });
    else if (la.tag == LongArgumentOther)
      ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = (uint64_t)b.additional_info });
    else
      ite =
        KRML_EABORT(CBOR_Spec_Raw_Base_raw_uint64,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Int,
          {
            .case_CBOR_Case_Int = {
              .cbor_int_type = b.major_type,
              .cbor_int_size = ite0.size,
              .cbor_int_value = ite.value
            }
          }
        }
      );
  }
}

static cbor_raw cbor_raw_read(Pulse_Lib_Slice_slice__uint8_t input)
{
  return cbor_raw_read_match_aux(input);
}

static cbor_raw cbor_raw_read_fuel(Pulse_Lib_Slice_slice__uint8_t input)
{
  return cbor_raw_read_match_aux(input);
}

#define None 0
#define Some 1

typedef uint8_t option__uint8_t_tags;

typedef struct option__uint8_t_s
{
  option__uint8_t_tags tag;
  uint8_t v;
}
option__uint8_t;

static uint8_t cbor_raw_get_major_type_aux(cbor_raw x)
{
  option__uint8_t scrut;
  if (x.tag == CBOR_Case_Int)
    scrut = ((option__uint8_t){ .tag = Some, .v = x.case_CBOR_Case_Int.cbor_int_type });
  else if (x.tag == CBOR_Case_Simple)
    scrut = ((option__uint8_t){ .tag = Some, .v = CBOR_MAJOR_TYPE_SIMPLE_VALUE });
  else if (x.tag == CBOR_Case_String)
    scrut = ((option__uint8_t){ .tag = Some, .v = x.case_CBOR_Case_String.cbor_string_type });
  else if (x.tag == CBOR_Case_Array)
    scrut = ((option__uint8_t){ .tag = Some, .v = CBOR_MAJOR_TYPE_ARRAY });
  else if (x.tag == CBOR_Case_Map)
    scrut = ((option__uint8_t){ .tag = Some, .v = CBOR_MAJOR_TYPE_MAP });
  else if (x.tag == CBOR_Case_Tagged)
    scrut = ((option__uint8_t){ .tag = Some, .v = CBOR_MAJOR_TYPE_TAGGED });
  else if (x.tag == CBOR_Case_Tagged_Serialized)
    scrut = ((option__uint8_t){ .tag = Some, .v = CBOR_MAJOR_TYPE_TAGGED });
  else if (x.tag == CBOR_Case_Invalid)
    scrut = ((option__uint8_t){ .tag = None });
  else
    scrut = KRML_EABORT(option__uint8_t, "unreachable (pattern matches are exhaustive in F*)");
  if (scrut.tag == Some)
    return scrut.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static uint8_t cbor_raw_get_major_type(cbor_raw x)
{
  return cbor_raw_get_major_type_aux(x);
}

static Pulse_Lib_Slice_slice__uint8_t cbor_raw_get_string_aux(cbor_raw x)
{
  if (x.tag == CBOR_Case_String)
    return x.case_CBOR_Case_String.cbor_string_ptr;
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Array)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Map)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged_Serialized)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
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

static Pulse_Lib_Slice_slice__uint8_t cbor_raw_get_string(cbor_raw x)
{
  return cbor_raw_get_string_aux(x);
}

static cbor_raw cbor_raw_get_tagged_payload(cbor_raw x)
{
  if (x.tag == CBOR_Case_Tagged)
    return *x.case_CBOR_Case_Tagged.cbor_tagged_ptr;
  else if (x.tag == CBOR_Case_Tagged_Serialized)
    return cbor_raw_read(x.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_ptr);
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_String)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Array)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Map)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
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

#define EElement 0
#define ESerialized 1

typedef uint8_t elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags;

typedef struct elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags tag;
  union {
    cbor_raw case_EElement;
    Pulse_Lib_Slice_slice__uint8_t case_ESerialized;
  }
  ;
}
elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_raw_get_tagged_payload_aux_eos(cbor_raw x)
{
  if (x.tag == CBOR_Case_Tagged)
    return
      (
        (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = EElement,
          { .case_EElement = *x.case_CBOR_Case_Tagged.cbor_tagged_ptr }
        }
      );
  else if (x.tag == CBOR_Case_Tagged_Serialized)
    return
      (
        (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = ESerialized,
          { .case_ESerialized = x.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_ptr }
        }
      );
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_String)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Array)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Map)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
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

static LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_raw_get_array_aux(cbor_raw x)
{
  if (x.tag == CBOR_Case_Array)
    return x.case_CBOR_Case_Array.cbor_array_ptr;
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_String)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Map)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged_Serialized)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
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

static LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_raw_get_array(cbor_raw x)
{
  return cbor_raw_get_array_aux(x);
}

static LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_raw_get_map_aux(cbor_raw x)
{
  if (x.tag == CBOR_Case_Map)
    return x.case_CBOR_Case_Map.cbor_map_ptr;
  else if (x.tag == CBOR_Case_Invalid)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Int)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Simple)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_String)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Array)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (x.tag == CBOR_Case_Tagged_Serialized)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
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

static LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_raw_get_map(cbor_raw x)
{
  return cbor_raw_get_map_aux(x);
}

static size_t
len__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw s
)
{
  return s.len;
}

static size_t
base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw i
)
{
  if (i.tag == LowParse_PulseParse_Iterator_Type_Empty)
    return (size_t)0U;
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Singleton)
    return (size_t)1U;
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Slice)
    return len__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i.case_Slice);
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Serialized)
    return i.case_Serialized.count;
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
mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw i
)
{
  if (i.tag == LowParse_PulseParse_Iterator_Type_Base)
    return base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i.case_Base);
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Append)
    return i.case_Append.cb + i.case_Append.ca;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static bool
uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw projectee
)
{
  if (projectee.tag == LowParse_PulseParse_Iterator_Type_Base)
    return true;
  else
    return false;
}

typedef struct
__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw fst;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw snd;
}
__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static __Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw s,
  size_t i
)
{
  return
    (
      (__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

typedef struct
__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw fst;
  size_t snd;
}
__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t;

static LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
  __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
  x
)
{
  return x.fst;
}

static size_t
snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
  __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
  x
)
{
  return x.snd;
}

static LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
iterator_start_raw_data_item_fuel(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ml
)
{
  size_t total_sz = mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  if (total_sz == (size_t)0U)
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IBase,
          { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
        }
      );
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    r_node = ml;
    size_t r_off = (size_t)0U;
    size_t r_n = total_sz;
    bool pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    while (pcontinue)
    {
      size_t cur_off_v = r_off;
      size_t cur_n_v = r_n;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      scrut = r_node;
      if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = scrut.case_Append.after;
        size_t oa = scrut.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = scrut.case_Append.before;
        size_t ob = scrut.case_Append.ob;
        size_t cb = scrut.case_Append.cb;
        size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
        if (child_n_before > (size_t)0U)
        {
          size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ib = *before;
          r_node = ib;
          r_off = child_off_sz;
          r_n = child_n_before;
          pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
        }
        else
        {
          size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
          size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ia = *after;
          r_node = ia;
          r_off = child_off_sz;
          r_n = child_n_sz;
          pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
        }
      }
      else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    size_t cur_off_v = r_off;
    size_t cur_n_v = r_n;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut = r_node;
    __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
    res;
    if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = scrut.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw bi_;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi.case_Singleton;
        if (cur_n_v == (size_t)0U)
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    cur_off_v).snd,
                  cur_n_v).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = cur_off_v;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = { .count = cur_n_v, .payload = split__uint8_t(pl, poffset).snd }
              }
            }
          );
      }
      else
        bi_ =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      res =
        (
          (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
            .fst = bi_,
            .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
          }
        );
    }
    else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      res =
        KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "Pulse.Lib.Dv.unreachable");
    else
      res =
        KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "unreachable (pattern matches are exhaustive in F*)");
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi_ =
      fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t
    len_sz =
      snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t rest_sz = total_sz - len_sz;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi.case_Singleton;
        if (rest_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    len_sz).snd,
                  rest_sz).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = len_sz;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = { .count = rest_sz, .payload = split__uint8_t(pl, poffset).snd }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = append_n_before_sz(len_sz, rest_sz, cb);
      size_t ca__sz = append_n_after_sz(len_sz, rest_sz, cb);
      size_t ob__sz = append_off_before_sz(len_sz, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = append_off_after_sz(len_sz, oa, cb), .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
        }
      );
  }
}

static size_t
len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s
)
{
  return s.len;
}

static size_t
base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  i
)
{
  if (i.tag == LowParse_PulseParse_Iterator_Type_Empty)
    return (size_t)0U;
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Singleton)
    return (size_t)1U;
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Slice)
    return
      len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i.case_Slice);
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Serialized)
    return i.case_Serialized.count;
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
mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  i
)
{
  if (i.tag == LowParse_PulseParse_Iterator_Type_Base)
    return
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i.case_Base);
  else if (i.tag == LowParse_PulseParse_Iterator_Type_Append)
    return i.case_Append.cb + i.case_Append.ca;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static bool
uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  projectee
)
{
  if (projectee.tag == LowParse_PulseParse_Iterator_Type_Base)
    return true;
  else
    return false;
}

typedef struct
__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  fst;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  snd;
}
__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static __Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s,
  size_t i
)
{
  return
    (
      (__Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .fst = { .elt = s.elt, .len = i },
        .snd = { .elt = s.elt + i, .len = s.len - i }
      }
    );
}

typedef struct
__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  fst;
  size_t snd;
}
__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t;

static LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
  __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
  x
)
{
  return x.fst;
}

static size_t
snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
  __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
  x
)
{
  return x.snd;
}

static LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
iterator_start_map_entry_raw_data_item_fuel(
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml
)
{
  size_t
  total_sz =
    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  if (total_sz == (size_t)0U)
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IBase,
          { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
        }
      );
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    r_node = ml;
    size_t r_off = (size_t)0U;
    size_t r_n = total_sz;
    bool
    pcontinue =
      !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    while (pcontinue)
    {
      size_t cur_off_v = r_off;
      size_t cur_n_v = r_n;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      scrut = r_node;
      if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = scrut.case_Append.after;
        size_t oa = scrut.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = scrut.case_Append.before;
        size_t ob = scrut.case_Append.ob;
        size_t cb = scrut.case_Append.cb;
        size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
        if (child_n_before > (size_t)0U)
        {
          size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ib = *before;
          r_node = ib;
          r_off = child_off_sz;
          r_n = child_n_before;
          pcontinue =
            !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
        }
        else
        {
          size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
          size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ia = *after;
          r_node = ia;
          r_off = child_off_sz;
          r_n = child_n_sz;
          pcontinue =
            !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
        }
      }
      else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    size_t cur_off_v = r_off;
    size_t cur_n_v = r_n;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut = r_node;
    __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
    res;
    if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = scrut.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi_;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
        if (cur_n_v == (size_t)0U)
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    cur_off_v).snd,
                  cur_n_v).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = cur_off_v;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = { .count = cur_n_v, .payload = split__uint8_t(pl, poffset).snd }
              }
            }
          );
      }
      else
        bi_ =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      res =
        (
          (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
            .fst = bi_,
            .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
          }
        );
    }
    else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      res =
        KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "Pulse.Lib.Dv.unreachable");
    else
      res =
        KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "unreachable (pattern matches are exhaustive in F*)");
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi_ =
      fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t
    len_sz =
      snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t rest_sz = total_sz - len_sz;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      ite;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
        if (rest_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    len_sz).snd,
                  rest_sz).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = len_sz;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = { .count = rest_sz, .payload = split__uint8_t(pl, poffset).snd }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = append_n_before_sz(len_sz, rest_sz, cb);
      size_t ca__sz = append_n_after_sz(len_sz, rest_sz, cb);
      size_t ob__sz = append_off_before_sz(len_sz, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = append_off_after_sz(len_sz, oa, cb), .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
        }
      );
  }
}

static cbor_raw
op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw a,
  size_t i
)
{
  return a.elt[i];
}

static elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
iterator_next_eos_raw_data_item_fuel_byref(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *r
)
{
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw scrut0 = *r;
  if (scrut0.tag == LowParse_PulseParse_Iterator_Type_IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IBase;
    size_t len_sz = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              {
                .case_EElement = op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = ESerialized,
              {
                .case_ESerialized = split__uint8_t(pl_suffix,
                  jump_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        *r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
        return x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n1 = pn;
            size_t offset_ = jump_raw_data_item_eta(pl, poffset);
            pn = n1 - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        *r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IBase,
              { .case_IBase = ite }
            }
          );
        return x1;
      }
    }
  }
  else if (scrut0.tag == LowParse_PulseParse_Iterator_Type_IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = scrut0.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IPair.before;
    size_t len_sz = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              {
                .case_EElement = op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = ESerialized,
              {
                .case_ESerialized = split__uint8_t(pl_suffix,
                  jump_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        size_t total_sz = mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = ml;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz;
          bool pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
              if (child_n_before > (size_t)0U)
              {
                size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
                size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_ =
            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz1 =
            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz - len_sz1;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite1;
          if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = ml.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (rest_sz == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          len_sz1).snd,
                        rest_sz).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = len_sz1;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = rest_sz,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = ml.case_Append.after;
            size_t oa = ml.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = ml.case_Append.before;
            size_t ob = ml.case_Append.ob;
            size_t cb = ml.case_Append.cb;
            size_t cb__sz = append_n_before_sz(len_sz1, rest_sz, cb);
            size_t ca__sz = append_n_after_sz(len_sz1, rest_sz, cb);
            size_t ob__sz = append_off_before_sz(len_sz1, ob, cb);
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(len_sz1, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        *r = ite0;
        return x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n1 = pn;
            size_t offset_ = jump_raw_data_item_eta(pl, poffset);
            pn = n1 - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        *r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IPair,
              { .case_IPair = { .before = ite, .after = ml } }
            }
          );
        return x1;
      }
    }
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

static cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a,
  size_t i
)
{
  return a.elt[i];
}

typedef struct
elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags tag;
  union {
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw case_EElement;
    Pulse_Lib_Slice_slice__uint8_t case_ESerialized;
  }
  ;
}
elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
iterator_next_eos_map_entry_raw_data_item_fuel_byref(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  *r
)
{
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  scrut0 = *r;
  if (scrut0.tag == LowParse_PulseParse_Iterator_Type_IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IBase;
    size_t
    len_sz =
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              {
                .case_EElement = op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = ESerialized,
              {
                .case_ESerialized = split__uint8_t(pl_suffix,
                  jump_nondep_then_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        *r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
        return x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n1 = pn;
            size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
            pn = n1 - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        *r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IBase,
              { .case_IBase = ite }
            }
          );
        return x1;
      }
    }
  }
  else if (scrut0.tag == LowParse_PulseParse_Iterator_Type_IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = scrut0.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IPair.before;
    size_t
    len_sz =
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              {
                .case_EElement = op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = ESerialized,
              {
                .case_ESerialized = split__uint8_t(pl_suffix,
                  jump_nondep_then_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        size_t
        total_sz =
          mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = ml;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz;
          bool
          pcontinue =
            !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
              if (child_n_before > (size_t)0U)
              {
                size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue =
                  !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
                size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue =
                  !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_ =
            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz1 =
            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz - len_sz1;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite1;
          if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = ml.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (rest_sz == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          len_sz1).snd,
                        rest_sz).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = len_sz1;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = rest_sz,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = ml.case_Append.after;
            size_t oa = ml.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = ml.case_Append.before;
            size_t ob = ml.case_Append.ob;
            size_t cb = ml.case_Append.cb;
            size_t cb__sz = append_n_before_sz(len_sz1, rest_sz, cb);
            size_t ca__sz = append_n_after_sz(len_sz1, rest_sz, cb);
            size_t ob__sz = append_off_before_sz(len_sz1, ob, cb);
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(len_sz1, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        *r = ite0;
        return x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n1 = pn;
            size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
            pn = n1 - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        *r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IPair,
              { .case_IPair = { .before = ite, .after = ml } }
            }
          );
        return x1;
      }
    }
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

static int16_t
byte_compare_pts_to_parsed_data_item(
  Pulse_Lib_Slice_slice__uint8_t s1,
  Pulse_Lib_Slice_slice__uint8_t s2
)
{
  return lex_compare_bytes(s1, s2);
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
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = split__uint8_t(a, jump_header(a, (size_t)0U));
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
  header
  h =
    read_header((
        (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = split__uint8_t(a, jump_header(a, (size_t)0U));
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
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
        ite = (size_t)argument_as_uint64(h.fst, h.snd);
      else
        ite = (size_t)0U;
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut0 = split__uint8_t(input2, ite);
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
      Pulse_Lib_Slice_slice__uint8_t
      input3 =
        (
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut2.fst,
            .snd = scrut2.snd
          }
        ).snd;
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut3 = split__uint8_t(input3, jump_raw_data_item(input3, (size_t)0U));
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut4 = { .fst = scrut3.fst, .snd = scrut3.snd };
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut5 = { .fst = scrut4.fst, .snd = scrut4.snd };
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut6 = { .fst = scrut5.fst, .snd = scrut5.snd };
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut7 = { .fst = scrut6.fst, .snd = scrut6.snd };
      Pulse_Lib_Slice_slice__uint8_t input4 = scrut7.snd;
      Pulse_Lib_Slice_slice__uint8_t pkey = scrut7.fst;
      uint64_t ppairs = nbpairs - 1ULL;
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut = split__uint8_t(input4, jump_raw_data_item(input4, (size_t)0U));
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut8 = { .fst = scrut.fst, .snd = scrut.snd };
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut9 = { .fst = scrut8.fst, .snd = scrut8.snd };
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut10 = { .fst = scrut9.fst, .snd = scrut9.snd };
      Pulse_Lib_Slice_slice__uint8_t
      ptail =
        (
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut10.fst,
            .snd = scrut10.snd
          }
        ).snd;
      bool pres = true;
      while (pres && ppairs > 0ULL)
      {
        Pulse_Lib_Slice_slice__uint8_t tail = ptail;
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut = split__uint8_t(tail, jump_raw_data_item(tail, (size_t)0U));
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
        Pulse_Lib_Slice_slice__uint8_t key2 = scrut3.fst;
        Pulse_Lib_Slice_slice__uint8_t tail2 = scrut3.snd;
        if (impl_deterministically_encoded_cbor_map_key_order(pkey, key2))
        {
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut = split__uint8_t(tail2, jump_raw_data_item(tail2, (size_t)0U));
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
          Pulse_Lib_Slice_slice__uint8_t
          tail_ =
            (
              (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = split__uint8_t(input, (size_t)0U);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut1 =
      split__uint8_t((
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).snd,
        len - (size_t)0U);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut2 = { .fst = scrut1.fst, .snd = scrut1.snd };
    Pulse_Lib_Slice_slice__uint8_t
    input1 =
      (
        (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut = split__uint8_t(pi, (size_t)0U);
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 =
          split__uint8_t((
              (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                .fst = scrut.fst,
                .snd = scrut.snd
              }
            ).snd,
            off1 - (size_t)0U);
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
        header
        x =
          read_header((
              (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
          ite = off1;
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut2 = split__uint8_t(pi, ite);
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
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
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut = split__uint8_t(pi, (size_t)0U);
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut0 =
            split__uint8_t((
                (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
                  .fst = scrut.fst,
                  .snd = scrut.snd
                }
              ).snd,
              off1 - (size_t)0U);
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
          header
          x =
            read_header((
                (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
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
            ite = off1;
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut2 = split__uint8_t(pi, ite);
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
          scrut3 = { .fst = scrut2.fst, .snd = scrut2.snd };
          __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
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

static cbor_raw cbor_parse_valid(Pulse_Lib_Slice_slice__uint8_t input)
{
  size_t len = len__uint8_t(input);
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut = split__uint8_t(input, (size_t)0U);
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 =
    split__uint8_t((
        (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut.fst,
          .snd = scrut.snd
        }
      ).snd,
      len - (size_t)0U);
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  return
    cbor_raw_read((
        (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
          .fst = scrut1.fst,
          .snd = scrut1.snd
        }
      ).fst);
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
          {
            .case_CBOR_Case_String = {
              .cbor_string_type = v.cbor_string_type,
              .cbor_string_size = v.cbor_string_size,
              .cbor_string_ptr = v.cbor_string_ptr
            }
          }
        }
      );
  }
  else if (c.tag == CBOR_Case_Tagged)
  {
    cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = c.case_CBOR_Case_Tagged;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Tagged,
          {
            .case_CBOR_Case_Tagged = {
              .cbor_tagged_tag = v.cbor_tagged_tag,
              .cbor_tagged_ptr = v.cbor_tagged_ptr
            }
          }
        }
      );
  }
  else if (c.tag == CBOR_Case_Tagged_Serialized)
  {
    cbor_tagged_serialized v = c.case_CBOR_Case_Tagged_Serialized;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Tagged_Serialized,
          {
            .case_CBOR_Case_Tagged_Serialized = {
              .cbor_tagged_serialized_tag = v.cbor_tagged_serialized_tag,
              .cbor_tagged_serialized_ptr = v.cbor_tagged_serialized_ptr
            }
          }
        }
      );
  }
  else if (c.tag == CBOR_Case_Array)
  {
    cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = c.case_CBOR_Case_Array;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Array,
          {
            .case_CBOR_Case_Array = {
              .cbor_array_length_size = v.cbor_array_length_size,
              .cbor_array_ptr = v.cbor_array_ptr
            }
          }
        }
      );
  }
  else if (c.tag == CBOR_Case_Map)
  {
    cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = c.case_CBOR_Case_Map;
    return
      (
        (cbor_raw){
          .tag = CBOR_Case_Map,
          {
            .case_CBOR_Case_Map = {
              .cbor_map_length_size = v.cbor_map_length_size,
              .cbor_map_ptr = v.cbor_map_ptr
            }
          }
        }
      );
  }
  else
    return c;
}

static cbor_raw cbor_raw_reset_perm(cbor_raw c)
{
  return cbor_raw_reset_perm_tot(c);
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
  size_t off0 = poff;
  bool cond = uu___is_CInProgress(pres) && off0 < off2;
  while (cond)
  {
    size_t off = poff;
    Pulse_Lib_Slice_slice__uint8_t out2kv = split__uint8_t(out, off).snd;
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut0 = split__uint8_t(out2kv, off2 - off);
    Pulse_Lib_Slice_slice__uint8_t out2 = scrut0.fst;
    Pulse_Lib_Slice_slice__uint8_t outk = split__uint8_t(scrut0.snd, off3 - off2).fst;
    size_t offk = jump_raw_data_item(out2, (size_t)0U);
    __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
    scrut = split__uint8_t(out2, offk);
    Pulse_Lib_Slice_slice__uint8_t outvq = scrut.snd;
    int16_t c = lex_compare_bytes(scrut.fst, outk);
    if (c < (int16_t)0)
      poff = off + offk + jump_raw_data_item(outvq, (size_t)0U);
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
    size_t off0 = poff;
    cond = uu___is_CInProgress(pres) && off0 < off2;
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

typedef struct option__CBOR_Spec_Raw_EverParse_header_s
{
  option__uint8_t_tags tag;
  header v;
}
option__CBOR_Spec_Raw_EverParse_header;

static header cbor_raw_get_header_impl(cbor_raw xl)
{
  option__CBOR_Spec_Raw_EverParse_header scrut;
  if (xl.tag == CBOR_Case_Int)
  {
    cbor_int v = xl.case_CBOR_Case_Int;
    scrut =
      (
        (option__CBOR_Spec_Raw_EverParse_header){
          .tag = Some,
          .v = raw_uint64_as_argument(v.cbor_int_type,
            ((CBOR_Spec_Raw_Base_raw_uint64){ .size = v.cbor_int_size, .value = v.cbor_int_value }))
        }
      );
  }
  else if (xl.tag == CBOR_Case_Simple)
    scrut =
      (
        (option__CBOR_Spec_Raw_EverParse_header){
          .tag = Some,
          .v = simple_value_as_argument(xl.case_CBOR_Case_Simple)
        }
      );
  else if (xl.tag == CBOR_Case_String)
  {
    cbor_string v = xl.case_CBOR_Case_String;
    scrut =
      (
        (option__CBOR_Spec_Raw_EverParse_header){
          .tag = Some,
          .v = raw_uint64_as_argument(v.cbor_string_type,
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = v.cbor_string_size,
                .value = (uint64_t)len__uint8_t(v.cbor_string_ptr)
              }
            ))
        }
      );
  }
  else if (xl.tag == CBOR_Case_Array)
  {
    cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = xl.case_CBOR_Case_Array;
    scrut =
      (
        (option__CBOR_Spec_Raw_EverParse_header){
          .tag = Some,
          .v = raw_uint64_as_argument(CBOR_MAJOR_TYPE_ARRAY,
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = v.cbor_array_length_size,
                .value = (uint64_t)mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_array_ptr)
              }
            ))
        }
      );
  }
  else if (xl.tag == CBOR_Case_Map)
  {
    cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = xl.case_CBOR_Case_Map;
    scrut =
      (
        (option__CBOR_Spec_Raw_EverParse_header){
          .tag = Some,
          .v = raw_uint64_as_argument(CBOR_MAJOR_TYPE_MAP,
            (
              (CBOR_Spec_Raw_Base_raw_uint64){
                .size = v.cbor_map_length_size,
                .value = (uint64_t)mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_map_ptr)
              }
            ))
        }
      );
  }
  else if (xl.tag == CBOR_Case_Tagged)
    scrut =
      (
        (option__CBOR_Spec_Raw_EverParse_header){
          .tag = Some,
          .v = raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED,
            xl.case_CBOR_Case_Tagged.cbor_tagged_tag)
        }
      );
  else if (xl.tag == CBOR_Case_Tagged_Serialized)
    scrut =
      (
        (option__CBOR_Spec_Raw_EverParse_header){
          .tag = Some,
          .v = raw_uint64_as_argument(CBOR_MAJOR_TYPE_TAGGED,
            xl.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag)
        }
      );
  else if (xl.tag == CBOR_Case_Invalid)
    scrut = ((option__CBOR_Spec_Raw_EverParse_header){ .tag = None });
  else
    scrut =
      KRML_EABORT(option__CBOR_Spec_Raw_EverParse_header,
        "unreachable (pattern matches are exhaustive in F*)");
  if (scrut.tag == Some)
    return scrut.v;
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
  return cbor_raw_get_header_impl(xl);
}

static void
copy__uint8_t(Pulse_Lib_Slice_slice__uint8_t dst, Pulse_Lib_Slice_slice__uint8_t src)
{
  memcpy(dst.elt, src.elt, src.len * sizeof (uint8_t));
}

size_t
CBOR_Pulse_Raw_EverParse_Serialize_ser_(
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
    Pulse_Lib_Slice_slice__uint8_t x2_ = cbor_raw_get_string(x_);
    size_t length = len__uint8_t(x2_);
    copy__uint8_t(split__uint8_t(split__uint8_t(out, res1).snd, length).fst, x2_);
    return res1 + length;
  }
  else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_ARRAY)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    arr = cbor_raw_get_array(x_);
    size_t n = (size_t)argument_as_uint64(xh1.fst, xh1.snd);
    if (n == (size_t)0U)
      return res1;
    else
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      p_node = arr;
      size_t p_offset = res1;
      size_t p_remaining = n;
      while (p_remaining > (size_t)0U)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        cur = p_node;
        size_t cur_off = p_offset;
        size_t cur_rem = p_remaining;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        r_node = cur;
        size_t r_off = (size_t)0U;
        size_t r_n = cur_rem;
        bool pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur);
        while (pcontinue)
        {
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = scrut.case_Append.after;
            size_t oa = scrut.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = scrut.case_Append.before;
            size_t ob = scrut.case_Append.ob;
            size_t cb = scrut.case_Append.cb;
            size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
            if (child_n_before > (size_t)0U)
            {
              size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ib = *before;
              r_node = ib;
              r_off = child_off_sz;
              r_n = child_n_before;
              pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
            }
            else
            {
              size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
              size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ia = *after;
              r_node = ia;
              r_off = child_off_sz;
              r_n = child_n_sz;
              pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
            }
          }
          else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        size_t cur_off_v = r_off;
        size_t cur_n_v = r_n;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        scrut = r_node;
        __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
        res;
        if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
        {
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi = scrut.case_Base;
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_;
          if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
          {
            cbor_raw *s = bi.case_Singleton;
            if (cur_n_v == (size_t)0U)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                    { .case_Singleton = s }
                  }
                );
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Slice,
                  {
                    .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                        cur_off_v).snd,
                      cur_n_v).fst
                  }
                }
              );
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
          {
            Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
            size_t pn = cur_off_v;
            size_t poffset = (size_t)0U;
            while (pn > (size_t)0U)
            {
              size_t n1 = pn;
              size_t offset_ = jump_raw_data_item_eta(pl, poffset);
              pn = n1 - (size_t)1U;
              poffset = offset_;
            }
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                  {
                    .case_Serialized = {
                      .count = cur_n_v,
                      .payload = split__uint8_t(pl, poffset).snd
                    }
                  }
                }
              );
          }
          else
            bi_ =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          res =
            (
              (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                .fst = bi_,
                .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
              }
            );
        }
        else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
          res =
            KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
              "Pulse.Lib.Dv.unreachable");
        else
          res =
            KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
              "unreachable (pattern matches are exhaustive in F*)");
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        bi =
          fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        size_t
        chunk_len =
          snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl_bi = bi.case_Serialized.payload;
          size_t pn0 = chunk_len;
          size_t poffset0 = (size_t)0U;
          while (pn0 > (size_t)0U)
          {
            size_t n1 = pn0;
            size_t offset_ = jump_raw_data_item_eta(pl_bi, poffset0);
            pn0 = n1 - (size_t)1U;
            poffset0 = offset_;
          }
          size_t byte_len = poffset0;
          Pulse_Lib_Slice_slice__uint8_t
          out21 = split__uint8_t(split__uint8_t(out, cur_off).snd, byte_len).fst;
          copy__uint8_t(out21, split__uint8_t(pl_bi, byte_len).fst);
          size_t off_ = cur_off + byte_len;
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        {
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ss_bi = bi.case_Slice;
          size_t pres = cur_off;
          size_t pi = (size_t)0U;
          while (pi < chunk_len)
          {
            size_t i1 = pi;
            size_t off = pres;
            size_t i_ = i1 + (size_t)1U;
            size_t
            off_ =
              CBOR_Pulse_Raw_EverParse_Serialize_ser_(op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ss_bi,
                  i1),
                out,
                off);
            pi = i_;
            pres = off_;
          }
          size_t off_ = pres;
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          size_t off_ = CBOR_Pulse_Raw_EverParse_Serialize_ser_(*bi.case_Singleton, out, cur_off);
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (!(bi.tag == LowParse_PulseParse_Iterator_Type_Empty))
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
      }
      return p_offset;
    }
  }
  else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_MAP)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    arr = cbor_raw_get_map(x_);
    size_t n = (size_t)argument_as_uint64(xh1.fst, xh1.snd);
    if (n == (size_t)0U)
      return res1;
    else
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      p_node = arr;
      size_t p_offset = res1;
      size_t p_remaining = n;
      while (p_remaining > (size_t)0U)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        cur = p_node;
        size_t cur_off = p_offset;
        size_t cur_rem = p_remaining;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        r_node = cur;
        size_t r_off = (size_t)0U;
        size_t r_n = cur_rem;
        bool
        pcontinue =
          !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur);
        while (pcontinue)
        {
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = scrut.case_Append.after;
            size_t oa = scrut.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = scrut.case_Append.before;
            size_t ob = scrut.case_Append.ob;
            size_t cb = scrut.case_Append.cb;
            size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
            if (child_n_before > (size_t)0U)
            {
              size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ib = *before;
              r_node = ib;
              r_off = child_off_sz;
              r_n = child_n_before;
              pcontinue =
                !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
            }
            else
            {
              size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
              size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ia = *after;
              r_node = ia;
              r_off = child_off_sz;
              r_n = child_n_sz;
              pcontinue =
                !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
            }
          }
          else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        size_t cur_off_v = r_off;
        size_t cur_n_v = r_n;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        scrut = r_node;
        __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
        res;
        if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
        {
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi = scrut.case_Base;
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_;
          if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
          {
            cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
            if (cur_n_v == (size_t)0U)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                    { .case_Singleton = s }
                  }
                );
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Slice,
                  {
                    .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                        cur_off_v).snd,
                      cur_n_v).fst
                  }
                }
              );
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
          {
            Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
            size_t pn = cur_off_v;
            size_t poffset = (size_t)0U;
            while (pn > (size_t)0U)
            {
              size_t n1 = pn;
              size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
              pn = n1 - (size_t)1U;
              poffset = offset_;
            }
            bi_ =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                  {
                    .case_Serialized = {
                      .count = cur_n_v,
                      .payload = split__uint8_t(pl, poffset).snd
                    }
                  }
                }
              );
          }
          else
            bi_ =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          res =
            (
              (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                .fst = bi_,
                .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
              }
            );
        }
        else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
          res =
            KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
              "Pulse.Lib.Dv.unreachable");
        else
          res =
            KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
              "unreachable (pattern matches are exhaustive in F*)");
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        bi =
          fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        size_t
        chunk_len =
          snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl_bi = bi.case_Serialized.payload;
          size_t pn0 = chunk_len;
          size_t poffset0 = (size_t)0U;
          while (pn0 > (size_t)0U)
          {
            size_t n1 = pn0;
            size_t offset_ = jump_nondep_then_raw_data_item_eta(pl_bi, poffset0);
            pn0 = n1 - (size_t)1U;
            poffset0 = offset_;
          }
          size_t byte_len = poffset0;
          Pulse_Lib_Slice_slice__uint8_t
          out21 = split__uint8_t(split__uint8_t(out, cur_off).snd, byte_len).fst;
          copy__uint8_t(out21, split__uint8_t(pl_bi, byte_len).fst);
          size_t off_ = cur_off + byte_len;
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        {
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ss_bi = bi.case_Slice;
          size_t pres = cur_off;
          size_t pi = (size_t)0U;
          while (pi < chunk_len)
          {
            size_t i1 = pi;
            size_t off = pres;
            cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            e =
              op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ss_bi,
                i1);
            size_t i_ = i1 + (size_t)1U;
            size_t
            off_ =
              CBOR_Pulse_Raw_EverParse_Serialize_ser_(e.cbor_map_entry_value,
                out,
                CBOR_Pulse_Raw_EverParse_Serialize_ser_(e.cbor_map_entry_key, out, off));
            pi = i_;
            pres = off_;
          }
          size_t off_ = pres;
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw xv = *bi.case_Singleton;
          size_t
          off_ =
            CBOR_Pulse_Raw_EverParse_Serialize_ser_(xv.cbor_map_entry_value,
              out,
              CBOR_Pulse_Raw_EverParse_Serialize_ser_(xv.cbor_map_entry_key, out, cur_off));
          size_t new_rem = cur_rem - chunk_len;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite0;
          if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = cur.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (new_rem == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          chunk_len).snd,
                        new_rem).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = chunk_len;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = new_rem,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = cur.case_Append.after;
            size_t oa = cur.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = cur.case_Append.before;
            size_t ob = cur.case_Append.ob;
            size_t cb = cur.case_Append.cb;
            size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
            size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
            size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
            ite0 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite0 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          p_node = ite0;
          p_offset = off_;
          p_remaining = new_rem;
        }
        else if (!(bi.tag == LowParse_PulseParse_Iterator_Type_Empty))
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
      }
      return p_offset;
    }
  }
  else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_TAGGED)
    return CBOR_Pulse_Raw_EverParse_Serialize_ser_(cbor_raw_get_tagged_payload(x_), out, res1);
  else
    return res1;
}

static size_t ser(cbor_raw x1_, Pulse_Lib_Slice_slice__uint8_t out, size_t offset)
{
  return CBOR_Pulse_Raw_EverParse_Serialize_ser_(x1_, out, offset);
}

static size_t cbor_serialize(cbor_raw x, Pulse_Lib_Slice_slice__uint8_t output)
{
  return ser(x, output, (size_t)0U);
}

bool CBOR_Pulse_Raw_EverParse_Serialize_siz_(cbor_raw x_, size_t *out)
{
  header xh1 = cbor_raw_with_perm_get_header(x_);
  if (size_header(xh1, out))
  {
    initial_byte_t b = xh1.fst;
    if (b.major_type == CBOR_MAJOR_TYPE_BYTE_STRING || b.major_type == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      size_t length = len__uint8_t(cbor_raw_get_string(x_));
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
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      arr = cbor_raw_get_array(x_);
      size_t n = (size_t)argument_as_uint64(xh1.fst, xh1.snd);
      if (n == (size_t)0U)
        return true;
      else
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        p_node = arr;
        size_t p_remaining = n;
        bool p_result = true;
        while (p_result && p_remaining > (size_t)0U)
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          cur = p_node;
          size_t cur_rem = p_remaining;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = cur;
          size_t r_off = (size_t)0U;
          size_t r_n = cur_rem;
          bool pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
              if (child_n_before > (size_t)0U)
              {
                size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
                size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi =
            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          chunk_len =
            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
          {
            Pulse_Lib_Slice_slice__uint8_t pl_bi = bi.case_Serialized.payload;
            size_t pn0 = chunk_len;
            size_t poffset0 = (size_t)0U;
            while (pn0 > (size_t)0U)
            {
              size_t n1 = pn0;
              size_t offset_ = jump_raw_data_item_eta(pl_bi, poffset0);
              pn0 = n1 - (size_t)1U;
              poffset0 = offset_;
            }
            size_t byte_len = poffset0;
            size_t remaining = *out;
            bool chunk_res;
            if (byte_len <= remaining)
            {
              *out = remaining - byte_len;
              chunk_res = true;
            }
            else
              chunk_res = false;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
              size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          {
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ss_bi = bi.case_Slice;
            bool pres = true;
            size_t pi = (size_t)0U;
            while (pres && pi < chunk_len)
            {
              size_t i1 = pi;
              if
              (
                CBOR_Pulse_Raw_EverParse_Serialize_siz_(op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ss_bi,
                    i1),
                  out)
              )
                pi = i1 + (size_t)1U;
              else
                pres = false;
            }
            bool chunk_res = pres;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
              size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
          {
            bool chunk_res = CBOR_Pulse_Raw_EverParse_Serialize_siz_(*bi.case_Singleton, out);
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
              size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (!(bi.tag == LowParse_PulseParse_Iterator_Type_Empty))
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        return p_result;
      }
    }
    else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_MAP)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      arr = cbor_raw_get_map(x_);
      size_t n = (size_t)argument_as_uint64(xh1.fst, xh1.snd);
      if (n == (size_t)0U)
        return true;
      else
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        p_node = arr;
        size_t p_remaining = n;
        bool p_result = true;
        while (p_result && p_remaining > (size_t)0U)
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          cur = p_node;
          size_t cur_rem = p_remaining;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = cur;
          size_t r_off = (size_t)0U;
          size_t r_n = cur_rem;
          bool
          pcontinue =
            !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
              if (child_n_before > (size_t)0U)
              {
                size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue =
                  !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
                size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue =
                  !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n1 = pn;
                size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                pn = n1 - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi =
            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          chunk_len =
            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
          {
            Pulse_Lib_Slice_slice__uint8_t pl_bi = bi.case_Serialized.payload;
            size_t pn0 = chunk_len;
            size_t poffset0 = (size_t)0U;
            while (pn0 > (size_t)0U)
            {
              size_t n1 = pn0;
              size_t offset_ = jump_nondep_then_raw_data_item_eta(pl_bi, poffset0);
              pn0 = n1 - (size_t)1U;
              poffset0 = offset_;
            }
            size_t byte_len = poffset0;
            size_t remaining = *out;
            bool chunk_res;
            if (byte_len <= remaining)
            {
              *out = remaining - byte_len;
              chunk_res = true;
            }
            else
              chunk_res = false;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
              size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          {
            Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ss_bi = bi.case_Slice;
            bool pres = true;
            size_t pi = (size_t)0U;
            while (pres && pi < chunk_len)
            {
              size_t i1 = pi;
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              e =
                op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ss_bi,
                  i1);
              bool ite;
              if (CBOR_Pulse_Raw_EverParse_Serialize_siz_(e.cbor_map_entry_key, out))
                ite = CBOR_Pulse_Raw_EverParse_Serialize_siz_(e.cbor_map_entry_value, out);
              else
                ite = false;
              if (ite)
                pi = i1 + (size_t)1U;
              else
                pres = false;
            }
            bool chunk_res = pres;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
              size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
          {
            cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw xv = *bi.case_Singleton;
            bool chunk_res;
            if (CBOR_Pulse_Raw_EverParse_Serialize_siz_(xv.cbor_map_entry_key, out))
              chunk_res = CBOR_Pulse_Raw_EverParse_Serialize_siz_(xv.cbor_map_entry_value, out);
            else
              chunk_res = false;
            size_t new_rem = cur_rem - chunk_len;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            new_node;
            if (cur.tag == LowParse_PulseParse_Iterator_Type_Base)
            {
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              bi1 = cur.case_Base;
              LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              ite;
              if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
              {
                cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
                if (new_rem == (size_t)0U)
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Empty
                      }
                    );
                else
                  ite =
                    (
                      (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                        .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                        { .case_Singleton = s }
                      }
                    );
              }
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Slice,
                      {
                        .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                            chunk_len).snd,
                          new_rem).fst
                      }
                    }
                  );
              else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
              {
                Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
                size_t pn = chunk_len;
                size_t poffset = (size_t)0U;
                while (pn > (size_t)0U)
                {
                  size_t n1 = pn;
                  size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                  pn = n1 - (size_t)1U;
                  poffset = offset_;
                }
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                      {
                        .case_Serialized = {
                          .count = new_rem,
                          .payload = split__uint8_t(pl, poffset).snd
                        }
                      }
                    }
                  );
              }
              else
                ite =
                  KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                    "unreachable (pattern matches are exhaustive in F*)");
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Base,
                    { .case_Base = ite }
                  }
                );
            }
            else if (cur.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = cur.case_Append.after;
              size_t oa = cur.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = cur.case_Append.before;
              size_t ob = cur.case_Append.ob;
              size_t cb = cur.case_Append.cb;
              size_t cb__sz = append_n_before_sz(chunk_len, new_rem, cb);
              size_t ca__sz = append_n_after_sz(chunk_len, new_rem, cb);
              size_t ob__sz = append_off_before_sz(chunk_len, ob, cb);
              new_node =
                (
                  (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Append,
                    {
                      .case_Append = {
                        .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                        .oa = append_off_after_sz(chunk_len, oa, cb), .after = after
                      }
                    }
                  }
                );
            }
            else
              new_node =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            if (chunk_res)
            {
              p_node = new_node;
              p_remaining = new_rem;
            }
            else
            {
              p_node = new_node;
              p_remaining = new_rem;
              p_result = false;
            }
          }
          else if (!(bi.tag == LowParse_PulseParse_Iterator_Type_Empty))
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
        return p_result;
      }
    }
    else if (xh1.fst.major_type == CBOR_MAJOR_TYPE_TAGGED)
      return CBOR_Pulse_Raw_EverParse_Serialize_siz_(cbor_raw_get_tagged_payload(x_), out);
    else
      return true;
  }
  else
    return false;
}

static bool siz(cbor_raw x1_, size_t *out)
{
  return CBOR_Pulse_Raw_EverParse_Serialize_siz_(x1_, out);
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

static option__uint8_t cbor_raw_simple_value(cbor_raw x)
{
  if (x.tag == CBOR_Case_Simple)
    return ((option__uint8_t){ .tag = Some, .v = x.case_CBOR_Case_Simple });
  else
    return ((option__uint8_t){ .tag = None });
}

static uint8_t cbor_raw_read_simple_value(cbor_raw x)
{
  option__uint8_t x0 = cbor_raw_simple_value(x);
  if (x0.tag == Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct option__uint64_t_s
{
  option__uint8_t_tags tag;
  uint64_t v;
}
option__uint64_t;

static option__uint64_t cbor_raw_int64_value(cbor_raw x)
{
  if (x.tag == CBOR_Case_Int)
    return ((option__uint64_t){ .tag = Some, .v = x.case_CBOR_Case_Int.cbor_int_value });
  else
    return ((option__uint64_t){ .tag = None });
}

static uint64_t cbor_raw_read_int64_value(cbor_raw x)
{
  option__uint64_t x0 = cbor_raw_int64_value(x);
  if (x0.tag == Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static option__uint64_t cbor_raw_tagged_tag(cbor_raw x)
{
  if (x.tag == CBOR_Case_Tagged)
    return ((option__uint64_t){ .tag = Some, .v = x.case_CBOR_Case_Tagged.cbor_tagged_tag.value });
  else if (x.tag == CBOR_Case_Tagged_Serialized)
    return
      (
        (option__uint64_t){
          .tag = Some,
          .v = x.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag.value
        }
      );
  else
    return ((option__uint64_t){ .tag = None });
}

static uint64_t cbor_raw_read_tagged_tag(cbor_raw x)
{
  option__uint64_t x0 = cbor_raw_tagged_tag(x);
  if (x0.tag == Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static option__uint64_t cbor_raw_array_length(cbor_raw x)
{
  if (x.tag == CBOR_Case_Array)
    return
      (
        (option__uint64_t){
          .tag = Some,
          .v = (uint64_t)mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_CBOR_Case_Array.cbor_array_ptr)
        }
      );
  else
    return ((option__uint64_t){ .tag = None });
}

static uint64_t cbor_raw_read_array_length(cbor_raw x)
{
  option__uint64_t x0 = cbor_raw_array_length(x);
  if (x0.tag == Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static option__uint64_t cbor_raw_map_length(cbor_raw x)
{
  if (x.tag == CBOR_Case_Map)
    return
      (
        (option__uint64_t){
          .tag = Some,
          .v = (uint64_t)mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_CBOR_Case_Map.cbor_map_ptr)
        }
      );
  else
    return ((option__uint64_t){ .tag = None });
}

static uint64_t cbor_raw_read_map_length(cbor_raw x)
{
  option__uint64_t x0 = cbor_raw_map_length(x);
  if (x0.tag == Some)
    return x0.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static cbor_raw cbor_mk_simple_value(uint8_t v)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = v } });
}

static cbor_raw cbor_mk_int64(uint8_t ty, uint64_t v)
{
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Int,
        {
          .case_CBOR_Case_Int = {
            .cbor_int_type = ty,
            .cbor_int_size = mk_raw_uint64(v).size,
            .cbor_int_value = v
          }
        }
      }
    );
}

static cbor_raw cbor_mk_string(uint8_t ty, Pulse_Lib_Slice_slice__uint8_t s)
{
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

static cbor_raw cbor_mk_tagged(uint64_t tag, cbor_raw *r)
{
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Tagged,
        { .case_CBOR_Case_Tagged = { .cbor_tagged_tag = mk_raw_uint64(tag), .cbor_tagged_ptr = r } }
      }
    );
}

static cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  return
    (
      (cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .cbor_map_entry_key = xk,
        .cbor_map_entry_value = xv
      }
    );
}

static cbor_raw
cbor_mk_array(
  uint8_t len_size,
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ml
)
{
  mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Array,
        { .case_CBOR_Case_Array = { .cbor_array_length_size = len_size, .cbor_array_ptr = ml } }
      }
    );
}

static cbor_raw
cbor_mk_map(
  uint8_t len_size,
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml
)
{
  mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  return
    (
      (cbor_raw){
        .tag = CBOR_Case_Map,
        { .case_CBOR_Case_Map = { .cbor_map_length_size = len_size, .cbor_map_ptr = ml } }
      }
    );
}

static cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_raw_read_map_entry(Pulse_Lib_Slice_slice__uint8_t input)
{
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut = split__uint8_t(input, jump_raw_data_item(input, (size_t)0U));
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  scrut1 = { .fst = scrut0.fst, .snd = scrut0.snd };
  Pulse_Lib_Slice_slice__uint8_t input2 = scrut1.snd;
  cbor_raw xk = cbor_raw_read(scrut1.fst);
  return cbor_mk_map_entry(xk, cbor_raw_read(input2));
}

typedef struct
__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  cbor_raw fst;
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw snd;
}
__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static __CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
iterator_next_raw_data_item(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x
)
{
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw r = x;
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw scrut0 = r;
  elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw scrut1;
  if (scrut0.tag == LowParse_PulseParse_Iterator_Type_IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IBase;
    size_t len_sz = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
      scrut1 =
        KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "Pulse.Lib.Dv.unreachable");
    else
    {
      elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              {
                .case_EElement = op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = jump_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = ESerialized,
              {
                .case_ESerialized = split__uint8_t(pl_suffix,
                  jump_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
        scrut1 = x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n = pn;
            size_t offset_ = jump_raw_data_item_eta(pl, poffset);
            pn = n - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IBase,
              { .case_IBase = ite }
            }
          );
        scrut1 = x1;
      }
    }
  }
  else if (scrut0.tag == LowParse_PulseParse_Iterator_Type_IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = scrut0.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IPair.before;
    size_t len_sz = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
      scrut1 =
        KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "Pulse.Lib.Dv.unreachable");
    else
    {
      elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              {
                .case_EElement = op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = jump_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = ESerialized,
              {
                .case_ESerialized = split__uint8_t(pl_suffix,
                  jump_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        size_t total_sz = mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = ml;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz;
          bool pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
              if (child_n_before > (size_t)0U)
              {
                size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
                size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n = pn;
                size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                pn = n - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_ =
            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz1 =
            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz - len_sz1;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite1;
          if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = ml.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_raw *s = bi1.case_Singleton;
              if (rest_sz == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          len_sz1).snd,
                        rest_sz).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = len_sz1;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n = pn;
                size_t offset_ = jump_raw_data_item_eta(pl, poffset);
                pn = n - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = rest_sz,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = ml.case_Append.after;
            size_t oa = ml.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = ml.case_Append.before;
            size_t ob = ml.case_Append.ob;
            size_t cb = ml.case_Append.cb;
            size_t cb__sz = append_n_before_sz(len_sz1, rest_sz, cb);
            size_t ca__sz = append_n_after_sz(len_sz1, rest_sz, cb);
            size_t ob__sz = append_off_before_sz(len_sz1, ob, cb);
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(len_sz1, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        r = ite0;
        scrut1 = x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n = pn;
            size_t offset_ = jump_raw_data_item_eta(pl, poffset);
            pn = n - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IPair,
              { .case_IPair = { .before = ite, .after = ml } }
            }
          );
        scrut1 = x1;
      }
    }
  }
  else
    scrut1 =
      KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        "unreachable (pattern matches are exhaustive in F*)");
  cbor_raw elt;
  if (scrut1.tag == EElement)
    elt = scrut1.case_EElement;
  else if (scrut1.tag == ESerialized)
    elt = cbor_raw_read(scrut1.case_ESerialized);
  else
    elt = KRML_EABORT(cbor_raw, "unreachable (pattern matches are exhaustive in F*)");
  return
    (
      (__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .fst = elt,
        .snd = r
      }
    );
}

typedef struct
__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw fst;
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  snd;
}
__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static __CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
iterator_next_map_entry_raw_data_item(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  x
)
{
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  r = x;
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  scrut0 = r;
  elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  scrut1;
  if (scrut0.tag == LowParse_PulseParse_Iterator_Type_IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IBase;
    size_t
    len_sz =
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
      scrut1 =
        KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "Pulse.Lib.Dv.unreachable");
    else
    {
      elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              {
                .case_EElement = op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = ESerialized,
              {
                .case_ESerialized = split__uint8_t(pl_suffix,
                  jump_nondep_then_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IBase,
              { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
            }
          );
        scrut1 = x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n = pn;
            size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
            pn = n - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IBase,
              { .case_IBase = ite }
            }
          );
        scrut1 = x1;
      }
    }
  }
  else if (scrut0.tag == LowParse_PulseParse_Iterator_Type_IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = scrut0.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = scrut0.case_IPair.before;
    size_t
    len_sz =
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    if (len_sz == (size_t)0U)
      scrut1 =
        KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "Pulse.Lib.Dv.unreachable");
    else
    {
      elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      x1;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "Pulse.Lib.Dv.unreachable");
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              { .case_EElement = *bi.case_Singleton }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = EElement,
              {
                .case_EElement = op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U)
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        Pulse_Lib_Slice_slice__uint8_t pl_suffix = split__uint8_t(pl, poffset).snd;
        x1 =
          (
            (elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = ESerialized,
              {
                .case_ESerialized = split__uint8_t(pl_suffix,
                  jump_nondep_then_raw_data_item_eta(pl_suffix, (size_t)0U)).fst
              }
            }
          );
      }
      else
        x1 =
          KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      if (len_sz == (size_t)1U)
      {
        size_t
        total_sz =
          mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite0;
        if (total_sz == (size_t)0U)
          ite0 =
            (
              (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_IBase,
                { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
              }
            );
        else
        {
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          r_node = ml;
          size_t r_off = (size_t)0U;
          size_t r_n = total_sz;
          bool
          pcontinue =
            !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
          while (pcontinue)
          {
            size_t cur_off_v = r_off;
            size_t cur_n_v = r_n;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            scrut = r_node;
            if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            {
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *after = scrut.case_Append.after;
              size_t oa = scrut.case_Append.oa;
              LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              *before = scrut.case_Append.before;
              size_t ob = scrut.case_Append.ob;
              size_t cb = scrut.case_Append.cb;
              size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
              if (child_n_before > (size_t)0U)
              {
                size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ib = *before;
                r_node = ib;
                r_off = child_off_sz;
                r_n = child_n_before;
                pcontinue =
                  !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
              }
              else
              {
                size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
                size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
                LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                ia = *after;
                r_node = ia;
                r_off = child_off_sz;
                r_n = child_n_sz;
                pcontinue =
                  !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
              }
            }
            else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
            {
              KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                __FILE__,
                __LINE__,
                "unreachable (pattern matches are exhaustive in F*)");
              KRML_HOST_EXIT(255U);
            }
          }
          size_t cur_off_v = r_off;
          size_t cur_n_v = r_n;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          scrut = r_node;
          __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
          res;
          if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = scrut.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi_;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (cur_n_v == (size_t)0U)
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                bi_ =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          cur_off_v).snd,
                        cur_n_v).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = cur_off_v;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n = pn;
                size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                pn = n - (size_t)1U;
                poffset = offset_;
              }
              bi_ =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = cur_n_v,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              bi_ =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            res =
              (
                (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
                  .fst = bi_,
                  .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
                }
              );
          }
          else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "Pulse.Lib.Dv.unreachable");
          else
            res =
              KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
                "unreachable (pattern matches are exhaustive in F*)");
          LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          bi_ =
            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t
          len_sz1 =
            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
          size_t rest_sz = total_sz - len_sz1;
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ite1;
          if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
          {
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            bi1 = ml.case_Base;
            LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            ite;
            if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Empty
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
            {
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi1.case_Singleton;
              if (rest_sz == (size_t)0U)
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Empty
                    }
                  );
              else
                ite =
                  (
                    (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                      .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                      { .case_Singleton = s }
                    }
                  );
            }
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Slice,
                    {
                      .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                          len_sz1).snd,
                        rest_sz).fst
                    }
                  }
                );
            else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
            {
              Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
              size_t pn = len_sz1;
              size_t poffset = (size_t)0U;
              while (pn > (size_t)0U)
              {
                size_t n = pn;
                size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
                pn = n - (size_t)1U;
                poffset = offset_;
              }
              ite =
                (
                  (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                    .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                    {
                      .case_Serialized = {
                        .count = rest_sz,
                        .payload = split__uint8_t(pl, poffset).snd
                      }
                    }
                  }
                );
            }
            else
              ite =
                KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                  "unreachable (pattern matches are exhaustive in F*)");
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Base,
                  { .case_Base = ite }
                }
              );
          }
          else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
          {
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *after = ml.case_Append.after;
            size_t oa = ml.case_Append.oa;
            LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            *before = ml.case_Append.before;
            size_t ob = ml.case_Append.ob;
            size_t cb = ml.case_Append.cb;
            size_t cb__sz = append_n_before_sz(len_sz1, rest_sz, cb);
            size_t ca__sz = append_n_after_sz(len_sz1, rest_sz, cb);
            size_t ob__sz = append_off_before_sz(len_sz1, ob, cb);
            ite1 =
              (
                (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Append,
                  {
                    .case_Append = {
                      .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                      .oa = append_off_after_sz(len_sz1, oa, cb), .after = after
                    }
                  }
                }
              );
          }
          else
            ite1 =
              KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                "unreachable (pattern matches are exhaustive in F*)");
          ite0 =
            (
              (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_IPair,
                { .case_IPair = { .before = bi_, .after = ite1 } }
              }
            );
        }
        r = ite0;
        scrut1 = x1;
      }
      else
      {
        size_t n_tail_sz = len_sz - (size_t)1U;
        LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        ite;
        if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
        {
          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
          if (n_tail_sz == (size_t)0U)
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Empty
                }
              );
          else
            ite =
              (
                (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                  .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                  { .case_Singleton = s }
                }
              );
        }
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Slice,
                {
                  .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                      (size_t)1U).snd,
                    n_tail_sz).fst
                }
              }
            );
        else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
        {
          Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
          size_t pn = (size_t)1U;
          size_t poffset = (size_t)0U;
          while (pn > (size_t)0U)
          {
            size_t n = pn;
            size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
            pn = n - (size_t)1U;
            poffset = offset_;
          }
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Serialized,
                {
                  .case_Serialized = {
                    .count = n_tail_sz,
                    .payload = split__uint8_t(pl, poffset).snd
                  }
                }
              }
            );
        }
        else
          ite =
            KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
              "unreachable (pattern matches are exhaustive in F*)");
        r =
          (
            (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_IPair,
              { .case_IPair = { .before = ite, .after = ml } }
            }
          );
        scrut1 = x1;
      }
    }
  }
  else
    scrut1 =
      KRML_EABORT(elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        "unreachable (pattern matches are exhaustive in F*)");
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw elt;
  if (scrut1.tag == EElement)
    elt = scrut1.case_EElement;
  else if (scrut1.tag == ESerialized)
    elt = cbor_raw_read_map_entry(scrut1.case_ESerialized);
  else
    elt =
      KRML_EABORT(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        "unreachable (pattern matches are exhaustive in F*)");
  return
    (
      (__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .fst = elt,
        .snd = r
      }
    );
}

static int16_t impl_cbor_compare_fuel(cbor_raw x1, cbor_raw x2)
{
  uint8_t ty1 = cbor_raw_get_major_type_aux(x1);
  int16_t c = impl_uint8_compare(ty1, cbor_raw_get_major_type_aux(x2));
  if (c == (int16_t)0)
    if (ty1 == CBOR_MAJOR_TYPE_UINT64 || ty1 == CBOR_MAJOR_TYPE_NEG_INT64)
    {
      CBOR_Spec_Raw_Base_raw_uint64 ru1;
      if (x1.tag == CBOR_Case_Int)
      {
        cbor_int v = x1.case_CBOR_Case_Int;
        ru1 =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = v.cbor_int_size, .value = v.cbor_int_value });
      }
      else
        ru1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Int)
      {
        cbor_int v = x2.case_CBOR_Case_Int;
        ite =
          ((CBOR_Spec_Raw_Base_raw_uint64){ .size = v.cbor_int_size, .value = v.cbor_int_value });
      }
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      return impl_raw_uint64_compare(ru1, ite);
    }
    else if (ty1 == CBOR_MAJOR_TYPE_BYTE_STRING || ty1 == CBOR_MAJOR_TYPE_TEXT_STRING)
    {
      CBOR_Spec_Raw_Base_raw_uint64 len1;
      if (x1.tag == CBOR_Case_String)
      {
        cbor_string v = x1.case_CBOR_Case_String;
        len1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_string_size,
              .value = (uint64_t)len__uint8_t(v.cbor_string_ptr)
            }
          );
      }
      else
        len1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_String)
      {
        cbor_string v = x2.case_CBOR_Case_String;
        ite =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_string_size,
              .value = (uint64_t)len__uint8_t(v.cbor_string_ptr)
            }
          );
      }
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      int16_t cl = impl_raw_uint64_compare(len1, ite);
      if (cl == (int16_t)0)
      {
        Pulse_Lib_Slice_slice__uint8_t s1 = cbor_raw_get_string_aux(x1);
        return lex_compare_bytes(s1, cbor_raw_get_string_aux(x2));
      }
      else
        return cl;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_TAGGED)
    {
      CBOR_Spec_Raw_Base_raw_uint64 tag1;
      if (x1.tag == CBOR_Case_Tagged)
        tag1 = x1.case_CBOR_Case_Tagged.cbor_tagged_tag;
      else if (x1.tag == CBOR_Case_Tagged_Serialized)
        tag1 = x1.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag;
      else
        tag1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Tagged)
        ite = x2.case_CBOR_Case_Tagged.cbor_tagged_tag;
      else if (x2.tag == CBOR_Case_Tagged_Serialized)
        ite = x2.case_CBOR_Case_Tagged_Serialized.cbor_tagged_serialized_tag;
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      int16_t ct = impl_raw_uint64_compare(tag1, ite);
      if (ct == (int16_t)0)
        return CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_tagged(x1, x2);
      else
        return ct;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_ARRAY)
    {
      CBOR_Spec_Raw_Base_raw_uint64 len1;
      if (x1.tag == CBOR_Case_Array)
      {
        cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = x1.case_CBOR_Case_Array;
        len1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_array_length_size,
              .value = (uint64_t)mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_array_ptr)
            }
          );
      }
      else
        len1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Array)
      {
        cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = x2.case_CBOR_Case_Array;
        ite =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_array_length_size,
              .value = (uint64_t)mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_array_ptr)
            }
          );
      }
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      int16_t cl = impl_raw_uint64_compare(len1, ite);
      if (cl == (int16_t)0)
        return
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_array(x1,
            x2,
            (size_t)len1.value);
      else
        return cl;
    }
    else if (ty1 == CBOR_MAJOR_TYPE_MAP)
    {
      CBOR_Spec_Raw_Base_raw_uint64 len1;
      if (x1.tag == CBOR_Case_Map)
      {
        cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = x1.case_CBOR_Case_Map;
        len1 =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_map_length_size,
              .value = (uint64_t)mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_map_ptr)
            }
          );
      }
      else
        len1 = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      CBOR_Spec_Raw_Base_raw_uint64 ite;
      if (x2.tag == CBOR_Case_Map)
      {
        cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v = x2.case_CBOR_Case_Map;
        ite =
          (
            (CBOR_Spec_Raw_Base_raw_uint64){
              .size = v.cbor_map_length_size,
              .value = (uint64_t)mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_map_ptr)
            }
          );
      }
      else
        ite = ((CBOR_Spec_Raw_Base_raw_uint64){ .size = 0U, .value = 0ULL });
      int16_t cl = impl_raw_uint64_compare(len1, ite);
      if (cl == (int16_t)0)
        return
          CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_map(x1,
            x2,
            (size_t)len1.value);
      else
        return cl;
    }
    else
    {
      uint8_t sv1;
      if (x1.tag == CBOR_Case_Simple)
        sv1 = x1.case_CBOR_Case_Simple;
      else
        sv1 = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      uint8_t ite;
      if (x2.tag == CBOR_Case_Simple)
        ite = x2.case_CBOR_Case_Simple;
      else
        ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
      return impl_uint8_compare(sv1, ite);
    }
  else
    return c;
}

int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_tagged(cbor_raw x1, cbor_raw x2)
{
  elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  e1 = cbor_raw_get_tagged_payload_aux_eos(x1);
  elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  e2 = cbor_raw_get_tagged_payload_aux_eos(x2);
  if (e1.tag == EElement)
  {
    cbor_raw xx1 = e1.case_EElement;
    if (e2.tag == EElement)
      return impl_cbor_compare_fuel(xx1, e2.case_EElement);
    else if (e2.tag == ESerialized)
      return impl_cbor_compare_fuel(xx1, cbor_raw_read_fuel(e2.case_ESerialized));
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (e1.tag == ESerialized)
  {
    Pulse_Lib_Slice_slice__uint8_t s1 = e1.case_ESerialized;
    if (e2.tag == EElement)
    {
      cbor_raw xx2 = e2.case_EElement;
      return impl_cbor_compare_fuel(cbor_raw_read_fuel(s1), xx2);
    }
    else if (e2.tag == ESerialized)
    {
      Pulse_Lib_Slice_slice__uint8_t s2 = e2.case_ESerialized;
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut0 = split__uint8_t(s1, jump_raw_data_item_eta(s1, (size_t)0U));
      Pulse_Lib_Slice_slice__uint8_t
      ex1 =
        (
          (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
            .fst = scrut0.fst,
            .snd = scrut0.snd
          }
        ).fst;
      __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
      scrut = split__uint8_t(s2, jump_raw_data_item_eta(s2, (size_t)0U));
      return
        lex_compare_bytes(ex1,
          (
            (__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){
              .fst = scrut.fst,
              .snd = scrut.snd
            }
          ).fst);
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
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_array(
  cbor_raw x1,
  cbor_raw x2,
  size_t len
)
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ar_ml1 = cbor_raw_get_array_aux(x1);
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ar_ml2 = cbor_raw_get_array_aux(x2);
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  r_it1 = iterator_start_raw_data_item_fuel(ar_ml1);
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  r_it2 = iterator_start_raw_data_item_fuel(ar_ml2);
  int16_t r_acc = (int16_t)0;
  size_t r_cnt = (size_t)0U;
  while (r_cnt < len && r_acc == (int16_t)0)
  {
    elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    e1 = iterator_next_eos_raw_data_item_fuel_byref(&r_it1);
    elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    e2 = iterator_next_eos_raw_data_item_fuel_byref(&r_it2);
    size_t old_cnt = r_cnt;
    if (e1.tag == EElement)
    {
      cbor_raw xx1 = e1.case_EElement;
      if (e2.tag == EElement)
      {
        r_acc = impl_cbor_compare_fuel(xx1, e2.case_EElement);
        r_cnt = old_cnt + (size_t)1U;
      }
      else if (e2.tag == ESerialized)
      {
        r_acc = impl_cbor_compare_fuel(xx1, cbor_raw_read_fuel(e2.case_ESerialized));
        r_cnt = old_cnt + (size_t)1U;
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
    else if (e1.tag == ESerialized)
    {
      Pulse_Lib_Slice_slice__uint8_t s1 = e1.case_ESerialized;
      if (e2.tag == EElement)
      {
        cbor_raw xx2 = e2.case_EElement;
        r_acc = impl_cbor_compare_fuel(cbor_raw_read_fuel(s1), xx2);
        r_cnt = old_cnt + (size_t)1U;
      }
      else if (e2.tag == ESerialized)
      {
        r_acc = byte_compare_pts_to_parsed_data_item(s1, e2.case_ESerialized);
        r_cnt = old_cnt + (size_t)1U;
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
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  return r_acc;
}

typedef struct
__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  cbor_raw fst;
  cbor_raw snd;
}
__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

static cbor_raw
fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  __CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw x
)
{
  return x.fst;
}

static cbor_raw
snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  __CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw x
)
{
  return x.snd;
}

int16_t
CBOR_Pulse_Raw_EverParse_Det_Compare_impl_cbor_compare_fuel_map(
  cbor_raw x1,
  cbor_raw x2,
  size_t len
)
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  map_ml1 = cbor_raw_get_map_aux(x1);
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  map_ml2 = cbor_raw_get_map_aux(x2);
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  r_it1 = iterator_start_map_entry_raw_data_item_fuel(map_ml1);
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  r_it2 = iterator_start_map_entry_raw_data_item_fuel(map_ml2);
  int16_t r_acc = (int16_t)0;
  size_t r_cnt = (size_t)0U;
  while (r_cnt < len && r_acc == (int16_t)0)
  {
    elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    e1 = iterator_next_eos_map_entry_raw_data_item_fuel_byref(&r_it1);
    elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    e2 = iterator_next_eos_map_entry_raw_data_item_fuel_byref(&r_it2);
    size_t old_cnt = r_cnt;
    if (e1.tag == EElement)
    {
      cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw entry1 = e1.case_EElement;
      if (e2.tag == EElement)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw entry2 = e2.case_EElement;
        int16_t ck = impl_cbor_compare_fuel(entry1.cbor_map_entry_key, entry2.cbor_map_entry_key);
        if (ck == (int16_t)0)
        {
          r_acc = impl_cbor_compare_fuel(entry1.cbor_map_entry_value, entry2.cbor_map_entry_value);
          r_cnt = old_cnt + (size_t)1U;
        }
        else
        {
          r_acc = ck;
          r_cnt = old_cnt + (size_t)1U;
        }
      }
      else if (e2.tag == ESerialized)
      {
        Pulse_Lib_Slice_slice__uint8_t s2 = e2.case_ESerialized;
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut = split__uint8_t(s2, jump_raw_data_item_eta(s2, (size_t)0U));
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
        Pulse_Lib_Slice_slice__uint8_t input2 = scrut0.snd;
        cbor_raw res1 = cbor_raw_read_fuel(scrut0.fst);
        __CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        pair = { .fst = res1, .snd = cbor_raw_read_fuel(input2) };
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        entry2 =
          {
            .cbor_map_entry_key = fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair),
            .cbor_map_entry_value = snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair)
          };
        int16_t ck = impl_cbor_compare_fuel(entry1.cbor_map_entry_key, entry2.cbor_map_entry_key);
        if (ck == (int16_t)0)
        {
          r_acc = impl_cbor_compare_fuel(entry1.cbor_map_entry_value, entry2.cbor_map_entry_value);
          r_cnt = old_cnt + (size_t)1U;
        }
        else
        {
          r_acc = ck;
          r_cnt = old_cnt + (size_t)1U;
        }
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
    else if (e1.tag == ESerialized)
    {
      Pulse_Lib_Slice_slice__uint8_t s1 = e1.case_ESerialized;
      if (e2.tag == EElement)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw entry2 = e2.case_EElement;
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut = split__uint8_t(s1, jump_raw_data_item_eta(s1, (size_t)0U));
        __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
        scrut0 = { .fst = scrut.fst, .snd = scrut.snd };
        Pulse_Lib_Slice_slice__uint8_t input2 = scrut0.snd;
        cbor_raw res1 = cbor_raw_read_fuel(scrut0.fst);
        __CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        pair = { .fst = res1, .snd = cbor_raw_read_fuel(input2) };
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        entry1 =
          {
            .cbor_map_entry_key = fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair),
            .cbor_map_entry_value = snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(pair)
          };
        int16_t ck = impl_cbor_compare_fuel(entry1.cbor_map_entry_key, entry2.cbor_map_entry_key);
        if (ck == (int16_t)0)
        {
          r_acc = impl_cbor_compare_fuel(entry1.cbor_map_entry_value, entry2.cbor_map_entry_value);
          r_cnt = old_cnt + (size_t)1U;
        }
        else
        {
          r_acc = ck;
          r_cnt = old_cnt + (size_t)1U;
        }
      }
      else if (e2.tag == ESerialized)
      {
        r_acc = lex_compare_bytes(s1, e2.case_ESerialized);
        r_cnt = old_cnt + (size_t)1U;
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
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  return r_acc;
}

static int16_t impl_cbor_compare_fuel_call(cbor_raw x1, cbor_raw x2)
{
  return impl_cbor_compare_fuel(x1, x2);
}

static int16_t impl_cbor_compare(cbor_raw x1, cbor_raw x2)
{
  return impl_cbor_compare_fuel_call(x1, x2);
}

static Pulse_Lib_Slice_slice__uint8_t arrayptr_to_slice_intro__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

static size_t cbor_det_serialize_arrayptr(cbor_raw x, uint8_t *output, size_t output_len)
{
  return cbor_serialize(x, arrayptr_to_slice_intro__uint8_t(output, output_len));
}

static Pulse_Lib_Slice_slice__uint8_t
fst__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t(
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t x
)
{
  return x.fst;
}

static size_t cbor_det_serialize_safe_arrayptr(cbor_raw x, uint8_t *output, size_t output_len)
{
  Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(output, output_len);
  size_t sz = cbor_size(x, output_len);
  if (sz == (size_t)0U)
    return (size_t)0U;
  else
    return
      cbor_serialize(x,
        fst__Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t(split__uint8_t(s, sz)));
}

static void
op_Array_Assignment__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a,
  size_t i,
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw v
)
{
  a.elt[i] = v;
}

bool
CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a
)
{
  size_t
  len =
    len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a);
  if (len < (size_t)2U)
    return true;
  else
  {
    size_t mi = len / (size_t)2U;
    __Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut =
      split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
        mi);
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    a2 = scrut.snd;
    if (!CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(scrut.fst))
      return false;
    else if (!CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(a2))
      return false;
    else
    {
      size_t pi1 = (size_t)0U;
      size_t pi2 = mi;
      bool pres = true;
      size_t i10 = pi1;
      size_t i20 = pi2;
      bool res20 = pres;
      bool
      cond =
        res20 &&
          !(i10 == i20 ||
            i20 ==
              len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a));
      while (cond)
      {
        size_t i1 = pi1;
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        x1 =
          op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
            i1);
        size_t i20 = pi2;
        int16_t
        comp =
          impl_cbor_compare(x1.cbor_map_entry_key,
            op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
              i20).cbor_map_entry_key);
        if (comp == (int16_t)0)
          pres = false;
        else if (comp < (int16_t)0)
          pi1 = i1 + (size_t)1U;
        else
        {
          size_t i2_ = i20 + (size_t)1U;
          Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ac1 =
            split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
                i2_).fst,
              i1).snd;
          if
          (
            !(i20 - i1 == (size_t)0U ||
              i20 - i1 ==
                len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1))
          )
          {
            size_t
            pn =
              len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1);
            size_t pl = i20 - i1;
            while (pl > (size_t)0U)
            {
              size_t l3 = pl;
              size_t l_ = pn % l3;
              pn = l3;
              pl = l_;
            }
            size_t d = pn;
            size_t
            q =
              len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1)
              / d;
            size_t pi = (size_t)0U;
            while (pi < d)
            {
              size_t i = pi;
              cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              save =
                op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1,
                  i);
              size_t pj = (size_t)0U;
              size_t pidx = i;
              while (pj < q - (size_t)1U)
              {
                size_t j = pj;
                size_t idx = pidx;
                size_t idx_;
                if
                (
                  idx - (size_t)0U >=
                    len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1)
                    - (i20 - i1)
                )
                  idx_ =
                    idx -
                      (len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1)
                      - (i20 - i1));
                else
                  idx_ = idx + i20 - i1 - (size_t)0U;
                size_t j_ = j + (size_t)1U;
                op_Array_Assignment__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1,
                  idx,
                  op_Array_Access__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1,
                    idx_));
                pj = j_;
                pidx = idx_;
              }
              op_Array_Assignment__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ac1,
                pidx,
                save);
              pi = i + (size_t)1U;
            }
          }
          pi1 = i1 + (size_t)1U;
          pi2 = i2_;
        }
        size_t i10 = pi1;
        size_t i2 = pi2;
        bool res2 = pres;
        cond =
          res2 &&
            !(i10 == i2 ||
              i2 ==
                len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a));
      }
      return pres;
    }
  }
}

static bool
cbor_raw_sort(
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  a
)
{
  return CBOR_Pulse_Raw_EverParse_Det_Impl_cbor_raw_sort_aux(a);
}

bool uu___is_CBOR_Case_Invalid(cbor_raw projectee)
{
  if (projectee.tag == CBOR_Case_Invalid)
    return true;
  else
    return false;
}

bool uu___is_CBOR_Case_Int(cbor_raw projectee)
{
  if (projectee.tag == CBOR_Case_Int)
    return true;
  else
    return false;
}

bool uu___is_CBOR_Case_Simple(cbor_raw projectee)
{
  if (projectee.tag == CBOR_Case_Simple)
    return true;
  else
    return false;
}

bool uu___is_CBOR_Case_String(cbor_raw projectee)
{
  if (projectee.tag == CBOR_Case_String)
    return true;
  else
    return false;
}

bool uu___is_CBOR_Case_Tagged(cbor_raw projectee)
{
  if (projectee.tag == CBOR_Case_Tagged)
    return true;
  else
    return false;
}

bool uu___is_CBOR_Case_Tagged_Serialized(cbor_raw projectee)
{
  if (projectee.tag == CBOR_Case_Tagged_Serialized)
    return true;
  else
    return false;
}

bool uu___is_CBOR_Case_Array(cbor_raw projectee)
{
  if (projectee.tag == CBOR_Case_Array)
    return true;
  else
    return false;
}

bool uu___is_CBOR_Case_Map(cbor_raw projectee)
{
  if (projectee.tag == CBOR_Case_Map)
    return true;
  else
    return false;
}

cbor_raw dummy_cbor_det_t(void)
{
  return ((cbor_raw){ .tag = CBOR_Case_Simple, { .case_CBOR_Case_Simple = 0U } });
}

cbor_raw cbor_det_reset_perm(cbor_raw x)
{
  return cbor_raw_reset_perm(x);
}

size_t cbor_det_validate(uint8_t *input, size_t input_len)
{
  return cbor_validate_det(arrayptr_to_slice_intro__uint8_t(input, input_len));
}

cbor_raw cbor_det_parse(uint8_t *input, size_t len)
{
  Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(input, len);
  len__uint8_t(s);
  return cbor_parse_valid(s);
}

size_t cbor_det_size(cbor_raw x, size_t bound)
{
  return cbor_size(x, bound);
}

size_t cbor_det_serialize(cbor_raw x, uint8_t *output, size_t output_len)
{
  return cbor_det_serialize_arrayptr(x, output, output_len);
}

size_t cbor_det_serialize_safe(cbor_raw x, uint8_t *output, size_t output_len)
{
  return cbor_det_serialize_safe_arrayptr(x, output, output_len);
}

bool cbor_det_impl_utf8_correct_from_array(uint8_t *s, size_t len)
{
  return impl_correct(arrayptr_to_slice_intro__uint8_t(s, len));
}

cbor_raw cbor_det_mk_simple_value(uint8_t v)
{
  return cbor_mk_simple_value(v);
}

cbor_raw cbor_det_mk_int64(uint8_t ty, uint64_t v)
{
  return cbor_mk_int64(ty, v);
}

cbor_raw cbor_det_mk_tagged(uint64_t tag, cbor_raw *r)
{
  mk_raw_uint64(tag);
  return cbor_mk_tagged(tag, r);
}

bool cbor_det_mk_byte_string_from_arrayptr(uint8_t *a, uint64_t len, cbor_raw *dest)
{
  bool __anf0 = a == NULL;
  if (__anf0 || dest == NULL)
    return false;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
    bool ite;
    if (CBOR_MAJOR_TYPE_BYTE_STRING == CBOR_MAJOR_TYPE_TEXT_STRING)
      ite = impl_correct(s);
    else
      ite = true;
    if (ite)
    {
      mk_raw_uint64((uint64_t)len__uint8_t(s));
      *dest = cbor_mk_string(CBOR_MAJOR_TYPE_BYTE_STRING, s);
      return true;
    }
    else
      return false;
  }
}

bool cbor_det_mk_text_string_from_arrayptr(uint8_t *a, uint64_t len, cbor_raw *dest)
{
  bool __anf0 = a == NULL;
  if (__anf0 || dest == NULL)
    return false;
  else
  {
    Pulse_Lib_Slice_slice__uint8_t s = arrayptr_to_slice_intro__uint8_t(a, (size_t)len);
    if (impl_correct(s))
    {
      mk_raw_uint64((uint64_t)len__uint8_t(s));
      *dest = cbor_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, s);
      return true;
    }
    else
      return false;
  }
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cbor_raw *a, size_t alen)
{
  return
    ((Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){ .elt = a, .len = alen });
}

cbor_raw cbor_det_mk_array_from_array(cbor_raw *a, uint64_t len)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s = from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a, (size_t)len);
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml =
    {
      .tag = LowParse_PulseParse_Iterator_Type_Base,
      { .case_Base = { .tag = LowParse_PulseParse_Iterator_Type_Slice, { .case_Slice = s } } }
    };
  return
    cbor_mk_array(mk_raw_uint64((uint64_t)len__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)).size,
      ml);
}

cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_mk_map_entry(cbor_raw xk, cbor_raw xv)
{
  cbor_raw xk_ = cbor_raw_reset_perm(xk);
  return cbor_mk_map_entry(xk_, cbor_raw_reset_perm(xv));
}

static Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *a,
  size_t alen
)
{
  return
    (
      (Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
        .elt = a,
        .len = alen
      }
    );
}

cbor_raw
cbor_det_mk_map_from_array(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *a,
  uint64_t len
)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s =
    from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
      (size_t)len);
  cbor_raw dest = dummy_cbor_det_t();
  bool ite;
  if
  (
    len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s) >
      (size_t)18446744073709551615ULL
  )
    ite = false;
  else if (cbor_raw_sort(s))
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml =
      {
        .tag = LowParse_PulseParse_Iterator_Type_Base,
        { .case_Base = { .tag = LowParse_PulseParse_Iterator_Type_Slice, { .case_Slice = s } } }
      };
    dest =
      cbor_mk_map(mk_raw_uint64((uint64_t)len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)).size,
        ml);
    ite = true;
  }
  else
    ite = false;
  KRML_MAYBE_UNUSED_VAR(ite);
  return dest;
}

bool
cbor_det_mk_map_from_array_safe(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *a,
  uint64_t len,
  cbor_raw *dest
)
{
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  s =
    from_array__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(a,
      (size_t)len);
  if
  (
    len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s) >
      (size_t)18446744073709551615ULL
  )
    return false;
  else if (cbor_raw_sort(s))
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml =
      {
        .tag = LowParse_PulseParse_Iterator_Type_Base,
        { .case_Base = { .tag = LowParse_PulseParse_Iterator_Type_Slice, { .case_Slice = s } } }
      };
    *dest =
      cbor_mk_map(mk_raw_uint64((uint64_t)len__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(s)).size,
        ml);
    return true;
  }
  else
    return false;
}

bool cbor_det_equal(cbor_raw x1, cbor_raw x2)
{
  return impl_cbor_compare(x1, x2) == (int16_t)0;
}

uint8_t cbor_det_major_type(cbor_raw x)
{
  return cbor_raw_get_major_type(x);
}

uint8_t cbor_det_read_simple_value(cbor_raw x)
{
  return cbor_raw_read_simple_value(x);
}

uint64_t cbor_det_read_uint64(cbor_raw x)
{
  return cbor_raw_read_int64_value(x);
}

uint64_t cbor_det_get_string_length(cbor_raw x)
{
  return (uint64_t)len__uint8_t(cbor_raw_get_string(x));
}

uint64_t cbor_det_get_tagged_tag(cbor_raw x)
{
  return cbor_raw_read_tagged_tag(x);
}

cbor_raw cbor_det_get_tagged_payload(cbor_raw x)
{
  return cbor_raw_get_tagged_payload(x);
}

static uint8_t *slice_to_arrayptr_intro__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.elt;
}

uint8_t *cbor_det_get_string(cbor_raw x)
{
  return slice_to_arrayptr_intro__uint8_t(cbor_raw_get_string(x));
}

uint64_t cbor_det_get_array_length(cbor_raw x)
{
  return cbor_raw_read_array_length(x);
}

LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_array_iterator_start(cbor_raw x)
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml = cbor_raw_get_array(x);
  size_t total_sz = mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  if (total_sz == (size_t)0U)
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IBase,
          { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
        }
      );
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    r_node = ml;
    size_t r_off = (size_t)0U;
    size_t r_n = total_sz;
    bool pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    while (pcontinue)
    {
      size_t cur_off_v = r_off;
      size_t cur_n_v = r_n;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      scrut = r_node;
      if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = scrut.case_Append.after;
        size_t oa = scrut.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = scrut.case_Append.before;
        size_t ob = scrut.case_Append.ob;
        size_t cb = scrut.case_Append.cb;
        size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
        if (child_n_before > (size_t)0U)
        {
          size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ib = *before;
          r_node = ib;
          r_off = child_off_sz;
          r_n = child_n_before;
          pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
        }
        else
        {
          size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
          size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ia = *after;
          r_node = ia;
          r_off = child_off_sz;
          r_n = child_n_sz;
          pcontinue = !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
        }
      }
      else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    size_t cur_off_v = r_off;
    size_t cur_n_v = r_n;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut = r_node;
    __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
    res;
    if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = scrut.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw bi_;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi.case_Singleton;
        if (cur_n_v == (size_t)0U)
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    cur_off_v).snd,
                  cur_n_v).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = cur_off_v;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = jump_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = { .count = cur_n_v, .payload = split__uint8_t(pl, poffset).snd }
              }
            }
          );
      }
      else
        bi_ =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      res =
        (
          (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
            .fst = bi_,
            .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
          }
        );
    }
    else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      res =
        KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "Pulse.Lib.Dv.unreachable");
    else
      res =
        KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "unreachable (pattern matches are exhaustive in F*)");
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi_ =
      fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t
    len_sz =
      snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t rest_sz = total_sz - len_sz;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi.case_Singleton;
        if (rest_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    len_sz).snd,
                  rest_sz).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = len_sz;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = jump_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = { .count = rest_sz, .payload = split__uint8_t(pl, poffset).snd }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = append_n_before_sz(len_sz, rest_sz, cb);
      size_t ca__sz = append_n_after_sz(len_sz, rest_sz, cb);
      size_t ob__sz = append_off_before_sz(len_sz, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = append_off_after_sz(len_sz, oa, cb), .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
        }
      );
  }
}

bool
cbor_det_array_iterator_is_empty(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x
)
{
  if (x.tag == LowParse_PulseParse_Iterator_Type_IBase)
    return
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IBase) == (size_t)0U;
  else if (x.tag == LowParse_PulseParse_Iterator_Type_IPair)
    return
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IPair.before) ==
        (size_t)0U;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint64_t
cbor_det_array_iterator_length(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x
)
{
  if (x.tag == LowParse_PulseParse_Iterator_Type_IBase)
    return (uint64_t)base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IBase);
  else if (x.tag == LowParse_PulseParse_Iterator_Type_IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = x.case_IPair.after;
    size_t
    len_before =
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IPair.before);
    return (uint64_t)(len_before + mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml));
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

cbor_raw
cbor_det_array_iterator_next(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *x
)
{
  __CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  scrut = iterator_next_raw_data_item(*x);
  cbor_raw res = scrut.fst;
  *x = scrut.snd;
  return res;
}

LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_array_iterator_truncate(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x,
  uint64_t len
)
{
  size_t len_sz = (size_t)len;
  if (x.tag == LowParse_PulseParse_Iterator_Type_IBase)
  {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = x.case_IBase;
    base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite;
    if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
      ite =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Empty
          }
        );
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
    {
      cbor_raw *s = bi.case_Singleton;
      if (len_sz == (size_t)0U)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Singleton,
              { .case_Singleton = s }
            }
          );
    }
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
      ite =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Slice,
            {
              .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U).snd,
                len_sz).fst
            }
          }
        );
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
    {
      Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
      size_t pn = (size_t)0U;
      size_t poffset = (size_t)0U;
      while (pn > (size_t)0U)
      {
        size_t n1 = pn;
        size_t offset_ = jump_raw_data_item_eta(pl, poffset);
        pn = n1 - (size_t)1U;
        poffset = offset_;
      }
      ite =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Serialized,
            { .case_Serialized = { .count = len_sz, .payload = split__uint8_t(pl, poffset).snd } }
          }
        );
    }
    else
      ite =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IBase,
          { .case_IBase = ite }
        }
      );
  }
  else if (x.tag == LowParse_PulseParse_Iterator_Type_IPair)
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ml = x.case_IPair.after;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi = x.case_IPair.before;
    size_t cb_sz = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi);
    size_t len_before_sz;
    if (len_sz <= cb_sz)
      len_before_sz = len_sz;
    else
      len_before_sz = cb_sz;
    size_t len_after_sz;
    if (len_sz <= cb_sz)
      len_after_sz = (size_t)0U;
    else
      len_after_sz = len_sz - cb_sz;
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw bi_;
    if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
      bi_ =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Empty
          }
        );
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
    {
      cbor_raw *s = bi.case_Singleton;
      if (len_before_sz == (size_t)0U)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Singleton,
              { .case_Singleton = s }
            }
          );
    }
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
      bi_ =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Slice,
            {
              .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                  (size_t)0U).snd,
                len_before_sz).fst
            }
          }
        );
    else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
    {
      Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
      size_t pn = (size_t)0U;
      size_t poffset = (size_t)0U;
      while (pn > (size_t)0U)
      {
        size_t n1 = pn;
        size_t offset_ = jump_raw_data_item_eta(pl, poffset);
        pn = n1 - (size_t)1U;
        poffset = offset_;
      }
      bi_ =
        (
          (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Serialized,
            {
              .case_Serialized = {
                .count = len_before_sz,
                .payload = split__uint8_t(pl, poffset).snd
              }
            }
          }
        );
    }
    else
      bi_ =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi1 = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw ite;
      if (bi1.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_raw *s = bi1.case_Singleton;
        if (len_after_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi1.case_Slice,
                    (size_t)0U).snd,
                  len_after_sz).fst
              }
            }
          );
      else if (bi1.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi1.case_Serialized.payload;
        size_t pn = (size_t)0U;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n1 = pn;
          size_t offset_ = jump_raw_data_item_eta(pl, poffset);
          pn = n1 - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = {
                  .count = len_after_sz,
                  .payload = split__uint8_t(pl, poffset).snd
                }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = append_n_before_sz((size_t)0U, len_after_sz, cb);
      size_t ca__sz = append_n_after_sz((size_t)0U, len_after_sz, cb);
      size_t ob__sz = append_off_before_sz((size_t)0U, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = append_off_after_sz((size_t)0U, oa, cb), .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
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

cbor_raw cbor_det_get_array_item(cbor_raw x, uint64_t i)
{
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  pit = cbor_det_array_iterator_start(x);
  uint64_t pj = 0ULL;
  bool pcont = 0ULL < i;
  while (pcont)
  {
    cbor_det_array_iterator_next(&pit);
    uint64_t j_val = pj;
    pj = j_val + 1ULL;
    pcont = j_val + 1ULL < i;
  }
  return cbor_det_array_iterator_next(&pit);
}

uint64_t cbor_det_get_map_length(cbor_raw x)
{
  return cbor_raw_read_map_length(x);
}

LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_map_iterator_start(cbor_raw x)
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  ml = cbor_raw_get_map(x);
  size_t
  total_sz =
    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
  if (total_sz == (size_t)0U)
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IBase,
          { .case_IBase = { .tag = LowParse_PulseParse_Iterator_Type_Empty } }
        }
      );
  else
  {
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    r_node = ml;
    size_t r_off = (size_t)0U;
    size_t r_n = total_sz;
    bool
    pcontinue =
      !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    while (pcontinue)
    {
      size_t cur_off_v = r_off;
      size_t cur_n_v = r_n;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      scrut = r_node;
      if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      {
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *after = scrut.case_Append.after;
        size_t oa = scrut.case_Append.oa;
        LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        *before = scrut.case_Append.before;
        size_t ob = scrut.case_Append.ob;
        size_t cb = scrut.case_Append.cb;
        size_t child_n_before = append_n_before_sz(cur_off_v, cur_n_v, cb);
        if (child_n_before > (size_t)0U)
        {
          size_t child_off_sz = append_off_before_sz(cur_off_v, ob, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ib = *before;
          r_node = ib;
          r_off = child_off_sz;
          r_n = child_n_before;
          pcontinue =
            !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib);
        }
        else
        {
          size_t child_off_sz = append_off_after_sz(cur_off_v, oa, cb);
          size_t child_n_sz = append_n_after_sz(cur_off_v, cur_n_v, cb);
          LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
          ia = *after;
          r_node = ia;
          r_off = child_off_sz;
          r_n = child_n_sz;
          pcontinue =
            !uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia);
        }
      }
      else if (!(scrut.tag == LowParse_PulseParse_Iterator_Type_Base))
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    size_t cur_off_v = r_off;
    size_t cur_n_v = r_n;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    scrut = r_node;
    __LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
    res;
    if (scrut.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = scrut.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi_;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
        if (cur_n_v == (size_t)0U)
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          bi_ =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    cur_off_v).snd,
                  cur_n_v).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = cur_off_v;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        bi_ =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = { .count = cur_n_v, .payload = split__uint8_t(pl, poffset).snd }
              }
            }
          );
      }
      else
        bi_ =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      res =
        (
          (__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t){
            .fst = bi_,
            .snd = base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi_)
          }
        );
    }
    else if (scrut.tag == LowParse_PulseParse_Iterator_Type_Append)
      res =
        KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "Pulse.Lib.Dv.unreachable");
    else
      res =
        KRML_EABORT(__LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t,
          "unreachable (pattern matches are exhaustive in F*)");
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    bi_ =
      fst__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t
    len_sz =
      snd__LowParse_PulseParse_Iterator_Type_base_mixed_list_CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(res);
    size_t rest_sz = total_sz - len_sz;
    LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    ite0;
    if (ml.tag == LowParse_PulseParse_Iterator_Type_Base)
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      bi = ml.case_Base;
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      ite;
      if (bi.tag == LowParse_PulseParse_Iterator_Type_Empty)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Empty
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Singleton)
      {
        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *s = bi.case_Singleton;
        if (rest_sz == (size_t)0U)
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Empty
              }
            );
        else
          ite =
            (
              (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
                .tag = LowParse_PulseParse_Iterator_Type_Singleton,
                { .case_Singleton = s }
              }
            );
      }
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Slice)
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Slice,
              {
                .case_Slice = split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(split__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi.case_Slice,
                    len_sz).snd,
                  rest_sz).fst
              }
            }
          );
      else if (bi.tag == LowParse_PulseParse_Iterator_Type_Serialized)
      {
        Pulse_Lib_Slice_slice__uint8_t pl = bi.case_Serialized.payload;
        size_t pn = len_sz;
        size_t poffset = (size_t)0U;
        while (pn > (size_t)0U)
        {
          size_t n = pn;
          size_t offset_ = jump_nondep_then_raw_data_item_eta(pl, poffset);
          pn = n - (size_t)1U;
          poffset = offset_;
        }
        ite =
          (
            (LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
              .tag = LowParse_PulseParse_Iterator_Type_Serialized,
              {
                .case_Serialized = { .count = rest_sz, .payload = split__uint8_t(pl, poffset).snd }
              }
            }
          );
      }
      else
        ite =
          KRML_EABORT(LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            "unreachable (pattern matches are exhaustive in F*)");
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Base,
            { .case_Base = ite }
          }
        );
    }
    else if (ml.tag == LowParse_PulseParse_Iterator_Type_Append)
    {
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after = ml.case_Append.after;
      size_t oa = ml.case_Append.oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before = ml.case_Append.before;
      size_t ob = ml.case_Append.ob;
      size_t cb = ml.case_Append.cb;
      size_t cb__sz = append_n_before_sz(len_sz, rest_sz, cb);
      size_t ca__sz = append_n_after_sz(len_sz, rest_sz, cb);
      size_t ob__sz = append_off_before_sz(len_sz, ob, cb);
      ite0 =
        (
          (LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = LowParse_PulseParse_Iterator_Type_Append,
            {
              .case_Append = {
                .cb = cb__sz, .ca = ca__sz, .ob = ob__sz, .before = before,
                .oa = append_off_after_sz(len_sz, oa, cb), .after = after
              }
            }
          }
        );
    }
    else
      ite0 =
        KRML_EABORT(LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
          .tag = LowParse_PulseParse_Iterator_Type_IPair,
          { .case_IPair = { .before = bi_, .after = ite0 } }
        }
      );
  }
}

bool
cbor_det_map_iterator_is_empty(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  x
)
{
  if (x.tag == LowParse_PulseParse_Iterator_Type_IBase)
    return
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IBase)
      == (size_t)0U;
  else if (x.tag == LowParse_PulseParse_Iterator_Type_IPair)
    return
      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(x.case_IPair.before)
      == (size_t)0U;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_map_iterator_next(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  *x
)
{
  __CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  scrut = iterator_next_map_entry_raw_data_item(*x);
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw res = scrut.fst;
  *x = scrut.snd;
  return res;
}

cbor_raw cbor_det_map_entry_key(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e)
{
  return e.cbor_map_entry_key;
}

cbor_raw cbor_det_map_entry_value(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e)
{
  return e.cbor_map_entry_value;
}

typedef struct option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  option__uint8_t_tags tag;
  cbor_raw v;
}
option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

bool cbor_det_map_get(cbor_raw x, cbor_raw k, cbor_raw *dest)
{
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  it = cbor_det_map_iterator_start(x);
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  pit = it;
  option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw pres = { .tag = None };
  bool pcont = !cbor_det_map_iterator_is_empty(it);
  while (pcont)
  {
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    entry = cbor_det_map_iterator_next(&pit);
    if (cbor_det_equal(cbor_det_map_entry_key(entry), k))
    {
      pres =
        (
          (option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw){
            .tag = Some,
            .v = cbor_det_map_entry_value(entry)
          }
        );
      pcont = false;
    }
    else
      pcont = !cbor_det_map_iterator_is_empty(pit);
  }
  option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw scrut = pres;
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

cbor_raw cbor_get_from_freeable(cbor_det_freeable_t_ r)
{
  return r.cbor;
}

void panic____(void)
{
  panic____();
}

static Pulse_Lib_Slice_slice__uint8_t from_array__uint8_t(uint8_t *a, size_t alen)
{
  return ((Pulse_Lib_Slice_slice__uint8_t){ .elt = a, .len = alen });
}

static cbor_det_freeable_t_ cbor_copy_impl(cbor_raw c)
{
  size_t size = cbor_size(c, (size_t)0xFFFFFFFFFFFFFFFFULL);
  if (size == (size_t)0U)
    panic____();
  KRML_CHECK_SIZE(sizeof (uint8_t), size);
  uint8_t *buf = KRML_HOST_CALLOC(size, sizeof (uint8_t));
  Pulse_Lib_Slice_slice__uint8_t sl = from_array__uint8_t(buf, size);
  cbor_det_serialize_arrayptr(c, slice_to_arrayptr_intro__uint8_t(sl), size);
  len__uint8_t(sl);
  return ((cbor_det_freeable_t_){ .cbor = cbor_parse_valid(sl), .buf = buf, .len = size });
}

cbor_det_freeable_t_ cbor_copy(cbor_raw c)
{
  return cbor_copy_impl(c);
}

static void cbor_free_(cbor_det_freeable_t_ x)
{
  KRML_HOST_FREE(x.buf);
}

void cbor_free(cbor_det_freeable_t_ x)
{
  cbor_free_(x);
}

