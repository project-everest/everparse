

#include "EverParquet.h"

typedef FStar_Pervasives_Native_option__int8_t variant_type;

typedef FStar_Pervasives_Native_option__Prims_string geometry_type;

bool
Parquet_Pulse_Toplevel_uu___is_ENCRYPTION_WITH_FOOTER_KEY(
  Parquet_Pulse_Toplevel_column_crypto_meta_data projectee
)
{
  if (projectee.tag == Parquet_Pulse_Toplevel_ENCRYPTION_WITH_FOOTER_KEY)
    return true;
  else
    return false;
}

bool
Parquet_Pulse_Toplevel_uu___is_ENCRYPTION_WITH_COLUMN_KEY(
  Parquet_Pulse_Toplevel_column_crypto_meta_data projectee
)
{
  if (projectee.tag == Parquet_Pulse_Toplevel_ENCRYPTION_WITH_COLUMN_KEY)
    return true;
  else
    return false;
}

static size_t len__uint8_t(Pulse_Lib_Slice_slice__uint8_t s)
{
  return s.len;
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

typedef struct
__Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t__s
{
  Pulse_Lib_Slice_slice__uint8_t fst;
  __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t snd;
}
__Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_;

bool Parquet_Pulse_Toplevel0_validate_header_magic_number(Pulse_Lib_Slice_slice__uint8_t input)
{
  if ((size_t)0U > len__uint8_t(input))
    return false;
  else if ((size_t)4U > len__uint8_t(input) - (size_t)0U)
    return false;
  else
  {
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    s_ = split__uint8_t(input, (size_t)4U);
    Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
    Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
    __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
    _letpattern = { .fst = s1, .snd = s2 };
    Pulse_Lib_Slice_slice__uint8_t s10 = _letpattern.fst;
    size_t poffset = (size_t)0U;
    size_t offset = poffset;
    size_t offset1 = poffset;
    bool is_valid0;
    if (len__uint8_t(s10) - offset1 < (size_t)4U)
      is_valid0 = false;
    else
    {
      poffset = offset1 + (size_t)4U;
      is_valid0 = true;
    }
    bool is_valid;
    if (is_valid0)
    {
      size_t off = poffset;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      s_ = split__uint8_t(s10, offset);
      Pulse_Lib_Slice_slice__uint8_t s110 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s210 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern1 = { .fst = s110, .snd = s210 };
      Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern1.fst;
      Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern1.snd;
      size_t consumed = off - offset;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern2 = split__uint8_t(input23, consumed);
      Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern2.fst;
      Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern2.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern20 = { .fst = s11, .snd = s21 };
      Pulse_Lib_Slice_slice__uint8_t left = _letpattern20.fst;
      Pulse_Lib_Slice_slice__uint8_t right = _letpattern20.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern21 = { .fst = left, .snd = right };
      Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern21.fst;
      Pulse_Lib_Slice_slice__uint8_t input3 = _letpattern21.snd;
      __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
      _letpattern10 = { .fst = input1, .snd = { .fst = input2, .snd = input3 } };
      Pulse_Lib_Slice_slice__uint8_t x = _letpattern10.snd.fst;
      is_valid = Parquet_Pulse_Toplevel0_validate_is_PAR1(x);
    }
    else
      is_valid = false;
    size_t off = poffset;
    return off == (size_t)4U && is_valid;
  }
}

bool
Parquet_Pulse_Toplevel0_impl_validate_all0(
  Parquet_Pulse_Toplevel_file_meta_data fmd,
  Pulse_Lib_Slice_slice__uint8_t data
)
{
  size_t footer_start = len__uint8_t(data);
  bool res1 = Parquet_Pulse_Toplevel0_impl_validate_file_meta_data(footer_start, fmd);
  if (res1)
  {
    bool res2 = Parquet_Pulse_Toplevel0_validate_header_magic_number(data);
    if (res2)
    {
      size_t pi = (size_t)0U;
      bool pres = true;
      bool __anf0 = pres;
      bool cond;
      if (__anf0)
      {
        size_t i = pi;
        cond = i < fmd.row_groups.len;
      }
      else
        cond = false;
      while (cond)
      {
        size_t i0 = pi;
        Parquet_Pulse_Toplevel_row_group elt = fmd.row_groups.data[i0];
        bool res = Parquet_Pulse_Toplevel0_impl_validate_all_row_groups(data, elt);
        pres = res;
        if (res)
          pi = i0 + (size_t)1U;
        bool __anf0 = pres;
        bool ite;
        if (__anf0)
        {
          size_t i = pi;
          ite = i < fmd.row_groups.len;
        }
        else
          ite = false;
        cond = ite;
      }
      return pres;
    }
    else
      return false;
  }
  else
    return false;
}

bool
Parquet_Pulse_Toplevel0_impl_validate_all(
  uint32_t len,
  Pulse_Lib_Slice_slice__uint8_t y,
  Pulse_Lib_Slice_slice__uint8_t x
)
{
  KRML_MAYBE_UNUSED_VAR(len);
  Parquet_Pulse_Toplevel_file_meta_data f = Parquet_Pulse_Toplevel0_read_footer(y);
  return Parquet_Pulse_Toplevel0_impl_validate_all0(f, x);
}

static uint8_t op_Array_Access__uint8_t(Pulse_Lib_Slice_slice__uint8_t a, size_t i)
{
  return a.elt[i];
}

bool
Parquet_Pulse_Toplevel0_validate_parquet(Pulse_Lib_Slice_slice__uint8_t input, size_t *poffset)
{
  size_t input_len = len__uint8_t(input);
  size_t offset1 = *poffset;
  if (input_len - offset1 < (size_t)4U)
    return false;
  else
  {
    size_t off = input_len - (size_t)4U;
    size_t poff = off;
    size_t offset20 = poff;
    size_t offset30 = poff;
    bool is_valid0;
    if (len__uint8_t(input) - offset30 < (size_t)4U)
      is_valid0 = false;
    else
    {
      poff = offset30 + (size_t)4U;
      is_valid0 = true;
    }
    bool is_valid2;
    if (is_valid0)
    {
      size_t off1 = poff;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      s_ = split__uint8_t(input, offset20);
      Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern = { .fst = s10, .snd = s20 };
      Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern.fst;
      Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern.snd;
      size_t consumed = off1 - offset20;
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
      Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern11.fst;
      Pulse_Lib_Slice_slice__uint8_t input3 = _letpattern11.snd;
      __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
      _letpattern0 = { .fst = input1, .snd = { .fst = input2, .snd = input3 } };
      Pulse_Lib_Slice_slice__uint8_t x = _letpattern0.snd.fst;
      is_valid2 = Parquet_Pulse_Toplevel0_validate_is_PAR1(x);
    }
    else
      is_valid2 = false;
    if (is_valid2)
    {
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t s_ = split__uint8_t(input, off);
      Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
      Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
      __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
      _letpattern = { .fst = s10, .snd = s20 };
      Pulse_Lib_Slice_slice__uint8_t l = _letpattern.fst;
      size_t input_len1 = len__uint8_t(l);
      size_t offset2 = *poffset;
      bool is_valid10;
      if (input_len1 - offset2 < (size_t)4U)
        is_valid10 = false;
      else
      {
        size_t off1 = input_len1 - (size_t)4U;
        size_t poff1 = off1;
        size_t offset30 = poff1;
        bool is_valid21;
        if (len__uint8_t(l) - offset30 < (size_t)4U)
          is_valid21 = false;
        else
        {
          poff1 = offset30 + (size_t)4U;
          is_valid21 = true;
        }
        if (is_valid21)
        {
          size_t off_ = poff1;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          s_ = split__uint8_t(l, off1);
          Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
          Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern1 = { .fst = s10, .snd = s20 };
          Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern1.fst;
          Pulse_Lib_Slice_slice__uint8_t input230 = _letpattern1.snd;
          size_t consumed0 = off_ - off1;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern2 = split__uint8_t(input230, consumed0);
          Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern2.fst;
          Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern2.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern20 = { .fst = s11, .snd = s21 };
          Pulse_Lib_Slice_slice__uint8_t left0 = _letpattern20.fst;
          Pulse_Lib_Slice_slice__uint8_t right0 = _letpattern20.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern21 = { .fst = left0, .snd = right0 };
          Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern21.fst;
          Pulse_Lib_Slice_slice__uint8_t input30 = _letpattern21.snd;
          __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
          _letpattern10 = { .fst = input10, .snd = { .fst = input20, .snd = input30 } };
          Pulse_Lib_Slice_slice__uint8_t input_ = _letpattern10.snd.fst;
          size_t pos_ = (size_t)1U;
          uint8_t first = op_Array_Access__uint8_t(input_, (size_t)0U);
          size_t pos_1 = pos_ + (size_t)1U;
          uint8_t first1 = op_Array_Access__uint8_t(input_, pos_);
          size_t pos_2 = pos_1 + (size_t)1U;
          uint8_t first2 = op_Array_Access__uint8_t(input_, pos_1);
          uint8_t first3 = op_Array_Access__uint8_t(input_, pos_2);
          uint32_t n = (uint32_t)first3;
          uint32_t bfirst0 = (uint32_t)first2;
          uint32_t n0 = bfirst0 + n * 256U;
          uint32_t bfirst1 = (uint32_t)first1;
          uint32_t n1 = bfirst1 + n0 * 256U;
          uint32_t bfirst = (uint32_t)first;
          uint32_t x = bfirst + n1 * 256U;
          uint32_t x0 = x;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          s_0 = split__uint8_t(l, off1);
          Pulse_Lib_Slice_slice__uint8_t s12 = s_0.fst;
          Pulse_Lib_Slice_slice__uint8_t s22 = s_0.snd;
          __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
          _letpattern11 = { .fst = s12, .snd = s22 };
          Pulse_Lib_Slice_slice__uint8_t l1 = _letpattern11.fst;
          size_t input_len2 = len__uint8_t(l1);
          size_t offset3 = *poffset;
          bool is_valid11;
          if (input_len2 - offset3 < (size_t)x0)
            is_valid11 = false;
          else
          {
            size_t off2 = input_len2 - (size_t)x0;
            size_t poff2 = off2;
            size_t off30 = poff2;
            bool is_valid22;
            if (len__uint8_t(l1) - off30 < (size_t)x0)
              is_valid22 = false;
            else
            {
              size_t off_len = off30 + (size_t)x0;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              s_ = split__uint8_t(l1, off_len);
              Pulse_Lib_Slice_slice__uint8_t s1 = s_.fst;
              Pulse_Lib_Slice_slice__uint8_t s2 = s_.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern2 = { .fst = s1, .snd = s2 };
              Pulse_Lib_Slice_slice__uint8_t inl = _letpattern2.fst;
              bool res = Parquet_Pulse_Toplevel0_validate_footer(inl, &poff2);
              size_t off_1 = poff2;
              is_valid22 = res && off_1 == off_len;
            }
            if (is_valid22)
            {
              size_t off_1 = poff2;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              s_ = split__uint8_t(l1, off2);
              Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
              Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern2 = { .fst = s10, .snd = s20 };
              Pulse_Lib_Slice_slice__uint8_t input10 = _letpattern2.fst;
              Pulse_Lib_Slice_slice__uint8_t input230 = _letpattern2.snd;
              size_t consumed0 = off_1 - off2;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern3 = split__uint8_t(input230, consumed0);
              Pulse_Lib_Slice_slice__uint8_t s11 = _letpattern3.fst;
              Pulse_Lib_Slice_slice__uint8_t s21 = _letpattern3.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern30 = { .fst = s11, .snd = s21 };
              Pulse_Lib_Slice_slice__uint8_t left0 = _letpattern30.fst;
              Pulse_Lib_Slice_slice__uint8_t right0 = _letpattern30.snd;
              __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
              _letpattern31 = { .fst = left0, .snd = right0 };
              Pulse_Lib_Slice_slice__uint8_t input20 = _letpattern31.fst;
              Pulse_Lib_Slice_slice__uint8_t input30 = _letpattern31.snd;
              __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
              _letpattern20 = { .fst = input10, .snd = { .fst = input20, .snd = input30 } };
              Pulse_Lib_Slice_slice__uint8_t y = _letpattern20.snd.fst;
              Pulse_Lib_Slice_slice__uint8_t l2 = _letpattern20.fst;
              size_t offset4 = *poffset;
              *poffset = len__uint8_t(l2);
              bool is_valid = true;
              bool is_valid1;
              if (is_valid)
              {
                size_t off3 = *poffset;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                s_ = split__uint8_t(l2, offset4);
                Pulse_Lib_Slice_slice__uint8_t s10 = s_.fst;
                Pulse_Lib_Slice_slice__uint8_t s20 = s_.snd;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern3 = { .fst = s10, .snd = s20 };
                Pulse_Lib_Slice_slice__uint8_t input1 = _letpattern3.fst;
                Pulse_Lib_Slice_slice__uint8_t input23 = _letpattern3.snd;
                size_t consumed = off3 - offset4;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern4 = split__uint8_t(input23, consumed);
                Pulse_Lib_Slice_slice__uint8_t s1 = _letpattern4.fst;
                Pulse_Lib_Slice_slice__uint8_t s2 = _letpattern4.snd;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern40 = { .fst = s1, .snd = s2 };
                Pulse_Lib_Slice_slice__uint8_t left = _letpattern40.fst;
                Pulse_Lib_Slice_slice__uint8_t right = _letpattern40.snd;
                __Pulse_Lib_Slice_slice_uint8_t_Pulse_Lib_Slice_slice_uint8_t
                _letpattern41 = { .fst = left, .snd = right };
                Pulse_Lib_Slice_slice__uint8_t input2 = _letpattern41.fst;
                Pulse_Lib_Slice_slice__uint8_t input3 = _letpattern41.snd;
                __Pulse_Lib_Slice_slice_uint8_t__Pulse_Lib_Slice_slice_uint8_t___Pulse_Lib_Slice_slice_uint8_t_
                _letpattern30 = { .fst = input1, .snd = { .fst = input2, .snd = input3 } };
                Pulse_Lib_Slice_slice__uint8_t x1 = _letpattern30.snd.fst;
                is_valid1 = Parquet_Pulse_Toplevel0_impl_validate_all(x0, y, x1);
              }
              else
                is_valid1 = false;
              *poffset = input_len2;
              is_valid11 = is_valid1;
            }
            else
              is_valid11 = false;
          }
          *poffset = input_len1;
          is_valid10 = is_valid11;
        }
        else
          is_valid10 = false;
      }
      *poffset = input_len;
      return is_valid10;
    }
    else
      return false;
  }
}

