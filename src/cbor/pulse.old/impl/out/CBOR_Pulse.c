/*
   Copyright 2023, 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/


#include "internal/CBOR_Pulse.h"

int16_t CBOR_Pulse_byte_array_compare(size_t sz, uint8_t *a1, uint8_t *a2)
{
  size_t pi = (size_t)0U;
  int16_t pres = (int16_t)0;
  size_t i0 = pi;
  int16_t res0 = pres;
  bool cond = i0 < sz && res0 == (int16_t)0;
  while (cond)
  {
    size_t i = pi;
    uint8_t x1 = a1[i];
    uint8_t x2 = a2[i];
    int16_t res0;
    if (x1 == x2)
      res0 = (int16_t)0;
    else if (x1 < x2)
      res0 = (int16_t)-1;
    else
      res0 = (int16_t)1;
    pi = i + (size_t)1U;
    pres = res0;
    size_t i0 = pi;
    int16_t res = pres;
    cond = i0 < sz && res == (int16_t)0;
  }
  return pres;
}

int16_t CBOR_Pulse_cbor_compare(cbor a1, cbor a2)
{
  int16_t test = cbor_compare_aux(a1, a2);
  int16_t _bind_c0;
  if (test == (int16_t)-1 || test == (int16_t)0 || test == (int16_t)1)
    _bind_c0 = test;
  else
  {
    uint8_t ty1 = cbor_get_major_type(a1);
    uint8_t ty2 = cbor_get_major_type(a2);
    int16_t c;
    if (ty1 == ty2)
      c = (int16_t)0;
    else if (ty1 < ty2)
      c = (int16_t)-1;
    else
      c = (int16_t)1;
    int16_t _bind_c1;
    if (c != (int16_t)0)
      _bind_c1 = c;
    else
    {
      int16_t _if_br0;
      if (ty1 == CBOR_MAJOR_TYPE_UINT64 || ty1 == CBOR_MAJOR_TYPE_NEG_INT64)
      {
        cbor_int i1 = cbor_destr_int64(a1);
        cbor_int i2 = cbor_destr_int64(a2);
        int16_t _bind_c;
        if (i1.cbor_int_value == i2.cbor_int_value)
          _bind_c = (int16_t)0;
        else if (i1.cbor_int_value < i2.cbor_int_value)
          _bind_c = (int16_t)-1;
        else
          _bind_c = (int16_t)1;
        int16_t _if_br = _bind_c;
        _if_br0 = _if_br;
      }
      else
      {
        int16_t _if_br1;
        if (ty1 == CBOR_MAJOR_TYPE_SIMPLE_VALUE)
        {
          uint8_t i1 = cbor_destr_simple_value(a1);
          uint8_t i2 = cbor_destr_simple_value(a2);
          int16_t _bind_c;
          if (i1 == i2)
            _bind_c = (int16_t)0;
          else if (i1 < i2)
            _bind_c = (int16_t)-1;
          else
            _bind_c = (int16_t)1;
          int16_t _if_br = _bind_c;
          _if_br1 = _if_br;
        }
        else
        {
          int16_t _if_br0;
          if (ty1 == CBOR_MAJOR_TYPE_BYTE_STRING || ty1 == CBOR_MAJOR_TYPE_TEXT_STRING)
          {
            cbor_string s1 = cbor_destr_string(a1);
            cbor_string s2 = cbor_destr_string(a2);
            int16_t c1;
            if (s1.cbor_string_length == s2.cbor_string_length)
              c1 = (int16_t)0;
            else if (s1.cbor_string_length < s2.cbor_string_length)
              c1 = (int16_t)-1;
            else
              c1 = (int16_t)1;
            int16_t _bind_c;
            if (c1 != (int16_t)0)
              _bind_c = c1;
            else
            {
              int16_t
              test1 =
                CBOR_Pulse_byte_array_compare((size_t)s1.cbor_string_length,
                  s1.cbor_string_payload,
                  s2.cbor_string_payload);
              int16_t _bind_c0 = test1;
              int16_t _bind_c1 = _bind_c0;
              int16_t _if_br = _bind_c1;
              _bind_c = _if_br;
            }
            int16_t _bind_c0 = _bind_c;
            int16_t _bind_c1 = _bind_c0;
            int16_t _if_br = _bind_c1;
            _if_br0 = _if_br;
          }
          else
          {
            int16_t _if_br1;
            if (ty1 == CBOR_MAJOR_TYPE_ARRAY)
            {
              uint64_t len1 = cbor_array_length(a1);
              uint64_t len2 = cbor_array_length(a2);
              int16_t c1;
              if (len1 == len2)
                c1 = (int16_t)0;
              else if (len1 < len2)
                c1 = (int16_t)-1;
              else
                c1 = (int16_t)1;
              int16_t _bind_c;
              if (c1 != (int16_t)0)
                _bind_c = c1;
              else
              {
                cbor_array_iterator_t i10 = cbor_array_iterator_init(a1);
                cbor_array_iterator_t i20 = cbor_array_iterator_init(a2);
                bool done0 = cbor_array_iterator_is_done(i10);
                cbor_array_iterator_t pi1 = i10;
                cbor_array_iterator_t pi2 = i20;
                bool pdone = done0;
                int16_t pres = (int16_t)0;
                bool done = pdone;
                int16_t res0 = pres;
                bool cond = res0 == (int16_t)0 && !done;
                while (cond)
                {
                  cbor x1 = cbor_array_iterator_next(&pi1);
                  cbor x2 = cbor_array_iterator_next(&pi2);
                  int16_t res0 = CBOR_Pulse_cbor_compare(x1, x2);
                  if (res0 == (int16_t)0)
                  {
                    cbor_array_iterator_t i1 = pi1;
                    bool done = cbor_array_iterator_is_done(i1);
                    pdone = done;
                  }
                  else
                    pres = res0;
                  bool done = pdone;
                  int16_t res = pres;
                  cond = res == (int16_t)0 && !done;
                }
                int16_t pres1 = pres;
                int16_t pdone1 = pres1;
                int16_t pi21 = pdone1;
                int16_t pi11 = pi21;
                int16_t _bind_c0 = pi11;
                int16_t _bind_c1 = _bind_c0;
                int16_t _bind_c2 = _bind_c1;
                int16_t _if_br = _bind_c2;
                _bind_c = _if_br;
              }
              int16_t _bind_c0 = _bind_c;
              int16_t _bind_c1 = _bind_c0;
              int16_t _if_br = _bind_c1;
              _if_br1 = _if_br;
            }
            else
            {
              int16_t _if_br0;
              if (ty1 == CBOR_MAJOR_TYPE_TAGGED)
              {
                cbor_tagged tg1 = cbor_destr_tagged(a1);
                cbor_tagged tg2 = cbor_destr_tagged(a2);
                int16_t c1;
                if (tg1.cbor_tagged_tag == tg2.cbor_tagged_tag)
                  c1 = (int16_t)0;
                else if (tg1.cbor_tagged_tag < tg2.cbor_tagged_tag)
                  c1 = (int16_t)-1;
                else
                  c1 = (int16_t)1;
                int16_t _bind_c;
                if (c1 != (int16_t)0)
                  _bind_c = c1;
                else
                {
                  int16_t
                  test1 = CBOR_Pulse_cbor_compare(tg1.cbor_tagged_payload, tg2.cbor_tagged_payload);
                  int16_t _if_br = test1;
                  _bind_c = _if_br;
                }
                int16_t _bind_c0 = _bind_c;
                int16_t _bind_c1 = _bind_c0;
                int16_t _if_br = _bind_c1;
                _if_br0 = _if_br;
              }
              else
              {
                int16_t _if_br;
                if (ty1 == CBOR_MAJOR_TYPE_MAP)
                {
                  uint64_t len1 = cbor_map_length(a1);
                  uint64_t len2 = cbor_map_length(a2);
                  int16_t c1;
                  if (len1 == len2)
                    c1 = (int16_t)0;
                  else if (len1 < len2)
                    c1 = (int16_t)-1;
                  else
                    c1 = (int16_t)1;
                  int16_t _bind_c;
                  if (c1 != (int16_t)0)
                    _bind_c = c1;
                  else
                  {
                    cbor_map_iterator_t i10 = cbor_map_iterator_init(a1);
                    cbor_map_iterator_t i20 = cbor_map_iterator_init(a2);
                    bool done0 = cbor_map_iterator_is_done(i10);
                    cbor_map_iterator_t pi1 = i10;
                    cbor_map_iterator_t pi2 = i20;
                    bool pdone = done0;
                    int16_t pres = (int16_t)0;
                    bool done = pdone;
                    int16_t res0 = pres;
                    bool cond = res0 == (int16_t)0 && !done;
                    while (cond)
                    {
                      cbor_map_entry x1 = cbor_map_iterator_next(&pi1);
                      cbor_map_entry x2 = cbor_map_iterator_next(&pi2);
                      int16_t
                      test1 =
                        CBOR_Pulse_cbor_compare(cbor_map_entry_key(x1),
                          cbor_map_entry_key(x2));
                      if (test1 == (int16_t)0)
                      {
                        int16_t
                        test2 =
                          CBOR_Pulse_cbor_compare(cbor_map_entry_value(x1),
                            cbor_map_entry_value(x2));
                        pres = test2;
                      }
                      else
                        pres = test1;
                      int16_t res0 = pres;
                      if (res0 == (int16_t)0)
                      {
                        cbor_map_iterator_t i1 = pi1;
                        bool done = cbor_map_iterator_is_done(i1);
                        pdone = done;
                      }
                      bool done = pdone;
                      int16_t res = pres;
                      cond = res == (int16_t)0 && !done;
                    }
                    int16_t pres1 = pres;
                    int16_t pdone1 = pres1;
                    int16_t pi21 = pdone1;
                    int16_t pi11 = pi21;
                    int16_t _bind_c0 = pi11;
                    int16_t _bind_c1 = _bind_c0;
                    int16_t _bind_c2 = _bind_c1;
                    int16_t _if_br = _bind_c2;
                    _bind_c = _if_br;
                  }
                  int16_t _bind_c0 = _bind_c;
                  int16_t _bind_c1 = _bind_c0;
                  int16_t _if_br0 = _bind_c1;
                  _if_br = _if_br0;
                }
                else
                  _if_br = (int16_t)2;
                _if_br0 = _if_br;
              }
              _if_br1 = _if_br0;
            }
            _if_br0 = _if_br1;
          }
          _if_br1 = _if_br0;
        }
        _if_br0 = _if_br1;
      }
      _bind_c1 = _if_br0;
    }
    int16_t _bind_c = _bind_c1;
    int16_t _bind_c2 = _bind_c;
    int16_t _if_br = _bind_c2;
    _bind_c0 = _if_br;
  }
  int16_t _fret = _bind_c0;
  return _fret;
}

bool CBOR_Pulse_cbor_is_equal(cbor a1, cbor a2)
{
  int16_t test = CBOR_Pulse_cbor_compare(a1, a2);
  return test == (int16_t)0;
}

CBOR_Pulse_cbor_map_get_t CBOR_Pulse_cbor_map_get(cbor key, cbor map)
{
  cbor_map_iterator_t i0 = cbor_map_iterator_init(map);
  bool done0 = cbor_map_iterator_is_done(i0);
  cbor_map_iterator_t pi = i0;
  CBOR_Pulse_cbor_map_get_t pres = { .tag = CBOR_Pulse_NotFound };
  bool pdone = done0;
  CBOR_Pulse_cbor_map_get_t res = pres;
  bool done1 = pdone;
  bool res_found0;
  if (res.tag == CBOR_Pulse_Found)
    res_found0 = true;
  else
    res_found0 = false;
  bool cond = !(done1 || res_found0);
  while (cond)
  {
    cbor_map_entry x = cbor_map_iterator_next(&pi);
    bool test = CBOR_Pulse_cbor_is_equal(key, cbor_map_entry_key(x));
    if (test)
      pres = ((CBOR_Pulse_cbor_map_get_t){ .tag = CBOR_Pulse_Found, ._0 = cbor_map_entry_value(x) });
    else
    {
      cbor_map_iterator_t i_ = pi;
      bool done = cbor_map_iterator_is_done(i_);
      pdone = done;
    }
    CBOR_Pulse_cbor_map_get_t res = pres;
    bool done = pdone;
    bool res_found;
    if (res.tag == CBOR_Pulse_Found)
      res_found = true;
    else
      res_found = false;
    cond = !(done || res_found);
  }
  return pres;
}

static bool cbor_map_sort_merge(cbor_map_entry *a, size_t lo, size_t mi, size_t hi)
{
  size_t pi1 = lo;
  size_t pi2 = mi;
  bool pres = true;
  size_t i10 = pi1;
  size_t i20 = pi2;
  bool res0 = pres;
  bool cond = res0 && !(i10 == i20 || i20 == hi);
  while (cond)
  {
    size_t i1 = pi1;
    cbor_map_entry x1 = a[i1];
    size_t i20 = pi2;
    cbor_map_entry x2 = a[i20];
    int16_t comp = CBOR_Pulse_cbor_compare(cbor_map_entry_key(x1), cbor_map_entry_key(x2));
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
      size_t _bind_c;
      if (i1 == i20)
        _bind_c = i2_;
      else
      {
        size_t _if_br;
        if (i20 == i2_)
          _if_br = i1;
        else
        {
          size_t pn = i2_ - i1;
          size_t pl = i20 - i1;
          size_t l0 = pl;
          bool cond = l0 > (size_t)0U;
          while (cond)
          {
            size_t n = pn;
            size_t l = pl;
            size_t l_ = n % l;
            pn = l;
            pl = l_;
            size_t l0 = pl;
            cond = l0 > (size_t)0U;
          }
          size_t pl1 = pn;
          size_t pn1 = pl1;
          size_t _fret = pn1;
          size_t d = _fret;
          size_t q = (i2_ - i1) / d;
          size_t pi = i1;
          size_t i0 = pi;
          bool cond0 = i0 - i1 < d;
          while (cond0)
          {
            size_t i = pi;
            cbor_map_entry save = a[i];
            size_t pj = (size_t)0U;
            size_t pidx = i;
            size_t j0 = pj;
            bool cond = j0 < q - (size_t)1U;
            while (cond)
            {
              size_t j = pj;
              size_t idx = pidx;
              size_t idx_;
              if (idx - i1 >= i2_ - i20)
                idx_ = idx - (i2_ - i20);
              else
                idx_ = idx + i20 - i1;
              cbor_map_entry x = a[idx_];
              size_t j_ = j + (size_t)1U;
              a[idx] = x;
              pj = j_;
              pidx = idx_;
              size_t j0 = pj;
              cond = j0 < q - (size_t)1U;
            }
            size_t idx = pidx;
            a[idx] = save;
            size_t i_ = i + (size_t)1U;
            pi = i_;
            size_t i0 = pi;
            cond0 = i0 - i1 < d;
          }
          size_t _bind_c = i1 + i2_ - i20;
          size_t _bind_c0 = _bind_c;
          size_t _bind_c1 = _bind_c0;
          size_t _bind_c2 = _bind_c1;
          size_t _bind_c3 = _bind_c2;
          size_t _if_br0 = _bind_c3;
          _if_br = _if_br0;
        }
        _bind_c = _if_br;
      }
      size_t _bind_c0 = _bind_c;
      size_t _bind_c1 = _bind_c0;
      size_t _fret = _bind_c1;
      size_t i1_ = _fret;
      pi1 = i1_;
      pi2 = i2_;
    }
    size_t i10 = pi1;
    size_t i2 = pi2;
    bool res = pres;
    cond = res && !(i10 == i2 || i2 == hi);
  }
  return pres;
}

bool CBOR_Pulse_cbor_map_sort_aux(cbor_map_entry *a, size_t lo, size_t hi)
{
  size_t len = hi - lo;
  bool _bind_c0;
  if (len < (size_t)2U)
    _bind_c0 = true;
  else
  {
    size_t len_half = len / (size_t)2U;
    size_t mi = lo + len_half;
    bool res = CBOR_Pulse_cbor_map_sort_aux(a, lo, mi);
    bool _bind_c1;
    if (!res)
      _bind_c1 = false;
    else
    {
      bool res1 = CBOR_Pulse_cbor_map_sort_aux(a, mi, hi);
      bool _bind_c;
      if (!res1)
        _bind_c = false;
      else
      {
        bool _if_br = cbor_map_sort_merge(a, lo, mi, hi);
        _bind_c = _if_br;
      }
      bool _bind_c0 = _bind_c;
      bool _if_br = _bind_c0;
      _bind_c1 = _if_br;
    }
    bool _bind_c = _bind_c1;
    bool _bind_c2 = _bind_c;
    bool _bind_c3 = _bind_c2;
    bool _bind_c4 = _bind_c3;
    bool _bind_c5 = _bind_c4;
    bool _bind_c6 = _bind_c5;
    bool _bind_c7 = _bind_c6;
    bool _bind_c8 = _bind_c7;
    bool _bind_c9 = _bind_c8;
    bool _if_br = _bind_c9;
    _bind_c0 = _if_br;
  }
  bool _bind_c = _bind_c0;
  bool _bind_c1 = _bind_c;
  bool _bind_c2 = _bind_c1;
  bool _fret = _bind_c2;
  return _fret;
}

bool CBOR_Pulse_cbor_map_sort(cbor_map_entry *a, size_t len)
{
  bool res = CBOR_Pulse_cbor_map_sort_aux(a, (size_t)0U, len);
  return res;
}

