#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub type cbornondet <'a> = crate::cbornondetveraux::cbor_raw <'a>;

pub fn cbor_nondet_reset_perm <'a>(c: crate::cbornondetveraux::cbor_raw <'a>) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_raw_reset_perm(c) }

fn fst__Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t <'a>(
    x: (&'a [u8], &'a [u8])
) ->
    &'a [u8]
{
    let _1: &[u8] = x.0;
    let __2: &[u8] = x.1;
    _1
}

fn snd__Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t <'a>(
    x: (&'a [u8], &'a [u8])
) ->
    &'a [u8]
{
    let __1: &[u8] = x.0;
    let _2: &[u8] = x.1;
    _2
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·CBOR_Pulse_Raw_EverParse_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (crate::cbornondetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn cbor_nondet_parse <'a>(
    map_key_bound: crate::cbornondetveraux::option__size_t,
    strict_check: bool,
    input: &'a [u8]
) ->
    option__·CBOR_Pulse_Raw_EverParse_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let len: usize =
        crate::cbornondetveraux::cbor_validate_nondet(map_key_bound, strict_check, input);
    if len == 0usize
    {
        option__·CBOR_Pulse_Raw_EverParse_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
    }
    else
    {
        let s·: (&[u8], &[u8]) = input.split_at(len);
        let _letpattern: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s·.0;
                let s2: &[u8] = s·.1;
                (s1,s2)
            };
        let inl: &[u8] = _letpattern.0;
        let inr: &[u8] = _letpattern.1;
        let s1s2: (&[u8], &[u8]) = inl.split_at(len);
        let s1: &[u8] = fst__Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t(s1s2);
        let s2: &[u8] = snd__Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t(s1s2);
        crate::lowstar::ignore::ignore::<&[u8]>(s2);
        let res: crate::cbornondetveraux::cbor_raw = crate::cbornondetveraux::cbor_parse_valid(s1);
        option__·CBOR_Pulse_Raw_EverParse_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: (res,inr) }
    }
}

pub fn cbor_nondet_size(x: crate::cbornondetveraux::cbor_raw, bound: usize) -> usize
{ crate::cbornondetveraux::cbor_nondet_size(x, bound) }

pub fn cbor_nondet_serialize(x: crate::cbornondetveraux::cbor_raw, output: &mut [u8]) ->
    crate::cbornondetveraux::option__size_t
{
    let len: usize = crate::cbornondetveraux::cbor_size(x, output.len());
    if len == 0usize
    { crate::cbornondetveraux::option__size_t::None }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = output.split_at_mut(len);
        let out: &mut [u8] = _letpattern.0;
        let _rem: &[u8] = _letpattern.1;
        let res: usize = crate::cbornondetveraux::cbor_serialize(x, out);
        crate::cbornondetveraux::option__size_t::Some { v: res }
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{
    None,
    Some { v: crate::cbornondetveraux::cbor_raw <'a> }
}

pub fn cbor_nondet_mk_simple_value <'a>(v: u8) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    if
    v <= crate::cbornondetveraux::max_simple_value_additional_info
    ||
    crate::cbornondetveraux::min_simple_value_long_argument <= v
    {
        let res: crate::cbornondetveraux::cbor_raw =
            crate::cbornondetveraux::cbor_mk_simple_value(v);
        option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res }
    }
    else
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_nondet_int_kind
{
    UInt64,
    NegInt64
}

pub fn cbor_nondet_mk_int64 <'a>(ty: cbor_nondet_int_kind, v: u64) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{
    if ty == cbor_nondet_int_kind::UInt64
    { crate::cbornondetveraux::cbor_nondet_mk_uint64(v) }
    else
    { crate::cbornondetveraux::cbor_nondet_mk_neg_int64(v) }
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_nondet_string_kind
{
    ByteString,
    TextString
}

pub fn cbor_impl_utf8_correct(s: &[u8]) -> bool { crate::cbornondetveraux::impl_correct(s) }

pub fn cbor_nondet_mk_string <'a>(ty: cbor_nondet_string_kind, s: &'a [u8]) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    if s.len() > 18446744073709551615u64 as usize
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
    else
    {
        let correct: bool =
            if ty == cbor_nondet_string_kind::TextString { cbor_impl_utf8_correct(s) } else { true };
        if correct
        {
            let ite: u8 =
                if ty == cbor_nondet_string_kind::ByteString
                { crate::cbornondetveraux::cbor_major_type_byte_string }
                else
                { crate::cbornondetveraux::cbor_major_type_text_string };
            let res_raw: crate::cbornondetveraux::cbor_raw =
                crate::cbornondetveraux::cbor_mk_string(ite, s);
            let res: crate::cbornondetveraux::cbor_raw =
                crate::cbornondetveraux::cbor_raw_reset_perm(res_raw);
            option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res }
        }
        else
        { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
    }
}

pub fn cbor_nondet_mk_tagged <'a>(tag: u64, r: &'a [crate::cbornondetveraux::cbor_raw <'a>]) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{
    let tag64: crate::cbornondetveraux::raw_uint64 = crate::cbornondetveraux::mk_raw_uint64(tag);
    crate::lowstar::ignore::ignore::<crate::cbornondetveraux::raw_uint64>(tag64);
    let res_raw: crate::cbornondetveraux::cbor_raw =
        crate::cbornondetveraux::cbor_mk_tagged(tag, r);
    crate::cbornondetveraux::cbor_raw_reset_perm(res_raw)
}

pub type cbor_nondet_map_entry <'a> =
crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>;

pub fn cbor_nondet_mk_map_entry <'a>(
    xk: crate::cbornondetveraux::cbor_raw <'a>,
    xv: crate::cbornondetveraux::cbor_raw <'a>
) ->
    crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_mk_map_entry(xk, xv) }

pub fn cbor_nondet_mk_array <'a>(a: &'a [crate::cbornondetveraux::cbor_raw <'a>]) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    if a.len() > 18446744073709551615u64 as usize
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
    else
    {
        let bml: crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
            { ss: a };
        let ml: crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
            { _0: bml };
        let len_sz: usize = a.len();
        let len64: u64 = len_sz as u64;
        let ru: crate::cbornondetveraux::raw_uint64 = crate::cbornondetveraux::mk_raw_uint64(len64);
        let res_raw: crate::cbornondetveraux::cbor_raw =
            crate::cbornondetveraux::cbor_mk_array(ru.size, ml);
        let res: crate::cbornondetveraux::cbor_raw =
            crate::cbornondetveraux::cbor_raw_reset_perm(res_raw);
        option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res }
    }
}

pub fn cbor_nondet_mk_map <'a>(
    a: &'a [crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>]
) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let mut dest: [crate::cbornondetveraux::cbor_raw; 1] =
        [crate::cbornondetveraux::cbor_raw::CBOR_Case_Invalid; 1usize];
    let bres: bool =
        if a.len() > 18446744073709551615u64 as usize
        { false }
        else
        {
            let correct: bool = crate::cbornondetveraux::cbor_nondet_no_setoid_repeats(a);
            if correct
            {
                let
                bml:
                crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                    { ss: a };
                let
                ml:
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                    { _0: bml };
                let len_sz: usize = a.len();
                let len64: u64 = len_sz as u64;
                let ru: crate::cbornondetveraux::raw_uint64 =
                    crate::cbornondetveraux::mk_raw_uint64(len64);
                let res_raw: crate::cbornondetveraux::cbor_raw =
                    crate::cbornondetveraux::cbor_mk_map(ru.size, ml);
                let res: crate::cbornondetveraux::cbor_raw =
                    crate::cbornondetveraux::cbor_raw_reset_perm(res_raw);
                (&mut dest)[0] = res;
                true
            }
            else
            { false }
        };
    if bres
    {
        let res: crate::cbornondetveraux::cbor_raw = (&dest)[0];
        option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res }
    }
    else
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
}

pub fn cbor_nondet_equal(
    x1: crate::cbornondetveraux::cbor_raw,
    x2: crate::cbornondetveraux::cbor_raw
) ->
    bool
{ crate::cbornondetveraux::cbor_nondet_equal(x1, x2) }

pub fn cbor_nondet_major_type(x: crate::cbornondetveraux::cbor_raw) -> u8
{ crate::cbornondetveraux::cbor_nondet_major_type(x) }

pub type cbor_nondet_array <'a> = crate::cbornondetveraux::cbor_raw <'a>;

pub type cbor_nondet_map <'a> = crate::cbornondetveraux::cbor_raw <'a>;

#[derive(PartialEq, Clone, Copy)]
enum cbor_nondet_view_tags
{
    Int64,
    String,
    Array,
    Map,
    Tagged,
    SimpleValue
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_nondet_view <'a>
{
    Int64 { kind: cbor_nondet_int_kind, value: u64 },
    String { kind: cbor_nondet_string_kind, payload: &'a [u8] },
    Array { _0: crate::cbornondetveraux::cbor_raw <'a> },
    Map { _0: crate::cbornondetveraux::cbor_raw <'a> },
    Tagged { tag: u64, payload: crate::cbornondetveraux::cbor_raw <'a> },
    SimpleValue { _0: u8 }
}

pub fn cbor_nondet_destruct <'a>(c: crate::cbornondetveraux::cbor_raw <'a>) ->
    cbor_nondet_view
    <'a>
{
    let ty: u8 = crate::cbornondetveraux::cbor_nondet_major_type(c);
    if
    ty == crate::cbornondetveraux::cbor_major_type_uint64
    ||
    ty == crate::cbornondetveraux::cbor_major_type_neg_int64
    {
        let k: cbor_nondet_int_kind =
            if ty == crate::cbornondetveraux::cbor_major_type_uint64
            { cbor_nondet_int_kind::UInt64 }
            else
            { cbor_nondet_int_kind::NegInt64 };
        let i: u64 = crate::cbornondetveraux::cbor_raw_read_int64_value(c);
        cbor_nondet_view::Int64 { kind: k, value: i }
    }
    else if
    ty == crate::cbornondetveraux::cbor_major_type_byte_string
    ||
    ty == crate::cbornondetveraux::cbor_major_type_text_string
    {
        let k: cbor_nondet_string_kind =
            if ty == crate::cbornondetveraux::cbor_major_type_byte_string
            { cbor_nondet_string_kind::ByteString }
            else
            { cbor_nondet_string_kind::TextString };
        let s: &[u8] = crate::cbornondetveraux::cbor_raw_get_string(c);
        cbor_nondet_view::String { kind: k, payload: s }
    }
    else if ty == crate::cbornondetveraux::cbor_major_type_array
    {
        let res: crate::cbornondetveraux::cbor_raw = c;
        cbor_nondet_view::Array { _0: res }
    }
    else if ty == crate::cbornondetveraux::cbor_major_type_map
    {
        let res: crate::cbornondetveraux::cbor_raw = c;
        cbor_nondet_view::Map { _0: res }
    }
    else if ty == crate::cbornondetveraux::cbor_major_type_tagged
    {
        let tag: u64 = crate::cbornondetveraux::cbor_raw_read_tagged_tag(c);
        let payload: crate::cbornondetveraux::cbor_raw =
            crate::cbornondetveraux::cbor_raw_get_tagged_payload(c);
        cbor_nondet_view::Tagged { tag, payload }
    }
    else
    {
        let i: u8 = crate::cbornondetveraux::cbor_raw_read_simple_value(c);
        cbor_nondet_view::SimpleValue { _0: i }
    }
}

pub fn cbor_nondet_get_array_length(x: crate::cbornondetveraux::cbor_raw) -> u64
{ crate::cbornondetveraux::cbor_raw_read_array_length(x) }

pub type cbor_nondet_array_iterator_t <'a> =
crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>;

pub fn cbor_nondet_array_iterator_start <'a>(x: crate::cbornondetveraux::cbor_raw <'a>) ->
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let ml: crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
        crate::cbornondetveraux::cbor_raw_get_array(x);
    let total_sz: usize =
        crate::cbornondetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    if total_sz == 0usize
    {
        crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        {
            before:
            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
            after:
            crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
            {
                _0:
                crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
            }
        }
    }
    else
    {
        let
        mut r_node: [crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1]
        =
            [ml; 1usize];
        let mut r_off: [usize; 1] = [0usize; 1usize];
        let mut r_n: [usize; 1] = [total_sz; 1usize];
        let mut pcontinue: [bool; 1] =
            [! crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
                1usize];
        while
        (&pcontinue)[0]
        {
            let node: crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                (&r_node)[0];
            let cur_off_v: usize = (&r_off)[0];
            let cur_n_v: usize = (&r_n)[0];
            match node
            {
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { cb, ca, ob, before, oa, after }
                =>
                  {
                      let child_n_before: usize =
                          crate::cbornondetveraux::append_n_before_sz(cur_off_v, cur_n_v, cb);
                      if child_n_before > 0usize
                      {
                          let child_off_sz: usize =
                              crate::cbornondetveraux::append_off_before_sz(cur_off_v, ob, cb);
                          let
                          ib:
                          crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              before[0];
                          (&mut r_node)[0] = ib;
                          (&mut r_off)[0] = child_off_sz;
                          (&mut r_n)[0] = child_n_before;
                          (&mut pcontinue)[0] =
                              !
                              crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  ib
                              )
                      }
                      else
                      {
                          let child_off_sz: usize =
                              crate::cbornondetveraux::append_off_after_sz(cur_off_v, oa, ca, cb);
                          let child_n_sz: usize =
                              crate::cbornondetveraux::append_n_after_sz(cur_off_v, cur_n_v, cb);
                          let
                          ia:
                          crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              after[0];
                          (&mut r_node)[0] = ia;
                          (&mut r_off)[0] = child_off_sz;
                          (&mut r_n)[0] = child_n_sz;
                          (&mut pcontinue)[0] =
                              !
                              crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  ia
                              )
                      }
                  },
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { .. }
                => (),
                _ => panic!("Incomplete pattern matching")
            }
        };
        let node: crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            (&r_node)[0];
        let cur_off_v: usize = (&r_off)[0];
        let cur_n_v: usize = (&r_n)[0];
        let
        res:
        (crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw, usize)
        =
            match node
            {
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { _0: bi }
                =>
                  {
                      let
                      bi·:
                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                      =
                          match bi
                          {
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                              =>
                                crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                              { sr: s }
                              =>
                                if cur_n_v == 0usize
                                {
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                }
                                else
                                {
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                },
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                              { ss: s }
                              =>
                                {
                                    let
                                    s_pr:
                                    (&[crate::cbornondetveraux::cbor_raw],
                                    &[crate::cbornondetveraux::cbor_raw])
                                    =
                                        s.split_at(cur_off_v);
                                    let _s_prefix: &[crate::cbornondetveraux::cbor_raw] = s_pr.0;
                                    let s_rest: &[crate::cbornondetveraux::cbor_raw] = s_pr.1;
                                    let
                                    s_ms:
                                    (&[crate::cbornondetveraux::cbor_raw],
                                    &[crate::cbornondetveraux::cbor_raw])
                                    =
                                        s_rest.split_at(cur_n_v);
                                    let s_middle: &[crate::cbornondetveraux::cbor_raw] = s_ms.0;
                                    let _s_suffix: &[crate::cbornondetveraux::cbor_raw] = s_ms.1;
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s_middle }
                                },
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                              { payload: pl, .. }
                              =>
                                {
                                    let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                    let n: usize = (&pn)[0];
                                    let mut cond: bool = n > 0usize;
                                    while
                                    cond
                                    {
                                        let n0: usize = (&pn)[0];
                                        let offset: usize = (&poffset)[0];
                                        let offset·: usize =
                                            crate::cbornondetveraux::jump_raw_data_item_eta(
                                                pl,
                                                offset
                                            );
                                        (&mut pn)[0] = n0.wrapping_sub(1usize);
                                        (&mut poffset)[0] = offset·;
                                        let n1: usize = (&pn)[0];
                                        cond = n1 > 0usize
                                    };
                                    let pos: usize = (&poffset)[0];
                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                    let _pl_prefix: &[u8] = pl_p.0;
                                    let pl_suffix: &[u8] = pl_p.1;
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { count: cur_n_v, payload: pl_suffix }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let len: usize =
                          crate::cbornondetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                              bi·
                          );
                      (bi·,len)
                  },
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { .. }
                => panic!("Pulse.Lib.Dv.unreachable"),
                _ => panic!("Incomplete pattern matching")
            };
        let bi·: crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            crate::cbornondetveraux::fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                res
            );
        let len_sz: usize =
            crate::cbornondetveraux::snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                res
            );
        let rest_sz: usize = total_sz.wrapping_sub(len_sz);
        let rest: crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            match ml
            {
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { _0: bi }
                =>
                  {
                      let
                      bi·1:
                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                      =
                          match bi
                          {
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                              =>
                                crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                              { sr: s }
                              =>
                                if rest_sz == 0usize
                                {
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                }
                                else
                                {
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                },
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                              { ss: s }
                              =>
                                {
                                    let
                                    s_pr:
                                    (&[crate::cbornondetveraux::cbor_raw],
                                    &[crate::cbornondetveraux::cbor_raw])
                                    =
                                        s.split_at(len_sz);
                                    let _s_prefix: &[crate::cbornondetveraux::cbor_raw] = s_pr.0;
                                    let s_rest: &[crate::cbornondetveraux::cbor_raw] = s_pr.1;
                                    let
                                    s_ms:
                                    (&[crate::cbornondetveraux::cbor_raw],
                                    &[crate::cbornondetveraux::cbor_raw])
                                    =
                                        s_rest.split_at(rest_sz);
                                    let s_middle: &[crate::cbornondetveraux::cbor_raw] = s_ms.0;
                                    let _s_suffix: &[crate::cbornondetveraux::cbor_raw] = s_ms.1;
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s_middle }
                                },
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                              { payload: pl, .. }
                              =>
                                {
                                    let mut pn: [usize; 1] = [len_sz; 1usize];
                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                    let n: usize = (&pn)[0];
                                    let mut cond: bool = n > 0usize;
                                    while
                                    cond
                                    {
                                        let n0: usize = (&pn)[0];
                                        let offset: usize = (&poffset)[0];
                                        let offset·: usize =
                                            crate::cbornondetveraux::jump_raw_data_item_eta(
                                                pl,
                                                offset
                                            );
                                        (&mut pn)[0] = n0.wrapping_sub(1usize);
                                        (&mut poffset)[0] = offset·;
                                        let n1: usize = (&pn)[0];
                                        cond = n1 > 0usize
                                    };
                                    let pos: usize = (&poffset)[0];
                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                    let _pl_prefix: &[u8] = pl_p.0;
                                    let pl_suffix: &[u8] = pl_p.1;
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { count: rest_sz, payload: pl_suffix }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                      { _0: bi·1 }
                  },
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { cb, ca, ob, before, oa, after }
                =>
                  {
                      let cb·_sz: usize =
                          crate::cbornondetveraux::append_n_before_sz(len_sz, rest_sz, cb);
                      let ca·_sz: usize =
                          crate::cbornondetveraux::append_n_after_sz(len_sz, rest_sz, cb);
                      let ob·_sz: usize =
                          crate::cbornondetveraux::append_off_before_sz(len_sz, ob, cb);
                      let oa·_sz: usize =
                          crate::cbornondetveraux::append_off_after_sz(len_sz, oa, ca, cb);
                      crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                      { cb: cb·_sz, ca: ca·_sz, ob: ob·_sz, before, oa: oa·_sz, after }
                  },
                _ => panic!("Incomplete pattern matching")
            };
        crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        { before: bi·, after: rest }
    }
}

pub fn cbor_nondet_array_iterator_is_empty(
    x: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    bool
{ crate::cbornondetveraux::cbor_nondet_array_iterator_is_empty(x) }

pub fn cbor_nondet_array_iterator_next <'a>(
    x: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
) ->
    (crate::cbornondetveraux::cbor_raw
    <'a>,
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>)
{
    let mut r: [crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
        [x; 1usize];
    let i_cur: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r)[0];
    let
    _letpattern:
    (crate::cbornondetveraux::cbor_raw,
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
    =
        crate::cbornondetveraux::iterator_next_raw_data_item(i_cur);
    let elt: crate::cbornondetveraux::cbor_raw =
        {
            let res: crate::cbornondetveraux::cbor_raw = _letpattern.0;
            let it·: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                _letpattern.1;
            (&mut r)[0] = it·;
            res
        };
    let x·: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r)[0];
    (elt,x·)
}

pub fn cbor_nondet_array_iterator_length(
    x: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    u64
{ crate::cbornondetveraux::cbor_nondet_array_iterator_length(x) }

pub fn cbor_nondet_array_iterator_truncate <'a>(
    x: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>,
    len: u64
) ->
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_array_iterator_truncate(x, len) }

pub fn cbor_nondet_get_array_item <'a>(x: crate::cbornondetveraux::cbor_raw <'a>, i: u64) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let len: u64 = cbor_nondet_get_array_length(x);
    if i >= len
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
    else
    {
        let ml: crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            crate::cbornondetveraux::cbor_raw_get_array(x);
        let total_sz: usize =
            crate::cbornondetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        let it: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            if total_sz == 0usize
            {
                crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                {
                    before:
                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                    after:
                    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                    {
                        _0:
                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                    }
                }
            }
            else
            {
                let
                mut
                r_node:
                [crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1]
                =
                    [ml; 1usize];
                let mut r_off: [usize; 1] = [0usize; 1usize];
                let mut r_n: [usize; 1] = [total_sz; 1usize];
                let mut pcontinue: [bool; 1] =
                    [!
                        crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                            ml
                        );
                        1usize];
                while
                (&pcontinue)[0]
                {
                    let
                    node:
                    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                    =
                        (&r_node)[0];
                    let cur_off_v: usize = (&r_off)[0];
                    let cur_n_v: usize = (&r_n)[0];
                    match node
                    {
                        crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                        { cb, ca, ob, before, oa, after }
                        =>
                          {
                              let child_n_before: usize =
                                  crate::cbornondetveraux::append_n_before_sz(
                                      cur_off_v,
                                      cur_n_v,
                                      cb
                                  );
                              if child_n_before > 0usize
                              {
                                  let child_off_sz: usize =
                                      crate::cbornondetveraux::append_off_before_sz(
                                          cur_off_v,
                                          ob,
                                          cb
                                      );
                                  let
                                  ib:
                                  crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                  =
                                      before[0];
                                  (&mut r_node)[0] = ib;
                                  (&mut r_off)[0] = child_off_sz;
                                  (&mut r_n)[0] = child_n_before;
                                  (&mut pcontinue)[0] =
                                      !
                                      crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                          ib
                                      )
                              }
                              else
                              {
                                  let child_off_sz: usize =
                                      crate::cbornondetveraux::append_off_after_sz(
                                          cur_off_v,
                                          oa,
                                          ca,
                                          cb
                                      );
                                  let child_n_sz: usize =
                                      crate::cbornondetveraux::append_n_after_sz(
                                          cur_off_v,
                                          cur_n_v,
                                          cb
                                      );
                                  let
                                  ia:
                                  crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                  =
                                      after[0];
                                  (&mut r_node)[0] = ia;
                                  (&mut r_off)[0] = child_off_sz;
                                  (&mut r_n)[0] = child_n_sz;
                                  (&mut pcontinue)[0] =
                                      !
                                      crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                          ia
                                      )
                              }
                          },
                        crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                        { .. }
                        => (),
                        _ => panic!("Incomplete pattern matching")
                    }
                };
                let
                node: crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    (&r_node)[0];
                let cur_off_v: usize = (&r_off)[0];
                let cur_n_v: usize = (&r_n)[0];
                let
                res:
                (crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                usize)
                =
                    match node
                    {
                        crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                        { _0: bi }
                        =>
                          {
                              let
                              bi·:
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                              =
                                  match bi
                                  {
                                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                      =>
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                      { sr: s }
                                      =>
                                        if cur_n_v == 0usize
                                        {
                                            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                        }
                                        else
                                        {
                                            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                            { sr: s }
                                        },
                                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                      { ss: s }
                                      =>
                                        {
                                            let
                                            s_pr:
                                            (&[crate::cbornondetveraux::cbor_raw],
                                            &[crate::cbornondetveraux::cbor_raw])
                                            =
                                                s.split_at(cur_off_v);
                                            let _s_prefix: &[crate::cbornondetveraux::cbor_raw] =
                                                s_pr.0;
                                            let s_rest: &[crate::cbornondetveraux::cbor_raw] =
                                                s_pr.1;
                                            let
                                            s_ms:
                                            (&[crate::cbornondetveraux::cbor_raw],
                                            &[crate::cbornondetveraux::cbor_raw])
                                            =
                                                s_rest.split_at(cur_n_v);
                                            let s_middle: &[crate::cbornondetveraux::cbor_raw] =
                                                s_ms.0;
                                            let _s_suffix: &[crate::cbornondetveraux::cbor_raw] =
                                                s_ms.1;
                                            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                            { ss: s_middle }
                                        },
                                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                      { payload: pl, .. }
                                      =>
                                        {
                                            let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                            let mut poffset: [usize; 1] = [0usize; 1usize];
                                            let n: usize = (&pn)[0];
                                            let mut cond: bool = n > 0usize;
                                            while
                                            cond
                                            {
                                                let n0: usize = (&pn)[0];
                                                let offset: usize = (&poffset)[0];
                                                let offset·: usize =
                                                    crate::cbornondetveraux::jump_raw_data_item_eta(
                                                        pl,
                                                        offset
                                                    );
                                                (&mut pn)[0] = n0.wrapping_sub(1usize);
                                                (&mut poffset)[0] = offset·;
                                                let n1: usize = (&pn)[0];
                                                cond = n1 > 0usize
                                            };
                                            let pos: usize = (&poffset)[0];
                                            let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                            let _pl_prefix: &[u8] = pl_p.0;
                                            let pl_suffix: &[u8] = pl_p.1;
                                            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                            { count: cur_n_v, payload: pl_suffix }
                                        },
                                      _ => panic!("Incomplete pattern matching")
                                  };
                              let len1: usize =
                                  crate::cbornondetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                      bi·
                                  );
                              (bi·,len1)
                          },
                        crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                        { .. }
                        => panic!("Pulse.Lib.Dv.unreachable"),
                        _ => panic!("Incomplete pattern matching")
                    };
                let
                bi·:
                crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    crate::cbornondetveraux::fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                        res
                    );
                let len_sz: usize =
                    crate::cbornondetveraux::snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                        res
                    );
                let rest_sz: usize = total_sz.wrapping_sub(len_sz);
                let
                rest: crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    match ml
                    {
                        crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                        { _0: bi }
                        =>
                          {
                              let
                              bi·1:
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                              =
                                  match bi
                                  {
                                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                      =>
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                      { sr: s }
                                      =>
                                        if rest_sz == 0usize
                                        {
                                            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                        }
                                        else
                                        {
                                            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                            { sr: s }
                                        },
                                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                      { ss: s }
                                      =>
                                        {
                                            let
                                            s_pr:
                                            (&[crate::cbornondetveraux::cbor_raw],
                                            &[crate::cbornondetveraux::cbor_raw])
                                            =
                                                s.split_at(len_sz);
                                            let _s_prefix: &[crate::cbornondetveraux::cbor_raw] =
                                                s_pr.0;
                                            let s_rest: &[crate::cbornondetveraux::cbor_raw] =
                                                s_pr.1;
                                            let
                                            s_ms:
                                            (&[crate::cbornondetveraux::cbor_raw],
                                            &[crate::cbornondetveraux::cbor_raw])
                                            =
                                                s_rest.split_at(rest_sz);
                                            let s_middle: &[crate::cbornondetveraux::cbor_raw] =
                                                s_ms.0;
                                            let _s_suffix: &[crate::cbornondetveraux::cbor_raw] =
                                                s_ms.1;
                                            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                            { ss: s_middle }
                                        },
                                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                      { payload: pl, .. }
                                      =>
                                        {
                                            let mut pn: [usize; 1] = [len_sz; 1usize];
                                            let mut poffset: [usize; 1] = [0usize; 1usize];
                                            let n: usize = (&pn)[0];
                                            let mut cond: bool = n > 0usize;
                                            while
                                            cond
                                            {
                                                let n0: usize = (&pn)[0];
                                                let offset: usize = (&poffset)[0];
                                                let offset·: usize =
                                                    crate::cbornondetveraux::jump_raw_data_item_eta(
                                                        pl,
                                                        offset
                                                    );
                                                (&mut pn)[0] = n0.wrapping_sub(1usize);
                                                (&mut poffset)[0] = offset·;
                                                let n1: usize = (&pn)[0];
                                                cond = n1 > 0usize
                                            };
                                            let pos: usize = (&poffset)[0];
                                            let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                            let _pl_prefix: &[u8] = pl_p.0;
                                            let pl_suffix: &[u8] = pl_p.1;
                                            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                            { count: rest_sz, payload: pl_suffix }
                                        },
                                      _ => panic!("Incomplete pattern matching")
                                  };
                              crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                              { _0: bi·1 }
                          },
                        crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                        { cb, ca, ob, before, oa, after }
                        =>
                          {
                              let cb·_sz: usize =
                                  crate::cbornondetveraux::append_n_before_sz(len_sz, rest_sz, cb);
                              let ca·_sz: usize =
                                  crate::cbornondetveraux::append_n_after_sz(len_sz, rest_sz, cb);
                              let ob·_sz: usize =
                                  crate::cbornondetveraux::append_off_before_sz(len_sz, ob, cb);
                              let oa·_sz: usize =
                                  crate::cbornondetveraux::append_off_after_sz(len_sz, oa, ca, cb);
                              crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                              { cb: cb·_sz, ca: ca·_sz, ob: ob·_sz, before, oa: oa·_sz, after }
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                { before: bi·, after: rest }
            };
        let
        mut pit: [crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1]
        =
            [it; 1usize];
        let mut pj: [u64; 1] = [0u64; 1usize];
        let cont0: bool = 0u64 < i;
        let mut pcont: [bool; 1] = [cont0; 1usize];
        while
        (&pcont)[0]
        {
            let i_cur: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                (&pit)[0];
            let
            _letpattern:
            (crate::cbornondetveraux::cbor_raw,
            crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
            =
                crate::cbornondetveraux::iterator_next_raw_data_item(i_cur);
            let elem: crate::cbornondetveraux::cbor_raw =
                {
                    let res: crate::cbornondetveraux::cbor_raw = _letpattern.0;
                    let
                    it·: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                    =
                        _letpattern.1;
                    (&mut pit)[0] = it·;
                    res
                };
            crate::lowstar::ignore::ignore::<crate::cbornondetveraux::cbor_raw>(elem);
            let j_val: u64 = (&pj)[0];
            (&mut pj)[0] = j_val.wrapping_add(1u64);
            let new_cont: bool = j_val.wrapping_add(1u64) < i;
            (&mut pcont)[0] = new_cont
        };
        let i_cur: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            (&pit)[0];
        let
        _letpattern:
        (crate::cbornondetveraux::cbor_raw,
        crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
        =
            crate::cbornondetveraux::iterator_next_raw_data_item(i_cur);
        let res: crate::cbornondetveraux::cbor_raw =
            {
                let res: crate::cbornondetveraux::cbor_raw = _letpattern.0;
                let
                it·: crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    _letpattern.1;
                (&mut pit)[0] = it·;
                res
            };
        option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res }
    }
}

pub fn cbor_nondet_map_length(x: crate::cbornondetveraux::cbor_raw) -> u64
{ crate::cbornondetveraux::cbor_raw_read_map_length(x) }

pub type cbor_nondet_map_iterator_t <'a> =
crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
<'a>;

pub fn cbor_nondet_map_iterator_start <'a>(x: crate::cbornondetveraux::cbor_raw <'a>) ->
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let
    ml:
    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        crate::cbornondetveraux::cbor_raw_get_map(x);
    let total_sz: usize =
        crate::cbornondetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
            ml
        );
    if total_sz == 0usize
    {
        crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        {
            before:
            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
            after:
            crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
            {
                _0:
                crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
            }
        }
    }
    else
    {
        let
        mut
        r_node:
        [crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
        1]
        =
            [ml; 1usize];
        let mut r_off: [usize; 1] = [0usize; 1usize];
        let mut r_n: [usize; 1] = [total_sz; 1usize];
        let mut pcontinue: [bool; 1] =
            [!
                crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                    ml
                );
                1usize];
        while
        (&pcontinue)[0]
        {
            let
            node:
            crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                (&r_node)[0];
            let cur_off_v: usize = (&r_off)[0];
            let cur_n_v: usize = (&r_n)[0];
            match node
            {
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { cb, ca, ob, before, oa, after }
                =>
                  {
                      let child_n_before: usize =
                          crate::cbornondetveraux::append_n_before_sz(cur_off_v, cur_n_v, cb);
                      if child_n_before > 0usize
                      {
                          let child_off_sz: usize =
                              crate::cbornondetveraux::append_off_before_sz(cur_off_v, ob, cb);
                          let
                          ib:
                          crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              before[0];
                          (&mut r_node)[0] = ib;
                          (&mut r_off)[0] = child_off_sz;
                          (&mut r_n)[0] = child_n_before;
                          (&mut pcontinue)[0] =
                              !
                              crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  ib
                              )
                      }
                      else
                      {
                          let child_off_sz: usize =
                              crate::cbornondetveraux::append_off_after_sz(cur_off_v, oa, ca, cb);
                          let child_n_sz: usize =
                              crate::cbornondetveraux::append_n_after_sz(cur_off_v, cur_n_v, cb);
                          let
                          ia:
                          crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              after[0];
                          (&mut r_node)[0] = ia;
                          (&mut r_off)[0] = child_off_sz;
                          (&mut r_n)[0] = child_n_sz;
                          (&mut pcontinue)[0] =
                              !
                              crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  ia
                              )
                      }
                  },
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { .. }
                => (),
                _ => panic!("Incomplete pattern matching")
            }
        };
        let
        node:
        crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        =
            (&r_node)[0];
        let cur_off_v: usize = (&r_off)[0];
        let cur_n_v: usize = (&r_n)[0];
        let
        res:
        (crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        usize)
        =
            match node
            {
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { _0: bi }
                =>
                  {
                      let
                      bi·:
                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                      =
                          match bi
                          {
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                              =>
                                crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                              { sr: s }
                              =>
                                if cur_n_v == 0usize
                                {
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                }
                                else
                                {
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                },
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                              { ss: s }
                              =>
                                {
                                    let
                                    s_pr:
                                    (&[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                    =
                                        s.split_at(cur_off_v);
                                    let
                                    _s_prefix:
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_pr.0;
                                    let
                                    s_rest:
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_pr.1;
                                    let
                                    s_ms:
                                    (&[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                    =
                                        s_rest.split_at(cur_n_v);
                                    let
                                    s_middle:
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_ms.0;
                                    let
                                    _s_suffix:
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_ms.1;
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s_middle }
                                },
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                              { payload: pl, .. }
                              =>
                                {
                                    let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                    let n: usize = (&pn)[0];
                                    let mut cond: bool = n > 0usize;
                                    while
                                    cond
                                    {
                                        let n0: usize = (&pn)[0];
                                        let offset: usize = (&poffset)[0];
                                        let offset·: usize =
                                            crate::cbornondetveraux::jump_nondep_then_raw_data_item_eta(
                                                pl,
                                                offset
                                            );
                                        (&mut pn)[0] = n0.wrapping_sub(1usize);
                                        (&mut poffset)[0] = offset·;
                                        let n1: usize = (&pn)[0];
                                        cond = n1 > 0usize
                                    };
                                    let pos: usize = (&poffset)[0];
                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                    let _pl_prefix: &[u8] = pl_p.0;
                                    let pl_suffix: &[u8] = pl_p.1;
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { count: cur_n_v, payload: pl_suffix }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let len: usize =
                          crate::cbornondetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                              bi·
                          );
                      (bi·,len)
                  },
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { .. }
                => panic!("Pulse.Lib.Dv.unreachable"),
                _ => panic!("Incomplete pattern matching")
            };
        let
        bi·:
        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        =
            crate::cbornondetveraux::fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                res
            );
        let len_sz: usize =
            crate::cbornondetveraux::snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                res
            );
        let rest_sz: usize = total_sz.wrapping_sub(len_sz);
        let
        rest:
        crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        =
            match ml
            {
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { _0: bi }
                =>
                  {
                      let
                      bi·1:
                      crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                      =
                          match bi
                          {
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                              =>
                                crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                              { sr: s }
                              =>
                                if rest_sz == 0usize
                                {
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                }
                                else
                                {
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                },
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                              { ss: s }
                              =>
                                {
                                    let
                                    s_pr:
                                    (&[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                    =
                                        s.split_at(len_sz);
                                    let
                                    _s_prefix:
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_pr.0;
                                    let
                                    s_rest:
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_pr.1;
                                    let
                                    s_ms:
                                    (&[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                    =
                                        s_rest.split_at(rest_sz);
                                    let
                                    s_middle:
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_ms.0;
                                    let
                                    _s_suffix:
                                    &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_ms.1;
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s_middle }
                                },
                              crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                              { payload: pl, .. }
                              =>
                                {
                                    let mut pn: [usize; 1] = [len_sz; 1usize];
                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                    let n: usize = (&pn)[0];
                                    let mut cond: bool = n > 0usize;
                                    while
                                    cond
                                    {
                                        let n0: usize = (&pn)[0];
                                        let offset: usize = (&poffset)[0];
                                        let offset·: usize =
                                            crate::cbornondetveraux::jump_nondep_then_raw_data_item_eta(
                                                pl,
                                                offset
                                            );
                                        (&mut pn)[0] = n0.wrapping_sub(1usize);
                                        (&mut poffset)[0] = offset·;
                                        let n1: usize = (&pn)[0];
                                        cond = n1 > 0usize
                                    };
                                    let pos: usize = (&poffset)[0];
                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                    let _pl_prefix: &[u8] = pl_p.0;
                                    let pl_suffix: &[u8] = pl_p.1;
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { count: rest_sz, payload: pl_suffix }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                      { _0: bi·1 }
                  },
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { cb, ca, ob, before, oa, after }
                =>
                  {
                      let cb·_sz: usize =
                          crate::cbornondetveraux::append_n_before_sz(len_sz, rest_sz, cb);
                      let ca·_sz: usize =
                          crate::cbornondetveraux::append_n_after_sz(len_sz, rest_sz, cb);
                      let ob·_sz: usize =
                          crate::cbornondetveraux::append_off_before_sz(len_sz, ob, cb);
                      let oa·_sz: usize =
                          crate::cbornondetveraux::append_off_after_sz(len_sz, oa, ca, cb);
                      crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                      { cb: cb·_sz, ca: ca·_sz, ob: ob·_sz, before, oa: oa·_sz, after }
                  },
                _ => panic!("Incomplete pattern matching")
            };
        crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        { before: bi·, after: rest }
    }
}

pub fn cbor_nondet_map_iterator_is_empty(
    x:
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    bool
{ crate::cbornondetveraux::cbor_nondet_map_iterator_is_empty(x) }

pub fn cbor_nondet_map_iterator_next <'a>(
    x:
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
) ->
    (crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>,
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>)
{
    let
    mut
    r:
    [crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
    1]
    =
        [x; 1usize];
    let
    i_cur:
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        (&r)[0];
    let
    _letpattern:
    (crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
    =
        crate::cbornondetveraux::iterator_next_map_entry_raw_data_item(i_cur);
    let elt: crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
        {
            let
            res: crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                _letpattern.0;
            let
            it·:
            crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                _letpattern.1;
            (&mut r)[0] = it·;
            res
        };
    let
    x·:
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        (&r)[0];
    (elt,x·)
}

pub fn cbor_nondet_map_entry_key <'a>(
    x2: crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_map_entry_key(x2) }

pub fn cbor_nondet_map_entry_value <'a>(
    x2: crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_map_entry_value(x2) }

pub fn cbor_nondet_map_get <'a>(
    x: crate::cbornondetveraux::cbor_raw <'a>,
    k: crate::cbornondetveraux::cbor_raw <'a>
) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let
    ml:
    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        crate::cbornondetveraux::cbor_raw_get_map(x);
    let total_sz: usize =
        crate::cbornondetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
            ml
        );
    let
    it:
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        if total_sz == 0usize
        {
            crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            {
                before:
                crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                after:
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                {
                    _0:
                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                }
            }
        }
        else
        {
            let
            mut
            r_node:
            [crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
            1]
            =
                [ml; 1usize];
            let mut r_off: [usize; 1] = [0usize; 1usize];
            let mut r_n: [usize; 1] = [total_sz; 1usize];
            let mut pcontinue: [bool; 1] =
                [!
                    crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                        ml
                    );
                    1usize];
            while
            (&pcontinue)[0]
            {
                let
                node:
                crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    (&r_node)[0];
                let cur_off_v: usize = (&r_off)[0];
                let cur_n_v: usize = (&r_n)[0];
                match node
                {
                    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                    { cb, ca, ob, before, oa, after }
                    =>
                      {
                          let child_n_before: usize =
                              crate::cbornondetveraux::append_n_before_sz(cur_off_v, cur_n_v, cb);
                          if child_n_before > 0usize
                          {
                              let child_off_sz: usize =
                                  crate::cbornondetveraux::append_off_before_sz(cur_off_v, ob, cb);
                              let
                              ib:
                              crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                              =
                                  before[0];
                              (&mut r_node)[0] = ib;
                              (&mut r_off)[0] = child_off_sz;
                              (&mut r_n)[0] = child_n_before;
                              (&mut pcontinue)[0] =
                                  !
                                  crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                      ib
                                  )
                          }
                          else
                          {
                              let child_off_sz: usize =
                                  crate::cbornondetveraux::append_off_after_sz(
                                      cur_off_v,
                                      oa,
                                      ca,
                                      cb
                                  );
                              let child_n_sz: usize =
                                  crate::cbornondetveraux::append_n_after_sz(cur_off_v, cur_n_v, cb);
                              let
                              ia:
                              crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                              =
                                  after[0];
                              (&mut r_node)[0] = ia;
                              (&mut r_off)[0] = child_off_sz;
                              (&mut r_n)[0] = child_n_sz;
                              (&mut pcontinue)[0] =
                                  !
                                  crate::cbornondetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                      ia
                                  )
                          }
                      },
                    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                    { .. }
                    => (),
                    _ => panic!("Incomplete pattern matching")
                }
            };
            let
            node:
            crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                (&r_node)[0];
            let cur_off_v: usize = (&r_off)[0];
            let cur_n_v: usize = (&r_n)[0];
            let
            res:
            (crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            usize)
            =
                match node
                {
                    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                    { _0: bi }
                    =>
                      {
                          let
                          bi·:
                          crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              match bi
                              {
                                  crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                  =>
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                  crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                  { sr: s }
                                  =>
                                    if cur_n_v == 0usize
                                    {
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                    }
                                    else
                                    {
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                        { sr: s }
                                    },
                                  crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                  { ss: s }
                                  =>
                                    {
                                        let
                                        s_pr:
                                        (&[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                        =
                                            s.split_at(cur_off_v);
                                        let
                                        _s_prefix:
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_pr.0;
                                        let
                                        s_rest:
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_pr.1;
                                        let
                                        s_ms:
                                        (&[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                        =
                                            s_rest.split_at(cur_n_v);
                                        let
                                        s_middle:
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_ms.0;
                                        let
                                        _s_suffix:
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_ms.1;
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                        { ss: s_middle }
                                    },
                                  crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                  { payload: pl, .. }
                                  =>
                                    {
                                        let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                        let mut poffset: [usize; 1] = [0usize; 1usize];
                                        let n: usize = (&pn)[0];
                                        let mut cond: bool = n > 0usize;
                                        while
                                        cond
                                        {
                                            let n0: usize = (&pn)[0];
                                            let offset: usize = (&poffset)[0];
                                            let offset·: usize =
                                                crate::cbornondetveraux::jump_nondep_then_raw_data_item_eta(
                                                    pl,
                                                    offset
                                                );
                                            (&mut pn)[0] = n0.wrapping_sub(1usize);
                                            (&mut poffset)[0] = offset·;
                                            let n1: usize = (&pn)[0];
                                            cond = n1 > 0usize
                                        };
                                        let pos: usize = (&poffset)[0];
                                        let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                        let _pl_prefix: &[u8] = pl_p.0;
                                        let pl_suffix: &[u8] = pl_p.1;
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                        { count: cur_n_v, payload: pl_suffix }
                                    },
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let len: usize =
                              crate::cbornondetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  bi·
                              );
                          (bi·,len)
                      },
                    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                    { .. }
                    => panic!("Pulse.Lib.Dv.unreachable"),
                    _ => panic!("Incomplete pattern matching")
                };
            let
            bi·:
            crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                crate::cbornondetveraux::fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                    res
                );
            let len_sz: usize =
                crate::cbornondetveraux::snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                    res
                );
            let rest_sz: usize = total_sz.wrapping_sub(len_sz);
            let
            rest:
            crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                match ml
                {
                    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                    { _0: bi }
                    =>
                      {
                          let
                          bi·1:
                          crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              match bi
                              {
                                  crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                  =>
                                    crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                  crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                  { sr: s }
                                  =>
                                    if rest_sz == 0usize
                                    {
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                    }
                                    else
                                    {
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                        { sr: s }
                                    },
                                  crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                  { ss: s }
                                  =>
                                    {
                                        let
                                        s_pr:
                                        (&[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                        =
                                            s.split_at(len_sz);
                                        let
                                        _s_prefix:
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_pr.0;
                                        let
                                        s_rest:
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_pr.1;
                                        let
                                        s_ms:
                                        (&[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                        =
                                            s_rest.split_at(rest_sz);
                                        let
                                        s_middle:
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_ms.0;
                                        let
                                        _s_suffix:
                                        &[crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_ms.1;
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                        { ss: s_middle }
                                    },
                                  crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                  { payload: pl, .. }
                                  =>
                                    {
                                        let mut pn: [usize; 1] = [len_sz; 1usize];
                                        let mut poffset: [usize; 1] = [0usize; 1usize];
                                        let n: usize = (&pn)[0];
                                        let mut cond: bool = n > 0usize;
                                        while
                                        cond
                                        {
                                            let n0: usize = (&pn)[0];
                                            let offset: usize = (&poffset)[0];
                                            let offset·: usize =
                                                crate::cbornondetveraux::jump_nondep_then_raw_data_item_eta(
                                                    pl,
                                                    offset
                                                );
                                            (&mut pn)[0] = n0.wrapping_sub(1usize);
                                            (&mut poffset)[0] = offset·;
                                            let n1: usize = (&pn)[0];
                                            cond = n1 > 0usize
                                        };
                                        let pos: usize = (&poffset)[0];
                                        let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                        let _pl_prefix: &[u8] = pl_p.0;
                                        let pl_suffix: &[u8] = pl_p.1;
                                        crate::cbornondetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                        { count: rest_sz, payload: pl_suffix }
                                    },
                                  _ => panic!("Incomplete pattern matching")
                              };
                          crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                          { _0: bi·1 }
                      },
                    crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                    { cb, ca, ob, before, oa, after }
                    =>
                      {
                          let cb·_sz: usize =
                              crate::cbornondetveraux::append_n_before_sz(len_sz, rest_sz, cb);
                          let ca·_sz: usize =
                              crate::cbornondetveraux::append_n_after_sz(len_sz, rest_sz, cb);
                          let ob·_sz: usize =
                              crate::cbornondetveraux::append_off_before_sz(len_sz, ob, cb);
                          let oa·_sz: usize =
                              crate::cbornondetveraux::append_off_after_sz(len_sz, oa, ca, cb);
                          crate::cbornondetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                          { cb: cb·_sz, ca: ca·_sz, ob: ob·_sz, before, oa: oa·_sz, after }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            { before: bi·, after: rest }
        };
    let
    it0:
    crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        it;
    let
    mut
    pit:
    [crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
    1]
    =
        [it0; 1usize];
    let mut pres: [option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
        [option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None; 1usize];
    let is_empty: bool = crate::cbornondetveraux::cbor_nondet_map_iterator_is_empty(it0);
    let cont0: bool = ! is_empty;
    let mut pcont: [bool; 1] = [cont0; 1usize];
    while
    (&pcont)[0]
    {
        let
        i_cur:
        crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        =
            (&pit)[0];
        let
        _letpattern:
        (crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
        =
            crate::cbornondetveraux::iterator_next_map_entry_raw_data_item(i_cur);
        let entry: crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            {
                let
                res: crate::cbornondetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    _letpattern.0;
                let
                it·:
                crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    _letpattern.1;
                (&mut pit)[0] = it·;
                res
            };
        let key: crate::cbornondetveraux::cbor_raw =
            crate::cbornondetveraux::cbor_nondet_map_entry_key(entry);
        let eq: bool = crate::cbornondetveraux::cbor_nondet_equal(key, k);
        if eq
        {
            let value: crate::cbornondetveraux::cbor_raw =
                crate::cbornondetveraux::cbor_nondet_map_entry_value(entry);
            (&mut pres)[0] = option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: value };
            (&mut pcont)[0] = false
        }
        else
        {
            let
            i·:
            crate::cbornondetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                (&pit)[0];
            let is_empty·: bool = crate::cbornondetveraux::cbor_nondet_map_iterator_is_empty(i·);
            let cont·: bool = ! is_empty·;
            (&mut pcont)[0] = cont·
        }
    };
    (&pres)[0]
}

pub fn dummy_cbor_nondet_t <'a>() -> crate::cbornondetveraux::cbor_raw <'a>
{ crate::cbornondetveraux::cbor_raw::CBOR_Case_Invalid }
